use std::collections::{BTreeSet, HashMap, HashSet};
use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Stdio};
use std::sync::{Arc, Mutex, Weak};
use std::time::{Instant, UNIX_EPOCH};

use anyhow::{Context, Result, bail, ensure};
use serde::{Deserialize, Serialize};

use crate::git::{dirty_lean_files, lake_command, merge_in_progress, project_lean_files};
use crate::issue::{TelemetryOperation, TelemetryStore, development_enabled};
use crate::repo::Repo;
use crate::state::{
    CheckProfile, CheckRecord, CheckRun, Diagnostic, FileCheckProfile, State, Workspace,
};
use crate::util::{hash_bytes, hash_file, now_unix_ms};

const WORKER_SOURCE: &str = r#"import Lean.Language.Lean
import Lean.Setup

open Lean Lean.Elab

structure Request where
  source : String
  version : Nat
deriving FromJson

structure Diagnostic where
  severity : String
  kind : String
  text : String
deriving ToJson

structure Response where
  ok : Bool
  diagnostics : Array Diagnostic
  version : Nat
deriving ToJson

def setupImports (setup : ModuleSetup) (stx : HeaderSyntax) :
    Language.ProcessingT IO
      (Except Language.Lean.HeaderProcessedSnapshot Language.Lean.SetupImportsResult) := do
  let header := stx.toModuleHeader
  return .ok {
    mainModuleName := setup.name
    isModule := setup.isModule || header.isModule
    imports := setup.imports?.getD header.imports
    opts := Elab.async.setIfNotSet setup.options.toOptions true
    importArts := setup.importArts
    plugins := setup.plugins
  }

partial def collectTree (tree : Language.SnapshotTree) : BaseIO MessageLog := do
  let mut messages := tree.element.diagnostics.msgLog
  for child in tree.children do
    messages := messages ++ (← collectTree child.get)
  return messages

partial def firstErrorOrFinal (task : Language.SnapshotTask Language.Lean.CommandParsedSnapshot) :
    BaseIO (Bool × MessageLog) := do
  let command := task.get
  let result := command.elabSnap.resultSnap.get
  if result.cmdState.messages.hasErrors then
    command.elabSnap.elabSnap.cancelRec
    command.elabSnap.infoTreeSnap.cancelRec
    command.elabSnap.reportSnap.cancelRec
    if let some next := command.nextCmdSnap? then next.cancelRec
    return (true, result.cmdState.messages)
  if let some next := command.nextCmdSnap? then
    firstErrorOrFinal next
  else
    return (false, result.cmdState.messages)

def renderMessages (messages : MessageLog) : BaseIO (Array Diagnostic) := do
  let mut output := #[]
  for message in messages.reportedPlusUnreported do
    output := output.push {
      severity := message.severity.toString
      kind := message.kind.toString
      text := ← message.toString
    }
  return output

def failureResponse (detail : String) (version : Nat) : Response :=
  { ok := false,
    diagnostics := #[{ severity := "error", kind := "mathmux", text := detail }],
    version := version }

def processSnapshot (snapshot : Language.Lean.InitialSnapshot) (version : Nat) : BaseIO Response := do
  let some header := snapshot.result? | return ← failureWithDiagnostics snapshot "header parsing failed" version
  let processed := header.processedSnap.get
  let some processed := processed.result? | return ← failureWithDiagnostics snapshot "import processing failed" version
  let (failed, commandMessages) ← firstErrorOrFinal processed.firstCmdSnap
  let messages ← if failed then pure commandMessages else collectTree (Language.toSnapshotTree snapshot)
  let diagnostics ← renderMessages messages
  return { ok := !messages.hasErrors, diagnostics, version := version }

where
  failureWithDiagnostics (snapshot : Language.Lean.InitialSnapshot) (detail : String)
      (version : Nat) : BaseIO Response := do
    let messages ← collectTree (Language.toSnapshotTree snapshot)
    let diagnostics ← renderMessages messages
    if diagnostics.isEmpty then
      return failureResponse detail version
    return { ok := false, diagnostics, version := version }

def writeResponse (response : Response) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStrLn (toJson response).compress
  stdout.flush

unsafe def runServer (setup : ModuleSetup) : IO Unit := do
  enableInitializersExecution
  setup.dynlibs.forM loadDynlib
  let processor ← Language.mkIncrementalProcessor (Language.Lean.process (setupImports setup))
  let stdin ← IO.getStdin
  let rec loop : IO Unit := do
    let line ← stdin.getLine
    if line.isEmpty then return
    if line.trimAscii.isEmpty then loop else
    match Json.parse line >>= fromJson? with
    | .error error =>
      writeResponse (failureResponse error 0)
      loop
    | .ok (request : Request) =>
      let snapshot ← processor (Parser.mkInputContext request.source setup.name.toString)
      writeResponse (← processSnapshot snapshot request.version)
      loop
  loop

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | [setupPath] => runServer (← ModuleSetup.load setupPath); return 0
  | _ => IO.eprintln "usage: MathmuxWorker SETUP_JSON"; return 2
"#;
const CHECK_RESULT_VERSION: &[u8] = b"check-result-v2";

#[derive(Debug, Clone)]
pub struct CheckOutcome {
    pub reference: String,
    pub ok: bool,
    pub elapsed_ms: u64,
    pub warnings: Vec<Diagnostic>,
    pub linters: Vec<Diagnostic>,
    pub suggestions: Vec<Diagnostic>,
    pub diagnostics: Vec<Diagnostic>,
    pub profile: Option<CheckProfile>,
}

#[derive(Debug, Serialize)]
struct WorkerRequest<'a> {
    source: &'a str,
    version: u64,
}

#[derive(Debug, Clone, Deserialize)]
struct WorkerResponse {
    ok: bool,
    diagnostics: Vec<WorkerDiagnostic>,
    version: u64,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq, Hash)]
struct WorkerDiagnostic {
    severity: String,
    kind: String,
    text: String,
}

struct FileCheck {
    certificate: CheckRecord,
    warnings: Vec<Diagnostic>,
    linters: Vec<Diagnostic>,
    suggestions: Vec<Diagnostic>,
    diagnostics: Vec<Diagnostic>,
    ok: bool,
    profile: FileCheckProfile,
}

#[derive(Debug, Deserialize)]
struct LakeSetup {
    name: String,
}

struct FileSetup {
    path: PathBuf,
}

type WorkerKey = (String, PathBuf);
type CheckLocks = Mutex<HashMap<WorkerKey, Weak<Mutex<()>>>>;

pub struct Checker {
    repo: Repo,
    state: State,
    workers: Mutex<HashMap<WorkerKey, Arc<Mutex<LeanWorker>>>>,
    check_locks: CheckLocks,
    setup_locks: Mutex<HashMap<String, Weak<Mutex<()>>>>,
}

impl Checker {
    pub fn new(repo: Repo, state: State) -> Result<Self> {
        let worker_path = repo.state_dir.join("MathmuxWorker.lean");
        if fs::read_to_string(&worker_path).ok().as_deref() != Some(WORKER_SOURCE) {
            fs::write(&worker_path, WORKER_SOURCE)
                .with_context(|| format!("cannot write {}", worker_path.display()))?;
        }
        Ok(Self {
            repo,
            state,
            workers: Mutex::new(HashMap::new()),
            check_locks: Mutex::new(HashMap::new()),
            setup_locks: Mutex::new(HashMap::new()),
        })
    }

    pub fn check(
        &self,
        workspace: &Workspace,
        requested: Option<&Path>,
        include_profile: bool,
    ) -> Result<CheckOutcome> {
        let started = Instant::now();
        let targets = match requested {
            Some(path) => vec![resolve_target(&workspace.path, path)?],
            None => {
                ensure!(
                    !merge_in_progress(&workspace.path),
                    "workspace has an unfinished sync; check the conflicted files, then rerun mathmux sync"
                );
                let files = dirty_lean_files(&workspace.path)?;
                ensure!(!files.is_empty(), "workspace has no dirty Lean files");
                dependency_order(&workspace.path, &files)?
            }
        };
        let planning_ms = started.elapsed().as_millis() as u64;
        let reference = self.state.next_ref('c')?;
        let files = targets
            .iter()
            .map(|path| path.to_string_lossy().into_owned())
            .collect::<Vec<_>>();
        let mut certificates = Vec::new();
        let mut passed = Vec::new();
        let mut warnings = Vec::new();
        let mut linters = Vec::new();
        let mut suggestions = Vec::new();
        let mut diagnostics = Vec::new();
        let mut failed = None;
        let mut file_profiles = Vec::new();

        for target in &targets {
            let target_name = target.to_string_lossy().into_owned();
            match self.check_one(workspace, target, &reference) {
                Ok(result) => {
                    file_profiles.push(result.profile.clone());
                    warnings.extend(result.warnings);
                    linters.extend(result.linters);
                    suggestions.extend(result.suggestions);
                    if result.ok {
                        passed.push(target_name);
                        certificates.push(result.certificate);
                    } else {
                        diagnostics.extend(result.diagnostics);
                        failed = Some(target_name);
                        break;
                    }
                }
                Err(error) => {
                    diagnostics.push(Diagnostic {
                        kind: "mathmux".into(),
                        text: format!("{error:#}"),
                        context: None,
                    });
                    failed = Some(target_name);
                    break;
                }
            }
        }
        deduplicate(&mut warnings);
        deduplicate(&mut linters);
        deduplicate(&mut suggestions);
        deduplicate(&mut diagnostics);
        let elapsed_ms = started.elapsed().as_millis() as u64;
        let ok = failed.is_none();
        let not_checked = failed
            .as_ref()
            .and_then(|target| files.iter().position(|file| file == target))
            .map(|index| files[index + 1..].to_vec())
            .unwrap_or_default();
        let run = CheckRun {
            reference: reference.clone(),
            workspace_ref: workspace.reference.clone(),
            status: if ok { "passed" } else { "failed" }.into(),
            files,
            passed,
            failed,
            not_checked,
            warnings: warnings.clone(),
            linters: linters.clone(),
            suggestions: suggestions.clone(),
            diagnostics: diagnostics.clone(),
            profile: include_profile.then_some(CheckProfile {
                planning_ms,
                files: file_profiles,
            }),
            duration_ms: elapsed_ms,
            created_at: now_unix_ms(),
        };
        self.state
            .add_check_run(&run, if ok { &certificates } else { &[] })?;
        self.state.touch_workspace(&workspace.reference)?;
        Ok(CheckOutcome {
            reference,
            ok,
            elapsed_ms,
            warnings,
            linters,
            suggestions,
            diagnostics,
            profile: run.profile,
        })
    }

    fn check_one(
        &self,
        workspace: &Workspace,
        target: &Path,
        reference: &str,
    ) -> Result<FileCheck> {
        let file_started = Instant::now();
        let check_lock = {
            let key = (workspace.reference.clone(), target.to_path_buf());
            let mut locks = self.check_locks.lock().expect("check lock map poisoned");
            locks.retain(|_, lock| lock.strong_count() > 0);
            locks.entry(key.clone()).or_default().upgrade().unwrap_or_else(|| {
                let lock = Arc::new(Mutex::new(()));
                locks.insert(key, Arc::downgrade(&lock));
                lock
            })
        };
        let _check_guard = check_lock.lock().expect("target check lock poisoned");
        let target_name = target.to_string_lossy().into_owned();
        let target_absolute = workspace.path.join(target);
        if !target_absolute.exists() {
            return Ok(FileCheck {
                certificate: CheckRecord {
                    reference: reference.to_owned(),
                    workspace_ref: workspace.reference.clone(),
                    target: target.to_string_lossy().into_owned(),
                    fingerprint: self.full_fingerprint(workspace, target, &[])?,
                    dependencies: Vec::new(),
                    source_version: 1,
                    created_at: now_unix_ms(),
                },
                warnings: Vec::new(),
                linters: Vec::new(),
                suggestions: Vec::new(),
                diagnostics: Vec::new(),
                ok: true,
                profile: FileCheckProfile {
                    target: target_name,
                    mode: "deleted".into(),
                    reused_prefix_lines: None,
                    dependencies_ms: 0,
                    cache_ms: 0,
                    setup_ms: 0,
                    elaborate_ms: 0,
                    total_ms: file_started.elapsed().as_millis() as u64,
                },
            });
        }
        let phase = Instant::now();
        let dependencies = transitive_dependencies(&workspace.path, target)?;
        let dependencies_ms = phase.elapsed().as_millis() as u64;
        let phase = Instant::now();
        if let Some(cached) = self.cached_check(workspace, target, &dependencies, reference)? {
            let mut cached = cached;
            cached.profile = FileCheckProfile {
                target: target_name,
                mode: "cached".into(),
                reused_prefix_lines: None,
                dependencies_ms,
                cache_ms: phase.elapsed().as_millis() as u64,
                setup_ms: 0,
                elaborate_ms: 0,
                total_ms: file_started.elapsed().as_millis() as u64,
            };
            return Ok(cached);
        }
        let cache_ms = phase.elapsed().as_millis() as u64;
        let phase = Instant::now();
        let (setup_path, environment) = self.worker_setup(workspace, target, &dependencies)?;
        let setup_ms = phase.elapsed().as_millis() as u64;
        let fingerprint = self.full_fingerprint(workspace, target, &dependencies)?;
        let source = fs::read_to_string(&target_absolute)
            .with_context(|| format!("cannot read {}", target.display()))?;

        let phase = Instant::now();
        let (response, mode, reused_prefix_lines) =
            self.run_worker(workspace, target, &setup_path, &environment, &source, true)?;
        let elaborate_ms = phase.elapsed().as_millis() as u64;
        ensure!(
            response.version > 0,
            "Lean worker returned an invalid source version"
        );
        let (warnings, linters, mut suggestions, mut diagnostics) =
            partition_diagnostics(&response.diagnostics);
        attach_source_context(&mut suggestions, target, &source);
        attach_source_context(&mut diagnostics, target, &source);
        Ok(FileCheck {
            certificate: CheckRecord {
                reference: reference.to_owned(),
                workspace_ref: workspace.reference.clone(),
                target: target.to_string_lossy().into_owned(),
                fingerprint,
                dependencies: dependencies
                    .iter()
                    .map(|path| path.to_string_lossy().into_owned())
                    .collect(),
                source_version: response.version,
                created_at: now_unix_ms(),
            },
            warnings,
            linters,
            suggestions,
            diagnostics,
            ok: response.ok,
            profile: FileCheckProfile {
                target: target_name,
                mode: mode.into(),
                reused_prefix_lines,
                dependencies_ms,
                cache_ms,
                setup_ms,
                elaborate_ms,
                total_ms: file_started.elapsed().as_millis() as u64,
            },
        })
    }

    fn cached_check(
        &self,
        workspace: &Workspace,
        target: &Path,
        dependencies: &[PathBuf],
        reference: &str,
    ) -> Result<Option<FileCheck>> {
        let fingerprint = self.full_fingerprint(workspace, target, dependencies)?;
        let target_name = target.to_string_lossy();
        let certificate = self
            .state
            .checks_for_workspace(&workspace.reference)?
            .into_iter()
            .find(|check| check.target == target_name && check.fingerprint == fingerprint);
        let Some(mut certificate) = certificate else {
            return Ok(None);
        };
        let Some(run) = self.state.check_run(&certificate.reference)? else {
            return Ok(None);
        };
        certificate.reference = reference.to_owned();
        certificate.created_at = now_unix_ms();
        Ok(Some(FileCheck {
            certificate,
            warnings: run.warnings,
            linters: run.linters,
            suggestions: run.suggestions,
            diagnostics: Vec::new(),
            ok: true,
            profile: FileCheckProfile {
                target: target.to_string_lossy().into_owned(),
                mode: "cached".into(),
                reused_prefix_lines: None,
                dependencies_ms: 0,
                cache_ms: 0,
                setup_ms: 0,
                elaborate_ms: 0,
                total_ms: 0,
            },
        }))
    }

    fn run_worker(
        &self,
        workspace: &Workspace,
        target: &Path,
        setup_path: &Path,
        environment: &str,
        source: &str,
        allow_fallback: bool,
    ) -> Result<(WorkerResponse, &'static str, Option<u64>)> {
        let key = (workspace.reference.clone(), target.to_path_buf());
        let (worker, inserted) = {
            let mut workers = self.workers.lock().expect("worker map poisoned");
            if let Some(worker) = workers.get(&key) {
                (worker.clone(), false)
            } else {
                let workspace_workers = workers
                    .keys()
                    .filter(|(reference, _)| reference == &workspace.reference)
                    .count();
                if workspace_workers >= 3
                    && let Some(oldest) = workers
                        .iter()
                        .filter(|((reference, _), _)| reference == &workspace.reference)
                        .filter_map(|(key, worker)| {
                            worker
                                .try_lock()
                                .ok()
                                .map(|worker| (key.clone(), worker.last_used.elapsed()))
                        })
                        .max_by_key(|(_, idle)| *idle)
                        .map(|(key, _)| key)
                {
                    workers.remove(&oldest);
                }
                match LeanWorker::start(
                    &self.repo,
                    &workspace.path,
                    setup_path,
                    environment,
                ) {
                    Ok(worker) => {
                        let worker = Arc::new(Mutex::new(worker));
                        workers.insert(key.clone(), worker.clone());
                        (worker, true)
                    }
                    Err(error) => {
                        drop(workers);
                        self.record_worker_failure(&format!("start: {error:#}"));
                        if allow_fallback {
                            return fallback_check(&self.repo, &workspace.path, target)
                                .map(|response| (response, "fallback", None))
                                .with_context(|| {
                                    format!("direct Lean worker unavailable: {error:#}")
                                });
                        }
                        return Err(error).context("direct Lean worker unavailable");
                    }
                }
            }
        };
        let mut worker_guard = worker.lock().expect("Lean worker poisoned");
        let replace = !inserted
            && (worker_guard.environment != environment || !worker_guard.alive());
        if replace {
            match LeanWorker::start(&self.repo, &workspace.path, setup_path, environment) {
                Ok(replacement) => *worker_guard = replacement,
                Err(error) => {
                    drop(worker_guard);
                    self.remove_worker(&key, &worker);
                    self.record_worker_failure(&format!("start: {error:#}"));
                    if allow_fallback {
                        return fallback_check(&self.repo, &workspace.path, target)
                            .map(|response| (response, "fallback", None))
                            .with_context(|| {
                                format!("direct Lean worker unavailable: {error:#}")
                            });
                    }
                    return Err(error).context("direct Lean worker unavailable");
                }
            }
        }
        match worker_guard.check(source) {
            Ok((response, reuse)) => Ok((
                response,
                if inserted || replace {
                    "cold-worker"
                } else if reuse.identical {
                    "worker-cache"
                } else {
                    "incremental"
                },
                (!replace).then_some(reuse.prefix_lines),
            )),
            Err(error) => {
                self.record_worker_failure(&format!("request: {error:#}"));
                drop(worker_guard);
                self.remove_worker(&key, &worker);
                if allow_fallback {
                    fallback_check(&self.repo, &workspace.path, target)
                        .map(|response| (response, "fallback", None))
                        .with_context(|| format!("direct Lean worker failed: {error:#}"))
                } else {
                    Err(error).context("direct Lean worker failed")
                }
            }
        }
    }

    fn remove_worker(&self, key: &WorkerKey, expected: &Arc<Mutex<LeanWorker>>) {
        let mut workers = self.workers.lock().expect("worker map poisoned");
        if workers
            .get(key)
            .is_some_and(|worker| Arc::ptr_eq(worker, expected))
        {
            workers.remove(key);
        }
    }

    pub fn probe_source(
        &self,
        workspace: &Workspace,
        requested: &Path,
        source: &str,
    ) -> Result<(bool, String)> {
        let target = resolve_target(&workspace.path, requested)?;
        let dependencies = transitive_dependencies(&workspace.path, &target)?;
        let (setup_path, environment) = self.worker_setup(workspace, &target, &dependencies)?;
        let (response, _, _) =
            self.run_worker(workspace, &target, &setup_path, &environment, source, false)?;
        let ok = response.ok;
        Ok((
            ok,
            response
                .diagnostics
                .into_iter()
                .map(|diagnostic| diagnostic.text)
                .collect::<Vec<_>>()
                .join("\n"),
        ))
    }

    pub fn probe_source_if_ready(
        &self,
        workspace: &Workspace,
        requested: &Path,
        source: &str,
    ) -> Result<Option<(bool, String)>> {
        let target = resolve_target(&workspace.path, requested)?;
        let worker = match self.workers.try_lock() {
            Ok(workers) => workers
                .get(&(workspace.reference.clone(), target))
                .cloned(),
            Err(std::sync::TryLockError::Poisoned(error)) => error
                .into_inner()
                .get(&(workspace.reference.clone(), target))
                .cloned(),
            Err(std::sync::TryLockError::WouldBlock) => None,
        };
        let ready = worker.is_some_and(|worker| {
            worker
                .try_lock()
                .is_ok_and(|mut worker| worker.alive())
        });
        if !ready {
            return Ok(None);
        }
        self.probe_source(workspace, requested, source).map(Some)
    }

    fn worker_setup(
        &self,
        workspace: &Workspace,
        target: &Path,
        dependencies: &[PathBuf],
    ) -> Result<(PathBuf, String)> {
        let setup_input = environment_fingerprint(&workspace.path, dependencies)?;
        let mut environment = self.worker_environment_from_base(workspace, target, &setup_input)?;
        let persisted_setup = self.setup_path(workspace, target);
        let setup_path = match self.current_setup(workspace, target, &environment) {
            Some(path) => path,
            None if setup_is_current(&persisted_setup, &setup_input) => persisted_setup,
            None => {
                let setup =
                    self.prepare_setup(workspace, target, &setup_input, !dependencies.is_empty())?;
                environment = self.worker_environment_from_base(workspace, target, &setup_input)?;
                setup.path
            }
        };
        Ok((setup_path, environment))
    }

    fn record_worker_failure(&self, detail: &str) {
        if let Ok(mut log) = fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.repo.log_path)
        {
            let _ = writeln!(log, "direct worker fallback: {detail}");
        }
        if development_enabled(&self.repo)
            && let Ok(store) = TelemetryStore::global()
        {
            let _ = store.record_operation(
                &self.repo,
                &TelemetryOperation {
                    workspace: None,
                    verb: "check_fallback",
                    reference: None,
                    ok: false,
                    duration_ms: 0,
                    detail,
                    rss_kib: None,
                },
            );
        }
    }

    fn current_setup(
        &self,
        workspace: &Workspace,
        target: &Path,
        environment: &str,
    ) -> Option<PathBuf> {
        let worker = self
            .workers
            .lock()
            .expect("worker map poisoned")
            .get(&(workspace.reference.clone(), target.to_path_buf()))
            .cloned()?;
        let mut worker = worker.lock().expect("Lean worker poisoned");
        (worker.environment == environment && worker.alive()).then(|| worker.setup_path.clone())
    }

    fn full_fingerprint(
        &self,
        workspace: &Workspace,
        target: &Path,
        dependencies: &[PathBuf],
    ) -> Result<String> {
        let base = certificate_fingerprint(&workspace.path, target, dependencies)?;
        let setup_path = self.setup_path(workspace, target);
        if !setup_path.is_file() {
            return Ok(base);
        }
        Ok(hash_bytes(
            format!("{base}{}", setup_artifact_fingerprint(&setup_path)?).as_bytes(),
        ))
    }

    fn worker_environment_from_base(
        &self,
        workspace: &Workspace,
        target: &Path,
        base: &str,
    ) -> Result<String> {
        let setup_path = self.setup_path(workspace, target);
        if !setup_path.is_file() {
            return Ok(base.to_owned());
        }
        Ok(hash_bytes(
            format!("{base}{}", setup_artifact_fingerprint(&setup_path)?).as_bytes(),
        ))
    }

    fn prepare_setup(
        &self,
        workspace: &Workspace,
        target: &Path,
        input_fingerprint: &str,
        has_project_dependencies: bool,
    ) -> Result<FileSetup> {
        let build_lock = has_project_dependencies.then(|| {
            let mut locks = self.setup_locks.lock().expect("setup lock map poisoned");
            locks.retain(|_, lock| lock.strong_count() > 0);
            locks
                .entry(input_fingerprint.to_owned())
                .or_default()
                .upgrade()
                .unwrap_or_else(|| {
                    let lock = Arc::new(Mutex::new(()));
                    locks.insert(input_fingerprint.to_owned(), Arc::downgrade(&lock));
                    lock
                })
        });
        let _build_guard = build_lock
            .as_ref()
            .map(|lock| lock.lock().expect("dependency build lock poisoned"));
        let path = self.setup_path(workspace, target);
        if setup_is_current(&path, input_fingerprint) {
            return Ok(FileSetup { path });
        }
        let output = lake_command(&self.repo, &workspace.path)
            .arg("setup-file")
            .arg(target)
            .output()
            .with_context(|| {
                format!(
                    "cannot start lake to configure {}; install the project's Lean toolchain and dependencies",
                    target.display()
                )
            })?;
        if !output.status.success() {
            bail!(
                "dependency setup failed for {}: {}",
                target.display(),
                String::from_utf8_lossy(&output.stderr).trim()
            );
        }
        let setup: LakeSetup = serde_json::from_slice(&output.stdout)
            .with_context(|| format!("invalid Lake setup for {}", target.display()))?;
        ensure!(!setup.name.is_empty(), "Lake returned an empty module name");
        let directory = self
            .repo
            .state_dir
            .join("setups")
            .join(&workspace.reference);
        fs::create_dir_all(&directory)?;
        fs::write(&path, &output.stdout)?;
        fs::write(setup_fingerprint_path(&path), input_fingerprint)?;
        Ok(FileSetup { path })
    }

    fn setup_path(&self, workspace: &Workspace, target: &Path) -> PathBuf {
        self.repo
            .state_dir
            .join("setups")
            .join(&workspace.reference)
            .join(format!(
                "{}.json",
                hash_bytes(target.to_string_lossy().as_bytes())
            ))
    }

    pub fn invalidate_workspace(&self, workspace_ref: &str) {
        self.workers
            .lock()
            .expect("worker map poisoned")
            .retain(|(reference, _), _| reference != workspace_ref);
    }

    pub fn evict_worker(&self, workspace_ref: &str) {
        self.workers
            .lock()
            .expect("worker map poisoned")
            .retain(|(reference, _), _| reference != workspace_ref);
    }

    pub fn handle_filesystem_change(&self, workspace: &Workspace, path: &Path) {
        let Ok(relative) = path.strip_prefix(&workspace.path) else {
            self.evict_worker(&workspace.reference);
            return;
        };
        self.workers
            .lock()
            .expect("worker map poisoned")
            .retain(|(reference, target), _| {
                reference != &workspace.reference
                    || !invalidates_worker(&workspace.path, relative, target)
            });
    }

    pub fn evict_idle_workers(&self, idle_for: std::time::Duration) -> bool {
        let mut workers = self.workers.lock().expect("worker map poisoned");
        workers.retain(|_, worker| match worker.try_lock() {
            Ok(mut worker) => worker.last_used.elapsed() < idle_for && worker.alive(),
            Err(std::sync::TryLockError::WouldBlock) => true,
            Err(std::sync::TryLockError::Poisoned(_)) => false,
        });
        if workers.len() > 1
            && available_memory_gib().is_some_and(|gib| gib < 4)
            && let Some(oldest) = workers
                .iter()
                .filter_map(|(key, worker)| {
                    worker
                        .try_lock()
                        .ok()
                        .map(|worker| (key.clone(), worker.last_used.elapsed()))
                })
                .max_by_key(|(_, idle)| *idle)
                .map(|(key, _)| key)
        {
            workers.remove(&oldest);
        }
        !workers.is_empty()
    }

    pub fn valid_certificates(
        &self,
        workspace: &Workspace,
        targets: &[PathBuf],
    ) -> Result<Vec<String>> {
        let mut uncovered: HashSet<PathBuf> = targets.iter().cloned().collect();
        let mut references = Vec::new();
        let mut seen_references = HashSet::new();
        let mut seen_targets = HashSet::new();
        for check in self.state.checks_for_workspace(&workspace.reference)? {
            let check_target = PathBuf::from(&check.target);
            if !seen_targets.insert(check_target.clone()) {
                continue;
            }
            let dependencies = transitive_dependencies(&workspace.path, &check_target)?;
            let fingerprint = self.full_fingerprint(workspace, &check_target, &dependencies)?;
            if check.fingerprint != fingerprint {
                continue;
            }
            let mut covers = false;
            for path in std::iter::once(check_target).chain(dependencies) {
                covers |= uncovered.remove(&path);
            }
            if covers && seen_references.insert(check.reference.clone()) {
                references.push(check.reference);
            }
            if uncovered.is_empty() {
                break;
            }
        }
        ensure!(
            uncovered.is_empty(),
            "missing current check coverage for {}",
            uncovered
                .iter()
                .map(|path| path.to_string_lossy())
                .collect::<Vec<_>>()
                .join(", ")
        );
        Ok(references)
    }
}

fn setup_fingerprint_path(setup_path: &Path) -> PathBuf {
    setup_path.with_extension("fingerprint")
}

fn setup_is_current(setup_path: &Path, input_fingerprint: &str) -> bool {
    setup_path.is_file()
        && fs::read_to_string(setup_fingerprint_path(setup_path))
            .is_ok_and(|fingerprint| fingerprint == input_fingerprint)
}

struct LeanWorker {
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
    environment: String,
    setup_path: PathBuf,
    version: u64,
    stderr: Arc<Mutex<String>>,
    last_used: Instant,
    last_source: Option<String>,
    last_response: Option<WorkerResponse>,
}

struct WorkerReuse {
    identical: bool,
    prefix_lines: u64,
}

impl LeanWorker {
    fn start(
        repo: &Repo,
        root: &Path,
        setup_path: &Path,
        environment: &str,
    ) -> Result<Self> {
        let mut command = lake_command(repo, root);
        command
            .args(["env", "lean", "--run"])
            .arg(repo.state_dir.join("MathmuxWorker.lean"))
            .arg(setup_path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        command.process_group(0);
        let mut child = command.spawn().context("cannot start direct Lean worker")?;
        let stdin = child.stdin.take().context("Lean worker has no stdin")?;
        let stdout = BufReader::new(child.stdout.take().context("Lean worker has no stdout")?);
        let mut stderr_pipe = child.stderr.take().context("Lean worker has no stderr")?;
        let stderr = Arc::new(Mutex::new(String::new()));
        let stderr_copy = stderr.clone();
        std::thread::spawn(move || {
            let mut contents = String::new();
            let _ = std::io::Read::read_to_string(&mut stderr_pipe, &mut contents);
            *stderr_copy.lock().expect("stderr buffer poisoned") = contents;
        });
        Ok(Self {
            child,
            stdin,
            stdout,
            environment: environment.to_owned(),
            setup_path: setup_path.to_path_buf(),
            version: 0,
            stderr,
            last_used: Instant::now(),
            last_source: None,
            last_response: None,
        })
    }

    fn check(&mut self, source: &str) -> Result<(WorkerResponse, WorkerReuse)> {
        self.last_used = Instant::now();
        if self.last_source.as_deref() == Some(source)
            && let Some(response) = &self.last_response
        {
            return Ok((
                response.clone(),
                WorkerReuse {
                    identical: true,
                    prefix_lines: source.lines().count() as u64,
                },
            ));
        }
        let prefix_lines = self
            .last_source
            .as_deref()
            .map(|previous| common_prefix_lines(previous, source))
            .unwrap_or(0);
        self.version += 1;
        serde_json::to_writer(
            &mut self.stdin,
            &WorkerRequest {
                source,
                version: self.version,
            },
        )?;
        self.stdin.write_all(b"\n")?;
        self.stdin.flush()?;
        let mut line = String::new();
        let read = self.stdout.read_line(&mut line)?;
        if read == 0 {
            let stderr = self.stderr.lock().expect("stderr buffer poisoned").clone();
            bail!("Lean worker exited: {stderr}");
        }
        let response: WorkerResponse = serde_json::from_str(&line)
            .with_context(|| format!("invalid Lean response: {}", line.trim()))?;
        ensure!(response.version == self.version, "stale Lean response");
        let response = deduplicate_diagnostics(response);
        self.last_source = Some(source.to_owned());
        self.last_response = Some(response.clone());
        Ok((
            response,
            WorkerReuse {
                identical: false,
                prefix_lines,
            },
        ))
    }

    fn alive(&mut self) -> bool {
        matches!(self.child.try_wait(), Ok(None))
    }
}

fn common_prefix_lines(previous: &str, current: &str) -> u64 {
    previous
        .split_inclusive('\n')
        .zip(current.split_inclusive('\n'))
        .take_while(|(left, right)| left == right)
        .count() as u64
}

impl Drop for LeanWorker {
    fn drop(&mut self) {
        let pid = self.child.id() as i32;
        unsafe {
            libc::kill(-pid, libc::SIGTERM);
        }
        let _ = self.child.wait();
    }
}

fn fallback_check(repo: &Repo, root: &Path, target: &Path) -> Result<WorkerResponse> {
    let output = lake_command(repo, root)
        .args(["env", "lean"])
        .arg(target)
        .output()?;
    let stderr = String::from_utf8_lossy(&output.stderr).trim().to_owned();
    let stdout = String::from_utf8_lossy(&output.stdout).trim().to_owned();
    let diagnostics = [stdout, stderr]
        .into_iter()
        .filter(|value| !value.is_empty())
        .map(|text| {
            let severity = if output.status.success() {
                "warning"
            } else {
                "error"
            };
            WorkerDiagnostic {
                severity: severity.into(),
                kind: "lean".into(),
                text,
            }
        })
        .collect::<Vec<_>>();
    Ok(WorkerResponse {
        ok: output.status.success(),
        diagnostics,
        version: 1,
    })
}

fn deduplicate_diagnostics(mut response: WorkerResponse) -> WorkerResponse {
    let mut seen = HashSet::new();
    response
        .diagnostics
        .retain(|diagnostic| seen.insert(diagnostic.clone()));
    response
}

fn invalidates_worker(root: &Path, path: &Path, target: &Path) -> bool {
    let other_lean_file = path
        .components()
        .next()
        .is_none_or(|component| component.as_os_str() != ".lake")
        && path
            .extension()
            .is_some_and(|extension| extension == "lean")
        && path != target;
    other_lean_file
        && transitive_dependencies(root, target)
            .map(|dependencies| dependencies.iter().any(|dependency| dependency == path))
            .unwrap_or(true)
}

fn partition_diagnostics(
    diagnostics: &[WorkerDiagnostic],
) -> (
    Vec<Diagnostic>,
    Vec<Diagnostic>,
    Vec<Diagnostic>,
    Vec<Diagnostic>,
) {
    let mut warnings = Vec::new();
    let mut linters = Vec::new();
    let mut suggestions = Vec::new();
    let mut errors = Vec::new();
    for diagnostic in diagnostics {
        let value = Diagnostic {
            kind: diagnostic.kind.clone(),
            text: diagnostic.text.clone(),
            context: None,
        };
        match diagnostic.severity.as_str() {
            "warning" if is_linter(diagnostic) => linters.push(value),
            "warning" => warnings.push(value),
            "information" | "info" if is_tactic_suggestion(diagnostic) => {
                suggestions.push(value)
            }
            "error" => errors.push(value),
            _ => {}
        }
    }
    deduplicate(&mut warnings);
    deduplicate(&mut linters);
    deduplicate(&mut suggestions);
    deduplicate(&mut errors);
    (warnings, linters, suggestions, errors)
}

fn is_tactic_suggestion(diagnostic: &WorkerDiagnostic) -> bool {
    diagnostic.text.contains("Try this:")
}

fn attach_source_context(diagnostics: &mut [Diagnostic], target: &Path, source: &str) {
    let target_path = target.to_string_lossy();
    let basename = target_path.rsplit('/').next().unwrap_or(&target_path);
    let module = target
        .with_extension("")
        .components()
        .filter_map(|component| component.as_os_str().to_str())
        .collect::<Vec<_>>()
        .join(".");
    let lines = source.lines().collect::<Vec<_>>();
    for diagnostic in diagnostics {
        let first = diagnostic.text.lines().next().unwrap_or_default();
        let rest = [target_path.as_ref(), basename, module.as_str()]
            .iter()
            .find_map(|prefix| {
                first
                    .strip_prefix(prefix)
                    .and_then(|rest| rest.strip_prefix(':'))
            });
        let Some(line) = rest
            .and_then(|rest| rest.split(':').next())
            .and_then(|line| line.parse::<usize>().ok())
            .filter(|line| *line > 0 && *line <= lines.len())
        else {
            continue;
        };
        let start = line.saturating_sub(2).max(1);
        let end = (line + 2).min(lines.len());
        diagnostic.context = Some(
            (start..=end)
                .map(|current| {
                    format!(
                        "{} {:>4} | {}",
                        if current == line { ">" } else { " " },
                        current,
                        lines[current - 1]
                    )
                })
                .collect::<Vec<_>>()
                .join("\n"),
        );
    }
}

fn is_linter(diagnostic: &WorkerDiagnostic) -> bool {
    let kind = diagnostic.kind.to_ascii_lowercase();
    let text = diagnostic.text.to_ascii_lowercase();
    kind.contains("linter")
        || text.contains("declaration uses 'sorry'")
        || text.contains("declaration uses `sorry`")
        || text.contains("unused variable")
        || text.contains("automatically included section variable")
        || text.contains("contains a placeholder")
}

fn deduplicate(diagnostics: &mut Vec<Diagnostic>) {
    let mut seen = HashSet::new();
    diagnostics.retain(|diagnostic| seen.insert(diagnostic.clone()));
}

pub fn resolve_target(root: &Path, requested: &Path) -> Result<PathBuf> {
    let absolute = if requested.is_absolute() {
        requested.to_path_buf()
    } else {
        std::env::current_dir()?.join(requested)
    };
    let absolute = fs::canonicalize(&absolute)
        .with_context(|| format!("cannot resolve {}", requested.display()))?;
    ensure!(
        absolute.starts_with(root),
        "target is outside the current workspace"
    );
    ensure!(
        absolute
            .extension()
            .is_some_and(|extension| extension == "lean"),
        "target is not a Lean file"
    );
    Ok(absolute.strip_prefix(root)?.to_path_buf())
}

pub fn transitive_dependencies(root: &Path, target: &Path) -> Result<Vec<PathBuf>> {
    if !root.join(target).is_file() {
        return Ok(Vec::new());
    }
    let files = project_lean_files(root);
    let modules: HashMap<String, PathBuf> = files
        .into_iter()
        .map(|path| (project_module_name(root, &path), path))
        .collect();
    let mut visited = HashSet::new();
    let mut ordered = Vec::new();
    visit_dependencies(root, target, &modules, &mut visited, &mut ordered)?;
    ordered.retain(|path| path != target);
    Ok(ordered)
}

fn visit_dependencies(
    root: &Path,
    target: &Path,
    modules: &HashMap<String, PathBuf>,
    visited: &mut HashSet<PathBuf>,
    ordered: &mut Vec<PathBuf>,
) -> Result<()> {
    if !visited.insert(target.to_path_buf()) {
        return Ok(());
    }
    if !root.join(target).is_file() {
        ordered.push(target.to_path_buf());
        return Ok(());
    }
    let source = fs::read_to_string(root.join(target))?;
    for import in parse_imports(&source) {
        if let Some(dependency) = modules.get(&import) {
            visit_dependencies(root, dependency, modules, visited, ordered)?;
        }
    }
    ordered.push(target.to_path_buf());
    Ok(())
}

fn dependency_order(root: &Path, targets: &[PathBuf]) -> Result<Vec<PathBuf>> {
    let target_set: HashSet<_> = targets.iter().cloned().collect();
    let files = project_lean_files(root);
    let modules: HashMap<String, PathBuf> = files
        .into_iter()
        .map(|path| (project_module_name(root, &path), path))
        .collect();
    let mut visited = HashSet::new();
    let mut ordered = Vec::new();
    for target in targets {
        visit_dependencies(root, target, &modules, &mut visited, &mut ordered)?;
    }
    ordered.retain(|path| target_set.contains(path));
    Ok(ordered)
}

pub(crate) fn parse_imports(source: &str) -> Vec<String> {
    let mut imports = Vec::new();
    for line in source.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with("--") || line == "module" {
            continue;
        }
        if let Some(rest) = line.strip_prefix("import ") {
            imports.extend(rest.split_whitespace().map(str::to_owned));
            continue;
        }
        if line.starts_with("prelude") || line.starts_with("public import ") {
            let rest = line.strip_prefix("public import ").unwrap_or("");
            imports.extend(rest.split_whitespace().map(str::to_owned));
            continue;
        }
        break;
    }
    let mut seen = HashSet::new();
    imports.retain(|module| seen.insert(module.clone()));
    imports
}

pub fn project_module_name(root: &Path, path: &Path) -> String {
    let roots = source_roots(root);
    let relative = roots
        .iter()
        .filter_map(|source_root| path.strip_prefix(source_root).ok())
        .min_by_key(|path| path.components().count())
        .unwrap_or(path);
    let mut path = relative.to_path_buf();
    path.set_extension("");
    path.components()
        .filter_map(|component| component.as_os_str().to_str())
        .collect::<Vec<_>>()
        .join(".")
}

fn source_roots(root: &Path) -> Vec<PathBuf> {
    let mut roots = vec![PathBuf::new()];
    for config in ["lakefile.toml", "lakefile.lean"] {
        let Ok(source) = fs::read_to_string(root.join(config)) else {
            continue;
        };
        for line in source.lines().filter(|line| line.contains("srcDir")) {
            let Some(start) = line.find('"') else {
                continue;
            };
            let Some(end) = line[start + 1..].find('"') else {
                continue;
            };
            let value = &line[start + 1..start + 1 + end];
            if !value.is_empty() {
                roots.push(PathBuf::from(value));
            }
        }
    }
    roots
}

fn artifact_path(root: &Path, source: &Path) -> PathBuf {
    let module = project_module_name(root, source).replace('.', "/");
    let mut artifact = root.join(".lake/build/lib/lean").join(module);
    artifact.set_extension("olean");
    artifact
}

pub fn certificate_fingerprint(
    root: &Path,
    target: &Path,
    dependencies: &[PathBuf],
) -> Result<String> {
    let mut entries = BTreeSet::new();
    entries.insert(target.to_path_buf());
    entries.extend(dependencies.iter().cloned());
    let mut material = CHECK_RESULT_VERSION.to_vec();
    for path in entries {
        material.extend_from_slice(path.to_string_lossy().as_bytes());
        if root.join(&path).is_file() {
            material.extend_from_slice(hash_file(&root.join(&path))?.as_bytes());
        } else {
            material.extend_from_slice(b"<absent>");
        }
        let artifact = artifact_path(root, &path);
        if artifact.is_file() {
            material.extend_from_slice(hash_file(&artifact)?.as_bytes());
        }
    }
    for config in [
        "lean-toolchain",
        "lakefile.lean",
        "lakefile.toml",
        "lake-manifest.json",
    ] {
        let path = root.join(config);
        if path.is_file() {
            material.extend_from_slice(config.as_bytes());
            material.extend_from_slice(hash_file(&path)?.as_bytes());
        }
    }
    Ok(hash_bytes(&material))
}

fn setup_artifact_fingerprint(path: &Path) -> Result<String> {
    let bytes = fs::read(path)?;
    let value: serde_json::Value = serde_json::from_slice(&bytes)?;
    let mut paths = BTreeSet::new();
    collect_artifact_paths(&value, &mut paths);
    let mut material = bytes;
    for artifact in paths {
        material.extend_from_slice(artifact.to_string_lossy().as_bytes());
        match fs::metadata(&artifact) {
            Ok(metadata) if metadata.is_file() => {
                let modified = metadata
                    .modified()?
                    .duration_since(UNIX_EPOCH)
                    .unwrap_or_default()
                    .as_nanos();
                material.extend_from_slice(format!("{}:{modified}", metadata.len()).as_bytes());
            }
            _ => material.extend_from_slice(b"<missing-artifact>"),
        }
    }
    Ok(hash_bytes(&material))
}

fn collect_artifact_paths(value: &serde_json::Value, paths: &mut BTreeSet<PathBuf>) {
    match value {
        serde_json::Value::String(value) => {
            let path = PathBuf::from(value);
            let artifact = path
                .extension()
                .and_then(|extension| extension.to_str())
                .is_some_and(|extension| {
                    matches!(
                        extension,
                        "olean" | "ilean" | "c" | "o" | "bc" | "so" | "dylib" | "dll"
                    )
                });
            if path.is_absolute() && artifact {
                paths.insert(path);
            }
        }
        serde_json::Value::Array(values) => {
            for value in values {
                collect_artifact_paths(value, paths);
            }
        }
        serde_json::Value::Object(values) => {
            for value in values.values() {
                collect_artifact_paths(value, paths);
            }
        }
        _ => {}
    }
}

fn environment_fingerprint(root: &Path, dependencies: &[PathBuf]) -> Result<String> {
    let mut material = Vec::new();
    for dependency in dependencies {
        material.extend_from_slice(hash_file(&root.join(dependency))?.as_bytes());
        let artifact = artifact_path(root, dependency);
        if artifact.is_file() {
            material.extend_from_slice(hash_file(&artifact)?.as_bytes());
        }
    }
    for config in [
        "lean-toolchain",
        "lakefile.lean",
        "lakefile.toml",
        "lake-manifest.json",
    ] {
        let path = root.join(config);
        if path.is_file() {
            material.extend_from_slice(hash_file(&path)?.as_bytes());
        }
    }
    Ok(hash_bytes(&material))
}

fn available_memory_gib() -> Option<u64> {
    fs::read_to_string("/proc/meminfo")
        .ok()?
        .lines()
        .find_map(|line| line.strip_prefix("MemAvailable:"))?
        .split_whitespace()
        .next()?
        .parse::<u64>()
        .ok()
        .map(|kib| kib / 1024 / 1024)
}

#[cfg(test)]
mod tests {
    use tempfile::tempdir;

    use super::*;

    #[test]
    fn duplicate_imports_are_ignored() {
        assert_eq!(
            parse_imports("import A B\npublic import A\n\ndef value := 1\n"),
            ["A", "B"]
        );
    }

    #[test]
    fn imports_drive_dependency_order_and_fingerprints() {
        let directory = tempdir().unwrap();
        fs::create_dir(directory.path().join("A")).unwrap();
        fs::write(directory.path().join("A/Base.lean"), "def n := 1\n").unwrap();
        fs::write(
            directory.path().join("A/Top.lean"),
            "import A.Base\n\ndef x := n\n",
        )
        .unwrap();
        fs::write(
            directory.path().join("lean-toolchain"),
            "leanprover/lean4:v4.24.0\n",
        )
        .unwrap();
        let dependencies =
            transitive_dependencies(directory.path(), Path::new("A/Top.lean")).unwrap();
        assert_eq!(dependencies, vec![PathBuf::from("A/Base.lean")]);
        let before =
            certificate_fingerprint(directory.path(), Path::new("A/Top.lean"), &dependencies)
                .unwrap();
        fs::write(directory.path().join("A/Base.lean"), "def n := 2\n").unwrap();
        let after =
            certificate_fingerprint(directory.path(), Path::new("A/Top.lean"), &dependencies)
                .unwrap();
        assert_ne!(before, after);
    }

    #[test]
    fn configuration_changes_invalidate_certificates() {
        let directory = tempdir().unwrap();
        fs::write(directory.path().join("Proof.lean"), "def proof := 1\n").unwrap();
        fs::write(
            directory.path().join("lean-toolchain"),
            "leanprover/lean4:v4.24.0\n",
        )
        .unwrap();
        fs::write(directory.path().join("lakefile.toml"), "name = \"proof\"\n").unwrap();
        let before =
            certificate_fingerprint(directory.path(), Path::new("Proof.lean"), &[]).unwrap();

        fs::write(
            directory.path().join("lakefile.toml"),
            "name = \"proof\"\nversion = \"0.2.0\"\n",
        )
        .unwrap();
        let after =
            certificate_fingerprint(directory.path(), Path::new("Proof.lean"), &[]).unwrap();
        assert_ne!(before, after);
    }

    #[test]
    fn setup_artifact_metadata_invalidates_certificates() {
        let directory = tempdir().unwrap();
        let artifact = directory.path().join("Dependency.olean");
        fs::write(&artifact, "one").unwrap();
        let setup = directory.path().join("setup.json");
        fs::write(
            &setup,
            serde_json::to_vec(&serde_json::json!({ "path": artifact })).unwrap(),
        )
        .unwrap();
        let before = setup_artifact_fingerprint(&setup).unwrap();
        fs::write(&artifact, "different size").unwrap();
        let after = setup_artifact_fingerprint(&setup).unwrap();
        assert_ne!(before, after);
    }

    #[test]
    fn persisted_setup_requires_matching_input_fingerprint() {
        let directory = tempdir().unwrap();
        let setup = directory.path().join("setup.json");
        fs::write(&setup, "{}").unwrap();
        assert!(!setup_is_current(&setup, "current"));

        fs::write(setup_fingerprint_path(&setup), "stale").unwrap();
        assert!(!setup_is_current(&setup, "current"));

        fs::write(setup_fingerprint_path(&setup), "current").unwrap();
        assert!(setup_is_current(&setup, "current"));
    }

    #[test]
    fn diagnostics_are_deduplicated_and_linters_are_separate() {
        let ordinary = WorkerDiagnostic {
            severity: "warning".into(),
            kind: "declaration".into(),
            text: "Proof.lean:1:1: warning: deprecated".into(),
        };
        let diagnostics = vec![
            ordinary.clone(),
            ordinary,
            WorkerDiagnostic {
                severity: "warning".into(),
                kind: "linter.unusedVariables".into(),
                text: "Proof.lean:2:1: warning: unused variable".into(),
            },
            WorkerDiagnostic {
                severity: "error".into(),
                kind: "typeMismatch".into(),
                text: "Proof.lean:3:1: error: type mismatch".into(),
            },
            WorkerDiagnostic {
                severity: "information".into(),
                kind: "tactic".into(),
                text: "Proof.lean:4:1: information: Try this: simp".into(),
            },
            WorkerDiagnostic {
                severity: "information".into(),
                kind: "trace".into(),
                text: "Proof.lean:5:1: information: ordinary trace".into(),
            },
        ];
        let (warnings, linters, suggestions, mut errors) =
            partition_diagnostics(&diagnostics);
        assert_eq!(
            (
                warnings.len(),
                linters.len(),
                suggestions.len(),
                errors.len()
            ),
            (1, 1, 1, 1)
        );
        attach_source_context(
            &mut errors,
            Path::new("Proof.lean"),
            "first\nsecond\nproblem\nfourth\nfifth\n",
        );
        assert_eq!(
            errors[0].context.as_deref(),
            Some(
                "     1 | first\n     2 | second\n>    3 | problem\n     4 | fourth\n     5 | fifth"
            )
        );

        errors[0].text = "Demo.Nested.Proof:3:1: error: type mismatch".into();
        errors[0].context = None;
        attach_source_context(
            &mut errors,
            Path::new("Demo/Nested/Proof.lean"),
            "first\nsecond\nproblem\nfourth\nfifth\n",
        );
        assert!(
            errors[0]
                .context
                .as_deref()
                .is_some_and(|context| context.contains(">    3 | problem"))
        );
    }

    #[test]
    fn source_dependency_changes_evict_the_worker() {
        let root = tempdir().unwrap();
        fs::write(root.path().join("Dependency.lean"), "def dependency := 1\n").unwrap();
        fs::write(
            root.path().join("Proof.lean"),
            "import Dependency\ndef proof := dependency\n",
        )
        .unwrap();
        fs::write(root.path().join("Unrelated.lean"), "def unrelated := 2\n").unwrap();
        let target = Path::new("Proof.lean");
        assert!(!invalidates_worker(root.path(), target, target));
        assert!(invalidates_worker(
            root.path(),
            Path::new("Dependency.lean"),
            target
        ));
        assert!(!invalidates_worker(
            root.path(),
            Path::new("Unrelated.lean"),
            target
        ));
        assert!(!invalidates_worker(
            root.path(),
            Path::new("lakefile.toml"),
            target
        ));
        assert!(!invalidates_worker(
            root.path(),
            Path::new("lean-toolchain"),
            target
        ));
        assert!(!invalidates_worker(
            root.path(),
            Path::new(".lake/build/lib/lean/Proof.olean"),
            target
        ));
    }
}
