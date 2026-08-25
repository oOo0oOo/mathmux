use std::collections::{BTreeSet, HashMap, HashSet};
use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Stdio};
use std::sync::{Arc, Mutex, Weak};
use std::time::Instant;

use anyhow::{Context, Result, bail, ensure};
use serde::{Deserialize, Serialize};

use crate::git::{dirty_lean_files, lake_command, project_lean_files};
use crate::repo::Repo;
use crate::state::{CheckRecord, CheckRun, Diagnostic, State, Workspace};
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
  let some header := snapshot.result? | return failureResponse "header parsing failed" version
  let processed := header.processedSnap.get
  let some processed := processed.result? | return failureResponse "import processing failed" version
  let (failed, commandMessages) ← firstErrorOrFinal processed.firstCmdSnap
  let messages ← if failed then pure commandMessages else collectTree (Language.toSnapshotTree snapshot)
  let diagnostics ← renderMessages messages
  return { ok := !messages.hasErrors, diagnostics, version := version }

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

#[derive(Debug, Clone)]
pub struct CheckOutcome {
    pub reference: String,
    pub ok: bool,
    pub elapsed_ms: u64,
    pub warnings: Vec<Diagnostic>,
    pub diagnostics: Vec<Diagnostic>,
}

#[derive(Debug, Serialize)]
struct WorkerRequest<'a> {
    source: &'a str,
    version: u64,
}

#[derive(Debug, Deserialize)]
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
    diagnostics: Vec<Diagnostic>,
    ok: bool,
}

#[derive(Debug, Deserialize)]
struct LakeSetup {
    name: String,
}

struct FileSetup {
    path: PathBuf,
}

pub struct Checker {
    repo: Repo,
    state: State,
    workers: Mutex<HashMap<String, LeanWorker>>,
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
            setup_locks: Mutex::new(HashMap::new()),
        })
    }

    pub fn check(&self, workspace: &Workspace, requested: Option<&Path>) -> Result<CheckOutcome> {
        let targets = match requested {
            Some(path) => vec![resolve_target(&workspace.path, path)?],
            None => {
                let files = dirty_lean_files(&workspace.path)?;
                ensure!(!files.is_empty(), "workspace has no dirty Lean files");
                dependency_order(&workspace.path, &files)?
            }
        };
        let reference = self.state.next_ref('c')?;
        let started = Instant::now();
        let files = targets
            .iter()
            .map(|path| path.to_string_lossy().into_owned())
            .collect::<Vec<_>>();
        let mut certificates = Vec::new();
        let mut passed = Vec::new();
        let mut warnings = Vec::new();
        let mut linters = Vec::new();
        let mut diagnostics = Vec::new();
        let mut failed = None;

        for target in &targets {
            let target_name = target.to_string_lossy().into_owned();
            match self.check_one(workspace, target, &reference) {
                Ok(result) => {
                    warnings.extend(result.warnings);
                    linters.extend(result.linters);
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
                    });
                    failed = Some(target_name);
                    break;
                }
            }
        }
        deduplicate(&mut warnings);
        deduplicate(&mut linters);
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
            diagnostics: diagnostics.clone(),
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
            diagnostics,
        })
    }

    fn check_one(
        &self,
        workspace: &Workspace,
        target: &Path,
        reference: &str,
    ) -> Result<FileCheck> {
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
                diagnostics: Vec::new(),
                ok: true,
            });
        }
        let dependencies = transitive_dependencies(&workspace.path, target)?;
        let mut environment = self.worker_environment(workspace, target, &dependencies)?;
        let setup_path = match self.current_setup(workspace, target, &environment) {
            Some(path) => path,
            None => {
                let setup =
                    self.prepare_setup(workspace, target, &environment, !dependencies.is_empty())?;
                environment = self.worker_environment(workspace, target, &dependencies)?;
                setup.path
            }
        };
        let fingerprint = self.full_fingerprint(workspace, target, &dependencies)?;
        let source = fs::read_to_string(&target_absolute)
            .with_context(|| format!("cannot read {}", target.display()))?;

        let response = self.run_worker(workspace, target, &setup_path, &environment, &source)?;
        ensure!(
            response.version > 0,
            "Lean worker returned an invalid source version"
        );
        let (warnings, linters, diagnostics) = partition_diagnostics(&response.diagnostics);
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
            diagnostics,
            ok: response.ok,
        })
    }

    fn run_worker(
        &self,
        workspace: &Workspace,
        target: &Path,
        setup_path: &Path,
        environment: &str,
        source: &str,
    ) -> Result<WorkerResponse> {
        let mut workers = self.workers.lock().expect("worker map poisoned");
        let replace = workers.get_mut(&workspace.reference).is_none_or(|worker| {
            worker.target != target || worker.environment != environment || !worker.alive()
        });
        if replace {
            workers.remove(&workspace.reference);
            match LeanWorker::start(&self.repo, &workspace.path, target, setup_path, environment) {
                Ok(worker) => {
                    workers.insert(workspace.reference.clone(), worker);
                }
                Err(error) => {
                    self.record_worker_failure(&format!("start: {error:#}"));
                    return fallback_check(&self.repo, &workspace.path, target)
                        .with_context(|| format!("direct Lean worker unavailable: {error:#}"));
                }
            }
        }
        let worker = workers
            .get_mut(&workspace.reference)
            .context("Lean worker did not start")?;
        match worker.check(source) {
            Ok(response) => Ok(response),
            Err(error) => {
                self.record_worker_failure(&format!("request: {error:#}"));
                workers.remove(&workspace.reference);
                fallback_check(&self.repo, &workspace.path, target)
                    .with_context(|| format!("direct Lean worker failed: {error:#}"))
            }
        }
    }

    fn record_worker_failure(&self, detail: &str) {
        if let Ok(mut log) = fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.repo.log_path)
        {
            let _ = writeln!(log, "direct worker fallback: {detail}");
        }
    }

    fn current_setup(
        &self,
        workspace: &Workspace,
        target: &Path,
        environment: &str,
    ) -> Option<PathBuf> {
        let mut workers = self.workers.lock().expect("worker map poisoned");
        workers.get_mut(&workspace.reference).and_then(|worker| {
            (worker.target == target && worker.environment == environment && worker.alive())
                .then(|| worker.setup_path.clone())
        })
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

    fn worker_environment(
        &self,
        workspace: &Workspace,
        target: &Path,
        dependencies: &[PathBuf],
    ) -> Result<String> {
        let base = environment_fingerprint(&workspace.path, dependencies)?;
        let setup_path = self.setup_path(workspace, target);
        if !setup_path.is_file() {
            return Ok(base);
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
        let output = lake_command(&self.repo, &workspace.path)
            .arg("setup-file")
            .arg(target)
            .output()
            .with_context(|| format!("cannot configure {}", target.display()))?;
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
        let path = self.setup_path(workspace, target);
        fs::write(&path, &output.stdout)?;
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
            .remove(workspace_ref);
    }

    pub fn evict_worker(&self, workspace_ref: &str) {
        self.workers
            .lock()
            .expect("worker map poisoned")
            .remove(workspace_ref);
    }

    pub fn handle_filesystem_change(&self, workspace: &Workspace, path: &Path) {
        let Ok(relative) = path.strip_prefix(&workspace.path) else {
            self.evict_worker(&workspace.reference);
            return;
        };
        let target = self
            .workers
            .lock()
            .expect("worker map poisoned")
            .get(&workspace.reference)
            .map(|worker| worker.target.clone());
        if target.is_some_and(|target| invalidates_worker(relative, &target)) {
            self.evict_worker(&workspace.reference);
        }
    }

    pub fn evict_idle_workers(&self, idle_for: std::time::Duration) -> bool {
        let mut workers = self.workers.lock().expect("worker map poisoned");
        workers.retain(|_, worker| worker.last_used.elapsed() < idle_for && worker.alive());
        if workers.len() > 1
            && available_memory_gib().is_some_and(|gib| gib < 4)
            && let Some(oldest) = workers
                .iter()
                .max_by_key(|(_, worker)| worker.last_used.elapsed())
                .map(|(reference, _)| reference.clone())
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

struct LeanWorker {
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
    target: PathBuf,
    environment: String,
    setup_path: PathBuf,
    version: u64,
    stderr: Arc<Mutex<String>>,
    last_used: Instant,
}

impl LeanWorker {
    fn start(
        repo: &Repo,
        root: &Path,
        target: &Path,
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
            target: target.to_path_buf(),
            environment: environment.to_owned(),
            setup_path: setup_path.to_path_buf(),
            version: 0,
            stderr,
            last_used: Instant::now(),
        })
    }

    fn check(&mut self, source: &str) -> Result<WorkerResponse> {
        self.last_used = Instant::now();
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
        Ok(deduplicate_diagnostics(response))
    }

    fn alive(&mut self) -> bool {
        matches!(self.child.try_wait(), Ok(None))
    }
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

fn invalidates_worker(path: &Path, target: &Path) -> bool {
    !path
        .components()
        .next()
        .is_some_and(|component| component.as_os_str() == ".lake")
        && path
            .extension()
            .is_some_and(|extension| extension == "lean")
        && path != target
}

fn partition_diagnostics(
    diagnostics: &[WorkerDiagnostic],
) -> (Vec<Diagnostic>, Vec<Diagnostic>, Vec<Diagnostic>) {
    let mut warnings = Vec::new();
    let mut linters = Vec::new();
    let mut errors = Vec::new();
    for diagnostic in diagnostics {
        let value = Diagnostic {
            kind: diagnostic.kind.clone(),
            text: diagnostic.text.clone(),
        };
        match diagnostic.severity.as_str() {
            "warning" if is_linter(diagnostic) => linters.push(value),
            "warning" => warnings.push(value),
            "error" => errors.push(value),
            _ => {}
        }
    }
    deduplicate(&mut warnings);
    deduplicate(&mut linters);
    deduplicate(&mut errors);
    (warnings, linters, errors)
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
    let mut material = Vec::new();
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
        if artifact.is_file() {
            material.extend_from_slice(hash_file(&artifact)?.as_bytes());
        } else {
            material.extend_from_slice(b"<missing-artifact>");
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
        ];
        let (warnings, linters, errors) = partition_diagnostics(&diagnostics);
        assert_eq!((warnings.len(), linters.len(), errors.len()), (1, 1, 1));
    }

    #[test]
    fn source_dependency_changes_evict_the_worker() {
        let target = Path::new("Proof.lean");
        assert!(!invalidates_worker(target, target));
        assert!(invalidates_worker(Path::new("Dependency.lean"), target));
        assert!(!invalidates_worker(Path::new("lakefile.toml"), target));
        assert!(!invalidates_worker(Path::new("lean-toolchain"), target));
        assert!(!invalidates_worker(
            Path::new(".lake/build/lib/lean/Proof.olean"),
            target
        ));
    }
}
