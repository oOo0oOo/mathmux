use std::collections::{BTreeSet, HashMap, HashSet};
use std::fs;
use std::io::Write;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::{Arc, Mutex, OnceLock, TryLockError, Weak};
use std::time::{Duration, Instant, UNIX_EPOCH};

use anyhow::{Context, Result, ensure};
use fs2::FileExt;
use regex::Regex;
use serde::{Deserialize, Serialize};

use crate::coordination::{lock_exclusive_until, lock_mutex_until, open_lock};
use crate::git::{dirty_lean_files, lake_command, merge_in_progress, project_lean_files};
use crate::issue::{TelemetryOperation, TelemetryStore};
use crate::lean_service::{LeanServiceProcess, ServiceRequestError, reap_stale_processes};
use crate::reference::ReferenceKind;
use crate::repo::Repo;
use crate::state::{
    CheckProfile, CheckProfileEntry, CheckRecord, CheckRun, CheckStatus, Diagnostic,
    FileCheckProfile, State, Workspace,
};
use crate::util::{hash_bytes, hash_file, now_unix_ms};

mod diagnostics;

use diagnostics::{attach_source_context, deduplicate, partition_diagnostics};

const CHECK_RESULT_VERSION: &[u8] = b"check-result-v2";
const CHECK_TIMEOUT: Duration = Duration::from_secs(5 * 60);
const CHECK_QUEUE_TIMEOUT: Duration = CHECK_TIMEOUT;
// A cold owner can spend one check budget preparing imports before it reaches
// Lean's own check budget. Duplicate target checks should wait for that owner
// rather than fail shortly before its reusable result becomes available.
const SHARED_CHECK_TIMEOUT: Duration = Duration::from_secs(2 * 5 * 60);
const COLD_PROBE_TIMEOUT: Duration = Duration::from_secs(16);
const SLOW_CHECK_PROFILE_MS: u64 = 5_000;
const PROFILE_ENTRY_LIMIT: usize = 512;
const PROJECT_CONFIG_FILES: [&str; 4] = [
    "lean-toolchain",
    "lakefile.lean",
    "lakefile.toml",
    "lake-manifest.json",
];

#[derive(Debug)]
struct CheckTimeout(Duration);

impl std::fmt::Display for CheckTimeout {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0 == CHECK_TIMEOUT {
            write!(
                formatter,
                "Lean elaboration exceeded five minutes; split the file or simplify the current declaration"
            )
        } else if self.0 < Duration::from_secs(1) {
            write!(formatter, "Lean probe exceeded {}ms", self.0.as_millis())
        } else {
            write!(
                formatter,
                "Lean probe exceeded {} seconds",
                self.0.as_secs()
            )
        }
    }
}

impl std::error::Error for CheckTimeout {}

#[derive(Debug)]
struct DependencySetupFailure {
    target: PathBuf,
    detail: String,
    formalization: bool,
}

impl std::fmt::Display for DependencySetupFailure {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "dependency setup failed for {}: {}",
            self.target.display(),
            self.detail
        )
    }
}

impl std::error::Error for DependencySetupFailure {}

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
    pub repetition: Option<CheckRepetition>,
}

#[derive(Debug, Clone)]
pub struct CheckRepetition {
    pub count: usize,
    pub first_reference: String,
    pub previous_reference: String,
    pub deterministic_timeout: bool,
}

#[derive(Debug, Serialize)]
struct WorkerRequest<'a> {
    operation: &'a str,
    source: &'a str,
    file_name: &'a str,
    version: u64,
    line: u64,
    column: u64,
    input: &'a str,
    names: &'a [String],
}

#[derive(Debug, Clone, Deserialize)]
struct WorkerResponse {
    ok: bool,
    diagnostics: Vec<WorkerDiagnostic>,
    #[serde(default)]
    profile: Vec<CheckProfileEntry>,
    #[serde(default)]
    detail: String,
    version: u64,
}

#[derive(Clone, Copy)]
struct WorkerAction<'a> {
    operation: &'a str,
    line: u64,
    column: u64,
    input: &'a str,
}

impl WorkerAction<'_> {
    const CHECK: Self = Self {
        operation: "check",
        line: 0,
        column: 0,
        input: "",
    };
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq, Hash)]
struct WorkerDiagnostic {
    severity: String,
    kind: String,
    text: String,
}

#[derive(Clone)]
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

type WorkerKey = (String, PathBuf, bool);
type CheckKey = (String, PathBuf);
type CheckLocks = Mutex<HashMap<CheckKey, Weak<Mutex<()>>>>;

#[derive(Default)]
struct CheckCoordinator {
    checks: CheckLocks,
    setups: Mutex<HashMap<String, Weak<Mutex<()>>>>,
}

#[derive(Default)]
struct CheckCache {
    failed: Mutex<HashMap<CheckKey, FileCheck>>,
}

#[derive(Default)]
struct LeanCheckRunner {
    workers: Mutex<HashMap<WorkerKey, Arc<Mutex<LeanWorker>>>>,
}

#[derive(Clone, Copy)]
enum WorkerRun<'a> {
    Check,
    Probe {
        timeout: Duration,
        action: WorkerAction<'a>,
    },
    Profile,
}

struct ImportCoverage<'a> {
    dirty: &'a HashSet<PathBuf>,
    passed: &'a HashSet<PathBuf>,
}

pub struct Checker {
    repo: Repo,
    state: State,
    coordinator: CheckCoordinator,
    cache: CheckCache,
    runner: LeanCheckRunner,
    telemetry: Option<Arc<TelemetryStore>>,
}

impl Checker {
    pub fn new(repo: Repo, state: State, telemetry: Option<Arc<TelemetryStore>>) -> Result<Self> {
        let reaped = reap_stale_processes(&repo);
        if reaped > 0
            && let Ok(mut log) = fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(&repo.log_path)
        {
            let _ = writeln!(log, "reaped {reaped} stale Lean worker group(s)");
        }
        Ok(Self {
            repo,
            state,
            coordinator: CheckCoordinator::default(),
            cache: CheckCache::default(),
            runner: LeanCheckRunner::default(),
            telemetry,
        })
    }

    pub fn check(
        &self,
        workspace: &Workspace,
        requested: Option<&Path>,
        include_profile: bool,
        report: &mut dyn FnMut(&str),
    ) -> Result<CheckOutcome> {
        let started = Instant::now();
        let (targets, dirty_targets) = match requested {
            Some(path) => (vec![resolve_target(&workspace.path, path)?], None),
            None => {
                ensure!(
                    !merge_in_progress(&workspace.path),
                    "workspace has an unfinished sync; check the conflicted files, then rerun mathmux sync"
                );
                let files = dirty_lean_files(&workspace.path)?;
                ensure!(!files.is_empty(), "workspace has no dirty Lean files");
                let targets = maximal_check_targets(&workspace.path, &files)?;
                (targets, Some(files.into_iter().collect::<HashSet<_>>()))
            }
        };
        let planning_ms = started.elapsed().as_millis() as u64;
        let mut covered_targets = HashSet::new();
        let reference = self.state.next_reference(ReferenceKind::Check)?;
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
            report(&format!("{reference} checking {target_name}"));
            match self.check_one(
                workspace,
                target,
                &reference,
                include_profile,
                dirty_targets.as_ref().map(|dirty| ImportCoverage {
                    dirty,
                    passed: &covered_targets,
                }),
                report,
            ) {
                Ok(result) => {
                    file_profiles.push(result.profile.clone());
                    warnings.extend(result.warnings);
                    linters.extend(result.linters);
                    suggestions.extend(result.suggestions);
                    if result.ok {
                        covered_targets.insert(target.clone());
                        covered_targets
                            .extend(result.certificate.dependencies.iter().map(PathBuf::from));
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
        let profile = CheckProfile {
            planning_ms,
            files: file_profiles,
        };
        let displayed_profile = include_profile.then(|| profile.clone());
        let run = CheckRun {
            reference: reference.clone(),
            workspace_ref: workspace.reference.clone(),
            status: if ok {
                CheckStatus::Passed
            } else {
                CheckStatus::Failed
            },
            files,
            passed,
            failed,
            not_checked,
            warnings: warnings.clone(),
            linters: linters.clone(),
            suggestions: suggestions.clone(),
            diagnostics: diagnostics.clone(),
            profile: (include_profile || elapsed_ms >= SLOW_CHECK_PROFILE_MS).then_some(profile),
            duration_ms: elapsed_ms,
            created_at: now_unix_ms(),
        };
        self.state
            .add_check_run(&run, if ok { &certificates } else { &[] })?;
        self.state.touch_workspace(&workspace.reference)?;
        let repetition = if cache_only_run(&run) {
            None
        } else {
            self.repeated_blocker(&run)?
        };
        Ok(CheckOutcome {
            reference,
            ok,
            elapsed_ms,
            warnings,
            linters,
            suggestions,
            diagnostics,
            profile: displayed_profile,
            repetition,
        })
    }

    fn repeated_blocker(&self, current: &CheckRun) -> Result<Option<CheckRepetition>> {
        let Some(target) = current.failed.as_deref() else {
            return Ok(None);
        };
        let Some(primary) = current.diagnostics.first() else {
            return Ok(None);
        };
        let primary_fingerprint = repetition_fingerprint(primary);
        let mut fingerprints = vec![(
            primary_fingerprint,
            primary.text.contains("deterministic timeout"),
        )];
        fingerprints.extend(
            current
                .diagnostics
                .iter()
                .skip(1)
                .filter(|diagnostic| diagnostic.text.contains("deterministic timeout"))
                .map(|diagnostic| (repetition_fingerprint(diagnostic), true)),
        );
        fingerprints.retain(|(fingerprint, _)| !fingerprint.is_empty());
        let mut seen = HashSet::new();
        fingerprints.retain(|(fingerprint, _)| seen.insert(fingerprint.clone()));

        let recent = self
            .state
            .recent_failed_checks(&current.workspace_ref, 64)?;
        let Some((deterministic_timeout, matches)) =
            fingerprints.into_iter().find_map(|(fingerprint, timeout)| {
                let matches = recent
                    .iter()
                    .filter(|run| !cache_only_run(run))
                    .filter(|run| run.failed.as_deref() == Some(target))
                    .filter(|run| {
                        run.diagnostics
                            .iter()
                            .any(|diagnostic| repetition_fingerprint(diagnostic) == fingerprint)
                    })
                    .collect::<Vec<_>>();
                (matches.len() >= 3).then_some((timeout, matches))
            })
        else {
            return Ok(None);
        };
        Ok(Some(CheckRepetition {
            count: matches.len(),
            first_reference: matches
                .last()
                .map(|run| run.reference.clone())
                .unwrap_or_else(|| current.reference.clone()),
            previous_reference: matches
                .iter()
                .find(|run| run.reference != current.reference)
                .map(|run| run.reference.clone())
                .unwrap_or_else(|| current.reference.clone()),
            deterministic_timeout,
        }))
    }

    fn check_one(
        &self,
        workspace: &Workspace,
        target: &Path,
        reference: &str,
        include_profile: bool,
        import_coverage: Option<ImportCoverage<'_>>,
        report: &mut dyn FnMut(&str),
    ) -> Result<FileCheck> {
        let file_started = Instant::now();
        let check_lock = {
            let key = (workspace.reference.clone(), target.to_path_buf());
            let mut locks = self
                .coordinator
                .checks
                .lock()
                .expect("check lock map poisoned");
            locks.retain(|_, lock| lock.strong_count() > 0);
            locks
                .entry(key.clone())
                .or_default()
                .upgrade()
                .unwrap_or_else(|| {
                    let lock = Arc::new(Mutex::new(()));
                    locks.insert(key, Arc::downgrade(&lock));
                    lock
                })
        };
        let _check_guard = match check_lock.try_lock() {
            Ok(guard) => guard,
            Err(TryLockError::WouldBlock) => {
                report(&format!(
                    "{reference} waiting for shared check of {}",
                    target.display()
                ));
                lock_mutex_until(&check_lock, SHARED_CHECK_TIMEOUT).with_context(|| {
                    format!(
                        "shared check of {} is still running after ten minutes; retry after it finishes",
                        target.display()
                    )
                })?
            }
            Err(TryLockError::Poisoned(_)) => panic!("target check lock poisoned"),
        };
        let lock_directory = self.repo.state_dir.join("check-locks");
        fs::create_dir_all(&lock_directory)?;
        let process_lock = open_lock(&lock_directory.join(format!(
            "{}-{}.lock",
            workspace.reference,
            hash_bytes(target.to_string_lossy().as_bytes())
        )))?;
        if let Err(error) = process_lock.try_lock_exclusive() {
            if error.kind() == std::io::ErrorKind::WouldBlock {
                report(&format!(
                    "{reference} waiting for shared check of {}",
                    target.display()
                ));
                lock_exclusive_until(&process_lock, SHARED_CHECK_TIMEOUT).with_context(|| {
                    format!(
                        "shared check of {} is still running after ten minutes; retry after it finishes",
                        target.display()
                    )
                })?;
            } else {
                return Err(error)
                    .with_context(|| format!("cannot lock check target {}", target.display()));
            }
        }
        report(&format!(
            "{reference} resolving imports for {}",
            target.display()
        ));
        let queue_ms = file_started.elapsed().as_millis() as u64;
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
                    queue_ms,
                    dependencies_ms: 0,
                    cache_ms: 0,
                    setup_ms: 0,
                    elaborate_ms: 0,
                    total_ms: file_started.elapsed().as_millis() as u64,
                    entries: Vec::new(),
                },
            });
        }
        let phase = Instant::now();
        let dependencies = transitive_dependencies(&workspace.path, target)?;
        let dependencies_ms = phase.elapsed().as_millis() as u64;
        let fingerprint = self.full_fingerprint(workspace, target, &dependencies)?;
        let check_key = (workspace.reference.clone(), target.to_path_buf());
        if !include_profile
            && let Some(cached) =
                matching_failed_check(&self.cache.failed, &check_key, &fingerprint)
        {
            let mut cached = cached;
            cached.certificate.reference = reference.to_owned();
            cached.certificate.created_at = now_unix_ms();
            cached.profile.mode = "shared-cache".into();
            cached.profile.reused_prefix_lines = None;
            cached.profile.queue_ms = queue_ms;
            cached.profile.dependencies_ms = dependencies_ms;
            cached.profile.cache_ms = 0;
            cached.profile.setup_ms = 0;
            cached.profile.elaborate_ms = 0;
            cached.profile.total_ms = file_started.elapsed().as_millis() as u64;
            return Ok(cached);
        }
        let phase = Instant::now();
        if let Some(cached) =
            self.cached_check(workspace, target, &fingerprint, reference, include_profile)?
        {
            let mut cached = cached;
            cached.profile.target = target_name;
            cached.profile.mode = if include_profile {
                "profile-cache".into()
            } else {
                "cached".into()
            };
            cached.profile.reused_prefix_lines = None;
            cached.profile.queue_ms = queue_ms;
            cached.profile.dependencies_ms = dependencies_ms;
            cached.profile.cache_ms = phase.elapsed().as_millis() as u64;
            cached.profile.setup_ms = 0;
            cached.profile.elaborate_ms = 0;
            cached.profile.total_ms = file_started.elapsed().as_millis() as u64;
            return Ok(cached);
        }
        let cache_ms = phase.elapsed().as_millis() as u64;
        let source = fs::read_to_string(&target_absolute)
            .with_context(|| format!("cannot read {}", target.display()))?;
        if let Some(coverage) = import_coverage
            && import_only_coverage(
                &workspace.path,
                target,
                &source,
                &dependencies,
                coverage.dirty,
                coverage.passed,
            )?
        {
            report(&format!(
                "{reference} certifying imports for {}",
                target.display()
            ));
            return Ok(FileCheck {
                certificate: CheckRecord {
                    reference: reference.to_owned(),
                    workspace_ref: workspace.reference.clone(),
                    target: target_name.clone(),
                    fingerprint: self.full_fingerprint(workspace, target, &dependencies)?,
                    dependencies: dependencies
                        .iter()
                        .map(|path| path.to_string_lossy().into_owned())
                        .collect(),
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
                    mode: "imports".into(),
                    reused_prefix_lines: None,
                    queue_ms,
                    dependencies_ms,
                    cache_ms,
                    setup_ms: 0,
                    elaborate_ms: 0,
                    total_ms: file_started.elapsed().as_millis() as u64,
                    entries: Vec::new(),
                },
            });
        }
        let phase = Instant::now();
        report(&format!(
            "{reference} preparing imports for {}",
            target.display()
        ));
        let (setup_path, environment) = match self.worker_setup(workspace, target, &dependencies) {
            Ok(setup) => setup,
            Err(error) => {
                let Some(failure) = error
                    .downcast_ref::<DependencySetupFailure>()
                    .filter(|failure| failure.formalization)
                else {
                    return Err(error);
                };
                let mut diagnostics = vec![Diagnostic {
                    kind: "lean.dependency".into(),
                    text: failure
                        .detail
                        .strip_prefix("error: ")
                        .unwrap_or(&failure.detail)
                        .to_owned(),
                    context: None,
                }];
                for dependency in &dependencies {
                    if let Ok(source) = fs::read_to_string(workspace.path.join(dependency)) {
                        attach_source_context(&mut diagnostics, dependency, &source);
                    }
                    if diagnostics[0].context.is_some() {
                        break;
                    }
                }
                let result = FileCheck {
                    certificate: CheckRecord {
                        reference: reference.to_owned(),
                        workspace_ref: workspace.reference.clone(),
                        target: target_name.clone(),
                        fingerprint,
                        dependencies: dependencies
                            .iter()
                            .map(|path| path.to_string_lossy().into_owned())
                            .collect(),
                        source_version: 1,
                        created_at: now_unix_ms(),
                    },
                    warnings: Vec::new(),
                    linters: Vec::new(),
                    suggestions: Vec::new(),
                    diagnostics,
                    ok: false,
                    profile: FileCheckProfile {
                        target: target_name,
                        mode: "dependency-failure".into(),
                        reused_prefix_lines: None,
                        queue_ms,
                        dependencies_ms,
                        cache_ms,
                        setup_ms: phase.elapsed().as_millis() as u64,
                        elaborate_ms: 0,
                        total_ms: file_started.elapsed().as_millis() as u64,
                        entries: Vec::new(),
                    },
                };
                self.cache
                    .failed
                    .lock()
                    .expect("failed check cache poisoned")
                    .insert(check_key, result.clone());
                return Ok(result);
            }
        };
        // Setup preparation can create or refresh artifacts included in the
        // certificate fingerprint. Certify the environment that Lean actually
        // uses, not the pre-setup state observed during cache lookup.
        let fingerprint = self.full_fingerprint(workspace, target, &dependencies)?;
        let setup_ms = phase.elapsed().as_millis() as u64;
        let phase = Instant::now();
        report(&format!("{reference} elaborating {}", target.display()));
        let (mut response, mode, reused_prefix_lines) = self.run_worker(
            workspace,
            target,
            &setup_path,
            &environment,
            &source,
            if include_profile {
                WorkerRun::Profile
            } else {
                WorkerRun::Check
            },
        )?;
        let elaborate_ms = phase.elapsed().as_millis() as u64;
        ensure!(
            response.version > 0,
            "Lean worker returned an invalid source version"
        );
        let source_lines = source.lines().collect::<Vec<_>>();
        for entry in response.profile.iter_mut().filter(|entry| entry.line > 0) {
            if entry.kind == "Elab.command"
                && let Some((line, kind, name)) =
                    profile_declaration_near(&source_lines, entry.line)
            {
                entry.line = line;
                entry.column = 1;
                entry.kind = kind.to_owned();
                entry.detail = name.to_owned();
                continue;
            }
            if let Some(line) = source_lines.get(entry.line.saturating_sub(1) as usize) {
                let line = line.trim();
                if entry.detail.is_empty() {
                    entry.detail = line.to_owned();
                } else if !line.is_empty() && !entry.detail.contains(line) {
                    entry.detail.push(' ');
                    entry.detail.push_str(line);
                }
            }
        }
        let (warnings, linters, mut suggestions, mut diagnostics) =
            partition_diagnostics(&response.diagnostics);
        let mut warnings = warnings;
        let mut linters = linters;
        attach_source_context(&mut warnings, target, &source);
        attach_source_context(&mut linters, target, &source);
        attach_source_context(&mut suggestions, target, &source);
        attach_source_context(&mut diagnostics, target, &source);
        let result = FileCheck {
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
                queue_ms,
                dependencies_ms,
                cache_ms,
                setup_ms,
                elaborate_ms,
                total_ms: file_started.elapsed().as_millis() as u64,
                entries: response.profile,
            },
        };
        let mut failed_checks = self
            .cache
            .failed
            .lock()
            .expect("failed check cache poisoned");
        if result.ok {
            failed_checks.remove(&check_key);
        } else {
            failed_checks.insert(check_key, result.clone());
        }
        Ok(result)
    }

    fn cached_check(
        &self,
        workspace: &Workspace,
        target: &Path,
        fingerprint: &str,
        reference: &str,
        require_profile: bool,
    ) -> Result<Option<FileCheck>> {
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
        let stored_profile = run
            .profile
            .as_ref()
            .and_then(|profile| profile.files.iter().find(|file| file.target == target_name));
        if require_profile
            && stored_profile.is_none_or(|profile| {
                profile.entries.is_empty()
                    || profile.entries.iter().all(|entry| entry.duration_ms < 0.01)
            })
        {
            return Ok(None);
        }
        certificate.reference = reference.to_owned();
        certificate.created_at = now_unix_ms();
        Ok(Some(FileCheck {
            certificate,
            warnings: run.warnings,
            linters: run.linters,
            suggestions: run.suggestions,
            diagnostics: Vec::new(),
            ok: true,
            profile: stored_profile.cloned().unwrap_or_else(|| FileCheckProfile {
                target: target.to_string_lossy().into_owned(),
                mode: "cached".into(),
                reused_prefix_lines: None,
                queue_ms: 0,
                dependencies_ms: 0,
                cache_ms: 0,
                setup_ms: 0,
                elaborate_ms: 0,
                total_ms: 0,
                entries: Vec::new(),
            }),
        }))
    }

    fn run_worker(
        &self,
        workspace: &Workspace,
        target: &Path,
        setup_path: &Path,
        environment: &str,
        source: &str,
        run: WorkerRun<'_>,
    ) -> Result<(WorkerResponse, &'static str, Option<u64>)> {
        let (allow_fallback, retry_worker, timeout, action) = match run {
            WorkerRun::Check => (true, true, CHECK_TIMEOUT, WorkerAction::CHECK),
            WorkerRun::Probe { timeout, action } => (false, false, timeout, action),
            WorkerRun::Profile => (false, true, CHECK_TIMEOUT, WorkerAction::CHECK),
        };
        let profile = matches!(run, WorkerRun::Profile);
        let key = (workspace.reference.clone(), target.to_path_buf(), profile);
        let (worker, inserted) = {
            let mut workers = self.runner.workers.lock().expect("worker map poisoned");
            if let Some(worker) = workers.get(&key) {
                (worker.clone(), false)
            } else {
                let workspace_workers = workers
                    .keys()
                    .filter(|(reference, _, _)| reference == &workspace.reference)
                    .count();
                if workspace_workers >= 3
                    && let Some(oldest) = workers
                        .iter()
                        .filter(|((reference, _, _), _)| reference == &workspace.reference)
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
                    profile,
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
        let mut worker_guard = if matches!(run, WorkerRun::Probe { .. }) {
            lock_mutex_until(&worker, timeout).context(
                "Lean worker is busy with another request; retry the probe after it finishes",
            )?
        } else {
            worker.lock().expect("Lean worker poisoned")
        };
        let replace =
            !inserted && (worker_guard.environment != environment || !worker_guard.alive());
        if replace {
            match LeanWorker::start(
                &self.repo,
                &workspace.path,
                setup_path,
                environment,
                profile,
            ) {
                Ok(replacement) => *worker_guard = replacement,
                Err(error) => {
                    drop(worker_guard);
                    self.remove_worker(&key, &worker);
                    self.record_worker_failure(&format!("start: {error:#}"));
                    if allow_fallback {
                        return fallback_check(&self.repo, &workspace.path, target)
                            .map(|response| (response, "fallback", None))
                            .with_context(|| format!("direct Lean worker unavailable: {error:#}"));
                    }
                    return Err(error).context("direct Lean worker unavailable");
                }
            }
        }
        let request_timeout = if matches!(run, WorkerRun::Probe { .. }) && (inserted || replace) {
            timeout.max(COLD_PROBE_TIMEOUT)
        } else {
            timeout
        };
        match worker_guard.request(
            source,
            &target.to_string_lossy(),
            request_timeout,
            !profile,
            action,
        ) {
            Ok((response, reuse)) => Ok((
                response,
                if profile {
                    "profile"
                } else if inserted || replace {
                    "cold-worker"
                } else if reuse.identical {
                    "worker-cache"
                } else {
                    "incremental"
                },
                (!profile && !replace).then_some(reuse.prefix_lines),
            )),
            Err(error) => {
                let timed_out = error.downcast_ref::<CheckTimeout>().is_some();
                if !(timed_out && matches!(run, WorkerRun::Probe { .. })) {
                    self.record_worker_failure(&format!("request: {error:#}"));
                }
                drop(worker_guard);
                self.remove_worker(&key, &worker);
                if timed_out {
                    Err(error)
                } else if retry_worker {
                    let mut replacement = LeanWorker::start(
                        &self.repo,
                        &workspace.path,
                        setup_path,
                        environment,
                        profile,
                    )
                    .with_context(|| format!("Lean worker restart failed after: {error:#}"))?;
                    match replacement.request(
                        source,
                        &target.to_string_lossy(),
                        timeout,
                        true,
                        action,
                    ) {
                        Ok((response, _)) => {
                            self.runner
                                .workers
                                .lock()
                                .expect("worker map poisoned")
                                .insert(key, Arc::new(Mutex::new(replacement)));
                            Ok((response, "cold-worker-retry", None))
                        }
                        Err(retry_error) => {
                            self.record_worker_failure(&format!("retry: {retry_error:#}"));
                            Err(retry_error).with_context(|| {
                                format!("Lean worker failed twice; first failure: {error:#}")
                            })
                        }
                    }
                } else {
                    Err(error).context("direct Lean worker failed")
                }
            }
        }
    }

    fn remove_worker(&self, key: &WorkerKey, expected: &Arc<Mutex<LeanWorker>>) {
        let mut workers = self.runner.workers.lock().expect("worker map poisoned");
        if workers
            .get(key)
            .is_some_and(|worker| Arc::ptr_eq(worker, expected))
        {
            workers.remove(key);
        }
    }

    pub fn probe_context(
        &self,
        workspace: &Workspace,
        requested: &Path,
        line: u64,
        column: u64,
        operation: &str,
        input: &str,
    ) -> Result<(bool, String)> {
        let target = resolve_target(&workspace.path, requested)?;
        let source = fs::read_to_string(workspace.path.join(&target))
            .with_context(|| format!("cannot read probe context {}", target.display()))?;
        let column = if !matches!(operation, "goal" | "tactic") && line > 0 && column == 0 {
            first_source_column(&source, line)
        } else {
            column
        };
        let (setup_path, environment) = match self.active_worker_setup(workspace, &target) {
            Some(current) => current,
            None => {
                let dependencies = transitive_dependencies(&workspace.path, &target)?;
                self.worker_setup(workspace, &target, &dependencies)?
            }
        };
        let (response, _, _) = self.run_worker(
            workspace,
            &target,
            &setup_path,
            &environment,
            &source,
            WorkerRun::Probe {
                timeout: Duration::from_secs(2),
                action: WorkerAction {
                    operation,
                    line,
                    column,
                    input,
                },
            },
        )?;
        let detail = if response.detail.trim().is_empty() {
            response
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.text.as_str())
                .collect::<Vec<_>>()
                .join("\n")
        } else {
            response.detail
        };
        Ok((response.ok, detail))
    }

    fn worker_setup(
        &self,
        workspace: &Workspace,
        target: &Path,
        dependencies: &[PathBuf],
    ) -> Result<(PathBuf, String)> {
        let setup_input = setup_input_fingerprint(&workspace.path, target, dependencies)?;
        let environment_base = environment_fingerprint(&workspace.path, dependencies)?;
        let mut environment =
            self.worker_environment_from_base(workspace, target, &environment_base)?;
        let persisted_setup = self.setup_path(workspace, target);
        let setup_path = match self.current_setup(workspace, target, &environment) {
            Some(path) => path,
            None if setup_is_usable(&persisted_setup, &setup_input) => persisted_setup,
            None => {
                let path =
                    self.prepare_setup(workspace, target, &setup_input, !dependencies.is_empty())?;
                environment =
                    self.worker_environment_from_base(workspace, target, &environment_base)?;
                path
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
        if let Some(store) = &self.telemetry {
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
        let (setup_path, current_environment) = self.active_worker_setup(workspace, target)?;
        (current_environment == environment).then_some(setup_path)
    }

    fn active_worker_setup(
        &self,
        workspace: &Workspace,
        target: &Path,
    ) -> Option<(PathBuf, String)> {
        let worker = self
            .runner
            .workers
            .lock()
            .expect("worker map poisoned")
            .get(&(workspace.reference.clone(), target.to_path_buf(), false))
            .cloned()?;
        let mut worker = worker.try_lock().ok()?;
        worker
            .alive()
            .then(|| (worker.setup_path.clone(), worker.environment.clone()))
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
        let immutable_artifact_roots = self.immutable_artifact_roots();
        Ok(hash_bytes(
            format!(
                "{base}{}",
                setup_artifact_fingerprint(&setup_path, &immutable_artifact_roots)?
            )
            .as_bytes(),
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
        let immutable_artifact_roots = self.immutable_artifact_roots();
        Ok(hash_bytes(
            format!(
                "{base}{}",
                setup_artifact_fingerprint(&setup_path, &immutable_artifact_roots)?
            )
            .as_bytes(),
        ))
    }

    fn prepare_setup(
        &self,
        workspace: &Workspace,
        target: &Path,
        input_fingerprint: &str,
        has_project_dependencies: bool,
    ) -> Result<PathBuf> {
        let build_lock = has_project_dependencies.then(|| {
            let mut locks = self
                .coordinator
                .setups
                .lock()
                .expect("setup lock map poisoned");
            locks.retain(|_, lock| lock.strong_count() > 0);
            locks
                .entry(workspace.reference.clone())
                .or_default()
                .upgrade()
                .unwrap_or_else(|| {
                    let lock = Arc::new(Mutex::new(()));
                    locks.insert(workspace.reference.clone(), Arc::downgrade(&lock));
                    lock
                })
        });
        let _build_guard = build_lock
            .as_ref()
            .map(|lock| {
                lock_mutex_until(lock, CHECK_QUEUE_TIMEOUT).context(
                    "workspace import preparation is still running after five minutes; retry after it finishes",
                )
            })
            .transpose()?;
        let path = self.setup_path(workspace, target);
        if setup_is_usable(&path, input_fingerprint) {
            return Ok(path);
        }
        let shared = self.shared_setup_path(target, input_fingerprint);
        fs::create_dir_all(shared.parent().expect("shared setup has a parent"))?;
        let shared_lock = open_lock(&shared.with_extension("lock"))?;
        lock_exclusive_until(&shared_lock, CHECK_QUEUE_TIMEOUT).context(
            "shared import preparation is still running after five minutes; retry after it finishes",
        )?;
        if setup_is_usable(&shared, input_fingerprint) {
            materialize_setup(&shared, &path, input_fingerprint)?;
            return Ok(path);
        }
        let output = lake_command(&self.repo, &workspace.path)
            .current_dir(lake_package_root(&workspace.path, target))
            .arg("setup-file")
            .arg(lake_package_target(&workspace.path, target))
            .output()
            .with_context(|| {
                format!(
                    "cannot start lake to configure {}; install the project's Lean toolchain and dependencies",
                    target.display()
                )
            })?;
        if !output.status.success() {
            return Err(DependencySetupFailure {
                target: target.to_path_buf(),
                detail: compact_dependency_failure(&output.stderr),
                formalization: dependency_failure_is_formalization(&output.stderr),
            }
            .into());
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
        fs::write(&shared, &output.stdout)?;
        fs::write(setup_fingerprint_path(&shared), input_fingerprint)?;
        materialize_setup(&shared, &path, input_fingerprint)?;
        prune_shared_setups(shared.parent().expect("shared setup has a parent"), &shared);
        Ok(path)
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

    fn shared_setup_path(&self, target: &Path, input_fingerprint: &str) -> PathBuf {
        self.repo.state_dir.join("setups/shared").join(format!(
            "{}.json",
            hash_bytes(format!("{}\0{input_fingerprint}", target.display()).as_bytes())
        ))
    }

    fn immutable_artifact_roots(&self) -> [PathBuf; 2] {
        [
            self.repo.cache_dir.join("artifacts"),
            self.repo.root.join(".lake/packages"),
        ]
    }

    pub fn evict_workspace_workers(&self, workspace_ref: &str) {
        self.runner
            .workers
            .lock()
            .expect("worker map poisoned")
            .retain(|(reference, _, _), _| reference != workspace_ref);
    }

    pub fn handle_filesystem_change(&self, workspace: &Workspace, path: &Path) {
        let Ok(relative) = path.strip_prefix(&workspace.path) else {
            self.evict_workspace_workers(&workspace.reference);
            return;
        };
        self.runner
            .workers
            .lock()
            .expect("worker map poisoned")
            .retain(|(reference, target, _), _| {
                reference != &workspace.reference
                    || !invalidates_worker(&workspace.path, relative, target)
            });
    }

    pub fn evict_idle_workers(&self, idle_for: std::time::Duration) -> bool {
        let mut workers = self.runner.workers.lock().expect("worker map poisoned");
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

    pub fn current_check_run_for_target(
        &self,
        workspace: &Workspace,
        target: &Path,
    ) -> Result<Option<CheckRun>> {
        let target_name = target.to_string_lossy();
        for check in self.state.checks_for_workspace(&workspace.reference)? {
            if check.target != target_name {
                continue;
            }
            let dependencies = transitive_dependencies(&workspace.path, target)?;
            if check.fingerprint != self.full_fingerprint(workspace, target, &dependencies)? {
                continue;
            }
            let Some(run) = self.state.check_run(&check.reference)? else {
                continue;
            };
            if run.status == CheckStatus::Passed {
                return Ok(Some(run));
            }
        }
        Ok(None)
    }

    pub fn latest_successful_check_run_for_target(
        &self,
        workspace: &Workspace,
        target: &Path,
    ) -> Result<Option<CheckRun>> {
        let target_name = target.to_string_lossy();
        for check in self.state.checks_for_workspace(&workspace.reference)? {
            if check.target != target_name {
                continue;
            }
            let Some(run) = self.state.check_run(&check.reference)? else {
                continue;
            };
            if run.status == CheckStatus::Passed {
                return Ok(Some(run));
            }
        }
        Ok(None)
    }
}

fn first_source_column(source: &str, line: u64) -> u64 {
    source
        .lines()
        .nth(line.saturating_sub(1) as usize)
        .map(|line| {
            let indentation = line.chars().take_while(|ch| ch.is_whitespace()).count();
            let trimmed = line.trim_start();
            let bullet = trimmed
                .strip_prefix('·')
                .map(|rest| 1 + rest.chars().take_while(|ch| ch.is_whitespace()).count())
                .unwrap_or(0);
            (indentation + bullet) as u64 + 2
        })
        .unwrap_or(1)
}

fn profile_declaration_near<'a>(
    lines: &[&'a str],
    reported_line: u64,
) -> Option<(u64, &'a str, &'a str)> {
    static DECLARATION: OnceLock<Regex> = OnceLock::new();
    let declaration = DECLARATION.get_or_init(|| {
        Regex::new(
            r"^(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(theorem|lemma|def|abbrev|opaque|axiom|structure|class|inductive|coinductive|instance)\s+([^\s(:{]+)",
        )
        .expect("valid profile declaration regex")
    });
    let index = reported_line.saturating_sub(1) as usize;
    if index >= lines.len() {
        return None;
    }
    let start = (0..index)
        .rev()
        .find(|&line| lines[line].trim().is_empty())
        .map_or(0, |line| line + 1);
    for line in (start..=index).rev() {
        if let Some(captures) = declaration.captures(lines[line].trim_start()) {
            return Some((
                line as u64 + 1,
                captures.get(1)?.as_str(),
                captures.get(2)?.as_str(),
            ));
        }
    }
    let end = lines.len().min(index + 9);
    for (line, text) in lines.iter().enumerate().take(end).skip(index + 1) {
        if text.trim().is_empty() {
            break;
        }
        if let Some(captures) = declaration.captures(text.trim_start()) {
            return Some((
                line as u64 + 1,
                captures.get(1)?.as_str(),
                captures.get(2)?.as_str(),
            ));
        }
    }
    None
}

fn compact_dependency_failure(stderr: &[u8]) -> String {
    const BLOCK_LINES: usize = 32;

    let output = String::from_utf8_lossy(stderr);
    let lines = output.lines().collect::<Vec<_>>();
    let warning_count = lines
        .iter()
        .filter(|line| line.trim_start().starts_with("warning:"))
        .count();
    let error_start = lines.iter().position(|line| {
        let line = line.trim_start();
        line.starts_with("error:") || line.contains(": error:")
    });
    let mut selected = if let Some(start) = error_start {
        let end = lines[start + 1..]
            .iter()
            .position(|line| {
                let line = line.trim_start();
                line.starts_with("warning:")
                    || line.starts_with("error:")
                    || line.contains(": error:")
                    || line.starts_with("Some required targets")
                    || line.starts_with("Failed to build")
            })
            .map_or(lines.len(), |offset| start + 1 + offset);
        let block = &lines[start..end];
        if block.len() <= BLOCK_LINES {
            block.iter().map(|line| (*line).to_owned()).collect()
        } else {
            let head = BLOCK_LINES / 2;
            let tail = BLOCK_LINES - head - 1;
            let mut compact = block[..head]
                .iter()
                .map(|line| (*line).to_owned())
                .collect::<Vec<_>>();
            compact.push(format!(
                "... {} diagnostic lines omitted ...",
                block.len() - head - tail
            ));
            compact.extend(
                block[block.len() - tail..]
                    .iter()
                    .map(|line| (*line).to_owned()),
            );
            compact
        }
    } else {
        lines
            .iter()
            .rev()
            .filter(|line| !line.trim().is_empty())
            .take(BLOCK_LINES)
            .map(|line| (*line).to_owned())
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect()
    };
    if warning_count > 0 {
        selected.push(format!("{warning_count} warnings omitted"));
    }
    let mut required_targets = false;
    for line in &lines {
        let trimmed = line.trim();
        if trimmed.starts_with("Some required targets") {
            required_targets = true;
            selected.push((*line).to_owned());
        } else if required_targets && trimmed.starts_with("- ") {
            selected.push((*line).to_owned());
        } else if trimmed.starts_with("Failed to build") {
            required_targets = false;
            selected.push((*line).to_owned());
        } else if required_targets && !trimmed.is_empty() {
            required_targets = false;
        }
    }
    selected.join("\n")
}

fn dependency_failure_is_formalization(stderr: &[u8]) -> bool {
    String::from_utf8_lossy(stderr).lines().any(|line| {
        let line = line.trim_start();
        line.contains(".lean:") && (line.starts_with("error:") || line.contains(": error:"))
    })
}

fn setup_fingerprint_path(setup_path: &Path) -> PathBuf {
    setup_path.with_extension("fingerprint")
}

fn setup_is_current(setup_path: &Path, input_fingerprint: &str) -> bool {
    setup_path.is_file()
        && fs::read_to_string(setup_fingerprint_path(setup_path))
            .is_ok_and(|fingerprint| fingerprint == input_fingerprint)
}

fn setup_is_usable(setup_path: &Path, input_fingerprint: &str) -> bool {
    if !setup_is_current(setup_path, input_fingerprint) {
        return false;
    }
    let Ok(bytes) = fs::read(setup_path) else {
        return false;
    };
    let Ok(value) = serde_json::from_slice(&bytes) else {
        return false;
    };
    let mut artifacts = BTreeSet::new();
    collect_artifact_paths(&value, &mut artifacts);
    artifacts.into_iter().all(|path| path.is_file())
}

fn materialize_setup(shared: &Path, path: &Path, input_fingerprint: &str) -> Result<()> {
    fs::create_dir_all(path.parent().context("setup path has no parent")?)?;
    if path.exists() {
        fs::remove_file(path)?;
    }
    if fs::hard_link(shared, path).is_err() {
        fs::copy(shared, path)?;
    }
    fs::write(setup_fingerprint_path(path), input_fingerprint)?;
    Ok(())
}

fn prune_shared_setups(directory: &Path, current: &Path) {
    const RETAIN_FOR: Duration = Duration::from_secs(60 * 60);

    let Ok(entries) = fs::read_dir(directory) else {
        return;
    };
    for path in entries.flatten().map(|entry| entry.path()).filter(|path| {
        path != current
            && path
                .extension()
                .is_some_and(|extension| extension == "json")
    }) {
        let Ok(metadata) = fs::metadata(&path) else {
            continue;
        };
        let old = metadata
            .modified()
            .ok()
            .and_then(|modified| modified.elapsed().ok())
            .is_some_and(|age| age >= RETAIN_FOR);
        if metadata.nlink() == 1 && old {
            let _ = fs::remove_file(setup_fingerprint_path(&path));
            let _ = fs::remove_file(path);
        }
    }
}

struct LeanWorker {
    process: LeanServiceProcess,
    environment: String,
    setup_path: PathBuf,
    version: u64,
    last_used: Instant,
    last_source: Option<String>,
    last_response: Option<WorkerResponse>,
    profile_baseline: HashMap<String, f64>,
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
        profile: bool,
    ) -> Result<Self> {
        let mut arguments = vec!["file".to_owned(), setup_path.to_string_lossy().into_owned()];
        if profile {
            arguments.push("--profile".to_owned());
        }
        let process = LeanServiceProcess::start(repo, root, &arguments)
            .context("cannot start file Lean service")?;
        Ok(Self {
            process,
            environment: environment.to_owned(),
            setup_path: setup_path.to_path_buf(),
            version: 0,
            last_used: Instant::now(),
            last_source: None,
            last_response: None,
            profile_baseline: HashMap::new(),
        })
    }

    fn request(
        &mut self,
        source: &str,
        file_name: &str,
        timeout: Duration,
        reuse_response: bool,
        action: WorkerAction<'_>,
    ) -> Result<(WorkerResponse, WorkerReuse)> {
        self.last_used = Instant::now();
        if reuse_response
            && action.operation == "check"
            && self.last_source.as_deref() == Some(source)
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
        let stderr_start = self.process.stderr_len();
        let response = self.process.request(
            &WorkerRequest {
                operation: action.operation,
                source,
                file_name,
                version: self.version,
                line: action.line,
                column: action.column,
                input: action.input,
                names: &[],
            },
            timeout,
        );
        let mut response: WorkerResponse = match response {
            Ok(response) => response,
            Err(ServiceRequestError::Timeout(_)) => return Err(CheckTimeout(timeout).into()),
            Err(ServiceRequestError::Failed(error)) => return Err(error),
        };
        ensure!(response.version == self.version, "stale Lean response");
        if !reuse_response {
            for _ in 0..10 {
                std::thread::sleep(Duration::from_millis(1));
                let stderr = self.process.stderr_since(stderr_start);
                if stderr.contains("cumulative profiling times:") {
                    let first_native = response.profile.len();
                    response.profile.extend(parse_native_profile(&stderr));
                    for entry in &mut response.profile[first_native..] {
                        if !entry.detail.is_empty() {
                            continue;
                        }
                        let cumulative = entry.duration_ms;
                        entry.duration_ms = (cumulative
                            - self
                                .profile_baseline
                                .get(&entry.kind)
                                .copied()
                                .unwrap_or_default())
                        .max(0.0);
                        self.profile_baseline.insert(entry.kind.clone(), cumulative);
                    }
                    break;
                }
            }
        }
        let response = deduplicate_diagnostics(response);
        self.last_source = Some(source.to_owned());
        self.last_response = (action.operation == "check").then(|| response.clone());
        Ok((
            response,
            WorkerReuse {
                identical: false,
                prefix_lines,
            },
        ))
    }

    fn alive(&mut self) -> bool {
        self.process.alive()
    }
}

fn parse_native_profile(output: &str) -> Vec<CheckProfileEntry> {
    let Some((events, cumulative)) = output.rsplit_once("cumulative profiling times:") else {
        return Vec::new();
    };
    let mut entries = events
        .lines()
        .filter_map(|line| {
            let (description, duration_ms) = parse_native_duration(line, " took ")?;
            let (kind, detail) = description
                .split_once(" of ")
                .map_or((description, ""), |(kind, detail)| (kind, detail));
            (!detail.is_empty()).then(|| CheckProfileEntry {
                line: 0,
                column: 0,
                kind: kind.to_owned(),
                detail: detail.to_owned(),
                duration_ms,
            })
        })
        .collect::<Vec<_>>();
    entries.extend(cumulative.lines().filter_map(|line| {
        let line = line.trim();
        let (kind, duration_ms) = parse_native_duration(line, " ")?;
        Some(CheckProfileEntry {
            line: 0,
            column: 0,
            kind: kind.to_owned(),
            detail: String::new(),
            duration_ms,
        })
    }));
    entries
}

fn parse_native_duration<'a>(line: &'a str, separator: &str) -> Option<(&'a str, f64)> {
    let (description, value) = line.trim().rsplit_once(separator)?;
    let (number, multiplier) = if let Some(number) = value.strip_suffix("ms") {
        (number, 1.0)
    } else {
        (value.strip_suffix('s')?, 1_000.0)
    };
    Some((description, number.parse::<f64>().ok()? * multiplier))
}

fn common_prefix_lines(previous: &str, current: &str) -> u64 {
    previous
        .split_inclusive('\n')
        .zip(current.split_inclusive('\n'))
        .take_while(|(left, right)| left == right)
        .count() as u64
}

fn fallback_check(repo: &Repo, root: &Path, target: &Path) -> Result<WorkerResponse> {
    let output = lake_command(repo, &lake_package_root(root, target))
        .args(["env", "lean"])
        .arg(lake_package_target(root, target))
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
        profile: Vec::new(),
        detail: String::new(),
        version: 1,
    })
}

fn deduplicate_diagnostics(mut response: WorkerResponse) -> WorkerResponse {
    let mut seen = HashSet::new();
    response
        .diagnostics
        .retain(|diagnostic| seen.insert(diagnostic.clone()));
    response.profile.sort_by(|left, right| {
        right
            .duration_ms
            .partial_cmp(&left.duration_ms)
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    let mut seen = HashSet::new();
    response.profile.retain(|entry| {
        seen.insert((
            entry.line,
            entry.column,
            entry.kind.clone(),
            entry.detail.clone(),
        ))
    });
    response.profile.truncate(PROFILE_ENTRY_LIMIT);
    response
}

fn diagnostic_fingerprint(diagnostic: &str) -> String {
    static LOCATION: OnceLock<Regex> = OnceLock::new();
    static GENERATED: OnceLock<Regex> = OnceLock::new();
    static DAGGER_SUFFIX: OnceLock<Regex> = OnceLock::new();
    let location = LOCATION.get_or_init(|| {
        Regex::new(r"^[^:\n]+:\d+:\d+:\s*").expect("valid diagnostic location regex")
    });
    let generated = GENERATED
        .get_or_init(|| Regex::new(r"\?[A-Za-z]+\.\d+").expect("valid generated name regex"));
    let dagger_suffix = DAGGER_SUFFIX
        .get_or_init(|| Regex::new(r"✝[⁰¹²³⁴⁵⁶⁷⁸⁹]+").expect("valid dagger suffix regex"));
    let without_location = location.replace(diagnostic, "");
    let without_generated = generated.replace_all(&without_location, "?_");
    let without_daggers = dagger_suffix.replace_all(&without_generated, "✝");
    without_daggers
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

fn cache_only_run(run: &CheckRun) -> bool {
    run.profile.as_ref().is_some_and(|profile| {
        !profile.files.is_empty()
            && profile
                .files
                .iter()
                .all(|file| matches!(file.mode.as_str(), "worker-cache" | "shared-cache"))
    })
}

fn matching_failed_check(
    failed_checks: &Mutex<HashMap<CheckKey, FileCheck>>,
    key: &CheckKey,
    fingerprint: &str,
) -> Option<FileCheck> {
    failed_checks
        .lock()
        .expect("failed check cache poisoned")
        .get(key)
        .filter(|cached| cached.certificate.fingerprint == fingerprint)
        .cloned()
}

fn repetition_fingerprint(diagnostic: &Diagnostic) -> String {
    let mut fingerprint = diagnostic_fingerprint(&diagnostic.text);
    if let Some(source) = diagnostic.context.as_deref().and_then(|context| {
        context.lines().find_map(|line| {
            line.trim_start()
                .strip_prefix('>')?
                .split_once('|')
                .map(|(_, source)| source.split_whitespace().collect::<Vec<_>>().join(" "))
        })
    }) && !source.is_empty()
    {
        fingerprint.push_str(" | ");
        fingerprint.push_str(&source);
    }
    fingerprint
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
    let mut files = project_lean_files(root);
    let package_root = lake_package_root(root, target);
    if package_root != root {
        files.extend(
            project_lean_files(&package_root)
                .into_iter()
                .filter_map(|path| {
                    package_root
                        .join(path)
                        .strip_prefix(root)
                        .ok()
                        .map(Path::to_path_buf)
                }),
        );
    }
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

fn maximal_check_targets(root: &Path, dirty: &[PathBuf]) -> Result<Vec<PathBuf>> {
    let ordered = dependency_order(root, dirty)?;
    let import_only = ordered
        .iter()
        .filter_map(|path| {
            fs::read_to_string(root.join(path))
                .ok()
                .filter(|source| source_is_import_only(source))
                .map(|_| path.clone())
        })
        .collect::<HashSet<_>>();
    let mut covered = HashSet::new();
    for target in ordered.iter().filter(|path| !import_only.contains(*path)) {
        covered.extend(transitive_dependencies(root, target)?);
    }
    Ok(ordered
        .into_iter()
        .filter(|target| import_only.contains(target) || !covered.contains(target))
        .collect())
}

fn source_is_import_only(source: &str) -> bool {
    source.lines().all(|line| {
        let line = line.trim();
        line.is_empty()
            || line.starts_with("--")
            || line == "module"
            || line == "prelude"
            || line.starts_with("import ")
            || line.starts_with("public import ")
    })
}

fn import_only_coverage(
    root: &Path,
    target: &Path,
    source: &str,
    dependencies: &[PathBuf],
    dirty_targets: &HashSet<PathBuf>,
    passed_targets: &HashSet<PathBuf>,
) -> Result<bool> {
    if !source_is_import_only(source)
        || dependencies
            .iter()
            .any(|path| dirty_targets.contains(path) && !passed_targets.contains(path))
    {
        return Ok(false);
    }

    let imports = parse_imports(source);
    if imports.is_empty() {
        return Ok(false);
    }
    let spec = format!("HEAD:{}", target.to_string_lossy());
    let output = Command::new("git")
        .args(["show", &spec])
        .current_dir(root)
        .stdin(Stdio::null())
        .output()
        .context("cannot inspect the checked import list")?;
    let base_imports = if output.status.success() {
        parse_imports(&String::from_utf8_lossy(&output.stdout))
    } else {
        Vec::new()
    }
    .into_iter()
    .collect::<HashSet<_>>();
    let project_modules = project_lean_files(root)
        .into_iter()
        .map(|path| (project_module_name(root, &path), path))
        .collect::<HashMap<_, _>>();
    Ok(imports.into_iter().all(|module| {
        base_imports.contains(&module)
            || project_modules
                .get(&module)
                .is_some_and(|path| !dirty_targets.contains(path) || passed_targets.contains(path))
    }))
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
    let absolute = root.join(path);
    let package_root = lake_package_root(root, path);
    let package_path = absolute.strip_prefix(&package_root).unwrap_or(path);
    let roots = source_roots(&package_root);
    let relative = roots
        .iter()
        .filter_map(|source_root| package_path.strip_prefix(source_root).ok())
        .min_by_key(|path| path.components().count())
        .unwrap_or(package_path);
    let mut path = relative.to_path_buf();
    path.set_extension("");
    path.components()
        .filter_map(|component| component.as_os_str().to_str())
        .collect::<Vec<_>>()
        .join(".")
}

fn lake_package_root(root: &Path, target: &Path) -> PathBuf {
    let absolute = root.join(target);
    absolute
        .ancestors()
        .skip(1)
        .take_while(|path| path.starts_with(root))
        .find(|path| path.join("lakefile.toml").is_file() || path.join("lakefile.lean").is_file())
        .unwrap_or(root)
        .to_path_buf()
}

fn lake_package_target(root: &Path, target: &Path) -> PathBuf {
    root.join(target)
        .strip_prefix(lake_package_root(root, target))
        .unwrap_or(target)
        .to_path_buf()
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
    let package_root = lake_package_root(root, source);
    let module = project_module_name(root, source).replace('.', "/");
    let mut artifact = package_root.join(".lake/build/lib/lean").join(module);
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
    for config in PROJECT_CONFIG_FILES {
        let path = root.join(config);
        if path.is_file() {
            material.extend_from_slice(config.as_bytes());
            material.extend_from_slice(hash_file(&path)?.as_bytes());
        }
    }
    Ok(hash_bytes(&material))
}

fn setup_artifact_fingerprint(path: &Path, immutable_artifact_roots: &[PathBuf]) -> Result<String> {
    let bytes = fs::read(path)?;
    let value: serde_json::Value = serde_json::from_slice(&bytes)?;
    let mut paths = BTreeSet::new();
    collect_artifact_paths(&value, &mut paths);
    let mut material = bytes;
    for artifact in paths {
        material.extend_from_slice(artifact.to_string_lossy().as_bytes());
        if immutable_artifact_roots
            .iter()
            .any(|root| artifact.starts_with(root))
        {
            continue;
        }
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
    for config in PROJECT_CONFIG_FILES {
        let path = root.join(config);
        if path.is_file() {
            material.extend_from_slice(hash_file(&path)?.as_bytes());
        }
    }
    Ok(hash_bytes(&material))
}

fn setup_input_fingerprint(root: &Path, target: &Path, dependencies: &[PathBuf]) -> Result<String> {
    let mut material = b"mathmux-setup-v1".to_vec();
    material.extend_from_slice(target.to_string_lossy().as_bytes());
    let target_source = fs::read_to_string(root.join(target))?;
    for line in target_source.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with("--") {
            continue;
        }
        if line == "module"
            || line == "prelude"
            || line.starts_with("import ")
            || line.starts_with("public import ")
        {
            material.extend_from_slice(line.as_bytes());
            material.push(b'\n');
            continue;
        }
        break;
    }
    let dependencies = dependencies.iter().collect::<BTreeSet<_>>();
    for dependency in dependencies {
        material.extend_from_slice(dependency.to_string_lossy().as_bytes());
        material.extend_from_slice(hash_file(&root.join(dependency))?.as_bytes());
    }
    for config in PROJECT_CONFIG_FILES {
        let path = root.join(config);
        if path.is_file() {
            material.extend_from_slice(config.as_bytes());
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
    use crate::util::run_checked;

    #[test]
    fn shared_target_wait_covers_import_and_elaboration_budgets() {
        assert_eq!(SHARED_CHECK_TIMEOUT, CHECK_QUEUE_TIMEOUT + CHECK_TIMEOUT);
    }

    fn failed_file_check(fingerprint: &str) -> FileCheck {
        FileCheck {
            certificate: CheckRecord {
                reference: "c1".into(),
                workspace_ref: "w1".into(),
                target: "Proof.lean".into(),
                fingerprint: fingerprint.into(),
                dependencies: Vec::new(),
                source_version: 1,
                created_at: 1,
            },
            warnings: Vec::new(),
            linters: Vec::new(),
            suggestions: Vec::new(),
            diagnostics: vec![Diagnostic {
                kind: "lean".into(),
                text: "declaration has errors".into(),
                context: None,
            }],
            ok: false,
            profile: FileCheckProfile {
                target: "Proof.lean".into(),
                mode: "incremental".into(),
                reused_prefix_lines: None,
                queue_ms: 0,
                dependencies_ms: 0,
                cache_ms: 0,
                setup_ms: 0,
                elaborate_ms: 1,
                total_ms: 1,
                entries: Vec::new(),
            },
        }
    }

    #[test]
    fn shared_failure_cache_requires_the_same_input() {
        let key = ("w1".into(), PathBuf::from("Proof.lean"));
        let cache = Mutex::new(HashMap::from([(key.clone(), failed_file_check("one"))]));
        assert!(matching_failed_check(&cache, &key, "one").is_some());
        assert!(matching_failed_check(&cache, &key, "two").is_none());
    }

    #[test]
    fn positioned_probes_start_at_the_first_source_token() {
        let source = "theorem demo : True := by\n    · trivial\n\t· exact True.intro\n";
        assert_eq!(first_source_column(source, 1), 2);
        assert_eq!(first_source_column(source, 2), 8);
        assert_eq!(first_source_column(source, 3), 5);
        assert_eq!(first_source_column(source, 99), 1);
    }

    #[test]
    fn duplicate_imports_are_ignored() {
        assert_eq!(
            parse_imports("import A B\npublic import A\n\ndef value := 1\n"),
            ["A", "B"]
        );
    }

    #[test]
    fn import_only_coverage_requires_checked_local_new_imports() {
        let directory = tempdir().unwrap();
        fs::write(directory.path().join("Base.lean"), "def base := 1\n").unwrap();
        fs::write(directory.path().join("Root.lean"), "import Mathlib\n").unwrap();
        run_checked("git", ["init", "-b", "main"], directory.path()).unwrap();
        run_checked("git", ["add", "."], directory.path()).unwrap();
        run_checked(
            "git",
            [
                "-c",
                "user.name=mathmux",
                "-c",
                "user.email=mathmux@example.invalid",
                "commit",
                "-m",
                "base",
            ],
            directory.path(),
        )
        .unwrap();

        let target = PathBuf::from("Root.lean");
        let dependency = PathBuf::from("Base.lean");
        let dirty = HashSet::from([target.clone(), dependency.clone()]);
        let source = "import Mathlib\nimport Base\n";
        assert!(
            !import_only_coverage(
                directory.path(),
                &target,
                source,
                std::slice::from_ref(&dependency),
                &dirty,
                &HashSet::new(),
            )
            .unwrap()
        );
        assert!(
            import_only_coverage(
                directory.path(),
                &target,
                source,
                std::slice::from_ref(&dependency),
                &dirty,
                &HashSet::from([dependency.clone()]),
            )
            .unwrap()
        );
        assert!(
            !import_only_coverage(
                directory.path(),
                &target,
                "import Mathlib\nimport Missing\n",
                &[],
                &HashSet::from([target.clone()]),
                &HashSet::new(),
            )
            .unwrap()
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
        fs::write(directory.path().join("Root.lean"), "import A.Top\n").unwrap();
        fs::write(
            directory.path().join("lean-toolchain"),
            "leanprover/lean4:v4.24.0\n",
        )
        .unwrap();
        let dependencies =
            transitive_dependencies(directory.path(), Path::new("A/Top.lean")).unwrap();
        assert_eq!(dependencies, vec![PathBuf::from("A/Base.lean")]);
        assert_eq!(
            maximal_check_targets(
                directory.path(),
                &[
                    PathBuf::from("A/Base.lean"),
                    PathBuf::from("A/Top.lean"),
                    PathBuf::from("Root.lean"),
                ],
            )
            .unwrap(),
            [PathBuf::from("A/Top.lean"), PathBuf::from("Root.lean")]
        );
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
        let immutable = directory.path().join("immutable");
        let before = setup_artifact_fingerprint(&setup, std::slice::from_ref(&immutable)).unwrap();
        fs::write(&artifact, "different size").unwrap();
        let after = setup_artifact_fingerprint(&setup, std::slice::from_ref(&immutable)).unwrap();
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
    fn setup_inputs_track_dependency_content_and_target_headers() {
        let directory = tempdir().unwrap();
        fs::write(directory.path().join("Base.lean"), "def value := 1\n").unwrap();
        fs::write(
            directory.path().join("Proof.lean"),
            "import Base\n\ntheorem result : True := by trivial\n",
        )
        .unwrap();
        let dependencies = vec![PathBuf::from("Base.lean")];
        let before =
            setup_input_fingerprint(directory.path(), Path::new("Proof.lean"), &dependencies)
                .unwrap();
        fs::write(
            directory.path().join("Proof.lean"),
            "import Base\n\ntheorem result : True := by exact True.intro\n",
        )
        .unwrap();
        let body_changed =
            setup_input_fingerprint(directory.path(), Path::new("Proof.lean"), &dependencies)
                .unwrap();
        assert_eq!(before, body_changed);

        fs::write(directory.path().join("Base.lean"), "def value := 2\n").unwrap();
        let dependency_changed =
            setup_input_fingerprint(directory.path(), Path::new("Proof.lean"), &dependencies)
                .unwrap();
        assert_ne!(before, dependency_changed);

        fs::write(directory.path().join("Base.lean"), "def value := 1\n").unwrap();
        fs::write(
            directory.path().join("Proof.lean"),
            "public import Base\n\ntheorem result : True := by exact True.intro\n",
        )
        .unwrap();
        let header_changed =
            setup_input_fingerprint(directory.path(), Path::new("Proof.lean"), &dependencies)
                .unwrap();
        assert_ne!(before, header_changed);
    }

    #[test]
    fn persisted_setup_requires_its_import_artifacts() {
        let directory = tempdir().unwrap();
        let artifact = directory.path().join("Base.olean");
        fs::write(&artifact, "compiled").unwrap();
        let setup = directory.path().join("setup.json");
        fs::write(
            &setup,
            serde_json::to_vec(&serde_json::json!({ "import": artifact })).unwrap(),
        )
        .unwrap();
        fs::write(setup_fingerprint_path(&setup), "current").unwrap();
        assert!(setup_is_usable(&setup, "current"));
        fs::remove_file(artifact).unwrap();
        assert!(!setup_is_usable(&setup, "current"));
    }

    #[test]
    fn native_profile_parses_cumulative_components() {
        let entries = parse_native_profile(
            "import took 3.16s\ncumulative profiling times:\n\telaboration 199ms\n\timport 3.16s\n",
        );
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].kind, "elaboration");
        assert_eq!(entries[0].duration_ms, 199.0);
        assert_eq!(entries[1].kind, "import");
        assert_eq!(entries[1].duration_ms, 3160.0);
    }

    #[test]
    fn profile_locations_resolve_binders_and_doc_comments_to_declarations() {
        let source = "\
theorem first
    (value : Nat) : True := by trivial

/-! context -/
/-- explanation
continued here -/
noncomputable def second : Nat := 2
";
        let lines = source.lines().collect::<Vec<_>>();
        assert_eq!(
            profile_declaration_near(&lines, 2),
            Some((1, "theorem", "first"))
        );
        assert_eq!(
            profile_declaration_near(&lines, 6),
            Some((7, "def", "second"))
        );
    }

    #[test]
    fn worker_request_matches_unified_lean_schema() {
        let request = WorkerRequest {
            operation: "check",
            source: "",
            file_name: "Demo.lean",
            version: 1,
            line: 0,
            column: 0,
            input: "",
            names: &[],
        };
        let value = serde_json::to_value(request).unwrap();
        assert_eq!(value["names"], serde_json::json!([]));
    }

    #[test]
    fn worker_profile_accepts_lean_field_names() {
        let response: WorkerResponse = serde_json::from_str(
            r#"{"ok":true,"diagnostics":[],"profile":[{"line":7,"column":1,"kind":"Elab.command","detail":"","duration_ms":12.5}],"version":1}"#,
        )
        .unwrap();
        assert_eq!(response.profile[0].line, 7);
        assert_eq!(response.profile[0].duration_ms, 12.5);
    }

    #[test]
    fn dependency_failures_keep_errors_and_drop_warning_floods() {
        let warnings = (1..=50)
            .map(|index| format!("warning: old warning {index}\n  detail {index}"))
            .collect::<Vec<_>>()
            .join("\n");
        let context = (1..=60)
            .map(|index| format!("context line {index}"))
            .collect::<Vec<_>>()
            .join("\n");
        let stderr = format!(
            "{warnings}\nerror: Demo.lean:12:3: type mismatch\n{context}\nwarning: trailing warning\nSome required targets logged failures:\n- Demo\nFailed to build module dependencies.\n"
        );
        let compact = compact_dependency_failure(stderr.as_bytes());
        assert!(compact.contains("error: Demo.lean:12:3: type mismatch"));
        assert!(compact.contains("context line 1"));
        assert!(compact.contains("context line 60"));
        assert!(compact.contains("30 diagnostic lines omitted"));
        assert!(compact.contains("51 warnings omitted"));
        assert!(compact.contains("Some required targets logged failures:\n- Demo"));
        assert!(compact.contains("Failed to build module dependencies."));
        assert!(!compact.contains("old warning"));
        assert!(compact.lines().count() <= 36);
        assert!(dependency_failure_is_formalization(stderr.as_bytes()));

        let source = (1..=15)
            .map(|line| format!("def line{line} := {line}"))
            .collect::<Vec<_>>()
            .join("\n");
        let mut diagnostics = vec![Diagnostic {
            kind: "lean.dependency".into(),
            text: compact
                .strip_prefix("error: ")
                .unwrap_or(&compact)
                .to_owned(),
            context: None,
        }];
        attach_source_context(&mut diagnostics, Path::new("Demo.lean"), &source);
        assert!(
            diagnostics[0]
                .context
                .as_deref()
                .is_some_and(|context| context.contains(">   12 | def line12 := 12"))
        );
        assert!(!dependency_failure_is_formalization(
            b"error: missing Lake package\nFailed to build module dependencies.\n"
        ));
    }

    #[test]
    fn diagnostics_are_deduplicated_and_linters_are_separate() {
        assert_eq!(
            diagnostic_fingerprint(
                "Demo.Proof:3:1: error: Type mismatch\n  ?m.127 x✝¹⁷ has type A"
            ),
            diagnostic_fingerprint("Demo.Proof:30:9: error: Type mismatch\n ?m.42 x✝² has type A")
        );
        let at = |line, source| Diagnostic {
            kind: "error".into(),
            text: format!("Demo.Proof:{line}:1: error: `simp` made no progress"),
            context: Some(format!("> {line} | {source}")),
        };
        assert_eq!(
            repetition_fingerprint(&at(3, "simp [first]")),
            repetition_fingerprint(&at(30, "simp [first]"))
        );
        assert_ne!(
            repetition_fingerprint(&at(3, "simp [first]")),
            repetition_fingerprint(&at(3, "simp [second]"))
        );
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
                kind: "declaration".into(),
                text:
                    "Proof.lean:2:1: warning: Try this: use let\nNote: This linter can be disabled"
                        .into(),
            },
            WorkerDiagnostic {
                severity: "error".into(),
                kind: "typeMismatch".into(),
                text: "Proof.lean:3:1: error: type mismatch".into(),
            },
            WorkerDiagnostic {
                severity: "error".into(),
                kind: "[anonymous]".into(),
                text: "Proof.lean:1:8: error: expected token".into(),
            },
            WorkerDiagnostic {
                severity: "error".into(),
                kind: "lean.synthInstanceFailed".into(),
                text:
                    "Proof.lean:1:9: error: failed to synthesize instance of type class\n  LE Type"
                        .into(),
            },
            WorkerDiagnostic {
                severity: "information".into(),
                kind: "tactic".into(),
                text: "Proof.lean:4:1: information: Try this: simp".into(),
            },
            WorkerDiagnostic {
                severity: "warning".into(),
                kind: "declaration".into(),
                text: "Proof.lean:4:1: warning: Try this: simp".into(),
            },
            WorkerDiagnostic {
                severity: "information".into(),
                kind: "trace".into(),
                text: "Proof.lean:5:1: information: ordinary trace".into(),
            },
        ];
        let (warnings, linters, suggestions, mut errors) = partition_diagnostics(&diagnostics);
        assert_eq!(
            (
                warnings.len(),
                linters.len(),
                suggestions.len(),
                errors.len()
            ),
            (1, 1, 2, 3)
        );
        assert!(errors[0].text.contains("expected token"));
        assert!(errors[0].text.contains("notation may be inactive"));
        attach_source_context(
            &mut errors,
            Path::new("Proof.lean"),
            "first\nsecond\nproblem\nfourth\nfifth\n",
        );
        assert_eq!(
            errors[1].context.as_deref(),
            Some(
                "     1 | first\n     2 | second\n>    3 | problem\n     4 | fourth\n     5 | fifth"
            )
        );

        let mut instance_error = vec![Diagnostic {
            kind: "lean.synthInstanceFailed".into(),
            text:
                "Proof.lean:9:1: error: failed to synthesize instance of type class\n  Nonempty B"
                    .into(),
            context: None,
        }];
        attach_source_context(
            &mut instance_error,
            Path::new("Proof.lean"),
            "namespace Demo\nvariable {B : Type}\nvariable [TopologicalSpace B]\n\ntheorem prior : True := by trivial\n\ntheorem current : True := by\n  have := True.intro\n  exact this\n",
        );
        let context = instance_error[0].context.as_deref().unwrap();
        assert!(context.contains("2 | variable {B : Type}"));
        assert!(context.contains("3 | variable [TopologicalSpace B]"));
        assert!(context.contains(">    9 |   exact this"));

        let (_, _, _, notation_errors) = partition_diagnostics(&[WorkerDiagnostic {
            severity: "error".into(),
            kind: "unsupportedSyntax".into(),
            text:
                "elaboration function for `Mathlib.Tactic.subscriptTerm` has not been implemented"
                    .into(),
        }]);
        assert!(notation_errors[0].text.contains("open its scoped notation"));

        let (_, _, _, decidable_errors) = partition_diagnostics(&[WorkerDiagnostic {
            severity: "error".into(),
            kind: "lean.synthInstanceFailed".into(),
            text: "Proof.lean:7:1: error: failed to synthesize instance of type class\n  DecidableEq α".into(),
        }]);
        assert!(decidable_errors[0].text.contains("add `classical` locally"));

        let (_, _, _, coherence_errors) = partition_diagnostics(&[WorkerDiagnostic {
            severity: "error".into(),
            kind: "lean.synthInstanceMismatch".into(),
            text: "Proof.lean:8:1: error: synthesized type class instance is not definitionally equal to expression inferred by typing rules".into(),
        }]);
        assert!(coherence_errors[0].text.contains("same local instance"));

        errors[1].text = "Demo.Nested.Proof:3:1: error: type mismatch".into();
        errors[1].context = None;
        attach_source_context(
            &mut errors,
            Path::new("Demo/Nested/Proof.lean"),
            "first\nsecond\nproblem\nfourth\nfifth\n",
        );
        assert!(
            errors[1]
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

    #[test]
    fn nested_lake_packages_resolve_sibling_modules_and_artifacts() {
        let root = tempdir().unwrap();
        fs::write(root.path().join("lakefile.toml"), "name = \"root\"\n").unwrap();
        let nested = root.path().join("comparator/example");
        fs::create_dir_all(&nested).unwrap();
        fs::write(nested.join("lakefile.toml"), "name = \"example\"\n").unwrap();
        fs::write(nested.join("Challenge.lean"), "def challenge := 1\n").unwrap();
        fs::write(
            nested.join("Review.lean"),
            "import Challenge\n#check challenge\n",
        )
        .unwrap();
        run_checked("git", ["init", "-b", "main"], root.path()).unwrap();
        run_checked("git", ["add", "."], root.path()).unwrap();
        let target = Path::new("comparator/example/Review.lean");
        assert_eq!(lake_package_root(root.path(), target), nested);
        assert_eq!(
            lake_package_target(root.path(), target),
            Path::new("Review.lean")
        );
        assert_eq!(project_module_name(root.path(), target), "Review");
        assert_eq!(
            transitive_dependencies(root.path(), target).unwrap(),
            vec![PathBuf::from("comparator/example/Challenge.lean")]
        );
        assert_eq!(
            artifact_path(root.path(), Path::new("comparator/example/Challenge.lean")),
            nested.join(".lake/build/lib/lean/Challenge.olean")
        );
    }
}
