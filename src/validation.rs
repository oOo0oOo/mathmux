use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use crate::artifact_cache::{restore_available_olean, restore_olean};
use crate::check::{Checker, parse_imports, project_module_name};
use crate::coordination::{lock_exclusive, open_lock};
use crate::git::{background_lake_command, lake_command, project_lean_files};
use crate::issue::{TelemetryOperation, TelemetryStore};
use crate::repo::Repo;
use crate::state::{State, Submission, ValidationReport, ValidationStatus};
use crate::util::{
    build_error_diagnostic, command_detail, output_text, run_checked, run_command_with_timeout,
    run_output,
};
use anyhow::{Context, Result, bail};

type ValidationSignal = Arc<(Mutex<bool>, Condvar)>;

// Validation builds the entire managed project, so it gets a larger bounded
// budget than an individual check while still releasing the validation lock
// when a compiler or dependency process stalls.
const VALIDATION_BUILD_TIMEOUT: Duration = Duration::from_secs(60 * 60);
const AXIOM_AUDIT_TIMEOUT: Duration = Duration::from_secs(10 * 60);
const VALIDATION_PERSIST_RETRY_DELAY: Duration = Duration::from_secs(1);

#[derive(Clone)]
pub struct ValidationQueue {
    signal: ValidationSignal,
}

impl ValidationQueue {
    pub fn start(
        repo: Repo,
        state: State,
        checker: Arc<Checker>,
        retiring: Arc<AtomicBool>,
        telemetry: Option<Arc<TelemetryStore>>,
    ) -> Result<Self> {
        let queue = Self {
            signal: Arc::new((Mutex::new(false), Condvar::new())),
        };
        let signal = queue.signal.clone();
        thread::Builder::new()
            .name("mathmux-validation".into())
            .spawn(move || validation_loop(repo, state, checker, signal, retiring, telemetry))?;
        Ok(queue)
    }

    pub fn wake(&self) {
        let (lock, condition) = &*self.signal;
        *lock.lock().expect("validation signal poisoned") = true;
        condition.notify_one();
    }
}

fn validation_loop(
    repo: Repo,
    state: State,
    checker: Arc<Checker>,
    signal: ValidationSignal,
    retiring: Arc<AtomicBool>,
    telemetry: Option<Arc<TelemetryStore>>,
) {
    loop {
        if retiring.load(Ordering::SeqCst) {
            return;
        }
        let validation_lock = match acquire_validation_lock(&repo.validation_lock) {
            Ok(lock) => lock,
            Err(_) => {
                thread::sleep(Duration::from_secs(1));
                continue;
            }
        };
        if retiring.load(Ordering::SeqCst) {
            return;
        }
        if host_load_brake() {
            drop(validation_lock);
            thread::sleep(Duration::from_secs(30));
            continue;
        }
        let next = state
            .recover_validation()
            .and_then(|_| state.next_validation());
        match next {
            Ok(Some(submission)) => {
                // Full validation is memory-heavy. Release only idle
                // incremental check workers before starting it; a busy worker
                // cannot be evicted and its live request remains untouched.
                let _ = checker.evict_idle_workers(Duration::ZERO);
                let started = Instant::now();
                let result = validate(&repo, &submission);
                let report = match result {
                    Ok(report) => report,
                    Err(error) => failed_report(
                        started,
                        format!("validation failed: {error:#}"),
                        String::new(),
                        Vec::new(),
                    ),
                };
                finish_validation_until_persisted(
                    &repo,
                    &state,
                    &submission.reference,
                    &report,
                    VALIDATION_PERSIST_RETRY_DELAY,
                );
                if let Some(store) = &telemetry {
                    let _ = store.record_operation(
                        &repo,
                        &TelemetryOperation {
                            workspace: Some(&submission.workspace_ref),
                            verb: "validation",
                            reference: Some(&submission.reference),
                            ok: report.passed,
                            duration_ms: report.duration_ms,
                            detail: &report.detail,
                            rss_kib: None,
                        },
                    );
                }
            }
            Ok(None) => {
                drop(validation_lock);
                let (lock, condition) = &*signal;
                let pending = lock.lock().expect("validation signal poisoned");
                let _ = condition
                    .wait_timeout_while(pending, Duration::from_secs(30), |value| !*value)
                    .map(|(mut pending, _)| *pending = false);
            }
            Err(_) => {
                drop(validation_lock);
                thread::sleep(Duration::from_secs(1));
            }
        }
    }
}

fn finish_validation_until_persisted(
    repo: &Repo,
    state: &State,
    reference: &str,
    report: &ValidationReport,
    retry_delay: Duration,
) -> u64 {
    let mut retries = 0_u64;
    loop {
        match state.finish_validation(reference, report) {
            Ok(()) => {
                if retries > 0 {
                    log_validation_persistence(
                        repo,
                        reference,
                        &format!("validation result persisted after {retries} retry(ies)"),
                    );
                }
                return retries;
            }
            Err(error) => {
                // `finish_validation` commits the terminal row before its
                // best-effort build-log pruning. If that cleanup is the only
                // failure, do not keep a durable terminal result looking
                // active while retrying it.
                if state
                    .submission(reference)
                    .ok()
                    .flatten()
                    .is_some_and(|submission| {
                        matches!(
                            submission.validation_status,
                            ValidationStatus::Passed
                                | ValidationStatus::Failed
                                | ValidationStatus::Skipped
                        )
                    })
                {
                    log_validation_persistence(
                        repo,
                        reference,
                        &format!("terminal state persisted; cleanup retry stopped: {error:#}"),
                    );
                    return retries;
                }
                retries += 1;
                if retries == 1 || retries.is_multiple_of(60) {
                    log_validation_persistence(
                        repo,
                        reference,
                        &format!("validation result persistence failed ({error:#}); retrying"),
                    );
                }
                thread::sleep(retry_delay);
            }
        }
    }
}

fn log_validation_persistence(repo: &Repo, reference: &str, detail: &str) {
    if let Ok(mut log) = fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&repo.log_path)
    {
        let _ = writeln!(log, "{reference}: {detail}");
    }
}

fn host_load_brake() -> bool {
    let Ok(loadavg) = fs::read_to_string("/proc/loadavg") else {
        return false;
    };
    let cpus = std::thread::available_parallelism()
        .map(usize::from)
        .unwrap_or(1);
    host_load_brake_for(&loadavg, cpus)
}

fn host_load_brake_for(loadavg: &str, cpus: usize) -> bool {
    let Some(load) = loadavg
        .split_whitespace()
        .next()
        .and_then(|value| value.parse::<f64>().ok())
    else {
        return false;
    };
    load >= cpus.max(1) as f64
}

fn acquire_validation_lock(path: &Path) -> Result<fs::File> {
    let lock = open_lock(path)?;
    lock_exclusive(&lock)?;
    Ok(lock)
}

fn validate(repo: &Repo, submission: &Submission) -> Result<ValidationReport> {
    let started = Instant::now();
    let root = prepare_worktree(repo, &submission.main_commit)?;
    let (roots, project_modules) = deliverable_modules(&root);
    invalidate_newer_project_artifacts(&root)?;
    // A timed-out build may leave cached outputs and their Lake traces behind
    // while removing the corresponding worktree artifacts. Restore those
    // reusable outputs before asking Lake to rebuild the project.
    restore_available_project_oleans(&repo.cache_dir, &root, &project_modules)?;
    let mut build = background_lake_command(repo, &root);
    build.arg("build").args(&roots);
    let output = run_command_with_timeout(build, VALIDATION_BUILD_TIMEOUT, "validation build")
        .context("cannot run validation build")?;
    let build_output = combined_output(&output);
    if !output.status.success() {
        return Ok(failed_report(
            started,
            build_failure_detail(&build_output, output.status.code()),
            build_output,
            Vec::new(),
        ));
    }
    restore_project_oleans(&repo.cache_dir, &root, &project_modules)?;
    let audit = match run_axiom_audit(repo, &root, &roots, &project_modules) {
        Ok(audit) => audit,
        Err(error) => {
            return Ok(failed_report(
                started,
                axiom_audit_detail(&format!("{error:#}")),
                build_output,
                Vec::new(),
            ));
        }
    };
    let passed = audit.axioms.is_empty();
    let detail = validation_detail_for_audit(&audit, project_modules.len());
    Ok(ValidationReport {
        passed,
        sorry_audit: true,
        detail,
        build_output,
        axioms: audit.axioms,
        sorries: audit.sorries,
        duration_ms: started.elapsed().as_millis() as u64,
    })
}

fn validation_detail_for_audit(audit: &AxiomAudit, module_count: usize) -> String {
    if audit.axioms.is_empty() {
        format!(
            "build passed; axioms clean ({} modules)",
            module_count
        )
    } else if audit.native_decides.is_empty() {
        format!(
            "build passed; {} extra axiom{}",
            audit.axioms.len(),
            if audit.axioms.len() == 1 { "" } else { "s" }
        )
    } else {
        format!(
            "build passed; native_decide detected in {} declaration{}: {}; {} extra axiom{}",
            audit.native_decides.len(),
            if audit.native_decides.len() == 1 {
                ""
            } else {
                "s"
            },
            audit.native_decides.join(", "),
            audit.axioms.len(),
            if audit.axioms.len() == 1 { "" } else { "s" }
        )
    }
}

fn axiom_audit_detail(detail: &str) -> String {
    if detail.starts_with("axiom audit failed:") {
        detail.to_owned()
    } else {
        format!("axiom audit failed: {detail}")
    }
}

fn invalidate_newer_project_artifacts(root: &Path) -> Result<()> {
    for source in project_lean_files(root) {
        let absolute_source = root.join(&source);
        let mut artifact = root
            .join(".lake/build/lib/lean")
            .join(project_module_name(root, &source).replace('.', "/"));
        artifact.set_extension("olean");
        let Ok(artifact_metadata) = fs::metadata(&artifact) else {
            continue;
        };
        let source_modified = fs::metadata(&absolute_source)?.modified()?;
        if source_modified <= artifact_metadata.modified()? {
            continue;
        }
        for extension in ["olean", "olean.hash", "ilean", "ilean.hash", "trace"] {
            let candidate = artifact.with_extension(extension);
            if candidate.is_file() {
                fs::remove_file(&candidate)
                    .with_context(|| format!("cannot invalidate {}", candidate.display()))?;
            }
        }
    }
    Ok(())
}

fn build_failure_detail(output: &str, exit_code: Option<i32>) -> String {
    if let Some(diagnostic) = missing_import_diagnostic(output) {
        return format!("build failed: {diagnostic}");
    }
    if let Some(diagnostic) = build_error_diagnostic(output) {
        return format!("build failed: {diagnostic}");
    }
    match exit_code {
        Some(code) => format!("build failed with exit code {code}; no Lean error diagnostic"),
        None => "build failed: process terminated by a signal or external interruption; no Lean error diagnostic".into(),
    }
}

fn missing_import_diagnostic(output: &str) -> Option<String> {
    const BAD_IMPORT_MARKER: &str = ": bad import '";

    let mut imports = Vec::new();
    for line in output.lines() {
        let line = line.trim();
        let line = line.strip_prefix("error:").unwrap_or(line).trim();
        let Some((importer, imported)) = line.split_once(BAD_IMPORT_MARKER) else {
            continue;
        };
        let Some(imported) = imported.strip_suffix('\'') else {
            continue;
        };
        let importer = importer.trim();
        if importer.is_empty() || imported.is_empty() {
            continue;
        }
        let entry = format!("'{imported}' required by {importer}");
        if !imports.contains(&entry) {
            imports.push(entry);
        }
    }

    match imports.as_slice() {
        [] => None,
        [entry] => Some(format!("missing source import {entry}")),
        entries => Some(format!("missing source imports: {}", entries.join("; "))),
    }
}

fn failed_report(
    started: Instant,
    detail: impl Into<String>,
    build_output: String,
    sorries: Vec<String>,
) -> ValidationReport {
    ValidationReport {
        passed: false,
        sorry_audit: false,
        detail: detail.into(),
        build_output,
        axioms: Vec::new(),
        sorries,
        duration_ms: started.elapsed().as_millis() as u64,
    }
}

fn restore_project_oleans(cache_dir: &Path, root: &Path, modules: &[String]) -> Result<()> {
    for module in modules {
        let artifact = root
            .join(".lake/build/lib/lean")
            .join(module.replace('.', "/"))
            .with_extension("olean");
        restore_olean(cache_dir, &artifact)
            .with_context(|| format!("cannot restore cached artifact for {module}"))?;
    }
    Ok(())
}

fn restore_available_project_oleans(
    cache_dir: &Path,
    root: &Path,
    modules: &[String],
) -> Result<usize> {
    let mut restored = 0;
    for module in modules {
        let artifact = root
            .join(".lake/build/lib/lean")
            .join(module.replace('.', "/"))
            .with_extension("olean");
        if restore_available_olean(cache_dir, &artifact)? {
            restored += 1;
        }
    }
    Ok(restored)
}

fn combined_output(output: &std::process::Output) -> String {
    let stdout = output_text(&output.stdout);
    let stderr = output_text(&output.stderr);
    if stdout.is_empty() {
        stderr
    } else if stderr.is_empty() {
        stdout
    } else {
        format!("{stdout}\n{stderr}")
    }
}

fn prepare_worktree(repo: &Repo, commit: &str) -> Result<PathBuf> {
    let path = repo.state_dir.join("validation-worktree");
    if !path.join(".git").exists() {
        if path.exists() {
            fs::remove_dir_all(&path)
                .with_context(|| format!("cannot replace {}", path.display()))?;
        }
        let output = run_output(
            "git",
            [
                "worktree",
                "add",
                "--detach",
                path.to_string_lossy().as_ref(),
                commit,
            ],
            &repo.root,
        )?;
        if !output.status.success() {
            bail!(
                "cannot create validation worktree: {}",
                command_detail(&output)
            );
        }
    } else {
        run_checked("git", ["reset", "--hard", commit], &path)?;
        run_checked("git", ["clean", "-fd"], &path)?;
    }
    crate::git::prepare_workspace(repo, &path)?;
    Ok(path)
}

fn deliverable_modules(root: &Path) -> (Vec<String>, Vec<String>) {
    let files = project_lean_files(root);
    let mut project_modules = files
        .iter()
        .map(|path| project_module_name(root, path))
        .collect::<Vec<_>>();
    project_modules.sort();
    project_modules.dedup();
    let project_set = project_modules
        .iter()
        .cloned()
        .collect::<std::collections::HashSet<_>>();
    let imported = files
        .iter()
        .filter_map(|path| fs::read_to_string(root.join(path)).ok())
        .flat_map(|source| parse_imports(&source))
        .filter(|module| project_set.contains(module))
        .collect::<std::collections::HashSet<_>>();
    let mut roots = project_modules
        .iter()
        .filter(|module| !imported.contains(*module))
        .cloned()
        .collect::<Vec<_>>();
    if roots.is_empty() {
        roots.clone_from(&project_modules);
    }
    roots.sort();
    (roots, project_modules)
}

struct AxiomAudit {
    axioms: Vec<String>,
    native_decides: Vec<String>,
    sorries: Vec<String>,
}

const AXIOM_AUDIT_MAX_REC_DEPTH: usize = 100_000;
const NATIVE_DECIDE_AXIOM_MARKER: &str = "._native.native_decide.ax_";

fn is_native_decide_axiom(axiom: &str) -> bool {
    axiom.contains(NATIVE_DECIDE_AXIOM_MARKER)
}

fn parse_axiom_audit_output(text: &str) -> (Vec<String>, Vec<String>, Vec<String>) {
    let mut axioms = Vec::new();
    let mut native_decides = Vec::new();
    let mut sorries = Vec::new();
    for line in text.lines() {
        if let Some(line) = line.strip_prefix("MATHMUX_AXIOM\t") {
            let Some((axiom, declaration)) = line.split_once('\t') else {
                continue;
            };
            axioms.push(axiom.to_owned());
            if is_native_decide_axiom(axiom) {
                native_decides.push(declaration.to_owned());
            }
        } else if let Some(declaration) = line.strip_prefix("MATHMUX_SORRY\t") {
            sorries.push(declaration.to_owned());
        }
    }
    axioms.sort();
    axioms.dedup();
    native_decides.sort();
    native_decides.dedup();
    sorries.sort();
    sorries.dedup();
    (axioms, native_decides, sorries)
}

fn axiom_audit_command_args() -> Vec<String> {
    vec![
        "env".into(),
        "lean".into(),
        "-D".into(),
        format!("maxRecDepth={AXIOM_AUDIT_MAX_REC_DEPTH}"),
        "--run".into(),
    ]
}

fn run_axiom_audit(
    repo: &Repo,
    root: &Path,
    roots: &[String],
    project_modules: &[String],
) -> Result<AxiomAudit> {
    if roots.is_empty() {
        return Ok(AxiomAudit {
            axioms: Vec::new(),
            native_decides: Vec::new(),
            sorries: Vec::new(),
        });
    }
    let imports = roots
        .iter()
        .map(|module| format!("{{ module := `{module} }}"))
        .collect::<Vec<_>>()
        .join(", ");
    let names = project_modules
        .iter()
        .map(|module| format!("`{module}"))
        .collect::<Vec<_>>()
        .join(", ");
    let source = format!(
        r#"import Lean
import Lean.Util.CollectAxioms

open Lean

unsafe def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{imports}] {{}} 0
  let projectModules : NameSet := #[{names}].foldl (fun set name => set.insert name) {{}}
  let allowed : NameSet := #[`propext, `Classical.choice, `Quot.sound].foldl
    (fun set name => set.insert name) {{}}
  let context : Core.Context := {{ fileName := "<mathmux-audit>", fileMap := default }}
  let state : Core.State := {{ env }}
  let mut failures : Array (Name × Name) := #[]
  let mut sorries : Array Name := #[]
  let projectConstants := env.checked.get.constants.foldStage2
    (fun names name _ =>
      match env.getModuleIdxFor? name with
      | some index =>
          let origin := env.header.moduleNames[index.toNat]!
          if projectModules.contains origin then names.push name else names
      | none => names) #[]
  for name in projectConstants do
    let action : CoreM (Array Name) := collectAxioms name
    let (axioms, _) ← action.toIO context state
    for axiomName in axioms do
      if axiomName == `sorryAx then
        sorries := sorries.push name
      else if !allowed.contains axiomName then
        failures := failures.push (axiomName, name)
  for name in sorries do
    IO.println s!"MATHMUX_SORRY\t{{name}}"
  for (axiomName, name) in failures do
    IO.println s!"MATHMUX_AXIOM\t{{axiomName}}\t{{name}}"
  return if failures.isEmpty then 0 else 1
"#
    );
    let path = repo.state_dir.join("MathmuxAxiomAudit.lean");
    fs::write(&path, source)?;
    let mut command = lake_command(repo, root);
    command.args(axiom_audit_command_args()).arg(&path);
    let output = run_command_with_timeout(command, AXIOM_AUDIT_TIMEOUT, "axiom audit")
        .context("cannot run axiom audit")?;
    let text = combined_output(&output);
    let (failures, native_decides, sorries) = parse_axiom_audit_output(&text);
    if !output.status.success() && failures.is_empty() {
        bail!("axiom audit failed: {}", command_detail(&output));
    }
    Ok(AxiomAudit {
        axioms: failures,
        native_decides,
        sorries,
    })
}

#[cfg(test)]
mod tests {
    use rusqlite::Connection;
    use tempfile::tempdir;

    use super::*;
    use crate::util::CommandTimeout;

    #[test]
    fn host_load_brake_matches_cpu_capacity() {
        assert!(!host_load_brake_for("23.99 20.0 18.0 1/1 1", 24));
        assert!(host_load_brake_for("24.00 20.0 18.0 1/1 1", 24));
        assert!(host_load_brake_for("29.06 20.0 18.0 1/1 1", 24));
        assert!(!host_load_brake_for("unavailable", 24));
    }

    #[test]
    fn axiom_audit_errors_are_labeled_once() {
        assert_eq!(
            axiom_audit_detail("axiom audit failed: uncaught exception"),
            "axiom audit failed: uncaught exception"
        );
        assert_eq!(
            axiom_audit_detail("cannot start axiom audit"),
            "axiom audit failed: cannot start axiom audit"
        );
    }

    #[test]
    fn axiom_audit_raises_recursion_limit_for_large_generated_inputs() {
        assert_eq!(
            axiom_audit_command_args(),
            ["env", "lean", "-D", "maxRecDepth=100000", "--run"]
        );
    }

    #[test]
    fn axiom_audit_classifies_native_decide_fixture_without_allowing_it() {
        let fixture = concat!(
            "MATHMUX_AXIOM\t",
            "AtiyahSinger.ExteriorKoszul.exteriorBasisTwo_singleton_zero._native.native_decide.ax_1",
            "\tAtiyahSinger.ExteriorKoszul.exteriorBasisTwo_singleton_zero\n",
            "MATHMUX_AXIOM\tUnsafe.assume\tDemo.bad\n",
            "MATHMUX_SORRY\tDemo.sorry\n",
        );
        let (axioms, native_decides, sorries) = parse_axiom_audit_output(fixture);

        assert_eq!(
            axioms,
            [
                "AtiyahSinger.ExteriorKoszul.exteriorBasisTwo_singleton_zero._native.native_decide.ax_1",
                "Unsafe.assume",
            ]
        );
        assert_eq!(
            native_decides,
            ["AtiyahSinger.ExteriorKoszul.exteriorBasisTwo_singleton_zero"]
        );
        assert_eq!(sorries, ["Demo.sorry"]);
        assert!(is_native_decide_axiom(
            "AtiyahSinger.ExteriorKoszul.exteriorBasisTwo_singleton_zero._native.native_decide.ax_1"
        ));
        assert!(!is_native_decide_axiom("Lean.ofReduceBool"));
        let audit = AxiomAudit {
            axioms,
            native_decides,
            sorries,
        };
        assert_eq!(
            validation_detail_for_audit(&audit, 2665),
            "build passed; native_decide detected in 1 declaration: "
                .to_owned()
                + "AtiyahSinger.ExteriorKoszul.exteriorBasisTwo_singleton_zero; 2 extra axioms"
        );
    }

    #[test]
    fn validation_phase_timeout_diagnostics_name_the_phase() {
        for phase in ["validation build", "axiom audit"] {
            let mut command = std::process::Command::new("sh");
            command.args(["-c", "sleep 30 & wait"]);
            let error = run_command_with_timeout(command, Duration::from_millis(50), phase)
                .expect_err("validation phase should time out");
            let timeout = error
                .downcast_ref::<CommandTimeout>()
                .expect("timeout error should retain its phase");
            assert_eq!(timeout.phase, phase);
            assert_eq!(timeout.timeout, Duration::from_millis(50));
            assert!(error.to_string().contains(&format!(
                "{phase} exceeded 50ms; child process group terminated"
            )));
        }
    }
    use crate::state::Workspace;

    #[test]
    fn validation_finish_retries_until_the_terminal_row_is_durable() {
        let directory = tempdir().unwrap();
        let state_dir = directory.path().join("state");
        fs::create_dir_all(&state_dir).unwrap();
        let repo = Repo {
            root: directory.path().join("root"),
            common_git_dir: directory.path().join("git"),
            state_dir: state_dir.clone(),
            socket_path: state_dir.join("daemon.sock"),
            db_path: state_dir.join("state.sqlite3"),
            search_db_path: state_dir.join("search.sqlite3"),
            log_path: state_dir.join("daemon.log"),
            cache_dir: state_dir.join("cache"),
            integration_lock: state_dir.join("integration.lock"),
            validation_lock: state_dir.join("validation.lock"),
            startup_lock: state_dir.join("startup.lock"),
        };
        let state = State::new(repo.db_path.clone()).unwrap();
        state
            .add_workspace(&Workspace {
                reference: "w1".into(),
                name: "agent".into(),
                path: directory.path().join("agent"),
                branch: "mathmux/agent".into(),
                model: None,
            })
            .unwrap();
        state
            .add_submission(&Submission {
                reference: "s1".into(),
                workspace_ref: "w1".into(),
                workspace_commit: "workspace".into(),
                main_commit: "main".into(),
                base_commit: "base".into(),
                checks: vec!["c1".into()],
                validation_status: ValidationStatus::Queued,
                validation_detail: None,
                build_output: None,
                build_summary: None,
                axioms: Vec::new(),
                sorries: Vec::new(),
                validation_duration_ms: None,
                validated_by: None,
                created_at: 1,
            })
            .unwrap();
        assert_eq!(state.next_validation().unwrap().unwrap().reference, "s1");

        Connection::open(&repo.db_path)
            .unwrap()
            .execute("DROP TABLE build_log_summaries", [])
            .unwrap();
        let db_path = repo.db_path.clone();
        let restore = thread::spawn(move || {
            thread::sleep(Duration::from_millis(25));
            Connection::open(db_path)
                .unwrap()
                .execute(
                    "CREATE TABLE build_log_summaries (
                        submission_ref TEXT PRIMARY KEY REFERENCES submissions(ref),
                        summary_json TEXT NOT NULL
                     )",
                    [],
                )
                .unwrap();
        });
        let retries = finish_validation_until_persisted(
            &repo,
            &state,
            "s1",
            &ValidationReport {
                passed: true,
                sorry_audit: true,
                detail: "build passed".into(),
                build_output: "output".into(),
                axioms: Vec::new(),
                sorries: Vec::new(),
                duration_ms: 25,
            },
            Duration::from_millis(10),
        );
        restore.join().unwrap();

        assert!(retries > 0);
        assert_eq!(
            state.submission("s1").unwrap().unwrap().validation_status,
            ValidationStatus::Passed
        );
    }

    #[test]
    fn build_failure_detail_prefers_the_concrete_lean_error() {
        let output = "warning: unrelated\nerror: Demo.lean:12:4: failed to synthesize CompactSpace B\nerror: build failed\n";
        assert_eq!(
            build_failure_detail(output, Some(1)),
            "build failed: Demo.lean:12:4: failed to synthesize CompactSpace B"
        );
    }

    #[test]
    fn build_failure_detail_names_missing_imports_before_generic_lake_errors() {
        let output = concat!(
            "error: no such file or directory (error code: 2)\n",
            "error: AtiyahSinger/Consumer.lean: bad import '",
            "AtiyahSinger.Missing",
            "'\n",
            "error: AtiyahSinger/Guards/ConsumerGuard.lean: bad import '",
            "AtiyahSinger.Consumer",
            "'\n",
        );
        let expected = concat!(
            "build failed: missing source imports: '",
            "AtiyahSinger.Missing' required by AtiyahSinger/Consumer.lean; '",
            "AtiyahSinger.Consumer' required by AtiyahSinger/Guards/ConsumerGuard.lean",
        );
        assert_eq!(build_failure_detail(output, Some(2)), expected);
    }

    #[test]
    fn build_failure_detail_distinguishes_exit_and_signal_without_diagnostics() {
        assert_eq!(
            build_failure_detail("error: build failed\n", Some(137)),
            "build failed with exit code 137; no Lean error diagnostic"
        );
        assert_eq!(
            build_failure_detail("", None),
            "build failed: process terminated by a signal or external interruption; no Lean error diagnostic"
        );
    }

    #[test]
    fn a_new_queue_does_not_recover_an_active_validator() {
        let directory = tempdir().unwrap();
        let state_dir = directory.path().join("state");
        fs::create_dir_all(&state_dir).unwrap();
        let repo = Repo {
            root: directory.path().join("root"),
            common_git_dir: directory.path().join("git"),
            state_dir: state_dir.clone(),
            socket_path: state_dir.join("daemon.sock"),
            db_path: state_dir.join("state.sqlite3"),
            search_db_path: state_dir.join("search.sqlite3"),
            log_path: state_dir.join("daemon.log"),
            cache_dir: state_dir.join("cache"),
            integration_lock: state_dir.join("integration.lock"),
            validation_lock: state_dir.join("validation.lock"),
            startup_lock: state_dir.join("startup.lock"),
        };
        let state = State::new(repo.db_path.clone()).unwrap();
        state
            .add_workspace(&Workspace {
                reference: "w1".into(),
                name: "agent".into(),
                path: directory.path().join("agent"),
                branch: "mathmux/agent".into(),
                model: None,
            })
            .unwrap();
        state
            .add_submission(&Submission {
                reference: "s1".into(),
                workspace_ref: "w1".into(),
                workspace_commit: "workspace".into(),
                main_commit: "main".into(),
                base_commit: "base".into(),
                checks: vec!["c1".into()],
                validation_status: ValidationStatus::Queued,
                validation_detail: None,
                build_output: None,
                build_summary: None,
                axioms: Vec::new(),
                sorries: Vec::new(),
                validation_duration_ms: None,
                validated_by: None,
                created_at: 1,
            })
            .unwrap();
        assert_eq!(state.next_validation().unwrap().unwrap().reference, "s1");
        let active_lock = acquire_validation_lock(&repo.validation_lock).unwrap();
        let retiring = Arc::new(AtomicBool::new(false));
        let checker = Arc::new(Checker::new(repo.clone(), state.clone(), None).unwrap());
        let _queue =
            ValidationQueue::start(repo, state.clone(), checker, retiring.clone(), None).unwrap();

        assert!(state.has_running_validation().unwrap());
        retiring.store(true, Ordering::SeqCst);
        drop(active_lock);
        thread::sleep(Duration::from_millis(20));
    }

    #[test]
    fn deliverable_modules_are_unimported_project_roots() {
        let directory = tempdir().unwrap();
        fs::write(directory.path().join("Base.lean"), "def base := 1\n").unwrap();
        fs::write(
            directory.path().join("Result.lean"),
            "import Base\n\ndef result := base\n",
        )
        .unwrap();
        fs::write(
            directory.path().join("Independent.lean"),
            "def other := 2\n",
        )
        .unwrap();
        let comparator = directory.path().join("comparator");
        fs::create_dir(&comparator).unwrap();
        fs::write(comparator.join("lakefile.toml"), "name = \"comparator\"\n").unwrap();
        fs::write(comparator.join("Challenge.lean"), "def challenge := 3\n").unwrap();

        let (roots, modules) = deliverable_modules(directory.path());
        assert_eq!(roots, ["Independent", "Result"]);
        assert_eq!(modules, ["Base", "Independent", "Result"]);
    }

    #[test]
    fn only_project_oleans_are_restored_from_the_artifact_cache() {
        let directory = tempdir().unwrap();
        let root = directory.path().join("worktree");
        let cache = directory.path().join("cache");
        let hash = "0123456789abcdef";
        let artifact = root.join(".lake/build/lib/lean/Demo/Result.olean");
        fs::create_dir_all(artifact.parent().unwrap()).unwrap();
        fs::write(artifact.with_extension("olean.hash"), hash).unwrap();
        fs::create_dir_all(cache.join("artifacts")).unwrap();
        fs::write(
            cache.join("artifacts").join(format!("{hash}.olean")),
            "olean",
        )
        .unwrap();

        restore_project_oleans(&cache, &root, &["Demo.Result".into()]).unwrap();
        assert_eq!(fs::read_to_string(artifact).unwrap(), "olean");
    }

    #[test]
    fn project_oleans_are_restored_from_synthetic_lake_traces() {
        let directory = tempdir().unwrap();
        let root = directory.path().join("worktree");
        let cache = directory.path().join("cache");
        let hash = "fedcba9876543210";
        let artifact = root.join(".lake/build/lib/lean/Demo/Result.olean");
        fs::create_dir_all(artifact.parent().unwrap()).unwrap();
        fs::write(
            artifact.with_extension("trace"),
            format!(r#"{{"synthetic":true,"outputs":{{"o":["{hash}.olean"]}}}}"#),
        )
        .unwrap();
        fs::create_dir_all(cache.join("artifacts")).unwrap();
        fs::write(
            cache.join("artifacts").join(format!("{hash}.olean")),
            "cached olean",
        )
        .unwrap();

        restore_project_oleans(&cache, &root, &["Demo.Result".into()]).unwrap();
        assert_eq!(fs::read_to_string(artifact).unwrap(), "cached olean");
    }

    #[test]
    fn lake_trace_output_wins_over_the_build_hash() {
        let directory = tempdir().unwrap();
        let root = directory.path().join("worktree");
        let cache = directory.path().join("cache");
        let artifact = root.join(".lake/build/lib/lean/Demo/Result.olean");
        fs::create_dir_all(artifact.parent().unwrap()).unwrap();
        fs::write(artifact.with_extension("olean.hash"), "1111111111111111").unwrap();
        fs::write(
            artifact.with_extension("trace"),
            r#"{"outputs":{"o":["2222222222222222.olean"]}}"#,
        )
        .unwrap();
        fs::create_dir_all(cache.join("artifacts")).unwrap();
        fs::write(cache.join("artifacts/2222222222222222.olean"), "olean").unwrap();

        restore_project_oleans(&cache, &root, &["Demo.Result".into()]).unwrap();
        assert_eq!(fs::read_to_string(artifact).unwrap(), "olean");
    }

    #[test]
    fn prebuild_restore_reuses_timeout_cache_without_blocking_changed_sources() {
        let directory = tempdir().unwrap();
        let root = directory.path().join("worktree");
        let cache = directory.path().join("cache");
        let cached_hash = "0123456789abcdef";
        let cached_artifact = root.join(".lake/build/lib/lean/Demo/Cached.olean");
        let changed_artifact = root.join(".lake/build/lib/lean/Demo/Changed.olean");
        fs::create_dir_all(cached_artifact.parent().unwrap()).unwrap();
        fs::write(
            cached_artifact.with_extension("trace"),
            format!(r#"{{"outputs":{{"o":["{cached_hash}.olean"]}}}}"#),
        )
        .unwrap();
        fs::create_dir_all(cache.join("artifacts")).unwrap();
        fs::write(
            cache.join("artifacts").join(format!("{cached_hash}.olean")),
            "cached after timeout",
        )
        .unwrap();

        let restored = restore_available_project_oleans(
            &cache,
            &root,
            &["Demo.Cached".into(), "Demo.Changed".into()],
        )
        .unwrap();

        assert_eq!(restored, 1);
        assert_eq!(
            fs::read_to_string(cached_artifact).unwrap(),
            "cached after timeout"
        );
        assert!(!changed_artifact.exists());
    }
}
