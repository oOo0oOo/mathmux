use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use anyhow::{Context, Result, bail, ensure};
use fs2::FileExt;

use crate::check::{parse_imports, project_module_name};
use crate::git::{lake_command, project_lean_files};
use crate::issue::{TelemetryOperation, TelemetryStore, development_enabled};
use crate::repo::Repo;
use crate::state::{State, Submission, ValidationReport};
use crate::util::{command_detail, output_text, run_checked, run_output};

type ValidationSignal = Arc<(Mutex<bool>, Condvar)>;

#[derive(Clone)]
pub struct ValidationQueue {
    signal: ValidationSignal,
}

impl ValidationQueue {
    pub fn start(repo: Repo, state: State, retiring: Arc<AtomicBool>) -> Result<Self> {
        state.recover_validation()?;
        let queue = Self {
            signal: Arc::new((Mutex::new(false), Condvar::new())),
        };
        let signal = queue.signal.clone();
        thread::Builder::new()
            .name("mathmux-validation".into())
            .spawn(move || validation_loop(repo, state, signal, retiring))?;
        Ok(queue)
    }

    pub fn wake(&self) {
        let (lock, condition) = &*self.signal;
        *lock.lock().expect("validation signal poisoned") = true;
        condition.notify_one();
    }
}

fn validation_loop(repo: Repo, state: State, signal: ValidationSignal, retiring: Arc<AtomicBool>) {
    loop {
        if retiring.load(Ordering::SeqCst) {
            return;
        }
        match state.next_validation() {
            Ok(Some(submission)) => {
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
                let _ = state.finish_validation(&submission.reference, &report);
                if development_enabled()
                    && let Ok(store) = TelemetryStore::global()
                {
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
                let (lock, condition) = &*signal;
                let pending = lock.lock().expect("validation signal poisoned");
                let _ = condition
                    .wait_timeout_while(pending, Duration::from_secs(30), |value| !*value)
                    .map(|(mut pending, _)| *pending = false);
            }
            Err(_) => thread::sleep(Duration::from_secs(1)),
        }
    }
}

fn validate(repo: &Repo, submission: &Submission) -> Result<ValidationReport> {
    let started = Instant::now();
    let validation_lock = fs::OpenOptions::new()
        .create(true)
        .truncate(false)
        .read(true)
        .write(true)
        .open(&repo.validation_lock)?;
    validation_lock.lock_exclusive()?;
    let root = prepare_worktree(repo, &submission.main_commit)?;
    let (roots, project_modules) = deliverable_modules(&root);
    invalidate_newer_project_artifacts(&root)?;
    let output = lake_command(repo, &root)
        .arg("build")
        .args(&roots)
        .output()
        .context("cannot start validation build")?;
    let build_output = combined_output(&output);
    if !output.status.success() {
        return Ok(failed_report(
            started,
            "build failed",
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
                format!("axiom audit failed: {error:#}"),
                build_output,
                Vec::new(),
            ));
        }
    };
    let passed = audit.axioms.is_empty();
    Ok(ValidationReport {
        passed,
        sorry_audit: true,
        detail: if passed {
            format!(
                "build passed; axioms clean ({} modules)",
                project_modules.len()
            )
        } else {
            format!(
                "build passed; {} extra axiom{}",
                audit.axioms.len(),
                if audit.axioms.len() == 1 { "" } else { "s" }
            )
        },
        build_output,
        axioms: audit.axioms,
        sorries: audit.sorries,
        duration_ms: started.elapsed().as_millis() as u64,
    })
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
        if artifact.is_file() {
            continue;
        }
        let hash = project_olean_hash(&artifact)
            .with_context(|| format!("missing artifact hash for {module}"))?;
        ensure!(
            hash.len() == 16 && hash.chars().all(|character| character.is_ascii_hexdigit()),
            "invalid artifact hash for {module}"
        );
        let cached = cache_dir.join("artifacts").join(format!("{hash}.olean"));
        ensure!(cached.is_file(), "cached artifact missing for {module}");
        if let Some(parent) = artifact.parent() {
            fs::create_dir_all(parent)?;
        }
        if let Err(error) = fs::hard_link(&cached, &artifact) {
            fs::copy(&cached, &artifact).with_context(|| {
                format!(
                    "cannot restore cached artifact for {module} after hard-link failed: {error}"
                )
            })?;
        }
    }
    Ok(())
}

fn project_olean_hash(artifact: &Path) -> Result<String> {
    let hash_path = artifact.with_extension("olean.hash");
    if hash_path.is_file() {
        return Ok(fs::read_to_string(hash_path)?.trim().to_owned());
    }
    let trace_path = artifact.with_extension("trace");
    let trace: serde_json::Value = serde_json::from_slice(&fs::read(trace_path)?)?;
    trace
        .pointer("/outputs/o")
        .and_then(serde_json::Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(serde_json::Value::as_str)
        .find_map(|name| {
            Path::new(name)
                .file_stem()
                .and_then(|stem| stem.to_str())
                .map(str::to_owned)
        })
        .context("trace has no olean output")
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
    sorries: Vec<String>,
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
    let output = lake_command(repo, root)
        .args(["env", "lean", "--run"])
        .arg(&path)
        .output()
        .context("cannot start axiom audit")?;
    let text = combined_output(&output);
    let mut failures = text
        .lines()
        .filter_map(|line| line.strip_prefix("MATHMUX_AXIOM\t"))
        .filter_map(|line| line.split_once('\t').map(|(axiom, _)| axiom.to_owned()))
        .collect::<Vec<_>>();
    failures.sort();
    failures.dedup();
    let mut sorries = text
        .lines()
        .filter_map(|line| line.strip_prefix("MATHMUX_SORRY\t"))
        .map(str::to_owned)
        .collect::<Vec<_>>();
    sorries.sort();
    sorries.dedup();
    if !output.status.success() && failures.is_empty() {
        bail!("axiom audit failed: {}", command_detail(&output));
    }
    Ok(AxiomAudit {
        axioms: failures,
        sorries,
    })
}

#[cfg(test)]
mod tests {
    use tempfile::tempdir;

    use super::*;

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
}
