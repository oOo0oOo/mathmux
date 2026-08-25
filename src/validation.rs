use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::Instant;

use anyhow::{Context, Result, bail};

use crate::check::{parse_imports, project_module_name};
use crate::git::{lake_command, project_lean_files};
use crate::issue::{TelemetryOperation, TelemetryStore, development_enabled};
use crate::repo::Repo;
use crate::state::{State, Submission, ValidationReport};
use crate::util::{run_checked, run_output};

#[derive(Clone)]
pub struct ValidationQueue {
    signal: Arc<(Mutex<bool>, Condvar)>,
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

fn validation_loop(
    repo: Repo,
    state: State,
    signal: Arc<(Mutex<bool>, Condvar)>,
    retiring: Arc<AtomicBool>,
) {
    loop {
        if retiring.load(Ordering::SeqCst) {
            return;
        }
        match state.next_validation() {
            Ok(Some(submission)) => {
                let result = validate(&repo, &submission);
                let report = match result {
                    Ok(report) => report,
                    Err(error) => ValidationReport {
                        passed: false,
                        detail: format!("validation failed: {error:#}"),
                        build_output: String::new(),
                        axioms: Vec::new(),
                        sorries: Vec::new(),
                        duration_ms: 0,
                    },
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
                    .wait_timeout_while(pending, std::time::Duration::from_secs(30), |value| {
                        !*value
                    })
                    .map(|(mut pending, _)| *pending = false);
            }
            Err(_) => thread::sleep(std::time::Duration::from_secs(1)),
        }
    }
}

fn validate(repo: &Repo, submission: &Submission) -> Result<ValidationReport> {
    let started = Instant::now();
    let root = prepare_worktree(repo, &submission.main_commit)?;
    let sorries = find_sorries(&root)?;
    let output = lake_command(repo, &root)
        .arg("build")
        .output()
        .context("cannot start validation build")?;
    let build_output = combined_output(&output);
    if !output.status.success() {
        return Ok(ValidationReport {
            passed: false,
            detail: "build failed".into(),
            build_output,
            axioms: Vec::new(),
            sorries,
            duration_ms: started.elapsed().as_millis() as u64,
        });
    }
    let (roots, project_modules) = deliverable_modules(&root);
    let axioms = match run_axiom_audit(repo, &root, &roots, &project_modules) {
        Ok(axioms) => axioms,
        Err(error) => {
            return Ok(ValidationReport {
                passed: false,
                detail: format!("axiom audit failed: {error:#}"),
                build_output,
                axioms: Vec::new(),
                sorries,
                duration_ms: started.elapsed().as_millis() as u64,
            });
        }
    };
    let passed = axioms.is_empty();
    Ok(ValidationReport {
        passed,
        detail: if passed {
            format!(
                "build passed; axioms clean ({} modules)",
                project_modules.len()
            )
        } else {
            format!(
                "build passed; {} extra axiom{}",
                axioms.len(),
                if axioms.len() == 1 { "" } else { "s" }
            )
        },
        build_output,
        axioms,
        sorries,
        duration_ms: started.elapsed().as_millis() as u64,
    })
}

fn combined_output(output: &std::process::Output) -> String {
    let stdout = String::from_utf8_lossy(&output.stdout).trim().to_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).trim().to_owned();
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

fn run_axiom_audit(
    repo: &Repo,
    root: &Path,
    roots: &[String],
    project_modules: &[String],
) -> Result<Vec<String>> {
    if roots.is_empty() {
        return Ok(Vec::new());
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
  for (name, _) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let origin := env.header.moduleNames[index.toNat]!
      if projectModules.contains origin then
        let action : CoreM (Array Name) := collectAxioms name
        let (axioms, _) ← action.toIO context state
        for axiomName in axioms do
          unless axiomName == `sorryAx || allowed.contains axiomName do
            failures := failures.push (axiomName, name)
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
    if !output.status.success() && failures.is_empty() {
        bail!("axiom audit failed: {}", command_detail(&output));
    }
    Ok(failures)
}

fn find_sorries(root: &Path) -> Result<Vec<String>> {
    let mut locations = Vec::new();
    for relative in project_lean_files(root) {
        let source = fs::read_to_string(root.join(&relative))?;
        for (line, column) in sorry_positions(&source) {
            locations.push(format!("{}:{line}:{column}", relative.display()));
        }
    }
    locations.sort();
    locations.dedup();
    Ok(locations)
}

fn sorry_positions(source: &str) -> Vec<(usize, usize)> {
    let bytes = source.as_bytes();
    let mut positions = Vec::new();
    let mut index = 0;
    let mut line = 1;
    let mut column = 1;
    let mut block_depth = 0usize;
    let mut string = false;
    let mut escaped = false;
    while index < bytes.len() {
        if block_depth > 0 {
            if bytes[index..].starts_with(b"/-") {
                block_depth += 1;
                index += 2;
                column += 2;
                continue;
            }
            if bytes[index..].starts_with(b"-/") {
                block_depth -= 1;
                index += 2;
                column += 2;
                continue;
            }
        } else if string {
            if bytes[index] == b'"' && !escaped {
                string = false;
            }
            escaped = bytes[index] == b'\\' && !escaped;
            if bytes[index] != b'\\' {
                escaped = false;
            }
        } else {
            if bytes[index..].starts_with(b"--") {
                while index < bytes.len() && bytes[index] != b'\n' {
                    index += 1;
                    column += 1;
                }
                continue;
            }
            if bytes[index..].starts_with(b"/-") {
                block_depth = 1;
                index += 2;
                column += 2;
                continue;
            }
            if bytes[index] == b'"' {
                string = true;
                escaped = false;
            } else if bytes[index..].starts_with(b"sorry")
                && token_start(bytes, index)
                && token_end(bytes, index + 5)
            {
                positions.push((line, column));
                index += 5;
                column += 5;
                continue;
            }
        }
        if bytes[index] == b'\n' {
            line += 1;
            column = 1;
        } else {
            column += 1;
        }
        index += 1;
    }
    positions
}

fn token_start(bytes: &[u8], index: usize) -> bool {
    index == 0 || !identifier_byte(bytes[index - 1])
}

fn token_end(bytes: &[u8], index: usize) -> bool {
    index == bytes.len() || !identifier_byte(bytes[index])
}

fn identifier_byte(byte: u8) -> bool {
    matches!(byte, b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_' | b'\'')
}

fn command_detail(output: &std::process::Output) -> String {
    let stderr = String::from_utf8_lossy(&output.stderr).trim().to_owned();
    if stderr.is_empty() {
        String::from_utf8_lossy(&output.stdout).trim().to_owned()
    } else {
        stderr
    }
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
    fn sorry_locations_ignore_comments_strings_and_longer_names() {
        let source = "-- sorry\n/- outer /- sorry -/ -/\ndef a : True := by\n  sorry\ndef sorryAx := \"sorry\"\n";
        assert_eq!(sorry_positions(source), vec![(4, 3)]);
    }
}
