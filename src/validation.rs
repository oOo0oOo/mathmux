use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Condvar, Mutex};
use std::thread;

use anyhow::{Context, Result, bail};

use crate::check::{project_module_name, transitive_dependencies};
use crate::git::{lake_command, project_lean_files};
use crate::repo::Repo;
use crate::state::{State, Submission};
use crate::util::{run_checked, run_output};

#[derive(Clone)]
pub struct ValidationQueue {
    signal: Arc<(Mutex<bool>, Condvar)>,
}

impl ValidationQueue {
    pub fn start(repo: Repo, state: State) -> Result<Self> {
        state.recover_validation()?;
        let queue = Self {
            signal: Arc::new((Mutex::new(false), Condvar::new())),
        };
        let signal = queue.signal.clone();
        thread::Builder::new()
            .name("mathmux-validation".into())
            .spawn(move || validation_loop(repo, state, signal))?;
        Ok(queue)
    }

    pub fn wake(&self) {
        let (lock, condition) = &*self.signal;
        *lock.lock().expect("validation signal poisoned") = true;
        condition.notify_one();
    }
}

fn validation_loop(repo: Repo, state: State, signal: Arc<(Mutex<bool>, Condvar)>) {
    loop {
        match state.next_validation() {
            Ok(Some(submission)) => {
                let result = validate(&repo, &submission);
                let (passed, detail) = match result {
                    Ok(detail) => (true, detail),
                    Err(error) => (false, format!("{error:#}")),
                };
                let _ = state.finish_validation(&submission.reference, passed, &detail);
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

fn validate(repo: &Repo, submission: &Submission) -> Result<String> {
    let root = prepare_worktree(repo, &submission.main_commit)?;
    let output = lake_command(repo, &root)
        .arg("build")
        .output()
        .context("cannot start validation build")?;
    if !output.status.success() {
        bail!("build failed: {}", command_detail(&output));
    }
    let (roots, project_modules) = deliverable_modules(&root);
    let audit = run_axiom_audit(repo, &root, &roots, &project_modules)?;
    Ok(format!(
        "build passed; axiom audit passed ({} modules); native evaluation: compiler trust",
        project_modules.len()
    ) + if audit.is_empty() {
        ""
    } else {
        "; audit output recorded"
    })
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
    let all = project_lean_files(root);
    let imported: std::collections::HashSet<PathBuf> = all
        .iter()
        .flat_map(|target| transitive_dependencies(root, target).unwrap_or_default())
        .collect();
    let mut roots: Vec<_> = all
        .iter()
        .filter(|path| !imported.contains(*path))
        .map(|path| project_module_name(root, path))
        .collect();
    let mut project_modules: Vec<_> = all
        .iter()
        .map(|path| project_module_name(root, path))
        .collect();
    if roots.is_empty() {
        roots.clone_from(&project_modules);
    }
    roots.sort();
    roots.dedup();
    project_modules.sort();
    project_modules.dedup();
    (roots, project_modules)
}

fn run_axiom_audit(
    repo: &Repo,
    root: &Path,
    roots: &[String],
    project_modules: &[String],
) -> Result<String> {
    if roots.is_empty() {
        return Ok(String::new());
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
  let mut failures : Array String := #[]
  for (name, _) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let origin := env.header.moduleNames[index.toNat]!
      if projectModules.contains origin then
        let action : CoreM (Array Name) := collectAxioms name
        let (axioms, _) ← action.toIO context state
        for axiomName in axioms do
          unless allowed.contains axiomName do
            failures := failures.push s!"{{name}} uses {{axiomName}}"
  for failure in failures do IO.eprintln failure
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
    if !output.status.success() {
        bail!("axiom audit failed: {}", command_detail(&output));
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

fn command_detail(output: &std::process::Output) -> String {
    let stderr = String::from_utf8_lossy(&output.stderr).trim().to_owned();
    if stderr.is_empty() {
        String::from_utf8_lossy(&output.stdout).trim().to_owned()
    } else {
        stderr
    }
}
