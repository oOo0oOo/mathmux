use std::fs::{self, File};
use std::os::unix::fs::symlink;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use anyhow::{Context, Result, bail, ensure};
use fs2::FileExt;
use walkdir::WalkDir;

use crate::repo::Repo;
use crate::state::{State, Workspace};
use crate::util::{canonical, command_detail, run_checked, run_output};

pub fn workspace_limit() -> usize {
    if let Some(limit) = std::env::var("MATHMUX_MAX_WORKSPACES")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
    {
        return limit.clamp(1, 64);
    }
    let gib = fs::read_to_string("/proc/meminfo")
        .ok()
        .and_then(|contents| {
            contents
                .lines()
                .find_map(|line| line.strip_prefix("MemTotal:"))
                .and_then(|value| value.split_whitespace().next())
                .and_then(|value| value.parse::<u64>().ok())
                .map(|kib| kib / 1024 / 1024)
        })
        .unwrap_or(32);
    (((gib.saturating_sub(8)) / 6) as usize).clamp(1, 8)
}

pub fn create_workspace(
    repo: &Repo,
    state: &State,
    name: &str,
    model: Option<&str>,
) -> Result<Workspace> {
    validate_name(name)?;
    let model = model.map(str::trim).filter(|model| !model.is_empty());
    if let Some(model) = model {
        ensure!(
            model.len() <= 128 && !model.chars().any(char::is_control),
            "model must be at most 128 characters without control characters"
        );
    }
    ensure!(
        dirty_paths(&repo.root)?.is_empty(),
        "managed main worktree is not clean"
    );
    ensure!(
        state.workspace_named(name)?.is_none(),
        "workspace {name} already exists"
    );
    let count = state.list_workspaces()?.len();
    let limit = workspace_limit();
    ensure!(count < limit, "workspace limit reached ({limit})");

    let reference = state.next_ref('w')?;
    let branch = format!("mathmux/{name}");
    let path = repo.workspace_parent()?.join(name);
    ensure!(
        !path.exists(),
        "workspace path already exists: {}",
        path.display()
    );
    let output = run_output(
        "git",
        [
            "worktree",
            "add",
            "-b",
            &branch,
            path.to_string_lossy().as_ref(),
            "main",
        ],
        &repo.root,
    )?;
    if !output.status.success() {
        bail!("cannot create workspace: {}", command_detail(&output));
    }
    let workspace = Workspace {
        reference,
        name: name.to_owned(),
        path: canonical(&path)?,
        branch,
        model: model.map(str::to_owned),
    };
    if let Err(error) =
        prepare_workspace(repo, &workspace.path).and_then(|()| state.add_workspace(&workspace))
    {
        let _ = run_output(
            "git",
            [
                "worktree",
                "remove",
                "--force",
                path.to_string_lossy().as_ref(),
            ],
            &repo.root,
        );
        return Err(error);
    }
    Ok(workspace)
}

pub fn prepare_workspace(repo: &Repo, workspace: &Path) -> Result<()> {
    let shared = repo.root.join(".lake/packages");
    if !shared.is_dir() {
        return Ok(());
    }
    let target = workspace.join(".lake/packages");
    match fs::symlink_metadata(&target) {
        Ok(metadata) if metadata.is_dir() => return Ok(()),
        Ok(metadata) if metadata.file_type().is_symlink() => {
            ensure!(
                canonical(&target)? == canonical(&shared)?,
                "workspace dependency link points outside managed main"
            );
            return Ok(());
        }
        Ok(_) => bail!("workspace dependency path is not a directory"),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => return Err(error.into()),
    }
    fs::create_dir_all(workspace.join(".lake"))?;
    symlink(canonical(shared)?, target)?;
    Ok(())
}

pub fn delete_workspace(repo: &Repo, state: &State, name: &str) -> Result<Workspace> {
    let workspace = state
        .workspace_named(name)?
        .with_context(|| format!("unknown workspace {name}"))?;
    ensure!(
        dirty_paths(&workspace.path)?.is_empty(),
        "workspace {name} has unsubmitted changes"
    );
    run_checked(
        "git",
        [
            "worktree",
            "remove",
            workspace.path.to_string_lossy().as_ref(),
        ],
        &repo.root,
    )?;
    run_checked("git", ["branch", "-D", &workspace.branch], &repo.root)?;
    state.remove_workspace(&workspace.reference)?;
    Ok(workspace)
}

pub fn dirty_paths(root: &Path) -> Result<Vec<PathBuf>> {
    let output = run_output(
        "git",
        ["status", "--porcelain=v1", "-z", "--untracked-files=all"],
        root,
    )?;
    ensure!(
        output.status.success(),
        "cannot inspect workspace: {}",
        command_detail(&output)
    );
    let mut paths = Vec::new();
    let fields = output
        .stdout
        .split(|byte| *byte == 0)
        .filter(|field| !field.is_empty());
    let mut skip_rename_source = false;
    for field in fields {
        if skip_rename_source {
            skip_rename_source = false;
            continue;
        }
        if field.len() < 4 {
            continue;
        }
        let status = &field[..2];
        let path = String::from_utf8_lossy(&field[3..]).into_owned();
        paths.push(PathBuf::from(path));
        if status.contains(&b'R') || status.contains(&b'C') {
            skip_rename_source = true;
        }
    }
    paths.sort();
    paths.dedup();
    Ok(paths)
}

pub fn dirty_lean_files(root: &Path) -> Result<Vec<PathBuf>> {
    Ok(dirty_paths(root)?
        .into_iter()
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "lean")
                && path.file_name().is_none_or(|name| name != "lakefile.lean")
        })
        .collect())
}

pub fn project_lean_files(root: &Path) -> Vec<PathBuf> {
    WalkDir::new(root)
        .into_iter()
        .filter_entry(|entry| {
            !matches!(
                entry.file_name().to_str(),
                Some(".git" | ".lake" | "target")
            )
        })
        .filter_map(Result::ok)
        .filter(|entry| entry.file_type().is_file())
        .map(|entry| entry.into_path())
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "lean")
                && path.file_name().is_none_or(|name| name != "lakefile.lean")
        })
        .filter_map(|path| path.strip_prefix(root).ok().map(Path::to_path_buf))
        .collect()
}

pub fn head(root: &Path) -> Result<String> {
    run_checked("git", ["rev-parse", "HEAD"], root)
}

pub fn reconcile_integration(repo: &Repo) -> Result<()> {
    if run_checked(
        "git",
        ["rev-parse", "-q", "--verify", "CHERRY_PICK_HEAD"],
        &repo.root,
    )
    .is_ok()
    {
        run_checked("git", ["cherry-pick", "--abort"], &repo.root)
            .context("cannot recover interrupted main integration")?;
    }
    Ok(())
}

pub struct SyncResult {
    pub clean: bool,
    pub detail: String,
}

pub fn push_main(repo: &Repo) -> Result<String> {
    let lock = File::options()
        .create(true)
        .truncate(false)
        .read(true)
        .write(true)
        .open(&repo.integration_lock)?;
    lock.lock_exclusive()?;
    ensure!(
        dirty_paths(&repo.root)?.is_empty(),
        "managed main worktree is not clean"
    );
    ensure!(
        run_checked(
            "git",
            ["rev-parse", "-q", "--verify", "CHERRY_PICK_HEAD"],
            &repo.root,
        )
        .is_err(),
        "managed main has an unfinished integration"
    );
    let output = run_output("git", ["push", "--porcelain"], &repo.root)?;
    if !output.status.success() {
        bail!("push failed: {}", command_detail(&output));
    }
    let detail = command_detail(&output);
    Ok(if detail.is_empty() {
        "up to date".into()
    } else {
        detail
    })
}

pub fn sync(repo: &Repo, workspace: &Workspace) -> Result<SyncResult> {
    ensure!(
        dirty_paths(&repo.root)?.is_empty(),
        "managed main worktree is not clean"
    );
    if merge_in_progress(&workspace.path) {
        return continue_sync(workspace);
    }
    let unmerged = unmerged_paths(&workspace.path)?;
    if !unmerged.is_empty() {
        return continue_autostash_sync(workspace, unmerged);
    }
    let output = run_output(
        "git",
        ["merge", "--no-edit", "--autostash", "main"],
        &workspace.path,
    )?;
    if output.status.success() {
        let conflicts = unmerged_paths(&workspace.path)?;
        if !conflicts.is_empty() {
            return Ok(SyncResult {
                clean: false,
                detail: conflict_detail(conflicts.iter().map(|path| path.to_string_lossy())),
            });
        }
        let detail = command_detail(&output);
        return Ok(SyncResult {
            clean: true,
            detail: if detail.is_empty() {
                "up to date".into()
            } else {
                detail
            },
        });
    }
    let conflicts = run_checked(
        "git",
        ["diff", "--name-only", "--diff-filter=U"],
        &workspace.path,
    )?;
    if conflicts.is_empty() {
        bail!("sync failed: {}", command_detail(&output));
    }
    Ok(SyncResult {
        clean: false,
        detail: conflict_detail(conflicts.lines()),
    })
}

fn continue_autostash_sync(
    workspace: &Workspace,
    conflicts: Vec<PathBuf>,
) -> Result<SyncResult> {
    let unresolved = conflicts
        .iter()
        .filter(|path| has_conflict_markers(&workspace.path.join(path)))
        .collect::<Vec<_>>();
    if !unresolved.is_empty() {
        return Ok(SyncResult {
            clean: false,
            detail: conflict_detail(unresolved.iter().map(|path| path.to_string_lossy())),
        });
    }
    let mut args = vec!["add".into(), "--".into()];
    args.extend(conflicts.iter().map(|path| path.as_os_str().to_owned()));
    run_checked("git", args, &workspace.path)
        .context("cannot mark resolved autostash conflicts")?;
    let mut args = vec!["reset".into(), "--".into()];
    args.extend(conflicts.iter().map(|path| path.as_os_str().to_owned()));
    run_checked("git", args, &workspace.path)
        .context("cannot restore resolved workspace changes")?;
    Ok(SyncResult {
        clean: true,
        detail: "resolved autostash conflicts".into(),
    })
}

fn continue_sync(workspace: &Workspace) -> Result<SyncResult> {
    let conflicts = unmerged_paths(&workspace.path)?;
    let unresolved = conflicts
        .iter()
        .filter(|path| has_conflict_markers(&workspace.path.join(path)))
        .cloned()
        .collect::<Vec<_>>();
    if !unresolved.is_empty() {
        return Ok(SyncResult {
            clean: false,
            detail: conflict_detail(unresolved.iter().map(|path| path.to_string_lossy())),
        });
    }
    if !conflicts.is_empty() {
        let mut args = vec!["add".into(), "--".into()];
        args.extend(conflicts.iter().map(|path| path.as_os_str().to_owned()));
        run_checked("git", args, &workspace.path)
            .context("cannot stage resolved sync conflicts")?;
    }
    let output = run_output(
        "git",
        ["-c", "core.editor=true", "merge", "--continue"],
        &workspace.path,
    )?;
    if output.status.success() {
        return Ok(SyncResult {
            clean: true,
            detail: command_detail(&output),
        });
    }
    let conflicts = unmerged_paths(&workspace.path)?;
    if conflicts.is_empty() {
        bail!("cannot continue sync: {}", command_detail(&output));
    }
    Ok(SyncResult {
        clean: false,
        detail: conflict_detail(conflicts.iter().map(|path| path.to_string_lossy())),
    })
}

fn unmerged_paths(root: &Path) -> Result<Vec<PathBuf>> {
    let output = run_output(
        "git",
        ["diff", "--name-only", "-z", "--diff-filter=U"],
        root,
    )?;
    ensure!(
        output.status.success(),
        "cannot inspect sync conflicts: {}",
        command_detail(&output)
    );
    Ok(output
        .stdout
        .split(|byte| *byte == 0)
        .filter(|field| !field.is_empty())
        .map(|field| PathBuf::from(String::from_utf8_lossy(field).into_owned()))
        .collect())
}

fn has_conflict_markers(path: &Path) -> bool {
    fs::read_to_string(path).is_ok_and(|source| {
        source.lines().any(|line| {
            line.starts_with("<<<<<<< ")
                || line == "======="
                || line.starts_with(">>>>>>> ")
        })
    })
}

fn conflict_detail(conflicts: impl IntoIterator<Item = impl AsRef<str>>) -> String {
    format!(
        "conflicts: {} (resolve them, check the affected files, then rerun mathmux sync)",
        conflicts
            .into_iter()
            .map(|path| path.as_ref().to_owned())
            .collect::<Vec<_>>()
            .join(", ")
    )
}

pub struct SubmitResult {
    pub workspace_commit: String,
    pub main_commit: String,
    pub base_commit: String,
}

pub fn submit(repo: &Repo, workspace: &Workspace, message: &str) -> Result<SubmitResult> {
    ensure!(!message.trim().is_empty(), "submission message is empty");
    let lock = File::options()
        .create(true)
        .truncate(false)
        .read(true)
        .write(true)
        .open(&repo.integration_lock)?;
    lock.lock_exclusive()?;

    ensure!(
        dirty_paths(&repo.root)?.is_empty(),
        "managed main worktree is not clean"
    );
    ensure!(
        !merge_in_progress(&workspace.path),
        "workspace has an unfinished merge; resolve it before submit"
    );
    let base_commit = head(&repo.root)?;
    run_checked("git", ["add", "-A"], &workspace.path)?;
    let staged = run_output("git", ["diff", "--cached", "--quiet"], &workspace.path)?;
    ensure!(
        staged.status.code() == Some(1),
        "workspace has no changes to submit"
    );
    run_checked("git", ["commit", "-m", message], &workspace.path)?;
    let workspace_commit = head(&workspace.path)?;

    let output = run_output("git", ["cherry-pick", &workspace_commit], &repo.root)?;
    if !output.status.success() {
        let detail = command_detail(&output);
        let _ = run_output("git", ["cherry-pick", "--abort"], &repo.root);
        let restore = run_output("git", ["reset", "--mixed", "HEAD^"], &workspace.path)?;
        if !restore.status.success() {
            bail!(
                "integration conflict; workspace change remains committed; run mathmux sync ({detail})"
            );
        }
        bail!("integration conflict; run mathmux sync ({detail})");
    }
    let main_commit = head(&repo.root)?;
    Ok(SubmitResult {
        workspace_commit,
        main_commit,
        base_commit,
    })
}

pub fn lake_command(repo: &Repo, root: &Path) -> Command {
    let mut command = Command::new(lake_executable());
    command
        .current_dir(root)
        .env("LAKE_ARTIFACT_CACHE", "true")
        .env("LAKE_CACHE_DIR", &repo.cache_dir)
        .env("LAKE_RESTORE_ARTIFACTS", "false")
        .stdin(Stdio::null());
    command
}

pub(crate) fn lake_executable() -> PathBuf {
    if let Some(path) = std::env::var_os("MATHMUX_LAKE") {
        return PathBuf::from(path);
    }
    if let Some(path) = std::env::var_os("PATH").and_then(|value| {
        std::env::split_paths(&value)
            .map(|directory| directory.join("lake"))
            .find(|path| path.is_file())
    }) {
        return path;
    }
    let elan_home = std::env::var_os("ELAN_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".elan")));
    elan_home
        .map(|home| home.join("bin/lake"))
        .filter(|path| path.is_file())
        .unwrap_or_else(|| PathBuf::from("lake"))
}

pub(crate) fn merge_in_progress(root: &Path) -> bool {
    run_checked("git", ["rev-parse", "-q", "--verify", "MERGE_HEAD"], root).is_ok()
}

fn validate_name(name: &str) -> Result<()> {
    let valid = !name.is_empty()
        && name.len() <= 64
        && name.chars().enumerate().all(|(index, value)| {
            value.is_ascii_alphanumeric() || (index > 0 && matches!(value, '-' | '_'))
        });
    ensure!(valid, "workspace names use letters, digits, '-' and '_'");
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::fs;

    use tempfile::tempdir;

    use super::*;
    use crate::repo::Repo;
    use crate::state::State;

    #[test]
    fn workspace_names_are_narrow_and_memory_limit_is_bounded() {
        assert!(validate_name("proof_2-a").is_ok());
        assert!(validate_name("-bad").is_err());
        assert!(validate_name("a/b").is_err());
        assert!((1..=8).contains(&workspace_limit()));
    }

    #[test]
    fn push_main_uses_the_configured_upstream() {
        let directory = tempdir().unwrap();
        let remote = directory.path().join("remote.git");
        let root = directory.path().join("repo");
        run_checked("git", ["init", "--bare", remote.to_str().unwrap()], directory.path())
            .unwrap();
        fs::create_dir(&root).unwrap();
        run_checked("git", ["init", "-b", "main"], &root).unwrap();
        run_checked("git", ["config", "user.name", "mathmux test"], &root).unwrap();
        run_checked(
            "git",
            ["config", "user.email", "mathmux@test.invalid"],
            &root,
        )
        .unwrap();
        fs::write(root.join("Proof.lean"), "def value := 0\n").unwrap();
        run_checked("git", ["add", "."], &root).unwrap();
        run_checked("git", ["commit", "-m", "initial"], &root).unwrap();
        run_checked("git", ["remote", "add", "origin", remote.to_str().unwrap()], &root)
            .unwrap();
        run_checked("git", ["push", "-u", "origin", "main"], &root).unwrap();
        fs::write(root.join("Proof.lean"), "def value := 1\n").unwrap();
        run_checked("git", ["add", "."], &root).unwrap();
        run_checked("git", ["commit", "-m", "next"], &root).unwrap();

        let repo = Repo::discover(&root).unwrap();
        assert!(push_main(&repo).unwrap().contains("main"));
        assert_eq!(
            head(&root).unwrap(),
            run_checked("git", ["rev-parse", "refs/heads/main"], &remote).unwrap()
        );
    }

    #[test]
    fn integration_conflict_preserves_managed_main() {
        let directory = tempdir().unwrap();
        let root = directory.path().join("repo");
        fs::create_dir(&root).unwrap();
        run_checked("git", ["init", "-b", "main"], &root).unwrap();
        run_checked("git", ["config", "user.name", "mathmux test"], &root).unwrap();
        run_checked(
            "git",
            ["config", "user.email", "mathmux@test.invalid"],
            &root,
        )
        .unwrap();
        fs::write(root.join(".gitignore"), ".lake\n").unwrap();
        fs::create_dir_all(root.join(".lake/packages/mathlib")).unwrap();
        fs::write(root.join("Proof.lean"), "def value := 0\n").unwrap();
        run_checked("git", ["add", "."], &root).unwrap();
        run_checked("git", ["commit", "-m", "initial"], &root).unwrap();

        let repo = Repo::discover(&root).unwrap();
        let state = State::new(&repo.db_path).unwrap();
        let workspace = create_workspace(&repo, &state, "agent", None).unwrap();
        assert_eq!(
            canonical(workspace.path.join(".lake/packages")).unwrap(),
            canonical(root.join(".lake/packages")).unwrap()
        );
        fs::write(root.join("Proof.lean"), "def value := 1\n").unwrap();
        run_checked("git", ["add", "."], &root).unwrap();
        run_checked("git", ["commit", "-m", "main change"], &root).unwrap();
        let main_before = head(&root).unwrap();
        fs::write(workspace.path.join("Proof.lean"), "def value := 2\n").unwrap();

        assert!(submit(&repo, &workspace, "workspace change").is_err());
        assert_eq!(head(&root).unwrap(), main_before);
        assert!(dirty_paths(&root).unwrap().is_empty());
        assert_eq!(
            dirty_paths(&workspace.path).unwrap(),
            vec![PathBuf::from("Proof.lean")]
        );
        assert_eq!(
            fs::read_to_string(root.join("Proof.lean")).unwrap(),
            "def value := 1\n"
        );
    }

    #[test]
    fn sync_rerun_continues_a_resolved_merge() {
        let directory = tempdir().unwrap();
        let root = directory.path().join("repo");
        fs::create_dir(&root).unwrap();
        run_checked("git", ["init", "-b", "main"], &root).unwrap();
        run_checked("git", ["config", "user.name", "mathmux test"], &root).unwrap();
        run_checked(
            "git",
            ["config", "user.email", "mathmux@test.invalid"],
            &root,
        )
        .unwrap();
        fs::write(root.join("Proof.lean"), "def value := 0\n").unwrap();
        run_checked("git", ["add", "."], &root).unwrap();
        run_checked("git", ["commit", "-m", "initial"], &root).unwrap();

        let repo = Repo::discover(&root).unwrap();
        let state = State::new(&repo.db_path).unwrap();
        let workspace = create_workspace(&repo, &state, "agent", None).unwrap();
        fs::write(workspace.path.join("Proof.lean"), "def value := 1\n").unwrap();
        run_checked("git", ["add", "."], &workspace.path).unwrap();
        run_checked("git", ["commit", "-m", "workspace"], &workspace.path).unwrap();
        fs::write(root.join("Proof.lean"), "def value := 2\n").unwrap();
        run_checked("git", ["add", "."], &root).unwrap();
        run_checked("git", ["commit", "-m", "main"], &root).unwrap();

        let first = sync(&repo, &workspace).unwrap();
        assert!(!first.clean);
        assert!(merge_in_progress(&workspace.path));
        fs::write(workspace.path.join("Proof.lean"), "def value := 3\n").unwrap();
        let second = sync(&repo, &workspace).unwrap();
        assert!(second.clean);
        assert!(!merge_in_progress(&workspace.path));
        assert_eq!(
            fs::read_to_string(workspace.path.join("Proof.lean")).unwrap(),
            "def value := 3\n"
        );
    }

    #[test]
    fn sync_reports_and_recovers_autostash_conflicts() {
        let directory = tempdir().unwrap();
        let root = directory.path().join("repo");
        fs::create_dir(&root).unwrap();
        run_checked("git", ["init", "-b", "main"], &root).unwrap();
        run_checked("git", ["config", "user.name", "mathmux test"], &root).unwrap();
        run_checked(
            "git",
            ["config", "user.email", "mathmux@test.invalid"],
            &root,
        )
        .unwrap();
        fs::write(root.join("Proof.lean"), "def value := 0\n").unwrap();
        run_checked("git", ["add", "."], &root).unwrap();
        run_checked("git", ["commit", "-m", "initial"], &root).unwrap();

        let repo = Repo::discover(&root).unwrap();
        let state = State::new(&repo.db_path).unwrap();
        let workspace = create_workspace(&repo, &state, "agent", None).unwrap();
        fs::write(workspace.path.join("Proof.lean"), "def value := 1\n").unwrap();
        fs::write(root.join("Proof.lean"), "def value := 2\n").unwrap();
        run_checked("git", ["add", "."], &root).unwrap();
        run_checked("git", ["commit", "-m", "main"], &root).unwrap();

        let first = sync(&repo, &workspace).unwrap();
        assert!(!first.clean);
        assert!(!merge_in_progress(&workspace.path));
        assert_eq!(unmerged_paths(&workspace.path).unwrap().len(), 1);
        assert!(has_conflict_markers(&workspace.path.join("Proof.lean")));

        fs::write(workspace.path.join("Proof.lean"), "def value := 3\n").unwrap();
        let second = sync(&repo, &workspace).unwrap();
        assert!(second.clean);
        assert!(unmerged_paths(&workspace.path).unwrap().is_empty());
        assert_eq!(
            dirty_paths(&workspace.path).unwrap(),
            vec![PathBuf::from("Proof.lean")]
        );
        assert_eq!(
            fs::read_to_string(workspace.path.join("Proof.lean")).unwrap(),
            "def value := 3\n"
        );
    }
}
