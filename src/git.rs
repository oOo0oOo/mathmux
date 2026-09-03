use std::fs;
use std::io::Write;
use std::os::unix::fs::symlink;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use anyhow::{Context, Result, bail, ensure};
use walkdir::WalkDir;

use crate::coordination::{lock_exclusive, open_lock};
use crate::reference::ReferenceKind;
use crate::repo::Repo;
use crate::state::{State, Workspace};
use crate::util::{canonical, command_detail, run_checked, run_output};

const MAX_MANAGED_WORKSPACES: usize = 100;
const INDEX_LOCK_RETRY_WINDOW: Duration = Duration::from_secs(10);
const INDEX_LOCK_RETRY_INTERVAL: Duration = Duration::from_millis(100);

fn acquire_integration_lock(repo: &Repo) -> Result<fs::File> {
    let lock = open_lock(&repo.integration_lock)?;
    lock_exclusive(&lock)?;
    Ok(lock)
}

fn run_git_checked_with_index_lock_retry<I, S>(args: I, cwd: &Path) -> Result<String>
where
    I: IntoIterator<Item = S> + Clone,
    S: AsRef<std::ffi::OsStr>,
{
    let deadline = Instant::now() + INDEX_LOCK_RETRY_WINDOW;
    loop {
        let output = run_output("git", args.clone(), cwd)?;
        if output.status.success() {
            return Ok(String::from_utf8_lossy(&output.stdout).trim().to_owned());
        }
        let detail = command_detail(&output);
        if !(detail.contains("index.lock") && detail.contains("File exists")) {
            bail!("command failed: {detail}");
        }
        if Instant::now() >= deadline {
            bail!(
                "command failed: {detail}\nGit index.lock remained busy for {} seconds; no lock was removed",
                INDEX_LOCK_RETRY_WINDOW.as_secs()
            );
        }
        std::thread::sleep(INDEX_LOCK_RETRY_INTERVAL);
    }
}

pub fn workspace_limit() -> usize {
    if let Some(limit) = std::env::var("MATHMUX_MAX_WORKSPACES")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
    {
        return clamp_workspace_limit(limit);
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
    clamp_workspace_limit(((gib.saturating_sub(8)) / 6) as usize)
}

fn clamp_workspace_limit(limit: usize) -> usize {
    limit.clamp(1, MAX_MANAGED_WORKSPACES)
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
    let _integration_lock = acquire_integration_lock(repo)?;
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

    let reference = state.next_reference(ReferenceKind::Workspace)?;
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

pub fn delete_workspace(repo: &Repo, state: &State, name: &str, force: bool) -> Result<Workspace> {
    let _integration_lock = acquire_integration_lock(repo)?;
    let workspace = state
        .workspace_named(name)?
        .with_context(|| format!("unknown workspace {name}"))?;
    if !workspace.path.exists() {
        ensure!(
            branch_tree_matches_main(repo, &workspace.branch)?,
            "workspace {name} path is missing and its branch contains unsubmitted commits; restore the worktree before deletion"
        );
        if registered_worktree(repo, &workspace.path)? {
            let mut args = vec!["worktree", "remove"];
            if force {
                args.push("--force");
            }
            let path = workspace.path.to_string_lossy();
            args.push(path.as_ref());
            run_checked("git", args, &repo.root)?;
        }
        if branch_exists(repo, &workspace.branch)? {
            run_checked("git", ["branch", "-D", &workspace.branch], &repo.root)?;
        }
        state.remove_workspace(&workspace.reference)?;
        return Ok(workspace);
    }
    if !force {
        ensure!(
            dirty_paths(&workspace.path)?.is_empty(),
            "workspace {name} has unsubmitted changes; rerun with `mathmux ws delete --force {name}` to discard them"
        );
    }
    let mut args = vec!["worktree", "remove"];
    if force {
        args.push("--force");
    }
    let path = workspace.path.to_string_lossy();
    args.push(path.as_ref());
    run_checked("git", args, &repo.root)?;
    run_checked("git", ["branch", "-D", &workspace.branch], &repo.root)?;
    state.remove_workspace(&workspace.reference)?;
    Ok(workspace)
}

fn branch_tree_matches_main(repo: &Repo, branch: &str) -> Result<bool> {
    let main_tree = run_checked("git", ["rev-parse", "main^{tree}"], &repo.root)?;
    let branch_tree = run_output(
        "git",
        ["rev-parse", &format!("{branch}^{{tree}}")],
        &repo.root,
    )?;
    Ok(branch_tree.status.success()
        && String::from_utf8_lossy(&branch_tree.stdout).trim() == main_tree)
}

fn branch_exists(repo: &Repo, branch: &str) -> Result<bool> {
    Ok(run_output(
        "git",
        [
            "show-ref",
            "--verify",
            "--quiet",
            &format!("refs/heads/{branch}"),
        ],
        &repo.root,
    )?
    .status
    .success())
}

fn registered_worktree(repo: &Repo, path: &Path) -> Result<bool> {
    Ok(
        run_checked("git", ["worktree", "list", "--porcelain"], &repo.root)?
            .lines()
            .filter_map(|line| line.strip_prefix("worktree "))
            .map(Path::new)
            .any(|candidate| candidate == path),
    )
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
                && !belongs_to_nested_lake_project(root, path)
        })
        .collect())
}

pub fn tracked_at_head(root: &Path, path: &Path) -> Result<bool> {
    let object = format!("HEAD:{}", path.to_string_lossy());
    Ok(run_output("git", ["cat-file", "-e", &object], root)?
        .status
        .success())
}

pub fn project_lean_files(root: &Path) -> Vec<PathBuf> {
    WalkDir::new(root)
        .into_iter()
        .filter_entry(|entry| {
            !matches!(
                entry.file_name().to_str(),
                Some(".git" | ".lake" | "target")
            ) && (entry.path() == root
                || !entry.file_type().is_dir()
                || !is_lake_project_root(entry.path()))
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

/// Enumerate project Lean files without allowing a slow directory walk to
/// exceed a caller's work budget.
pub fn project_lean_files_until(root: &Path, deadline: Instant) -> (Vec<PathBuf>, bool) {
    let mut files = Vec::new();
    let mut timed_out = false;
    let mut walker = WalkDir::new(root).into_iter();
    while let Some(entry) = walker.next() {
        if Instant::now() >= deadline {
            timed_out = true;
            break;
        }
        let Ok(entry) = entry else {
            continue;
        };
        if entry.file_type().is_dir() {
            let path = entry.path();
            let name = path.file_name().and_then(|name| name.to_str());
            if matches!(name, Some(".git" | ".lake" | "target"))
                || (path != root && is_lake_project_root(path))
            {
                walker.skip_current_dir();
            }
            continue;
        }
        if entry
            .path()
            .extension()
            .is_some_and(|extension| extension == "lean")
            && entry
                .path()
                .file_name()
                .is_none_or(|name| name != "lakefile.lean")
        {
            files.push(entry.into_path());
        }
    }
    (files, timed_out)
}

fn belongs_to_nested_lake_project(root: &Path, path: &Path) -> bool {
    path.parent().is_some_and(|parent| {
        parent
            .ancestors()
            .take_while(|directory| !directory.as_os_str().is_empty())
            .any(|directory| is_lake_project_root(&root.join(directory)))
    })
}

fn is_lake_project_root(path: &Path) -> bool {
    path.join("lakefile.toml").is_file() || path.join("lakefile.lean").is_file()
}

pub fn head(root: &Path) -> Result<String> {
    run_checked("git", ["rev-parse", "HEAD"], root)
}

pub fn reconcile_integration(repo: &Repo) -> Result<()> {
    let _integration_lock = acquire_integration_lock(repo)?;
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
    let _integration_lock = acquire_integration_lock(repo)?;
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
    let _integration_lock = acquire_integration_lock(repo)?;
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
                detail: conflict_detail(&workspace.path, &conflicts),
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
    let conflicts = conflicts.lines().map(PathBuf::from).collect::<Vec<_>>();
    Ok(SyncResult {
        clean: false,
        detail: conflict_detail(&workspace.path, &conflicts),
    })
}

fn continue_autostash_sync(workspace: &Workspace, conflicts: Vec<PathBuf>) -> Result<SyncResult> {
    let unresolved = conflicts
        .iter()
        .filter(|path| has_conflict_markers(&workspace.path.join(path)))
        .collect::<Vec<_>>();
    if !unresolved.is_empty() {
        return Ok(SyncResult {
            clean: false,
            detail: conflict_detail(&workspace.path, &unresolved),
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
            detail: conflict_detail(&workspace.path, &unresolved),
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
        detail: conflict_detail(&workspace.path, &conflicts),
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
            line.starts_with("<<<<<<< ") || line == "=======" || line.starts_with(">>>>>>> ")
        })
    })
}

fn conflict_detail(root: &Path, conflicts: &[impl AsRef<Path>]) -> String {
    format!(
        "conflicts: {} (resolve them, check the affected files, then rerun mathmux sync)",
        conflicts
            .iter()
            .flat_map(|path| {
                let path = path.as_ref();
                let display = path.to_string_lossy();
                let spans = conflict_spans(&root.join(path));
                if spans.is_empty() {
                    vec![display.into_owned()]
                } else {
                    spans
                        .into_iter()
                        .map(|(start, split, end)| {
                            format!("{display}:{start}-{end} (split {split})")
                        })
                        .collect()
                }
            })
            .collect::<Vec<_>>()
            .join(", ")
    )
}

fn conflict_spans(path: &Path) -> Vec<(usize, usize, usize)> {
    let Ok(source) = fs::read_to_string(path) else {
        return Vec::new();
    };
    let mut start = None;
    let mut split = None;
    let mut spans = Vec::new();
    for (index, line) in source.lines().enumerate() {
        let line_number = index + 1;
        if line.starts_with("<<<<<<< ") {
            start = Some(line_number);
            split = None;
        } else if line == "=======" && start.is_some() {
            split = Some(line_number);
        } else if line.starts_with(">>>>>>> ")
            && let (Some(start), Some(split)) = (start.take(), split.take())
        {
            spans.push((start, split, line_number));
        }
    }
    spans
}

pub struct SubmitResult {
    pub workspace_commit: String,
    pub main_commit: String,
    pub base_commit: String,
}

pub fn submit(repo: &Repo, workspace: &Workspace, message: &str) -> Result<SubmitResult> {
    ensure!(!message.trim().is_empty(), "submission message is empty");
    let _integration_lock = acquire_integration_lock(repo)?;

    ensure!(
        dirty_paths(&repo.root)?.is_empty(),
        "managed main worktree is not clean"
    );
    ensure!(
        !merge_in_progress(&workspace.path),
        "workspace has an unfinished merge; resolve it before submit"
    );
    let base_commit = head(&repo.root)?;
    run_git_checked_with_index_lock_retry(["add", "-A"], &workspace.path)?;
    let staged = run_output("git", ["diff", "--cached", "--quiet"], &workspace.path)?;
    ensure!(
        staged.status.code() == Some(1),
        "workspace has no changes to submit"
    );
    run_git_checked_with_index_lock_retry(["commit", "-m", message], &workspace.path)?;
    let workspace_commit = head(&workspace.path)?;

    let merge = run_output(
        "git",
        [
            "merge-tree",
            "--write-tree",
            &base_commit,
            &workspace_commit,
        ],
        &repo.root,
    )?;
    if !merge.status.success() {
        let restore = run_output("git", ["reset", "--mixed", "HEAD^"], &workspace.path)?;
        if !restore.status.success() {
            bail!("integration conflict; workspace change remains committed; run mathmux sync");
        }
        bail!("integration conflict; run mathmux sync");
    }
    let merged_tree = String::from_utf8_lossy(&merge.stdout).trim().to_owned();
    ensure!(
        !merged_tree.is_empty(),
        "cannot read workspace integration tree: {}",
        command_detail(&merge)
    );

    let diff = run_output(
        "git",
        [
            "diff",
            "--binary",
            "--no-ext-diff",
            &base_commit,
            &merged_tree,
        ],
        &workspace.path,
    )?;
    ensure!(
        diff.status.success(),
        "cannot compute workspace integration diff: {}",
        command_detail(&diff)
    );
    if diff.stdout.is_empty() {
        let restore = run_output("git", ["reset", "--mixed", "HEAD^"], &workspace.path)?;
        if !restore.status.success() {
            bail!(
                "workspace changes are already represented on managed main; workspace change remains committed; run mathmux sync"
            );
        }
        bail!("workspace changes are already represented on managed main; run mathmux sync");
    }

    let mut apply = Command::new("git");
    apply
        .args(["apply", "--index", "--whitespace=nowarn", "-"])
        .current_dir(&repo.root)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = apply
        .spawn()
        .context("cannot start workspace integration")?;
    child
        .stdin
        .take()
        .context("workspace integration has no input")?
        .write_all(&diff.stdout)?;
    let output = child.wait_with_output()?;
    if !output.status.success() {
        let _ = run_output("git", ["reset", "--hard", &base_commit], &repo.root);
        let restore = run_output("git", ["reset", "--mixed", "HEAD^"], &workspace.path)?;
        if !restore.status.success() {
            bail!("integration conflict; workspace change remains committed; run mathmux sync");
        }
        bail!("integration conflict; run mathmux sync");
    }
    let commit = run_output("git", ["commit", "-m", message], &repo.root)?;
    if !commit.status.success() {
        let _ = run_output("git", ["reset", "--hard", &base_commit], &repo.root);
        bail!(
            "managed main integration commit failed; workspace change remains committed: {}",
            command_detail(&commit)
        );
    }
    let main_commit = head(&repo.root)?;
    Ok(SubmitResult {
        workspace_commit,
        main_commit,
        base_commit,
    })
}

pub fn lake_command(repo: &Repo, root: &Path) -> Command {
    configure_lake_command(Command::new(lake_executable()), repo, root)
}

pub fn background_lake_command(repo: &Repo, root: &Path) -> Command {
    let mut command = Command::new("taskset");
    command
        .args(["--cpu-list", &background_cpu_list(), "ionice"])
        .args(["-c", "2", "-n", "7", "nice", "-n", "10"])
        .arg(lake_executable());
    configure_lake_command(command, repo, root)
}

fn background_cpu_list() -> String {
    let cpus = std::thread::available_parallelism()
        .map(usize::from)
        .unwrap_or(1);
    format!("0-{}", cpus.div_ceil(2).saturating_sub(1))
}

fn configure_lake_command(mut command: Command, repo: &Repo, root: &Path) -> Command {
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
    use std::time::Duration;

    use tempfile::tempdir;

    use super::*;
    use crate::repo::Repo;
    use crate::state::State;

    #[test]
    fn workspace_names_are_narrow_and_memory_limit_is_bounded() {
        assert!(validate_name("proof_2-a").is_ok());
        assert!(validate_name("-bad").is_err());
        assert!(validate_name("a/b").is_err());
        assert!((1..=MAX_MANAGED_WORKSPACES).contains(&workspace_limit()));
    }

    #[test]
    fn workspace_limit_has_a_single_100_workspace_ceiling() {
        assert_eq!(clamp_workspace_limit(0), 1);
        assert_eq!(clamp_workspace_limit(MAX_MANAGED_WORKSPACES), 100);
        assert_eq!(clamp_workspace_limit(MAX_MANAGED_WORKSPACES + 1), 100);
        assert_eq!(clamp_workspace_limit(usize::MAX), 100);
    }

    #[test]
    fn git_index_lock_retry_waits_for_a_transient_lock() {
        let directory = tempdir().unwrap();
        let root = directory.path().join("repo");
        fs::create_dir(&root).unwrap();
        run_checked("git", ["init", "-b", "main"], &root).unwrap();
        fs::write(root.join("README"), "initial\n").unwrap();
        let lock_path = root.join(".git/index.lock");
        fs::write(&lock_path, "").unwrap();

        let remover = std::thread::spawn({
            let lock_path = lock_path.clone();
            move || {
                std::thread::sleep(Duration::from_millis(150));
                fs::remove_file(lock_path).unwrap();
            }
        });
        run_git_checked_with_index_lock_retry(["add", "README"], &root).unwrap();
        remover.join().unwrap();
        assert!(!lock_path.exists());
        assert_eq!(dirty_paths(&root).unwrap(), vec![PathBuf::from("README")]);
    }

    #[test]
    fn delete_missing_clean_workspace_cleans_metadata() {
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
        let missing_path = workspace.path.clone();
        let moved_path = directory.path().join("removed-workspace");
        fs::rename(&missing_path, &moved_path).unwrap();

        delete_workspace(&repo, &state, "agent", false).unwrap();

        assert!(state.list_workspaces().unwrap().is_empty());
        assert!(!branch_exists(&repo, "mathmux/agent").unwrap());
        assert!(!registered_worktree(&repo, &missing_path).unwrap());
        assert!(moved_path.is_dir());
    }

    #[test]
    fn delete_missing_workspace_preserves_unsubmitted_branch() {
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
        run_checked("git", ["commit", "-m", "unsubmitted"], &workspace.path).unwrap();
        let missing_path = workspace.path.clone();
        let moved_path = directory.path().join("removed-workspace");
        fs::rename(&missing_path, &moved_path).unwrap();

        let error = delete_workspace(&repo, &state, "agent", false)
            .err()
            .expect("missing workspace with branch changes should be preserved");
        assert!(
            error
                .to_string()
                .contains("branch contains unsubmitted commits")
        );
        assert_eq!(state.list_workspaces().unwrap().len(), 1);
        assert!(branch_exists(&repo, "mathmux/agent").unwrap());
        assert!(registered_worktree(&repo, &missing_path).unwrap());
        assert!(moved_path.is_dir());
    }

    #[test]
    fn force_delete_discards_dirty_workspace_and_unsubmitted_branch() {
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
        run_checked("git", ["commit", "-m", "unsubmitted"], &workspace.path).unwrap();
        fs::write(workspace.path.join("Scratch.lean"), "def scratch := true\n").unwrap();

        delete_workspace(&repo, &state, "agent", true).unwrap();

        assert!(state.list_workspaces().unwrap().is_empty());
        assert!(!workspace.path.exists());
        assert!(!branch_exists(&repo, "mathmux/agent").unwrap());
        assert!(!registered_worktree(&repo, &workspace.path).unwrap());
        assert_eq!(
            fs::read_to_string(root.join("Proof.lean")).unwrap(),
            "def value := 0\n"
        );
    }

    #[test]
    fn budgeted_project_file_walk_stops_before_an_expired_deadline() {
        let directory = tempdir().unwrap();
        fs::write(directory.path().join("Proof.lean"), "def value := 0\n").unwrap();

        let (files, timed_out) =
            project_lean_files_until(directory.path(), Instant::now() - Duration::from_secs(1));

        assert!(files.is_empty());
        assert!(timed_out);
    }

    #[test]
    fn validation_lake_commands_are_background_priority() {
        let directory = tempdir().unwrap();
        run_checked("git", ["init"], directory.path()).unwrap();
        let repo = Repo::discover(directory.path()).unwrap();
        let command = background_lake_command(&repo, directory.path());
        assert_eq!(command.get_program(), "taskset");
        let arguments = command
            .get_args()
            .map(|argument| argument.to_string_lossy().into_owned())
            .collect::<Vec<_>>();
        assert_eq!(arguments[0], "--cpu-list");
        assert_eq!(arguments[1], background_cpu_list());
        assert_eq!(
            &arguments[2..9],
            ["ionice", "-c", "2", "-n", "7", "nice", "-n"]
        );
        assert_eq!(arguments[9], "10");
        assert!(
            arguments
                .last()
                .is_some_and(|argument| argument.ends_with("lake"))
        );
    }

    #[test]
    fn push_main_uses_the_configured_upstream() {
        let directory = tempdir().unwrap();
        let remote = directory.path().join("remote.git");
        let root = directory.path().join("repo");
        run_checked(
            "git",
            ["init", "--bare", remote.to_str().unwrap()],
            directory.path(),
        )
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
        run_checked(
            "git",
            ["remote", "add", "origin", remote.to_str().unwrap()],
            &root,
        )
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

        let error = submit(&repo, &workspace, "workspace change")
            .err()
            .expect("conflicting submission should fail");
        assert_eq!(error.to_string(), "integration conflict; run mathmux sync");
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
    fn submit_integrates_unmerged_workspace_history() {
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
        run_checked(
            "git",
            ["commit", "-m", "first workspace change"],
            &workspace.path,
        )
        .unwrap();
        fs::write(workspace.path.join("Extra.lean"), "def extra := true\n").unwrap();

        submit(&repo, &workspace, "second workspace change").unwrap();

        assert_eq!(
            fs::read_to_string(root.join("Proof.lean")).unwrap(),
            "def value := 1\n"
        );
        assert_eq!(
            fs::read_to_string(root.join("Extra.lean")).unwrap(),
            "def extra := true\n"
        );
        assert!(dirty_paths(&root).unwrap().is_empty());
        assert!(dirty_paths(&workspace.path).unwrap().is_empty());

        fs::write(workspace.path.join("Later.lean"), "def later := true\n").unwrap();
        submit(&repo, &workspace, "later workspace change").unwrap();
        assert_eq!(
            fs::read_to_string(root.join("Later.lean")).unwrap(),
            "def later := true\n"
        );
        assert!(dirty_paths(&root).unwrap().is_empty());
        assert!(dirty_paths(&workspace.path).unwrap().is_empty());
    }

    #[test]
    fn submit_preserves_intervening_main_changes_when_workspace_is_stale() {
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
        fs::write(workspace.path.join("Workspace.lean"), "def workspace := true\n").unwrap();
        run_checked("git", ["add", "."], &workspace.path).unwrap();
        run_checked(
            "git",
            ["commit", "-m", "workspace change"],
            &workspace.path,
        )
        .unwrap();

        // Main advances independently after the workspace was created. The
        // submission must not replay the stale workspace tree and delete this file.
        fs::write(root.join("Main.lean"), "def main := true\n").unwrap();
        run_checked("git", ["add", "."], &root).unwrap();
        run_checked("git", ["commit", "-m", "main change"], &root).unwrap();
        fs::write(
            workspace.path.join("Workspace.lean"),
            "def workspace := false\n",
        )
        .unwrap();

        submit(&repo, &workspace, "workspace change").unwrap();

        assert_eq!(
            fs::read_to_string(root.join("Main.lean")).unwrap(),
            "def main := true\n"
        );
        assert_eq!(
            fs::read_to_string(root.join("Workspace.lean")).unwrap(),
            "def workspace := false\n"
        );
        assert!(dirty_paths(&root).unwrap().is_empty());
        assert!(dirty_paths(&workspace.path).unwrap().is_empty());
    }

    #[test]
    fn submit_uses_workspace_tree_delta_after_sync() {
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
        run_checked("git", ["commit", "-m", "workspace proof"], &workspace.path).unwrap();

        // Main reaches the same proof through a different patch, so the
        // workspace history is not patch-equivalent even though sync is clean.
        fs::write(root.join("Proof.lean"), "def value := 1\n").unwrap();
        fs::write(root.join("Main.lean"), "def main := true\n").unwrap();
        run_checked("git", ["add", "."], &root).unwrap();
        run_checked("git", ["commit", "-m", "main proof and extra"], &root).unwrap();
        assert!(sync(&repo, &workspace).unwrap().clean);
        assert!(dirty_paths(&workspace.path).unwrap().is_empty());

        fs::write(workspace.path.join("New.lean"), "def new := true\n").unwrap();
        submit(&repo, &workspace, "new workspace file").unwrap();

        assert_eq!(
            fs::read_to_string(root.join("Proof.lean")).unwrap(),
            "def value := 1\n"
        );
        assert_eq!(
            fs::read_to_string(root.join("New.lean")).unwrap(),
            "def new := true\n"
        );
        assert!(dirty_paths(&root).unwrap().is_empty());
        assert!(dirty_paths(&workspace.path).unwrap().is_empty());
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
        assert!(first.detail.contains("Proof.lean:1-5 (split 3)"));
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
