use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};

use crate::util::{canonical, run_checked};

#[derive(Debug, Clone)]
pub struct Repo {
    pub root: PathBuf,
    pub common_git_dir: PathBuf,
    pub state_dir: PathBuf,
    pub socket_path: PathBuf,
    pub db_path: PathBuf,
    pub log_path: PathBuf,
    pub cache_dir: PathBuf,
    pub integration_lock: PathBuf,
    pub startup_lock: PathBuf,
}

impl Repo {
    pub fn discover(cwd: &Path) -> Result<Self> {
        let current_root =
            PathBuf::from(run_checked("git", ["rev-parse", "--show-toplevel"], cwd)?);
        let common_raw = PathBuf::from(run_checked("git", ["rev-parse", "--git-common-dir"], cwd)?);
        let common_git_dir = canonical(if common_raw.is_absolute() {
            common_raw
        } else {
            current_root.join(common_raw)
        })?;
        let root = find_main_worktree(cwd, &current_root)?;
        Self::from_parts(root, common_git_dir)
    }

    pub fn from_root(root: &Path) -> Result<Self> {
        Self::discover(root)
    }

    fn from_parts(root: PathBuf, common_git_dir: PathBuf) -> Result<Self> {
        let root = canonical(root)?;
        let state_dir = common_git_dir.join("mathmux");
        fs::create_dir_all(&state_dir)
            .with_context(|| format!("cannot create {}", state_dir.display()))?;
        Ok(Self {
            root,
            socket_path: state_dir.join("daemon.sock"),
            db_path: state_dir.join("state.sqlite3"),
            log_path: state_dir.join("daemon.log"),
            cache_dir: state_dir.join("lake-cache"),
            integration_lock: state_dir.join("integration.lock"),
            startup_lock: state_dir.join("startup.lock"),
            state_dir,
            common_git_dir,
        })
    }

    pub fn workspace_parent(&self) -> Result<PathBuf> {
        let repo_name = self
            .root
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("repo");
        let parent = self
            .root
            .parent()
            .context("repository has no parent directory")?
            .join(format!(".mathmux-{repo_name}"));
        fs::create_dir_all(&parent)
            .with_context(|| format!("cannot create {}", parent.display()))?;
        Ok(parent)
    }
}

fn find_main_worktree(cwd: &Path, fallback: &Path) -> Result<PathBuf> {
    let output = run_checked("git", ["worktree", "list", "--porcelain"], cwd)?;
    let mut worktree: Option<PathBuf> = None;
    for line in output.lines() {
        if let Some(path) = line.strip_prefix("worktree ") {
            worktree = Some(PathBuf::from(path));
        } else if line == "branch refs/heads/main" {
            return worktree.context("main worktree entry has no path");
        }
    }
    let branch = run_checked("git", ["branch", "--show-current"], fallback)?;
    if branch == "main" {
        return Ok(fallback.to_path_buf());
    }
    bail!("local main must be checked out in a worktree")
}
