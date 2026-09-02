use std::collections::{HashMap, HashSet};
use std::ffi::OsStr;
use std::fs;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::time::Duration;

use anyhow::{Context, Result, bail, ensure};
use rusqlite::Connection;
use walkdir::WalkDir;

use crate::coordination::{lock_exclusive_until, open_lock};
use crate::issue::TelemetryStore;
use crate::lean_service;
use crate::repo::Repo;
use crate::state::State;
use crate::util::{run_checked, run_output};

#[derive(Debug)]
struct CleanupPlan {
    deleted_setup_directories: Vec<PathBuf>,
    shared_setup_files: Vec<PathBuf>,
    lean_service_directories: Vec<PathBuf>,
    reclaimable_bytes: u64,
}

#[derive(Debug, Default)]
struct HardCleanupPlan {
    lake_artifacts: Vec<PathBuf>,
    lake_artifact_bytes: u64,
    validation_build: Option<PathBuf>,
    validation_build_bytes: u64,
    worktree_targets: Vec<PathBuf>,
    worktree_target_bytes: u64,
    unregistered_worktrees: Vec<PathBuf>,
    unregistered_worktree_bytes: u64,
}

#[derive(Debug)]
struct UnregisteredWorktree {
    path: PathBuf,
    exists: bool,
    dirty_paths: Option<usize>,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
struct Inode {
    device: u64,
    number: u64,
}

const GC_LOCK_TIMEOUT: Duration = Duration::from_secs(5 * 60);

pub(crate) fn render_storage(repo: &Repo, state: &State) -> Result<String> {
    let active = state.list_workspaces()?;
    let deleted = state.deleted_workspace_references()?;
    let setups = repo.state_dir.join("setups");
    let active_setup_paths = active
        .iter()
        .map(|workspace| setups.join(&workspace.reference))
        .collect::<Vec<_>>();
    let deleted_setup_paths = deleted
        .iter()
        .map(|reference| setups.join(reference))
        .collect::<Vec<_>>();
    let plan = cleanup_plan(repo, state)?;
    let unregistered = unregistered_worktrees(repo, state)?;

    let mut output = format!("MathMux storage: {}", format_bytes(size(&repo.state_dir)?));
    for (label, paths) in [
        (
            "SQLite",
            database_paths(&[&repo.db_path, &repo.search_db_path]),
        ),
        ("active setups", active_setup_paths),
        ("deleted-workspace setups", deleted_setup_paths),
        ("shared setups", vec![setups.join("shared")]),
        ("Lake artifact cache", vec![repo.cache_dir.clone()]),
        (
            "validation worktree",
            vec![repo.state_dir.join("validation-worktree")],
        ),
        ("Lean service", vec![repo.state_dir.join("lean-service")]),
        ("Loogle", vec![repo.state_dir.join("loogle")]),
        (
            "type-search index",
            vec![repo.state_dir.join("type-search-index")],
        ),
    ] {
        output.push_str(&format!("\n{label}: {}", format_bytes(size_many(&paths)?)));
    }
    output.push_str(&format!(
        "\nnormal GC reclaimable: {} ({} deleted workspaces, {} shared setup files, {} obsolete Lean-service generations)",
        format_bytes(plan.reclaimable_bytes),
        plan.deleted_setup_directories.len(),
        plan.shared_setup_files.len(),
        plan.lean_service_directories.len(),
    ));
    output.push_str(
        "\nCategory sizes are physical estimates and may overlap where setups are hard-linked.",
    );
    append_unregistered_worktrees(&mut output, &unregistered);
    Ok(output)
}

pub(crate) fn run_gc(
    repo: &Repo,
    state: &State,
    dry_run: bool,
    hard: bool,
    confirm: bool,
) -> Result<String> {
    if confirm && !hard {
        bail!("--confirm is only valid with --hard");
    }
    if hard && !dry_run && !confirm {
        bail!("hard GC requires --confirm; run --hard --dry-run first");
    }

    let setup_lock = open_lock(&repo.state_dir.join("setup-gc.lock"))?;
    lock_exclusive_until(&setup_lock, GC_LOCK_TIMEOUT)
        .context("setup generation is still active after five minutes; retry GC later")?;
    let lean_lock = open_lock(&repo.state_dir.join("lean-service.lock"))?;
    lock_exclusive_until(&lean_lock, GC_LOCK_TIMEOUT)
        .context("Lean-service generation is still active after five minutes; retry GC later")?;
    let _validation_lock = if hard {
        let lock = open_lock(&repo.validation_lock)?;
        lock_exclusive_until(&lock, GC_LOCK_TIMEOUT)
            .context("validation is still active after five minutes; retry hard GC later")?;
        Some(lock)
    } else {
        None
    };
    let _integration_lock = if hard {
        let lock = open_lock(&repo.integration_lock)?;
        lock_exclusive_until(&lock, GC_LOCK_TIMEOUT)
            .context("integration is still active after five minutes; retry hard GC later")?;
        Some(lock)
    } else {
        None
    };
    if hard {
        let running_checks = state.running_check_runs()?;
        ensure!(
            running_checks.is_empty(),
            "hard GC refused while checks are running: {}",
            running_checks
                .iter()
                .map(|run| run.reference.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        );
        ensure!(
            !state.has_validation_work()?,
            "hard GC refused while the validation queue is not empty"
        );
    }
    let plan = cleanup_plan(repo, state)?;
    let unregistered = unregistered_worktrees(repo, state)?;
    let hard_plan = if hard {
        hard_cleanup_plan(repo, &unregistered)?
    } else {
        HardCleanupPlan::default()
    };

    let reclaimable_bytes = if hard {
        let mut paths = cleanup_paths(&plan);
        paths.extend(hard_cleanup_paths(&hard_plan));
        fully_reclaimed_size(&paths)?
    } else {
        plan.reclaimable_bytes
    };

    if !dry_run {
        for path in &plan.deleted_setup_directories {
            remove_directory(path)?;
        }
        for path in &plan.shared_setup_files {
            remove_file(path)?;
        }
        for path in &plan.lean_service_directories {
            remove_directory(path)?;
        }
        if hard {
            for path in &hard_plan.unregistered_worktrees {
                run_checked(
                    "git",
                    [
                        "worktree",
                        "remove",
                        "--force",
                        path.to_string_lossy().as_ref(),
                    ],
                    &repo.root,
                )?;
            }
            for path in &hard_plan.lake_artifacts {
                remove_file(path)?;
            }
            for path in &hard_plan.worktree_targets {
                remove_directory(path)?;
            }
            if let Some(path) = &hard_plan.validation_build {
                remove_directory(path)?;
            }
        }
    }

    let (search_rows, telemetry_rows) = if dry_run {
        (0, 0)
    } else {
        let search_rows = state.prune_search_history()?;
        let telemetry = TelemetryStore::global_for_repo(repo)?;
        let telemetry_rows = telemetry.prune_history()?;
        checkpoint(&repo.db_path)?;
        checkpoint(&repo.search_db_path)?;
        telemetry.checkpoint()?;
        (search_rows, telemetry_rows)
    };

    let action = if dry_run {
        "would reclaim"
    } else {
        "reclaimed"
    };
    let mut output = if hard {
        format!(
            "MathMux hard GC {} {}\ndeleted setup workspaces: {}\nshared setup files: {}\nobsolete Lean-service generations: {}\nhard Lake artifacts: {} ({} under {})\nvalidation build: {} ({})\nunregistered clean worktree targets: {} ({})\nunregistered clean worktrees: {} ({})",
            action,
            format_bytes(reclaimable_bytes),
            plan.deleted_setup_directories.len(),
            plan.shared_setup_files.len(),
            plan.lean_service_directories.len(),
            hard_plan.lake_artifacts.len(),
            format_bytes(hard_plan.lake_artifact_bytes),
            repo.cache_dir.join("artifacts").display(),
            hard_plan
                .validation_build
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "none".into()),
            format_bytes(hard_plan.validation_build_bytes),
            hard_plan.worktree_targets.len(),
            format_bytes(hard_plan.worktree_target_bytes),
            hard_plan.unregistered_worktrees.len(),
            format_bytes(hard_plan.unregistered_worktree_bytes),
        )
    } else {
        format!(
            "MathMux normal GC {} {}\ndeleted setup workspaces: {}\nshared setup files: {}\nobsolete Lean-service generations: {}",
            action,
            format_bytes(reclaimable_bytes),
            plan.deleted_setup_directories.len(),
            plan.shared_setup_files.len(),
            plan.lean_service_directories.len(),
        )
    };
    if hard {
        for path in &hard_plan.unregistered_worktrees {
            output.push_str(&format!("\n  worktree: {}", path.display()));
        }
        if let Some(path) = &hard_plan.validation_build {
            output.push_str(&format!("\n  validation build: {}", path.display()));
        }
        for path in &hard_plan.worktree_targets {
            output.push_str(&format!("\n  target: {}", path.display()));
        }
    }
    if dry_run {
        output.push_str("\nhistory: unchanged by dry run");
    } else {
        output.push_str(&format!(
            "\nsearch history rows pruned: {search_rows}\ntelemetry rows pruned: {telemetry_rows}\nSQLite: passive checkpoint complete"
        ));
    }
    if hard && !dry_run {
        let removed = hard_plan
            .unregistered_worktrees
            .iter()
            .collect::<HashSet<_>>();
        let remaining = unregistered
            .into_iter()
            .filter(|worktree| !removed.contains(&worktree.path))
            .collect::<Vec<_>>();
        append_unregistered_worktrees(&mut output, &remaining);
    } else {
        append_unregistered_worktrees(&mut output, &unregistered);
    }
    Ok(output)
}

fn hard_cleanup_plan(
    repo: &Repo,
    unregistered: &[UnregisteredWorktree],
) -> Result<HardCleanupPlan> {
    let mut lake_artifacts = Vec::new();
    let artifact_root = repo.cache_dir.join("artifacts");
    if artifact_root.is_dir() {
        for entry in WalkDir::new(&artifact_root) {
            let Some(entry) = tolerate_missing(entry)? else {
                continue;
            };
            if !entry.file_type().is_file() {
                continue;
            }
            let metadata = entry.metadata()?;
            // A cache artifact with one link is reachable only through the
            // cache itself. Any workspace materialization adds another link.
            if metadata.nlink() == 1 {
                lake_artifacts.push(entry.path().to_path_buf());
            }
        }
    }
    lake_artifacts.sort();

    let validation_build = repo.state_dir.join("validation-worktree/.lake/build");
    let validation_build = match fs::symlink_metadata(&validation_build) {
        Ok(metadata) if metadata.file_type().is_dir() => Some(validation_build),
        Ok(_) => None,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
        Err(error) => return Err(error.into()),
    };

    let parent = repo.workspace_parent()?;
    let main_tree = run_checked("git", ["rev-parse", "main^{tree}"], &repo.root)?;
    let mut unregistered_worktrees = Vec::new();
    for worktree in unregistered {
        if !worktree.exists
            || worktree.dirty_paths != Some(0)
            || !worktree.path.starts_with(&parent)
            || worktree_is_locked(&worktree.path)?
            || worktree_has_active_process(&worktree.path)
        {
            continue;
        }
        let head = run_output("git", ["rev-parse", "HEAD^{tree}"], &worktree.path)?;
        if head.status.success() && String::from_utf8_lossy(&head.stdout).trim() == main_tree {
            unregistered_worktrees.push(worktree.path.clone());
        }
    }
    unregistered_worktrees.sort();

    let mut worktree_targets = Vec::new();
    for worktree in unregistered {
        if !worktree.exists
            || worktree.dirty_paths != Some(0)
            || worktree_is_locked(&worktree.path)?
            || worktree_has_active_process(&worktree.path)
            || unregistered_worktrees.contains(&worktree.path)
            || !worktree.path.join("Cargo.toml").is_file()
        {
            continue;
        }
        let target = worktree.path.join("target");
        let Ok(metadata) = fs::symlink_metadata(&target) else {
            continue;
        };
        if metadata.file_type().is_dir() {
            worktree_targets.push(target);
        }
    }
    worktree_targets.sort();

    let lake_artifact_bytes = fully_reclaimed_size(&lake_artifacts)?;
    let validation_build_bytes = validation_build
        .as_ref()
        .map(|path| fully_reclaimed_size(std::slice::from_ref(path)))
        .transpose()?
        .unwrap_or(0);
    let worktree_target_bytes = fully_reclaimed_size(&worktree_targets)?;
    let unregistered_worktree_bytes = fully_reclaimed_size(&unregistered_worktrees)?;
    Ok(HardCleanupPlan {
        lake_artifacts,
        lake_artifact_bytes,
        validation_build,
        validation_build_bytes,
        worktree_targets,
        worktree_target_bytes,
        unregistered_worktrees,
        unregistered_worktree_bytes,
    })
}

fn worktree_is_locked(path: &Path) -> Result<bool> {
    let git_file = path.join(".git");
    let metadata = match fs::symlink_metadata(&git_file) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(true),
        Err(error) => return Err(error.into()),
    };
    if !metadata.file_type().is_file() {
        return Ok(true);
    }
    let contents = fs::read_to_string(&git_file)?;
    let Some(git_dir) = contents.strip_prefix("gitdir:") else {
        return Ok(true);
    };
    let git_dir = PathBuf::from(git_dir.trim());
    let git_dir = if git_dir.is_absolute() {
        git_dir
    } else {
        path.join(git_dir)
    };
    Ok(git_dir.join("locked").is_file())
}

fn worktree_has_active_process(path: &Path) -> bool {
    let Some(path_text) = path.to_str() else {
        return true;
    };
    let path_bytes = path_text.as_bytes();
    let Ok(processes) = fs::read_dir("/proc") else {
        return true;
    };
    processes.flatten().any(|process| {
        let name = process.file_name();
        if !name
            .to_string_lossy()
            .chars()
            .all(|character| character.is_ascii_digit())
        {
            return false;
        }
        let process_path = process.path();
        if fs::read_link(process_path.join("cwd")).is_ok_and(|cwd| cwd.starts_with(path)) {
            return true;
        }
        fs::read(process_path.join("cmdline")).is_ok_and(|cmdline| {
            cmdline
                .windows(path_bytes.len())
                .any(|window| window == path_bytes)
        })
    })
}

fn cleanup_paths(plan: &CleanupPlan) -> Vec<PathBuf> {
    plan.deleted_setup_directories
        .iter()
        .chain(plan.shared_setup_files.iter())
        .chain(plan.lean_service_directories.iter())
        .cloned()
        .collect()
}

fn hard_cleanup_paths(plan: &HardCleanupPlan) -> Vec<PathBuf> {
    plan.lake_artifacts
        .iter()
        .chain(plan.validation_build.iter())
        .chain(plan.worktree_targets.iter())
        .chain(plan.unregistered_worktrees.iter())
        .cloned()
        .collect()
}

fn unregistered_worktrees(repo: &Repo, state: &State) -> Result<Vec<UnregisteredWorktree>> {
    let active = state
        .list_workspaces()?
        .into_iter()
        .map(|workspace| workspace.path)
        .collect::<HashSet<_>>();
    let validation = repo.state_dir.join("validation-worktree");
    let output = match run_output("git", ["worktree", "list", "--porcelain"], &repo.root) {
        Ok(output) if output.status.success() => output,
        _ => return Ok(Vec::new()),
    };
    let mut paths = String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| line.strip_prefix("worktree "))
        .map(PathBuf::from)
        .filter(|path| path != &repo.root && path != &validation && !active.contains(path))
        .collect::<Vec<_>>();
    paths.sort();
    paths.dedup();
    Ok(paths
        .into_iter()
        .map(|path| {
            let exists = path.is_dir();
            let dirty_paths = exists
                .then(|| crate::git::dirty_paths(&path).ok().map(|paths| paths.len()))
                .flatten();
            UnregisteredWorktree {
                path,
                exists,
                dirty_paths,
            }
        })
        .collect())
}

fn append_unregistered_worktrees(output: &mut String, worktrees: &[UnregisteredWorktree]) {
    if worktrees.is_empty() {
        return;
    }
    let clean = worktrees
        .iter()
        .filter(|worktree| worktree.exists && worktree.dirty_paths == Some(0))
        .count();
    let dirty = worktrees
        .iter()
        .filter(|worktree| worktree.dirty_paths.is_some_and(|paths| paths > 0))
        .count();
    let missing = worktrees.iter().filter(|worktree| !worktree.exists).count();
    let unavailable = worktrees
        .iter()
        .filter(|worktree| worktree.exists && worktree.dirty_paths.is_none())
        .count();
    output.push_str(&format!(
        "\ngit worktrees outside MathMux registry: {} ({} clean, {} dirty, {} missing, {} status unavailable)",
        worktrees.len(), clean, dirty, missing, unavailable
    ));
    for worktree in worktrees
        .iter()
        .filter(|worktree| !worktree.exists || worktree.dirty_paths.is_none_or(|paths| paths > 0))
    {
        let detail = if !worktree.exists {
            "missing".to_owned()
        } else if let Some(paths) = worktree.dirty_paths {
            format!("dirty ({paths} path{})", if paths == 1 { "" } else { "s" })
        } else {
            "status unavailable".to_owned()
        };
        output.push_str(&format!("\n  {}: {detail}", worktree.path.display()));
    }
    output
        .push_str("\nGC leaves these git worktrees untouched; inspect before any manual removal.");
}

fn cleanup_plan(repo: &Repo, state: &State) -> Result<CleanupPlan> {
    let setups = repo.state_dir.join("setups");
    let active = state.list_workspaces()?;
    let active_references = active
        .iter()
        .map(|workspace| workspace.reference.as_str())
        .collect::<HashSet<_>>();
    let deleted_references = state
        .deleted_workspace_references()?
        .into_iter()
        .collect::<HashSet<_>>();

    let mut deleted_setup_directories = Vec::new();
    if let Ok(entries) = fs::read_dir(&setups) {
        for entry in entries.flatten() {
            let path = entry.path();
            let Some(name) = path.file_name().and_then(OsStr::to_str) else {
                continue;
            };
            if path.is_dir() && name != "shared" && deleted_references.contains(name) {
                deleted_setup_directories.push(path);
            }
        }
    }

    let active_inodes = inode_set(
        &active_references
            .iter()
            .map(|reference| setups.join(reference))
            .collect::<Vec<_>>(),
    )?;
    let shared = setups.join("shared");
    let mut shared_setup_files = Vec::new();
    if let Ok(entries) = fs::read_dir(&shared) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension() != Some(OsStr::new("json")) {
                continue;
            }
            let metadata = fs::metadata(&path)?;
            if !active_inodes.contains(&inode(&metadata)) {
                shared_setup_files.push(path.clone());
                for companion in [
                    path.with_extension("fingerprint"),
                    path.with_extension("lock"),
                ] {
                    if companion.is_file() {
                        shared_setup_files.push(companion);
                    }
                }
            }
        }
    }

    let expected_generations = active
        .iter()
        .map(|workspace| lean_service::generation_name(&workspace.path))
        .chain(in_use_lean_service_generations(repo))
        .collect::<HashSet<_>>();
    let service_root = repo.state_dir.join("lean-service");
    let mut lean_service_directories = Vec::new();
    if let Ok(entries) = fs::read_dir(&service_root) {
        for entry in entries.flatten() {
            let path = entry.path();
            let Some(name) = path.file_name().and_then(OsStr::to_str) else {
                continue;
            };
            if path.is_dir() && !expected_generations.contains(name) {
                lean_service_directories.push(path);
            }
        }
    }

    deleted_setup_directories.sort();
    shared_setup_files.sort();
    lean_service_directories.sort();
    let reclaimable_paths = deleted_setup_directories
        .iter()
        .chain(lean_service_directories.iter())
        .cloned()
        .chain(shared_setup_files.iter().cloned())
        .collect::<Vec<_>>();
    let reclaimable_bytes = fully_reclaimed_size(&reclaimable_paths)?;
    Ok(CleanupPlan {
        deleted_setup_directories,
        shared_setup_files,
        lean_service_directories,
        reclaimable_bytes,
    })
}

fn in_use_lean_service_generations(repo: &Repo) -> impl Iterator<Item = String> {
    let prefix = format!("{}/", repo.state_dir.join("lean-service").display());
    let mut generations = HashSet::new();
    if let Ok(processes) = fs::read_dir("/proc") {
        for process in processes.flatten() {
            let Ok(command) = fs::read(process.path().join("cmdline")) else {
                continue;
            };
            let text = String::from_utf8_lossy(&command);
            for argument in text.split('\0') {
                if let Some(rest) = argument.strip_prefix(&prefix)
                    && let Some(generation) = rest.split('/').next()
                    && !generation.is_empty()
                {
                    generations.insert(generation.to_owned());
                }
            }
        }
    }
    generations.into_iter()
}

fn checkpoint(path: &Path) -> Result<()> {
    if !path.is_file() {
        return Ok(());
    }
    let connection = Connection::open(path)?;
    connection.busy_timeout(std::time::Duration::from_secs(60))?;
    connection.query_row("PRAGMA wal_checkpoint(PASSIVE)", [], |_| Ok(()))?;
    Ok(())
}

fn database_paths(databases: &[&PathBuf]) -> Vec<PathBuf> {
    databases
        .iter()
        .flat_map(|path| {
            let display = path.to_string_lossy();
            [
                (*path).clone(),
                PathBuf::from(format!("{display}-wal")),
                PathBuf::from(format!("{display}-shm")),
            ]
        })
        .collect()
}

fn remove_directory(path: &Path) -> Result<()> {
    match fs::remove_dir_all(path) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error).with_context(|| format!("cannot remove {}", path.display())),
    }
}

fn remove_file(path: &Path) -> Result<()> {
    match fs::remove_file(path) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error).with_context(|| format!("cannot remove {}", path.display())),
    }
}

fn inode(metadata: &fs::Metadata) -> Inode {
    Inode {
        device: metadata.dev(),
        number: metadata.ino(),
    }
}

fn inode_set(paths: &[PathBuf]) -> Result<HashSet<Inode>> {
    let mut inodes = HashSet::new();
    visit_files(paths, |_, metadata| {
        inodes.insert(inode(metadata));
    })?;
    Ok(inodes)
}

fn size(path: &Path) -> Result<u64> {
    size_many(&[path.to_path_buf()])
}

fn size_many(paths: &[PathBuf]) -> Result<u64> {
    let mut sizes = HashMap::new();
    visit_files(paths, |_, metadata| {
        sizes
            .entry(inode(metadata))
            .or_insert_with(|| metadata.blocks().saturating_mul(512));
    })?;
    Ok(sizes.values().sum())
}

fn fully_reclaimed_size(paths: &[PathBuf]) -> Result<u64> {
    let mut candidates: HashMap<Inode, (u64, u64, u64)> = HashMap::new();
    visit_files(paths, |_, metadata| {
        let entry = candidates.entry(inode(metadata)).or_insert((
            metadata.blocks().saturating_mul(512),
            metadata.nlink(),
            0,
        ));
        entry.2 += 1;
    })?;
    Ok(candidates
        .values()
        .filter(|(_, links, candidates)| candidates >= links)
        .map(|(bytes, _, _)| bytes)
        .sum())
}

fn visit_files(paths: &[PathBuf], mut visit: impl FnMut(&Path, &fs::Metadata)) -> Result<()> {
    for path in paths {
        if !path.exists() {
            continue;
        }
        for entry in WalkDir::new(path).follow_links(false) {
            let Some(entry) = tolerate_missing(entry)? else {
                continue;
            };
            if entry.file_type().is_file() {
                let Some(metadata) = tolerate_missing(entry.metadata())? else {
                    continue;
                };
                visit(entry.path(), &metadata);
            }
        }
    }
    Ok(())
}

fn tolerate_missing<T>(result: walkdir::Result<T>) -> Result<Option<T>> {
    match result {
        Ok(value) => Ok(Some(value)),
        Err(error)
            if error
                .io_error()
                .is_some_and(|error| error.kind() == std::io::ErrorKind::NotFound) =>
        {
            Ok(None)
        }
        Err(error) => Err(error.into()),
    }
}

fn format_bytes(bytes: u64) -> String {
    const KIB: f64 = 1024.0;
    const MIB: f64 = KIB * 1024.0;
    const GIB: f64 = MIB * 1024.0;
    let bytes = bytes as f64;
    if bytes >= GIB {
        format!("{:.1} GiB", bytes / GIB)
    } else if bytes >= MIB {
        format!("{:.1} MiB", bytes / MIB)
    } else if bytes >= KIB {
        format!("{:.1} KiB", bytes / KIB)
    } else {
        format!("{bytes:.0} B")
    }
}

#[cfg(test)]
mod tests {
    use tempfile::tempdir;

    use super::*;
    use crate::state::Workspace;
    use crate::util::run_checked;

    fn repo(root: &Path) -> Repo {
        let git = root.join(".git");
        let state_dir = git.join("mathmux");
        fs::create_dir_all(&state_dir).unwrap();
        Repo {
            root: root.to_path_buf(),
            common_git_dir: git,
            socket_path: state_dir.join("daemon.sock"),
            db_path: state_dir.join("state.sqlite3"),
            search_db_path: state_dir.join("search.sqlite3"),
            log_path: state_dir.join("daemon.log"),
            cache_dir: state_dir.join("lake-cache"),
            integration_lock: state_dir.join("integration.lock"),
            validation_lock: state_dir.join("validation.lock"),
            startup_lock: state_dir.join("startup.lock"),
            state_dir,
        }
    }

    fn workspace(reference: &str, root: &Path) -> Workspace {
        let path = root.join(reference);
        fs::create_dir_all(&path).unwrap();
        fs::write(path.join("lean-toolchain"), "leanprover/lean4:v4.19.0").unwrap();
        Workspace {
            reference: reference.into(),
            name: reference.into(),
            path,
            branch: reference.into(),
            model: None,
        }
    }

    #[test]
    fn reports_unregistered_worktrees_without_removing_them() {
        let directory = tempdir().unwrap();
        let root = directory.path().join("root");
        fs::create_dir_all(&root).unwrap();
        run_checked("git", ["init", "-b", "main"], &root).unwrap();
        run_checked("git", ["config", "user.name", "mathmux test"], &root).unwrap();
        run_checked(
            "git",
            ["config", "user.email", "mathmux@example.invalid"],
            &root,
        )
        .unwrap();
        fs::write(root.join("README"), "main\n").unwrap();
        run_checked("git", ["add", "README"], &root).unwrap();
        run_checked("git", ["commit", "-m", "initial"], &root).unwrap();

        let repo = repo(&root);
        let state = State::new(&repo.db_path).unwrap();
        let external = directory.path().join("external");
        run_checked(
            "git",
            [
                "worktree",
                "add",
                "-b",
                "external",
                external.to_string_lossy().as_ref(),
                "main",
            ],
            &root,
        )
        .unwrap();

        let report = unregistered_worktrees(&repo, &state).unwrap();
        assert_eq!(report.len(), 1);
        assert_eq!(report[0].path, external);
        assert_eq!(report[0].dirty_paths, Some(0));

        fs::write(report[0].path.join("untracked"), "pending\n").unwrap();
        let report = unregistered_worktrees(&repo, &state).unwrap();
        assert_eq!(report[0].dirty_paths, Some(1));
        let mut summary = String::new();
        append_unregistered_worktrees(&mut summary, &report);
        assert!(summary.contains("git worktrees outside MathMux registry: 1"));
        assert!(summary.contains("external: dirty (1 path)"));
        assert!(summary.contains("GC leaves these git worktrees untouched"));

        state
            .add_workspace(&Workspace {
                reference: "w1".into(),
                name: "external".into(),
                path: report[0].path.clone(),
                branch: "external".into(),
                model: None,
            })
            .unwrap();
        assert!(unregistered_worktrees(&repo, &state).unwrap().is_empty());
    }

    #[test]
    fn hard_gc_selects_only_clean_main_tree_worktrees() {
        let directory = tempdir().unwrap();
        let root = directory.path().join("root");
        fs::create_dir_all(&root).unwrap();
        run_checked("git", ["init", "-b", "main"], &root).unwrap();
        run_checked("git", ["config", "user.name", "mathmux test"], &root).unwrap();
        run_checked(
            "git",
            ["config", "user.email", "mathmux@example.invalid"],
            &root,
        )
        .unwrap();
        fs::write(
            root.join("Cargo.toml"),
            "[package]\nname = \"fixture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .unwrap();
        fs::write(root.join(".gitignore"), "target/\n").unwrap();
        fs::write(root.join("README"), "main\n").unwrap();
        run_checked("git", ["add", "."], &root).unwrap();
        run_checked("git", ["commit", "-m", "initial"], &root).unwrap();

        let repo = repo(&root);
        let state = State::new(&repo.db_path).unwrap();
        let parent = repo.workspace_parent().unwrap();
        let orphan = parent.join("orphan");
        run_checked(
            "git",
            [
                "worktree",
                "add",
                "-b",
                "orphan",
                orphan.to_string_lossy().as_ref(),
                "main",
            ],
            &root,
        )
        .unwrap();
        let target = orphan.join("target/debug/generated");
        fs::create_dir_all(target.parent().unwrap()).unwrap();
        fs::write(&target, "generated\n").unwrap();

        let report = unregistered_worktrees(&repo, &state).unwrap();
        let plan = hard_cleanup_plan(&repo, &report).unwrap();
        assert_eq!(plan.unregistered_worktrees, vec![orphan.clone()]);
        assert!(plan.worktree_targets.is_empty());

        // A divergent worktree is still safe for generated-target cleanup,
        // but an untracked source change must protect the whole worktree.
        run_checked("git", ["checkout", "-b", "orphan-diverged"], &orphan).unwrap();
        fs::write(orphan.join("tracked-change"), "diverged\n").unwrap();
        run_checked("git", ["add", "tracked-change"], &orphan).unwrap();
        run_checked("git", ["commit", "-m", "diverge"], &orphan).unwrap();
        let report = unregistered_worktrees(&repo, &state).unwrap();
        let plan = hard_cleanup_plan(&repo, &report).unwrap();
        assert!(plan.unregistered_worktrees.is_empty());
        assert_eq!(plan.worktree_targets, vec![orphan.join("target")]);

        fs::write(orphan.join("untracked"), "keep\n").unwrap();
        let report = unregistered_worktrees(&repo, &state).unwrap();
        let plan = hard_cleanup_plan(&repo, &report).unwrap();
        assert!(plan.worktree_targets.is_empty());
        assert!(orphan.exists());
    }

    #[test]
    fn gc_removes_only_deleted_and_unreferenced_setups() {
        let directory = tempdir().unwrap();
        let repo = repo(directory.path());
        let state = State::new(&repo.db_path).unwrap();
        let active = workspace("w1", directory.path());
        let deleted = workspace("w2", directory.path());
        state.add_workspace(&active).unwrap();
        state.add_workspace(&deleted).unwrap();
        state.remove_workspace("w2").unwrap();

        let shared = repo.state_dir.join("setups/shared");
        let active_setup = repo.state_dir.join("setups/w1/setup.json");
        let deleted_setup = repo.state_dir.join("setups/w2/setup.json");
        fs::create_dir_all(&shared).unwrap();
        fs::create_dir_all(active_setup.parent().unwrap()).unwrap();
        fs::create_dir_all(deleted_setup.parent().unwrap()).unwrap();
        fs::write(shared.join("active.json"), "active").unwrap();
        fs::hard_link(shared.join("active.json"), &active_setup).unwrap();
        fs::write(shared.join("deleted.json"), "deleted").unwrap();
        fs::hard_link(shared.join("deleted.json"), &deleted_setup).unwrap();
        fs::write(shared.join("deleted.fingerprint"), "hash").unwrap();

        let dry_run = run_gc(&repo, &state, true, false, false).unwrap();
        assert!(dry_run.contains("deleted setup workspaces: 1"));
        assert!(active_setup.exists());
        assert!(deleted_setup.exists());

        run_gc(&repo, &state, false, false, false).unwrap();
        assert!(active_setup.exists());
        assert!(shared.join("active.json").exists());
        assert!(!deleted_setup.exists());
        assert!(!shared.join("deleted.json").exists());
        assert!(!shared.join("deleted.fingerprint").exists());
    }

    #[test]
    fn hard_gc_prunes_single_link_artifacts_and_validation_build() {
        let directory = tempdir().unwrap();
        let root = directory.path().join("root");
        fs::create_dir_all(&root).unwrap();
        run_checked("git", ["init", "-b", "main"], &root).unwrap();
        run_checked("git", ["config", "user.name", "mathmux test"], &root).unwrap();
        run_checked(
            "git",
            ["config", "user.email", "mathmux@example.invalid"],
            &root,
        )
        .unwrap();
        fs::write(root.join("README"), "main\n").unwrap();
        run_checked("git", ["add", "README"], &root).unwrap();
        run_checked("git", ["commit", "-m", "initial"], &root).unwrap();

        let repo = repo(&root);
        let state = State::new(&repo.db_path).unwrap();
        let artifacts = repo.cache_dir.join("artifacts");
        fs::create_dir_all(&artifacts).unwrap();
        let orphan = artifacts.join("orphan.olean");
        let live = artifacts.join("live.olean");
        fs::write(&orphan, "orphan").unwrap();
        fs::write(&live, "live").unwrap();
        let active_artifact = root.join(".lake/build/lib/lean/live.olean");
        fs::create_dir_all(active_artifact.parent().unwrap()).unwrap();
        fs::hard_link(&live, &active_artifact).unwrap();

        let validation_build = repo
            .state_dir
            .join("validation-worktree/.lake/build/lib/lean");
        fs::create_dir_all(&validation_build).unwrap();
        fs::write(validation_build.join("generated.olean"), "generated").unwrap();

        let dry_run = run_gc(&repo, &state, true, true, false).unwrap();
        assert!(dry_run.contains("hard Lake artifacts: 1"));
        assert!(dry_run.contains("validation build:"));
        assert!(orphan.exists());
        assert!(validation_build.exists());

        let summary = run_gc(&repo, &state, false, true, true).unwrap();
        assert!(summary.contains("MathMux hard GC reclaimed"));
        assert!(!orphan.exists());
        assert!(live.exists());
        assert!(active_artifact.exists());
        assert!(
            !repo
                .state_dir
                .join("validation-worktree/.lake/build")
                .exists()
        );
    }

    #[test]
    fn byte_format_is_compact() {
        assert_eq!(format_bytes(0), "0 B");
        assert_eq!(format_bytes(1024), "1.0 KiB");
        assert_eq!(format_bytes(1024 * 1024 * 1024), "1.0 GiB");
    }

    #[test]
    fn size_many_ignores_missing_optional_database_sidecars() {
        let directory = tempdir().unwrap();
        let database = directory.path().join("state.sqlite3");
        fs::write(&database, "state").unwrap();

        let paths = database_paths(&[&database]);
        assert_eq!(
            size_many(&paths).unwrap(),
            fs::metadata(&database).unwrap().blocks() * 512
        );
    }

    #[test]
    fn missing_walk_entries_are_ignored() {
        let directory = tempdir().unwrap();
        let missing = directory.path().join("gone");
        let error = WalkDir::new(missing)
            .into_iter()
            .next()
            .expect("missing root should produce an error")
            .expect_err("missing root should not be visited");
        assert!(tolerate_missing::<()>(Err(error)).unwrap().is_none());
    }
}
