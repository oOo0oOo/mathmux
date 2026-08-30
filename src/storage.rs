use std::collections::{HashMap, HashSet};
use std::ffi::OsStr;
use std::fs;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::time::Duration;

use anyhow::{Context, Result};
use rusqlite::Connection;
use walkdir::WalkDir;

use crate::coordination::{lock_exclusive_until, open_lock};
use crate::issue::TelemetryStore;
use crate::lean_service;
use crate::repo::Repo;
use crate::state::State;

#[derive(Debug)]
struct CleanupPlan {
    deleted_setup_directories: Vec<PathBuf>,
    shared_setup_files: Vec<PathBuf>,
    lean_service_directories: Vec<PathBuf>,
    reclaimable_bytes: u64,
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
    Ok(output)
}

pub(crate) fn run_gc(repo: &Repo, state: &State, dry_run: bool) -> Result<String> {
    let setup_lock = open_lock(&repo.state_dir.join("setup-gc.lock"))?;
    lock_exclusive_until(&setup_lock, GC_LOCK_TIMEOUT)
        .context("setup generation is still active after five minutes; retry GC later")?;
    let lean_lock = open_lock(&repo.state_dir.join("lean-service.lock"))?;
    lock_exclusive_until(&lean_lock, GC_LOCK_TIMEOUT)
        .context("Lean-service generation is still active after five minutes; retry GC later")?;
    let plan = cleanup_plan(repo, state)?;

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
    }

    let (search_rows, telemetry_rows) = if dry_run {
        (0, 0)
    } else {
        let search_rows = state.prune_search_history()?;
        let telemetry = TelemetryStore::global()?;
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
    let mut output = format!(
        "MathMux normal GC {} {}\ndeleted setup workspaces: {}\nshared setup files: {}\nobsolete Lean-service generations: {}",
        action,
        format_bytes(plan.reclaimable_bytes),
        plan.deleted_setup_directories.len(),
        plan.shared_setup_files.len(),
        plan.lean_service_directories.len(),
    );
    if dry_run {
        output.push_str("\nhistory: unchanged by dry run");
    } else {
        output.push_str(&format!(
            "\nsearch history rows pruned: {search_rows}\ntelemetry rows pruned: {telemetry_rows}\nSQLite: passive checkpoint complete"
        ));
    }
    Ok(output)
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
            let entry = entry?;
            if entry.file_type().is_file() {
                let metadata = entry.metadata()?;
                visit(entry.path(), &metadata);
            }
        }
    }
    Ok(())
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

        let dry_run = run_gc(&repo, &state, true).unwrap();
        assert!(dry_run.contains("deleted setup workspaces: 1"));
        assert!(active_setup.exists());
        assert!(deleted_setup.exists());

        run_gc(&repo, &state, false).unwrap();
        assert!(active_setup.exists());
        assert!(shared.join("active.json").exists());
        assert!(!deleted_setup.exists());
        assert!(!shared.join("deleted.json").exists());
        assert!(!shared.join("deleted.fingerprint").exists());
    }

    #[test]
    fn byte_format_is_compact() {
        assert_eq!(format_bytes(0), "0 B");
        assert_eq!(format_bytes(1024), "1.0 KiB");
        assert_eq!(format_bytes(1024 * 1024 * 1024), "1.0 GiB");
    }
}
