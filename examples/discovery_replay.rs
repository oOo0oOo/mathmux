//! Maintainer-only replay against an explicitly isolated workspace.
//! cargo run --example discovery_replay -- WORKSPACE SCRATCH_DIRECTORY
//! stdin lines: search QUERY or probe QUERY. Never edits source or contacts a daemon.
use anyhow::{Result, ensure};
use mathmux::{
    check::Checker,
    repo::Repo,
    search::Searcher,
    state::{State, Workspace},
};
use std::{
    io::{self, BufRead},
    path::PathBuf,
    sync::Arc,
};
fn main() -> Result<()> {
    let args: Vec<_> = std::env::args().collect();
    ensure!(
        args.len() == 3,
        "expected isolated workspace and separate scratch directory"
    );
    let path = PathBuf::from(&args[1]).canonicalize()?;
    let scratch = PathBuf::from(&args[2]);
    std::fs::create_dir_all(&scratch)?;
    let scratch = scratch.canonicalize()?;
    ensure!(
        !scratch.starts_with(&path),
        "scratch must be outside source workspace"
    );
    let actual = Repo::discover(&path)?;
    ensure!(
        scratch != actual.state_dir && !scratch.starts_with(&actual.common_git_dir),
        "scratch must not be live repository state"
    );
    let repo = Repo {
        root: actual.root,
        common_git_dir: actual.common_git_dir,
        state_dir: scratch.clone(),
        socket_path: scratch.join("unused.sock"),
        db_path: scratch.join("state.sqlite3"),
        search_db_path: scratch.join("search.sqlite3"),
        log_path: scratch.join("replay.log"),
        cache_dir: scratch.join("cache"),
        integration_lock: scratch.join("integration.lock"),
        validation_lock: scratch.join("validation.lock"),
        startup_lock: scratch.join("startup.lock"),
    };
    let state = State::new(&repo.db_path)?;
    let ws = Workspace {
        reference: "w1".into(),
        name: "replay".into(),
        path: path.clone(),
        branch: "replay".into(),
        model: None,
    };
    if state.workspace_for_path(&path).is_err() {
        state.add_workspace(&ws)?;
    }
    let checker = Arc::new(Checker::new(repo.clone(), state.clone(), None)?);
    let searcher = Searcher::new(repo, state, checker, None)?;
    for line in io::stdin().lock().lines() {
        let line = line?;
        let Some((verb, query)) = line.split_once(' ') else {
            continue;
        };
        let start = std::time::Instant::now();
        let result = match verb {
            "search" => searcher.search(&ws, &path, query, None, false),
            "probe" => searcher.probe(&ws, &path, query),
            _ => {
                eprintln!("unsupported replay verb");
                continue;
            }
        };
        println!("REQUEST {line}");
        match result {
            Ok(output) => println!("{output}"),
            Err(e) => println!("ERROR {e:#}"),
        }
        println!("ELAPSED {}ms", start.elapsed().as_millis());
    }
    Ok(())
}
