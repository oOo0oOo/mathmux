use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::os::fd::AsRawFd;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Stdio};
use std::sync::{Arc, Mutex, OnceLock};
use std::time::Instant;

use anyhow::{Context, Result, bail, ensure};
use regex::Regex;
use rusqlite::{Connection, OptionalExtension, params};
use serde_json::Value;
use walkdir::WalkDir;

use crate::check::{Checker, parse_imports, project_module_name};
use crate::git::{dirty_lean_files, lake_command, lake_executable, project_lean_files};
use crate::issue::{TelemetryOperation, TelemetryStore, development_enabled};
use crate::repo::Repo;
use crate::state::{SearchHit, SearchRun, SearchUsage, State, Workspace};
use crate::util::{
    SOURCE_PREVIEW_LINES, clean_line, hash_bytes, now_unix_ms, query_requests_proof_body,
    single_line, truncate_line,
};

const RESULT_LIMIT: usize = 24;
const SUMMARY_LIMIT: usize = 5;
const LOCATION_PREVIEW_LINES: usize = 32;
const LOCATION_MORE_LINES: usize = 96;
const GOAL_STATE_BEGIN: &str = "MATHMUX_GOAL_BEGIN";
const GOAL_STATE_END: &str = "MATHMUX_GOAL_END";
const SEARCH_INDEX_VERSION: i64 = 6;
const SOURCE_INDEX_KIND: &str = "source-v6";
const DECLARATION_DETAIL_LINES: usize = 48;
const INDEX_COMMIT_BATCH: usize = 64;
const SEARCH_REFRESH_INTERVAL: std::time::Duration = std::time::Duration::from_millis(500);

pub struct Searcher {
    repo: Repo,
    state: State,
    checker: Arc<Checker>,
    index_lock: Mutex<()>,
    last_refresh: Mutex<HashMap<String, Instant>>,
    dirty_cache: Mutex<HashMap<String, (Instant, Vec<PathBuf>)>>,
    base_lock: Arc<Mutex<()>>,
    loogle: Mutex<LoogleState>,
    base: Mutex<HashMap<String, BaseState>>,
}

struct SearchResult {
    hits: Vec<SearchHit>,
    inference: String,
    note: Option<String>,
    ok: bool,
}

#[derive(Debug)]
struct RankedHit {
    hit: SearchHit,
    score: f64,
}

struct ImportContext {
    accessible: HashSet<String>,
    complete: bool,
}

#[derive(Debug)]
struct IndexedRow {
    owner: String,
    path: String,
    module: String,
    line: u64,
    name: String,
    kind: String,
    signature: String,
    docs: String,
    body: String,
    rank: f64,
}

fn indexed_row_from_row(row: &rusqlite::Row<'_>) -> rusqlite::Result<IndexedRow> {
    Ok(IndexedRow {
        owner: row.get(0)?,
        path: row.get(1)?,
        module: row.get(2)?,
        line: row.get::<_, i64>(3)?.max(1) as u64,
        name: row.get(4)?,
        kind: row.get(5)?,
        signature: row.get(6)?,
        docs: row.get(7)?,
        body: row.get(8)?,
        rank: row.get(9)?,
    })
}

fn install_active_scopes(connection: &Connection, scopes: &HashSet<String>) -> Result<()> {
    connection.execute_batch(
        "CREATE TEMP TABLE active_search_scopes (owner TEXT PRIMARY KEY) WITHOUT ROWID",
    )?;
    let mut insert = connection.prepare("INSERT INTO active_search_scopes(owner) VALUES (?1)")?;
    for scope in scopes {
        insert.execute([scope])?;
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum SourceKind {
    Project,
    Dependency,
    Stdlib,
}

enum LoogleState {
    Empty,
    Starting(std::sync::mpsc::Receiver<std::result::Result<LoogleWorker, String>>),
    Running(LoogleWorker),
    Unavailable,
}

enum BaseState {
    Starting(
        std::sync::mpsc::Receiver<std::result::Result<HashSet<String>, String>>,
        HashSet<String>,
    ),
    Ready(HashSet<String>),
    Failed(HashSet<String>),
}

struct LoogleWorker {
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
    last_used: Instant,
}

#[derive(Debug)]
struct LoogleHit {
    name: String,
    signature: String,
    module: String,
    doc: Option<String>,
}

struct SourceRoot {
    owner: String,
    root: PathBuf,
    kind: SourceKind,
}

impl Searcher {
    pub fn new(repo: Repo, state: State, checker: Arc<Checker>) -> Result<Self> {
        let searcher = Self::initialized(repo, state, checker);
        searcher.migrate()?;
        Ok(searcher)
    }

    fn initialized(repo: Repo, state: State, checker: Arc<Checker>) -> Self {
        Self {
            repo,
            state,
            checker,
            index_lock: Mutex::new(()),
            last_refresh: Mutex::new(HashMap::new()),
            dirty_cache: Mutex::new(HashMap::new()),
            base_lock: Arc::new(Mutex::new(())),
            loogle: Mutex::new(LoogleState::Empty),
            base: Mutex::new(HashMap::new()),
        }
    }

    pub fn search(
        &self,
        workspace: &Workspace,
        cwd: &Path,
        query: &str,
        all: bool,
    ) -> Result<String> {
        if let Some(reference) = more_search_reference(query.trim()) {
            return self.state.show(reference, true);
        }
        let query = self.expand_reference_query(query.trim())?;
        let query = query.trim();
        ensure!(!query.is_empty(), "search query is empty");
        let reference = self.state.next_ref('q')?;
        let started = Instant::now();
        let result = if let Some(location) = parse_goal_location(&workspace.path, cwd, query)? {
            self.goal_search(workspace, location)?
        } else {
            let (scopes, base_warming) = {
                let _guard = self
                    .index_lock
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
                self.refresh(workspace)?
            };
            self.combined_search(workspace, query, &scopes, base_warming)?
        };
        let run = SearchRun {
            reference: reference.clone(),
            workspace_ref: workspace.reference.clone(),
            query: query.to_owned(),
            inference: result.inference,
            hits: result.hits,
            note: result.note,
            duration_ms: started.elapsed().as_millis() as u64,
            created_at: now_unix_ms(),
        };
        let ok = result.ok;
        self.state.add_search(&run)?;
        self.state.touch_workspace(&workspace.reference)?;
        let rendered = if all {
            self.state.show(&run.reference, true)
        } else {
            Ok(render_summary(&run))
        }?;
        if ok { Ok(rendered) } else { bail!(rendered) }
    }

    fn expand_reference_query(&self, query: &str) -> Result<String> {
        let mut parts = query.splitn(2, char::is_whitespace);
        let reference = parts.next().unwrap_or_default();
        let refinement = parts.next().unwrap_or_default().trim();
        if reference
            .strip_prefix('q')
            .is_some_and(|digits| !digits.is_empty() && digits.chars().all(|c| c.is_ascii_digit()))
        {
            let prior = self
                .state
                .search_run(reference)?
                .with_context(|| format!("unknown search reference {reference}"))?;
            if prior.inference == "goal"
                && !refinement.is_empty()
                && let Some(goal) = prior
                    .hits
                    .iter()
                    .find(|hit| hit.kind == "goal-state")
                    .and_then(|hit| hit.source.as_deref())
            {
                return Ok(goal_refinement_query(goal, refinement));
            }
            return Ok([prior.query.as_str(), refinement]
                .into_iter()
                .filter(|part| !part.is_empty())
                .collect::<Vec<_>>()
                .join(" "));
        }
        if reference
            .strip_prefix('c')
            .is_some_and(|digits| !digits.is_empty() && digits.chars().all(|c| c.is_ascii_digit()))
        {
            let run = self
                .state
                .check_run(reference)?
                .with_context(|| format!("unknown check reference {reference}"))?;
            let diagnostic = run
                .diagnostics
                .first()
                .or_else(|| run.warnings.first())
                .map(|diagnostic| diagnostic.text.as_str())
                .unwrap_or_default();
            let mut diagnostic_query = diagnostic_search_query(diagnostic);
            if diagnostic.contains("Invalid field")
                && let Some(nearest) = self.nearest_field_declaration(&diagnostic_query)?
            {
                diagnostic_query = nearest;
            }
            ensure!(
                !diagnostic_query.is_empty() || !refinement.is_empty(),
                "{reference} has no diagnostic to search"
            );
            return Ok([diagnostic_query.as_str(), refinement]
                .into_iter()
                .filter(|part| !part.is_empty())
                .collect::<Vec<_>>()
                .join(" "));
        }
        Ok(query.to_owned())
    }

    fn nearest_field_declaration(&self, missing: &str) -> Result<Option<String>> {
        let Some((namespace, leaf)) = missing.rsplit_once('.') else {
            return Ok(None);
        };
        let connection = self.open()?;
        let mut statement = connection.prepare(
            "SELECT DISTINCT name FROM search_fts WHERE name LIKE ?1 COLLATE NOCASE LIMIT 2048",
        )?;
        let names = statement
            .query_map([format!("{namespace}.%")], |row| row.get::<_, String>(0))?
            .collect::<rusqlite::Result<Vec<_>>>()?;
        let closest = names
            .into_iter()
            .filter_map(|name| {
                let candidate = name.rsplit('.').next()?;
                Some((edit_distance(leaf, candidate), candidate.len(), name))
            })
            .min();
        Ok(closest
            .filter(|(distance, _, _)| *distance <= 2.max(leaf.chars().count() / 3))
            .map(|(_, _, name)| name))
    }

    pub fn evict_idle_worker(&self, idle_for: std::time::Duration) -> bool {
        let base_running = self.poll_base_workers();
        let mut state = self
            .loogle
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let retain = match &mut *state {
            LoogleState::Starting(_) => true,
            LoogleState::Running(worker) => worker.last_used.elapsed() < idle_for && worker.alive(),
            _ => false,
        };
        if !retain && matches!(&*state, LoogleState::Running(_)) {
            *state = LoogleState::Empty;
        }
        retain || base_running
    }

    fn loogle_hits(&self, workspace: &Workspace, query: &str) -> (Vec<LoogleHit>, bool) {
        if !type_search_enabled() || !workspace.path.join(".lake/packages/mathlib").is_dir() {
            return (Vec::new(), false);
        }
        let mut state = self
            .loogle
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let stopped = match &mut *state {
            LoogleState::Running(worker) => !worker.alive(),
            _ => false,
        };
        if stopped {
            *state = LoogleState::Empty;
        }
        if matches!(&*state, LoogleState::Empty) {
            let (sender, receiver) = std::sync::mpsc::channel();
            let repo = self.repo.clone();
            let workspace = workspace.path.clone();
            std::thread::spawn(move || {
                let started = Instant::now();
                let result =
                    LoogleWorker::start(&repo, &workspace).map_err(|error| format!("{error:#}"));
                if development_enabled(&repo)
                    && let Ok(store) = TelemetryStore::global()
                {
                    let detail = result
                        .as_ref()
                        .map(|_| "Loogle ready")
                        .unwrap_or_else(|error| error.as_str());
                    let rss_kib = result.as_ref().ok().and_then(LoogleWorker::rss_kib);
                    let _ = store.record_operation(
                        &repo,
                        &TelemetryOperation {
                            workspace: None,
                            verb: "loogle_index",
                            reference: None,
                            ok: result.is_ok(),
                            duration_ms: started.elapsed().as_millis() as u64,
                            detail,
                            rss_kib,
                        },
                    );
                }
                let _ = sender.send(result);
            });
            *state = LoogleState::Starting(receiver);
            return (Vec::new(), true);
        }
        if let LoogleState::Starting(receiver) = &*state {
            match receiver.try_recv() {
                Ok(Ok(worker)) => *state = LoogleState::Running(worker),
                Ok(Err(error)) => {
                    append_log(&self.repo, &format!("Loogle unavailable: {error}"));
                    *state = LoogleState::Unavailable;
                }
                Err(std::sync::mpsc::TryRecvError::Disconnected) => {
                    *state = LoogleState::Unavailable;
                }
                Err(std::sync::mpsc::TryRecvError::Empty) => return (Vec::new(), true),
            }
        }
        let LoogleState::Running(worker) = &mut *state else {
            return (Vec::new(), false);
        };
        match worker.query(query) {
            Ok(hits) => (hits, false),
            Err(error) => {
                append_log(&self.repo, &format!("Loogle query failed: {error:#}"));
                *state = LoogleState::Unavailable;
                (Vec::new(), false)
            }
        }
    }

    fn migrate(&self) -> Result<()> {
        let connection = self.open()?;
        connection.pragma_update(None, "journal_mode", "WAL")?;
        connection.execute_batch(
            "CREATE TABLE IF NOT EXISTS search_files (
                owner TEXT NOT NULL,
                path TEXT NOT NULL,
                kind TEXT NOT NULL,
                modified_ns INTEGER NOT NULL,
                size INTEGER NOT NULL,
                PRIMARY KEY(owner, path, kind)
             );
             CREATE VIRTUAL TABLE IF NOT EXISTS search_fts USING fts5(
                owner UNINDEXED,
                origin UNINDEXED,
                file UNINDEXED,
                module UNINDEXED,
                line UNINDEXED,
                name,
                kind UNINDEXED,
                signature,
                docs,
                body,
                tokenize = 'unicode61 remove_diacritics 2'
             );
             CREATE TABLE IF NOT EXISTS search_origins (
                rowid INTEGER PRIMARY KEY,
                owner TEXT NOT NULL,
                origin TEXT NOT NULL
             );
             CREATE INDEX IF NOT EXISTS search_origins_origin
                ON search_origins(owner, origin);
             CREATE TABLE IF NOT EXISTS search_references (
                owner TEXT NOT NULL,
                file TEXT NOT NULL,
                target TEXT NOT NULL,
                source_module TEXT NOT NULL,
                line INTEGER NOT NULL,
                context TEXT
             );
             CREATE INDEX IF NOT EXISTS search_references_target
                ON search_references(target);
             CREATE INDEX IF NOT EXISTS search_references_file
                ON search_references(owner, file);
             CREATE TABLE IF NOT EXISTS search_imports (
                owner TEXT NOT NULL,
                origin TEXT NOT NULL,
                module TEXT NOT NULL,
                imported TEXT NOT NULL,
                PRIMARY KEY(owner, origin, imported)
             );
             CREATE INDEX IF NOT EXISTS search_imports_module
                ON search_imports(module);
             CREATE TABLE IF NOT EXISTS search_meta (
                key TEXT PRIMARY KEY,
                value INTEGER NOT NULL
             );",
        )?;
        let version = connection
            .query_row(
                "SELECT value FROM search_meta WHERE key = 'version'",
                [],
                |row| row.get::<_, i64>(0),
            )
            .optional()?;
        if version != Some(SEARCH_INDEX_VERSION) {
            connection.execute_batch(
                "DELETE FROM search_files;
                 DELETE FROM search_fts;
                 DELETE FROM search_origins;
                 DELETE FROM search_references;
                 DELETE FROM search_imports;
                 DELETE FROM search_meta WHERE key = 'origins_mapped';",
            )?;
            connection.execute(
                "INSERT INTO search_meta(key, value) VALUES ('version', ?1)
                 ON CONFLICT(key) DO UPDATE SET value = excluded.value",
                [SEARCH_INDEX_VERSION],
            )?;
        }
        let has_stale_sources = connection.query_row(
            "SELECT EXISTS(
                SELECT 1 FROM search_files
                WHERE (kind = 'source' OR kind LIKE 'source-v%') AND kind <> ?1
             )",
            [SOURCE_INDEX_KIND],
            |row| row.get::<_, bool>(0),
        )?;
        if has_stale_sources {
            connection.execute(
                "DELETE FROM search_fts
                 WHERE EXISTS (
                    SELECT 1 FROM search_files
                    WHERE search_files.owner = search_fts.owner
                      AND search_files.path = search_fts.origin
                      AND (search_files.kind = 'source' OR search_files.kind LIKE 'source-v%')
                      AND search_files.kind <> ?1
                 )",
                [SOURCE_INDEX_KIND],
            )?;
            connection.execute(
                "DELETE FROM search_files
                 WHERE (kind = 'source' OR kind LIKE 'source-v%') AND kind <> ?1",
                [SOURCE_INDEX_KIND],
            )?;
        }
        let origins_mapped = connection
            .query_row(
                "SELECT value FROM search_meta WHERE key = 'origins_mapped'",
                [],
                |row| row.get::<_, i64>(0),
            )
            .optional()?
            == Some(1);
        if !origins_mapped {
            connection.execute_batch(
                "DELETE FROM search_origins;
                 INSERT INTO search_origins(rowid, owner, origin)
                    SELECT rowid, owner, origin FROM search_fts;
                 INSERT INTO search_meta(key, value) VALUES ('origins_mapped', 1)
                    ON CONFLICT(key) DO UPDATE SET value = excluded.value;",
            )?;
        }
        Ok(())
    }

    fn open(&self) -> Result<Connection> {
        let connection = Connection::open(&self.repo.search_db_path)?;
        connection.busy_timeout(std::time::Duration::from_secs(10))?;
        Ok(connection)
    }

    fn refresh(&self, workspace: &Workspace) -> Result<(HashSet<String>, bool)> {
        let roots = vec![SourceRoot {
            owner: format!("workspace:{}", workspace.reference),
            root: workspace.path.clone(),
            kind: SourceKind::Project,
        }];

        let mut scopes = roots
            .iter()
            .map(|root| root.owner.clone())
            .collect::<HashSet<_>>();
        let project_artifacts = workspace.path.join(".lake/build/lib/lean");
        if project_artifacts.is_dir() {
            scopes.insert(format!("artifacts:{}", workspace.reference));
        }
        let refresh_due = self
            .last_refresh
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .get(&workspace.reference)
            .is_none_or(|last| last.elapsed() >= SEARCH_REFRESH_INTERVAL);
        if refresh_due && let Ok(_base_guard) = self.base_lock.try_lock() {
            match search_index_writer_lock(&self.repo) {
                Ok(_process_guard) => {
                    for root in &roots {
                        if let Err(error) = self.refresh_sources(root, &workspace.path) {
                            append_log(
                                &self.repo,
                                &format!("workspace source refresh deferred: {error:#}"),
                            );
                        }
                    }
                    if project_artifacts.is_dir() {
                        let owner = format!("artifacts:{}", workspace.reference);
                        if let Err(error) = self.refresh_ileans(&owner, &project_artifacts) {
                            append_log(
                                &self.repo,
                                &format!("workspace artifact refresh deferred: {error:#}"),
                            );
                        }
                    }
                    self.last_refresh
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner)
                        .insert(workspace.reference.clone(), Instant::now());
                }
                Err(error) => {
                    append_log(
                        &self.repo,
                        &format!("workspace index refresh deferred: {error:#}"),
                    );
                }
            }
        }
        let (base_scopes, warming) = self.base_scopes(workspace);
        scopes.extend(base_scopes);
        Ok((scopes, warming))
    }

    fn base_scopes(&self, workspace: &Workspace) -> (HashSet<String>, bool) {
        let key = base_input_id(&workspace.path);
        let mut states = self
            .base
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        match states.remove(&key) {
            Some(BaseState::Ready(scopes)) => {
                let result = scopes.clone();
                states.insert(key, BaseState::Ready(scopes));
                (result, false)
            }
            Some(BaseState::Failed(scopes)) => {
                let result = scopes.clone();
                states.insert(key, BaseState::Failed(scopes));
                (result, false)
            }
            Some(BaseState::Starting(receiver, partial)) => match receiver.try_recv() {
                Ok(Ok(scopes)) => {
                    let result = scopes.clone();
                    states.insert(key, BaseState::Ready(scopes));
                    (result, false)
                }
                Ok(Err(error)) => {
                    append_log(&self.repo, &format!("source index unavailable: {error}"));
                    let result = partial.clone();
                    states.insert(key, BaseState::Failed(partial));
                    (result, false)
                }
                Err(std::sync::mpsc::TryRecvError::Disconnected) => {
                    let result = partial.clone();
                    states.insert(key, BaseState::Failed(partial));
                    (result, false)
                }
                Err(std::sync::mpsc::TryRecvError::Empty) => {
                    let result = partial.clone();
                    states.insert(key, BaseState::Starting(receiver, partial));
                    (result, true)
                }
            },
            None => {
                let (sender, receiver) = std::sync::mpsc::channel();
                let repo = self.repo.clone();
                let state = self.state.clone();
                let checker = self.checker.clone();
                let workspace = workspace.clone();
                let base_lock = self.base_lock.clone();
                let partial = package_scopes(&workspace.path);
                std::thread::spawn(move || {
                    let started = Instant::now();
                    let result = {
                        let _guard = base_lock
                            .lock()
                            .unwrap_or_else(std::sync::PoisonError::into_inner);
                        let _process_guard = match search_index_writer_lock(&repo) {
                            Ok(guard) => guard,
                            Err(error) => {
                                let _ = sender.send(Err(format!("{error:#}")));
                                return;
                            }
                        };
                        Searcher::initialized(repo.clone(), state, checker)
                            .refresh_base(&workspace)
                            .map_err(|error| format!("{error:#}"))
                    };
                    if development_enabled(&repo)
                        && let Ok(store) = TelemetryStore::global()
                    {
                        let detail = result
                            .as_ref()
                            .map(|scopes| format!("{} scopes ready", scopes.len()))
                            .unwrap_or_else(|error| error.clone());
                        let _ = store.record_operation(
                            &repo,
                            &TelemetryOperation {
                                workspace: Some(&workspace.reference),
                                verb: "source_index",
                                reference: None,
                                ok: result.is_ok(),
                                duration_ms: started.elapsed().as_millis() as u64,
                                detail: &detail,
                                rss_kib: None,
                            },
                        );
                    }
                    let _ = sender.send(result);
                });
                states.insert(key, BaseState::Starting(receiver, partial.clone()));
                (partial, true)
            }
        }
    }

    fn refresh_base(&self, workspace: &Workspace) -> Result<HashSet<String>> {
        let mut scopes = HashSet::new();
        let packages = workspace.path.join(".lake/packages");
        if packages.is_dir() {
            let packages = fs::canonicalize(packages)?;
            let owner = shared_owner("packages", &packages);
            let artifact_owner = shared_owner("artifact-packages", &packages);
            self.refresh_ileans(&artifact_owner, &packages)?;
            scopes.insert(artifact_owner);
            self.refresh_sources(
                &SourceRoot {
                    owner: owner.clone(),
                    root: packages.clone(),
                    kind: SourceKind::Dependency,
                },
                &workspace.path,
            )?;
            scopes.insert(owner);
        }
        if let Some(stdlib) = lean_source_root(&self.repo, &workspace.path) {
            let owner = shared_owner("stdlib", &stdlib);
            self.refresh_sources(
                &SourceRoot {
                    owner: owner.clone(),
                    root: stdlib,
                    kind: SourceKind::Stdlib,
                },
                &workspace.path,
            )?;
            scopes.insert(owner);
        }
        Ok(scopes)
    }

    fn poll_base_workers(&self) -> bool {
        let mut states = self
            .base
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let keys = states.keys().cloned().collect::<Vec<_>>();
        let mut running = false;
        for key in keys {
            let Some(state) = states.remove(&key) else {
                continue;
            };
            match state {
                BaseState::Starting(receiver, partial) => match receiver.try_recv() {
                    Ok(Ok(scopes)) => {
                        states.insert(key, BaseState::Ready(scopes));
                    }
                    Ok(Err(error)) => {
                        append_log(&self.repo, &format!("source index unavailable: {error}"));
                        states.insert(key, BaseState::Failed(partial));
                    }
                    Err(std::sync::mpsc::TryRecvError::Disconnected) => {
                        states.insert(key, BaseState::Failed(partial));
                    }
                    Err(std::sync::mpsc::TryRecvError::Empty) => {
                        states.insert(key, BaseState::Starting(receiver, partial));
                        running = true;
                    }
                },
                other => {
                    states.insert(key, other);
                }
            }
        }
        running
    }

    fn refresh_sources(&self, source_root: &SourceRoot, workspace_root: &Path) -> Result<()> {
        let files = WalkDir::new(&source_root.root)
            .into_iter()
            .filter_entry(|entry| source_entry(entry.path(), source_root.kind))
            .filter_map(Result::ok)
            .filter(|entry| entry.file_type().is_file())
            .map(|entry| entry.into_path())
            .filter(|path| {
                path.extension()
                    .is_some_and(|extension| extension == "lean")
            })
            .collect::<Vec<_>>();
        self.remove_missing(&source_root.owner, SOURCE_INDEX_KIND, &files)?;
        let changed = self.changed_files(&source_root.owner, SOURCE_INDEX_KIND, &files)?;
        let mut connection = self.open()?;
        for batch in changed.chunks(INDEX_COMMIT_BATCH) {
            let transaction = connection.transaction()?;
            for path in batch {
                let source = fs::read_to_string(path)
                    .with_context(|| format!("cannot index {}", path.display()))?;
                let display =
                    display_path(path, workspace_root, &source_root.root, source_root.kind);
                let module = module_name(path, &source_root.root, source_root.kind);
                let entries = parse_source(&source, &module);
                delete_search_origin(
                    &transaction,
                    &source_root.owner,
                    path.to_string_lossy().as_ref(),
                )?;
                transaction.execute(
                    "DELETE FROM search_imports WHERE owner = ?1 AND origin = ?2",
                    params![source_root.owner, path.to_string_lossy()],
                )?;
                {
                    let mut insert = transaction.prepare_cached(
                        "INSERT OR IGNORE INTO search_imports(owner, origin, module, imported)
                         VALUES (?1, ?2, ?3, ?4)",
                    )?;
                    for imported in parse_imports(&source) {
                        insert.execute(params![
                            source_root.owner,
                            path.to_string_lossy(),
                            module,
                            imported,
                        ])?;
                    }
                }
                {
                    let mut insert = transaction.prepare_cached(
                        "INSERT INTO search_fts(
                            owner, origin, file, module, line, name, kind, signature, docs, body
                         ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10)",
                    )?;
                    let mut map_origin = transaction.prepare_cached(
                        "INSERT INTO search_origins(rowid, owner, origin)
                         VALUES (?1, ?2, ?3)",
                    )?;
                    for entry in entries {
                        insert.execute(params![
                            source_root.owner,
                            path.to_string_lossy(),
                            display,
                            module,
                            entry.line,
                            entry.name,
                            entry.kind,
                            entry.signature,
                            entry.docs,
                            entry.body,
                        ])?;
                        map_origin.execute(params![
                            transaction.last_insert_rowid(),
                            source_root.owner,
                            path.to_string_lossy(),
                        ])?;
                    }
                }
                record_file(&transaction, &source_root.owner, path, SOURCE_INDEX_KIND)?;
            }
            transaction.commit()?;
        }
        Ok(())
    }

    fn refresh_ileans(&self, owner: &str, root: &Path) -> Result<()> {
        if !root.is_dir() {
            return Ok(());
        }
        let files = WalkDir::new(root)
            .into_iter()
            .filter_map(Result::ok)
            .filter(|entry| entry.file_type().is_file())
            .map(|entry| entry.into_path())
            .filter(|path| {
                path.extension()
                    .is_some_and(|extension| extension == "ilean")
            })
            .collect::<Vec<_>>();
        self.remove_missing(owner, "ilean", &files)?;
        let changed = self.changed_files(owner, "ilean", &files)?;
        let mut connection = self.open()?;
        for batch in changed.chunks(INDEX_COMMIT_BATCH) {
            let transaction = connection.transaction()?;
            for path in batch {
                let value: Value = serde_json::from_slice(&fs::read(path)?)
                    .with_context(|| format!("cannot index {}", path.display()))?;
                let module = value
                    .get("module")
                    .and_then(Value::as_str)
                    .unwrap_or_default();
                let source_path = format!("{}.lean", module.replace('.', "/"));
                let artifact = path.to_string_lossy();
                delete_search_origin(&transaction, owner, artifact.as_ref())?;
                transaction.execute(
                    "DELETE FROM search_references WHERE owner = ?1 AND file = ?2",
                    params![owner, artifact],
                )?;
                if let Some(declarations) = value.get("decls").and_then(Value::as_object) {
                    let mut insert = transaction.prepare_cached(
                        "INSERT INTO search_fts(
                            owner, origin, file, module, line, name, kind, signature, docs, body
                         ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, 'declaration', '', '', '')",
                    )?;
                    let mut map_origin = transaction.prepare_cached(
                        "INSERT INTO search_origins(rowid, owner, origin)
                         VALUES (?1, ?2, ?3)",
                    )?;
                    for (name, range) in declarations {
                        let line = range
                            .as_array()
                            .and_then(|range| range.get(4).or_else(|| range.first()))
                            .and_then(Value::as_u64)
                            .unwrap_or(0)
                            + 1;
                        insert.execute(params![
                            owner,
                            artifact,
                            source_path,
                            module,
                            line,
                            name
                        ])?;
                        map_origin.execute(params![
                            transaction.last_insert_rowid(),
                            owner,
                            artifact,
                        ])?;
                    }
                }
                if let Some(references) = value.get("references").and_then(Value::as_object) {
                    let mut insert = transaction.prepare_cached(
                        "INSERT INTO search_references(
                            owner, file, target, source_module, line, context
                         ) VALUES (?1, ?2, ?3, ?4, ?5, ?6)",
                    )?;
                    for (encoded, reference) in references {
                        let Some(target) = reference_name(encoded) else {
                            continue;
                        };
                        let Some(usages) = reference.get("usages").and_then(Value::as_array) else {
                            continue;
                        };
                        for usage in usages {
                            let Some(parts) = usage.as_array() else {
                                continue;
                            };
                            let line = parts.first().and_then(Value::as_u64).unwrap_or(0) + 1;
                            let context = parts.get(4).and_then(Value::as_str);
                            insert
                                .execute(params![owner, artifact, target, module, line, context])?;
                        }
                    }
                }
                record_file(&transaction, owner, path, "ilean")?;
            }
            transaction.commit()?;
        }
        Ok(())
    }

    fn remove_missing(&self, owner: &str, kind: &str, present: &[PathBuf]) -> Result<()> {
        let present = present
            .iter()
            .map(|path| path.to_string_lossy().into_owned())
            .collect::<HashSet<_>>();
        let connection = self.open()?;
        let mut statement =
            connection.prepare("SELECT path FROM search_files WHERE owner = ?1 AND kind = ?2")?;
        let indexed = statement
            .query_map(params![owner, kind], |row| row.get::<_, String>(0))?
            .collect::<rusqlite::Result<Vec<_>>>()?;
        drop(statement);
        for missing in indexed.into_iter().filter(|path| !present.contains(path)) {
            connection.execute(
                "DELETE FROM search_files WHERE owner = ?1 AND path = ?2 AND kind = ?3",
                params![owner, missing, kind],
            )?;
            delete_search_origin(&connection, owner, &missing)?;
            connection.execute(
                "DELETE FROM search_imports WHERE owner = ?1 AND origin = ?2",
                params![owner, missing],
            )?;
            if kind == "ilean" {
                connection.execute(
                    "DELETE FROM search_references WHERE owner = ?1 AND file = ?2",
                    params![owner, missing],
                )?;
            }
        }
        Ok(())
    }

    fn changed_files(&self, owner: &str, kind: &str, files: &[PathBuf]) -> Result<Vec<PathBuf>> {
        let connection = self.open()?;
        let mut statement = connection.prepare(
            "SELECT path, modified_ns, size,
                    EXISTS(
                        SELECT 1 FROM search_origins
                        WHERE search_origins.owner = search_files.owner
                          AND search_origins.origin = search_files.path
                    )
             FROM search_files
             WHERE owner = ?1 AND kind = ?2",
        )?;
        let prior = statement
            .query_map(params![owner, kind], |row| {
                Ok((
                    row.get::<_, String>(0)?,
                    (
                        row.get::<_, i64>(1)?,
                        row.get::<_, i64>(2)?,
                        row.get::<_, bool>(3)?,
                    ),
                ))
            })?
            .collect::<rusqlite::Result<HashMap<_, _>>>()?;
        files
            .iter()
            .filter_map(|path| match fs::metadata(path) {
                Ok(metadata)
                    if prior.get(path.to_string_lossy().as_ref())
                        == Some(&(modified_ns(&metadata), metadata.len() as i64, true)) =>
                {
                    None
                }
                Ok(_) => Some(Ok(path.clone())),
                Err(error) => Some(Err(error.into())),
            })
            .collect()
    }

    fn combined_search(
        &self,
        workspace: &Workspace,
        query: &str,
        scopes: &HashSet<String>,
        base_warming: bool,
    ) -> Result<SearchResult> {
        let explicit_declaration = explicit_declaration_name(query);
        let query = explicit_declaration.unwrap_or(query);
        let type_search = type_search_enabled() && type_shaped(query);
        let query_tokens = meaningful_query_tokens(query);
        let import_context = self.import_context(workspace, scopes, base_warming);
        if !type_search && declaration_name_query(query) {
            let exact = self
                .exact_candidates(query, scopes)?
                .into_iter()
                .map(|row| {
                    let score = lexical_score(query, &query_tokens, &row)
                        + if row.owner == format!("workspace:{}", workspace.reference) {
                            8.0
                        } else {
                            0.0
                        }
                        - row.rank.max(0.0);
                    let (source, matched_line) = detailed_source_excerpt(
                        &row.body,
                        query,
                        &query_tokens,
                        row.line,
                        &row.kind,
                        &row.name,
                    );
                    RankedHit {
                        hit: SearchHit {
                            name: row.name.clone(),
                            kind: row.kind.clone(),
                            signature: nonempty(row.signature.clone()),
                            module: row.module.clone(),
                            path: row.path.clone(),
                            line: matched_line,
                            doc: nonempty(row.docs.clone()),
                            source,
                            usages: Vec::new(),
                            applicable: false,
                            required_import: None,
                        },
                        score,
                    }
                })
                .collect::<Vec<_>>();
            if unique_qualified_hit_name(exact.iter().map(|candidate| &candidate.hit), query)
                .is_some()
            {
                let mut resolved = merge_exact_candidates(exact);
                self.enrich_exact_source(&mut resolved.hit, scopes)?;
                resolved.hit.usages = self.usages(&resolved.hit.name, scopes, workspace)?;
                if let Some(context) = &import_context {
                    apply_import_context(&mut resolved, context);
                }
                let mut hits = vec![resolved.hit];
                hits.extend(self.api_neighborhood(
                    &hits[0],
                    scopes,
                    workspace,
                    import_context.as_ref(),
                )?);
                return Ok(exact_search_result(hits, base_warming));
            }
        }
        let rows = self.candidates(query, &query_tokens, type_search, scopes)?;
        let name_search = !type_search && declaration_name_query(query);
        let mut ranked = Vec::new();
        let mut warming = false;
        if type_search {
            let explicit_conclusion = conclusion_query(query);
            let applicability_query = (!explicit_conclusion).then(|| format!("⊢ {query}"));
            let (applicable_hits, applicable_warming) = match applicability_query.as_deref() {
                Some(query) => self.loogle_hits(workspace, query),
                None => self.loogle_hits(workspace, query),
            };
            warming |= applicable_warming;
            let has_full_applicability_page = applicable_hits.len() >= RESULT_LIMIT;
            for (position, hit) in applicable_hits.into_iter().enumerate() {
                let usages = self.usages(&hit.name, scopes, workspace)?;
                ranked.push(RankedHit {
                    hit: SearchHit {
                        path: format!("{}.lean", hit.module.replace('.', "/")),
                        line: 1,
                        kind: "declaration".into(),
                        signature: nonempty(hit.signature),
                        doc: hit.doc,
                        source: None,
                        usages,
                        name: hit.name,
                        module: hit.module,
                        applicable: true,
                        required_import: None,
                    },
                    score: 280.0 - position as f64,
                });
            }
            if !explicit_conclusion && !has_full_applicability_page {
                let (loogle_hits, is_warming) = self.loogle_hits(workspace, query);
                warming |= is_warming;
                for (position, hit) in loogle_hits.into_iter().enumerate() {
                    let usages = self.usages(&hit.name, scopes, workspace)?;
                    ranked.push(RankedHit {
                        hit: SearchHit {
                            path: format!("{}.lean", hit.module.replace('.', "/")),
                            line: 1,
                            kind: "declaration".into(),
                            signature: nonempty(hit.signature),
                            doc: hit.doc,
                            source: None,
                            usages,
                            name: hit.name,
                            module: hit.module,
                            applicable: false,
                            required_import: None,
                        },
                        score: 180.0 - position as f64,
                    });
                }
            }
        } else if name_search && base_warming {
            let (mut loogle_hits, is_warming) = self.loogle_hits(workspace, query);
            warming |= is_warming;
            let exact_positions = loogle_hits
                .iter()
                .enumerate()
                .filter(|(_, hit)| qualified_name_matches(&hit.name, query))
                .map(|(position, _)| position)
                .collect::<Vec<_>>();
            if let [position] = exact_positions.as_slice() {
                let position = *position;
                let hit = loogle_hits.remove(position);
                let usages = self.usages(&hit.name, scopes, workspace)?;
                let mut resolved = RankedHit {
                    hit: SearchHit {
                        path: format!("{}.lean", hit.module.replace('.', "/")),
                        line: 1,
                        kind: "declaration".into(),
                        signature: nonempty(hit.signature),
                        doc: hit.doc,
                        source: None,
                        usages,
                        name: hit.name,
                        module: hit.module,
                        applicable: false,
                        required_import: None,
                    },
                    score: 900.0,
                };
                self.enrich_exact_source(&mut resolved.hit, scopes)?;
                if let Some(context) = &import_context {
                    apply_import_context(&mut resolved, context);
                }
                let mut hits = vec![resolved.hit];
                hits.extend(self.api_neighborhood(
                    &hits[0],
                    scopes,
                    workspace,
                    import_context.as_ref(),
                )?);
                return Ok(exact_search_result(hits, base_warming));
            }
            for (position, hit) in loogle_hits.into_iter().enumerate() {
                let usages = self.usages(&hit.name, scopes, workspace)?;
                let member_score = qualified_member_score(query, &hit.name);
                ranked.push(RankedHit {
                    hit: SearchHit {
                        path: format!("{}.lean", hit.module.replace('.', "/")),
                        line: 1,
                        kind: "declaration".into(),
                        signature: nonempty(hit.signature),
                        doc: hit.doc,
                        source: None,
                        usages,
                        name: hit.name,
                        module: hit.module,
                        applicable: false,
                        required_import: None,
                    },
                    score: 160.0 - position as f64 + member_score,
                });
            }
        }
        for row in rows.into_iter().filter(|row| scopes.contains(&row.owner)) {
            let type_score = if type_search {
                structural_type_score(query, &row.signature)
            } else {
                0.0
            };
            let lexical = lexical_score(query, &query_tokens, &row);
            if type_search && row.kind == "file" && type_score == 0.0 {
                continue;
            }
            if lexical <= 0.0 && type_score <= 0.0 {
                continue;
            }
            let (source, matched_line) = detailed_source_excerpt(
                &row.body,
                query,
                &query_tokens,
                row.line,
                &row.kind,
                &row.name,
            );
            let score = lexical
                + type_score
                + if row.owner == format!("workspace:{}", workspace.reference) {
                    8.0
                } else {
                    0.0
                }
                - row.rank.max(0.0);
            ranked.push(RankedHit {
                hit: SearchHit {
                    name: row.name,
                    kind: row.kind,
                    signature: nonempty(row.signature),
                    module: row.module,
                    path: row.path,
                    line: matched_line,
                    doc: nonempty(row.docs),
                    source,
                    usages: Vec::new(),
                    applicable: false,
                    required_import: None,
                },
                score,
            });
        }
        ranked.extend(project_source_hits(
            workspace,
            query,
            &query_tokens,
            base_warming,
        ));
        if name_search {
            let exact_name = unique_qualified_hit_name(
                ranked
                    .iter()
                    .map(|candidate| &candidate.hit)
                    .filter(|hit| !matches!(hit.kind.as_str(), "file" | "imports")),
                query,
            );
            if let Some(exact_name) = exact_name {
                let exact = ranked
                    .into_iter()
                    .filter(|candidate| candidate.hit.name.to_lowercase() == exact_name)
                    .collect::<Vec<_>>();
                let mut resolved = merge_exact_candidates(exact);
                self.enrich_exact_source(&mut resolved.hit, scopes)?;
                resolved.hit.usages = self.usages(&resolved.hit.name, scopes, workspace)?;
                if let Some(context) = &import_context {
                    apply_import_context(&mut resolved, context);
                }
                let mut hits = vec![resolved.hit];
                hits.extend(self.api_neighborhood(
                    &hits[0],
                    scopes,
                    workspace,
                    import_context.as_ref(),
                )?);
                return Ok(exact_search_result(hits, base_warming || warming));
            }
        }
        let missing_specific_term = specific_query_tokens(query).iter().any(|token| {
            !ranked.iter().any(|candidate| {
                !matches!(candidate.hit.kind.as_str(), "file" | "imports")
                    && (text_matches_token(&candidate.hit.name.to_lowercase(), token)
                        || candidate.hit.signature.as_deref().is_some_and(|signature| {
                            text_matches_token(&signature.to_lowercase(), token)
                        }))
            })
        });
        let missing_source_identifier = source_specific_query_tokens(query).iter().any(|token| {
            !ranked.iter().any(|candidate| {
                if matches!(candidate.hit.kind.as_str(), "file" | "imports") {
                    return false;
                }
                let name = candidate.hit.name.to_lowercase();
                let base = name.rsplit('.').next().unwrap_or(&name);
                if token.contains('_') {
                    name.contains(token)
                } else {
                    base == token
                }
            })
        });
        let missing_named_detail =
            query_tokens
                .iter()
                .filter(|token| token.len() >= 8)
                .any(|token| {
                    let matches = ranked
                        .iter()
                        .filter(|candidate| hit_name_matches(&candidate.hit.name, token))
                        .collect::<Vec<_>>();
                    !matches.is_empty()
                        && matches.iter().all(|candidate| {
                            candidate.hit.signature.is_none() && candidate.hit.source.is_none()
                        })
                });
        let warm_name_coverage = name_search
            && !base_warming
            && ranked
                .iter()
                .filter(|candidate| !matches!(candidate.hit.kind.as_str(), "file" | "imports"))
                .take(3)
                .count()
                == 3;
        if !warm_name_coverage
            && (ranked.len() < 3
                || missing_specific_term
                || missing_source_identifier
                || missing_named_detail
                || (!base_warming
                    && !type_search
                    && (query.contains('|') || !named_argument_terms(query).is_empty())))
        {
            match fallback_source_hits(&workspace.path, query, &query_tokens) {
                Ok(hits) => ranked.extend(hits),
                Err(error) => append_log(
                    &self.repo,
                    &format!("source fallback unavailable: {error:#}"),
                ),
            }
        }
        if declaration_glob_query(query) {
            ranked.retain(|candidate| declaration_glob_matches(&candidate.hit.name, query));
        }
        if let Some(context) = &import_context {
            for candidate in &mut ranked {
                apply_import_context(candidate, context);
            }
        }
        ranked.sort_by(|left, right| {
            right
                .score
                .partial_cmp(&left.score)
                .unwrap_or(Ordering::Equal)
                .then_with(|| left.hit.name.cmp(&right.hit.name))
        });
        let mut positions: HashMap<String, usize> = HashMap::new();
        let mut deduplicated: Vec<RankedHit> = Vec::new();
        for mut candidate in ranked {
            if let Some(index) = positions.get(&candidate.hit.name).copied() {
                merge_duplicate_hit(&mut deduplicated[index].hit, &mut candidate.hit);
            } else {
                positions.insert(candidate.hit.name.clone(), deduplicated.len());
                deduplicated.push(candidate);
            }
        }
        let mut ranked = deduplicated;
        if explicit_declaration.is_some() {
            ranked.sort_by_key(|candidate| !qualified_name_matches(&candidate.hit.name, query));
        } else {
            promote_query_coverage(&mut ranked, &query_tokens);
        }
        ranked.truncate(RESULT_LIMIT);
        for candidate in &mut ranked {
            if candidate.hit.usages.is_empty()
                && !matches!(candidate.hit.kind.as_str(), "file" | "imports")
            {
                candidate.hit.usages = self.usages(&candidate.hit.name, scopes, workspace)?;
            }
        }
        let no_hits = ranked.is_empty();
        let dependency_sources_missing = dependency_sources_missing(&workspace.path);
        Ok(SearchResult {
            hits: ranked.into_iter().map(|candidate| candidate.hit).collect(),
            inference: if type_search {
                "hybrid+applicability".into()
            } else if !type_search_enabled() {
                "hybrid(type-off)".into()
            } else {
                "hybrid".into()
            },
            note: match (base_warming, warming, no_hits && dependency_sources_missing) {
                (_, _, true) => {
                    Some("dependency sources unavailable: .lake/packages is missing".into())
                }
                (true, true, _) => Some("source and type indexes warming".into()),
                (true, false, _) => Some("source index warming".into()),
                (false, true, _) => Some("type index warming".into()),
                (false, false, false) => None,
            },
            ok: true,
        })
    }

    fn import_context(
        &self,
        workspace: &Workspace,
        scopes: &HashSet<String>,
        base_warming: bool,
    ) -> Option<ImportContext> {
        if base_warming {
            return None;
        }
        let dirty = self.dirty_lean_files(workspace)?;
        let nested = dirty
            .iter()
            .filter(|path| path.components().count() > 1)
            .collect::<Vec<_>>();
        let target = if nested.len() == 1 {
            nested[0]
        } else if dirty.len() == 1 {
            &dirty[0]
        } else {
            return None;
        };
        let source = fs::read_to_string(workspace.path.join(target)).ok()?;
        let module = project_module_name(&workspace.path, target);
        let mut graph: HashMap<String, Vec<String>> = HashMap::new();
        let connection = self.open().ok()?;
        let mut statement = connection
            .prepare("SELECT owner, module, imported FROM search_imports")
            .ok()?;
        let rows = statement
            .query_map([], |row| {
                Ok((
                    row.get::<_, String>(0)?,
                    row.get::<_, String>(1)?,
                    row.get::<_, String>(2)?,
                ))
            })
            .ok()?;
        for row in rows.flatten() {
            if scopes.contains(&row.0) {
                graph.entry(row.1).or_default().push(row.2);
            }
        }
        graph.insert(module.clone(), parse_imports(&source));
        let mut accessible = HashSet::from([module.clone()]);
        let mut pending = vec![module];
        while let Some(module) = pending.pop() {
            for imported in graph.get(&module).into_iter().flatten() {
                if accessible.insert(imported.clone()) {
                    pending.push(imported.clone());
                }
            }
        }
        Some(ImportContext {
            accessible,
            complete: !base_warming,
        })
    }

    fn dirty_lean_files(&self, workspace: &Workspace) -> Option<Vec<PathBuf>> {
        let mut cache = self
            .dirty_cache
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if let Some((updated, paths)) = cache.get(&workspace.reference)
            && updated.elapsed() < SEARCH_REFRESH_INTERVAL
        {
            return Some(paths.clone());
        }
        let paths = dirty_lean_files(&workspace.path).ok()?;
        cache.insert(
            workspace.reference.clone(),
            (Instant::now(), paths.clone()),
        );
        Some(paths)
    }

    fn candidates(
        &self,
        query: &str,
        tokens: &[String],
        include_all_signatures: bool,
        scopes: &HashSet<String>,
    ) -> Result<Vec<IndexedRow>> {
        let connection = self.open()?;
        install_active_scopes(&connection, scopes)?;
        let fts_query = fts_query(&tokens.join(" "));
        let name_query = declaration_name_query(query);
        let sql = if fts_query.is_empty() && include_all_signatures {
            "SELECT owner, file, module, line, name, kind, signature, docs, body, 0.0
             FROM search_fts WHERE signature <> ''
               AND owner IN (SELECT owner FROM active_search_scopes) LIMIT 20000"
        } else if name_query {
            "SELECT owner, file, module, line, name, kind, signature, docs, body,
                    bm25(search_fts, 0.0, 0.0, 0.0, 0.0, 0.0, 12.0, 0.0, 7.0, 3.0, 1.0)
             FROM search_fts WHERE search_fts MATCH ?1
               AND owner IN (SELECT owner FROM active_search_scopes) LIMIT 256"
        } else {
            "SELECT owner, file, module, line, name, kind, signature, docs, body,
                    bm25(search_fts, 0.0, 0.0, 0.0, 0.0, 0.0, 12.0, 0.0, 7.0, 3.0, 1.0)
             FROM search_fts WHERE search_fts MATCH ?1
               AND owner IN (SELECT owner FROM active_search_scopes) LIMIT 1000"
        };
        let mut statement = connection.prepare(sql)?;
        let mut rows = if fts_query.is_empty() && include_all_signatures {
            statement
                .query_map([], indexed_row_from_row)?
                .collect::<rusqlite::Result<Vec<_>>>()
                .map_err(anyhow::Error::from)?
        } else if fts_query.is_empty() {
            Vec::new()
        } else {
            statement
                .query_map([fts_query], indexed_row_from_row)?
                .collect::<rusqlite::Result<Vec<_>>>()
                .map_err(anyhow::Error::from)?
        };
        drop(statement);
        let mut named = connection.prepare(
            "SELECT owner, file, module, line, name, kind, signature, docs, body,
                    bm25(search_fts, 0.0, 0.0, 0.0, 0.0, 0.0, 12.0, 0.0, 7.0, 3.0, 1.0)
             FROM search_fts WHERE search_fts MATCH ?1
               AND owner IN (SELECT owner FROM active_search_scopes) LIMIT 128",
        )?;
        let mut named_contains = connection.prepare(
            "SELECT owner, file, module, line, name, kind, signature, docs, body, 0.0
             FROM search_fts WHERE name LIKE ?1 COLLATE NOCASE
               AND owner IN (SELECT owner FROM active_search_scopes) LIMIT 32",
        )?;
        let mut qualified = connection.prepare(
            "SELECT owner, file, module, line, name, kind, signature, docs, body,
                    bm25(search_fts, 0.0, 0.0, 0.0, 0.0, 0.0, 12.0, 0.0, 7.0, 3.0, 1.0)
             FROM search_fts WHERE search_fts MATCH ?1
               AND owner IN (SELECT owner FROM active_search_scopes) LIMIT 256",
        )?;
        for token in tokens
            .iter()
            .filter(|token| token.len() >= 4 && token.as_str() != "_")
        {
            let query = format!("name : \"{}\"*", token.replace('"', "\"\""));
            rows.extend(
                named
                    .query_map([query], indexed_row_from_row)?
                    .collect::<rusqlite::Result<Vec<_>>>()?,
            );
            if token.len() >= 8 || token.contains(['.', '_']) {
                rows.extend(
                    named_contains
                        .query_map([format!("%{token}%")], indexed_row_from_row)?
                        .collect::<rusqlite::Result<Vec<_>>>()?,
                );
            }
        }
        if name_query && let Some((owner, leaf)) = query.rsplit_once('.')
        {
            let owner = owner.rsplit('.').next().unwrap_or(owner).to_lowercase();
            let mut seen = HashSet::new();
            for part in identifier_query_parts(leaf)
                .into_iter()
                .filter(|part| part.len() >= 2 && seen.insert(part.clone()))
            {
                let query = format!(
                    "name : \"{}\" AND name : \"{}\"*",
                    owner.replace('"', "\"\""),
                    part.replace('"', "\"\"")
                );
                rows.extend(
                    qualified
                        .query_map([query], indexed_row_from_row)?
                        .collect::<rusqlite::Result<Vec<_>>>()?,
                );
            }
        }
        Ok(rows)
    }

    fn exact_candidates(
        &self,
        query: &str,
        scopes: &HashSet<String>,
    ) -> Result<Vec<IndexedRow>> {
        let connection = self.open()?;
        install_active_scopes(&connection, scopes)?;
        let mut statement = connection.prepare(
            "SELECT owner, file, module, line, name, kind, signature, docs, body, 0.0
             FROM search_fts
             WHERE search_fts MATCH ?1
               AND owner IN (SELECT owner FROM active_search_scopes)
             LIMIT 128",
        )?;
        let exact = format!("name : \"{}\"", query.replace('"', "\"\""));
        statement
            .query_map([exact], indexed_row_from_row)?
            .collect::<rusqlite::Result<Vec<_>>>()
            .map(|rows| {
                rows.into_iter()
                    .filter(|row| qualified_name_matches(&row.name, query))
                    .collect()
            })
            .map_err(anyhow::Error::from)
    }

    fn api_neighborhood(
        &self,
        exact: &SearchHit,
        scopes: &HashSet<String>,
        workspace: &Workspace,
        import_context: Option<&ImportContext>,
    ) -> Result<Vec<SearchHit>> {
        let connection = self.open()?;
        install_active_scopes(&connection, scopes)?;
        let prefix = format!("{}.", exact.name);
        let leaf = exact.name.rsplit('.').next().unwrap_or(&exact.name);
        let mut nested = connection.prepare(
            "SELECT owner, file, module, line, name, kind, signature, docs, body, 0.0
             FROM search_fts
             WHERE search_fts MATCH ?1
               AND owner IN (SELECT owner FROM active_search_scopes)
             LIMIT 128",
        )?;
        let mut same_module = connection.prepare(
            "SELECT owner, file, module, line, name, kind, signature, docs, body, 0.0
             FROM search_fts
             WHERE search_fts MATCH ?1 AND module = ?2
               AND owner IN (SELECT owner FROM active_search_scopes)
             LIMIT 128",
        )?;
        let nested_query = format!("name : \"{}\"*", exact.name.replace('"', "\"\""));
        let signature_query = format!("signature : \"{}\"*", leaf.replace('"', "\"\""));
        let mut rows = nested
            .query_map([nested_query], indexed_row_from_row)?
            .collect::<rusqlite::Result<Vec<_>>>()?;
        rows.extend(
            same_module
                .query_map(params![signature_query, exact.module], indexed_row_from_row)?
                .collect::<rusqlite::Result<Vec<_>>>()?,
        );
        let mut seen = HashSet::new();
        let mut ranked = rows
            .into_iter()
            .filter(|row| {
                row.name != exact.name
                    && (row.name.starts_with(&prefix)
                        || (row.module == exact.module && row.signature.contains(leaf)))
                    && scopes.contains(&row.owner)
                    && seen.insert(row.name.clone())
            })
            .map(|row| {
                let priority = if row.name == format!("{}.mk", exact.name) {
                    0
                } else if row.name.starts_with(&format!("{}.", exact.name)) {
                    1
                } else {
                    2
                };
                (priority, row)
            })
            .collect::<Vec<_>>();
        ranked.sort_by(|(left_priority, left), (right_priority, right)| {
            left_priority
                .cmp(right_priority)
                .then_with(|| left.name.cmp(&right.name))
        });
        ranked
            .into_iter()
            .take(4)
            .map(|(_, row)| {
                let mut candidate = RankedHit {
                    hit: SearchHit {
                        name: row.name.clone(),
                        kind: row.kind,
                        signature: nonempty(row.signature),
                        module: row.module,
                        path: row.path,
                        line: row.line,
                        doc: nonempty(row.docs),
                        source: None,
                        usages: self.usages(&row.name, scopes, workspace)?,
                        applicable: false,
                        required_import: None,
                    },
                    score: 0.0,
                };
                if let Some(context) = import_context {
                    apply_import_context(&mut candidate, context);
                }
                Ok(candidate.hit)
            })
            .collect()
    }

    fn enrich_exact_source(&self, hit: &mut SearchHit, scopes: &HashSet<String>) -> Result<()> {
        if hit.source.is_some() && hit.signature.is_some() {
            return Ok(());
        }
        let leaf = hit.name.rsplit('.').next().unwrap_or(&hit.name);
        let connection = self.open()?;
        let mut statement = connection.prepare(
            "SELECT owner, file, module, line, name, kind, signature, docs, body, 0.0
             FROM search_fts WHERE search_fts MATCH ?1 LIMIT 128",
        )?;
        let query = format!("name : \"{}\"", leaf.replace('"', "\"\""));
        let rows = statement
            .query_map([query], indexed_row_from_row)?
            .collect::<rusqlite::Result<Vec<_>>>()?;
        let Some(row) = rows.into_iter().find(|row| {
            scopes.contains(&row.owner)
                && row.module == hit.module
                && row.line == hit.line
                && row.name.rsplit('.').next() == Some(leaf)
                && (!row.body.is_empty() || !row.signature.is_empty())
        }) else {
            return Ok(());
        };
        let (source, line) = detailed_source_excerpt(
            &row.body,
            leaf,
            &[leaf.to_lowercase()],
            row.line,
            &row.kind,
            &row.name,
        );
        let mut source_hit = SearchHit {
            name: hit.name.clone(),
            kind: row.kind,
            signature: nonempty(row.signature),
            module: row.module,
            path: row.path,
            line,
            doc: nonempty(row.docs),
            source,
            usages: Vec::new(),
            applicable: false,
            required_import: None,
        };
        merge_duplicate_hit(hit, &mut source_hit);
        Ok(())
    }

    fn usages(
        &self,
        name: &str,
        scopes: &HashSet<String>,
        workspace: &Workspace,
    ) -> Result<Vec<SearchUsage>> {
        let connection = self.open()?;
        let mut statement = connection.prepare(
            "SELECT owner, source_module, line, context
             FROM search_references WHERE target = ?1 LIMIT 100",
        )?;
        let rows = statement.query_map([name], |row| {
            Ok((
                row.get::<_, String>(0)?,
                row.get::<_, String>(1)?,
                row.get::<_, i64>(2)? as u64,
                row.get::<_, Option<String>>(3)?,
            ))
        })?;
        let mut usages = Vec::new();
        for row in rows {
            let (owner, module, line, context) = row?;
            if !scopes.contains(&owner) {
                continue;
            }
            usages.push(SearchUsage {
                path: reference_display_path(&module, workspace),
                module,
                line,
                context,
            });
        }
        Ok(usages)
    }

    fn goal_search(&self, workspace: &Workspace, location: GoalLocation) -> Result<SearchResult> {
        let source = fs::read_to_string(&location.path)?;
        if location.tail || location.more {
            return Ok(source_location_result(
                workspace, &location, &source, None, true,
            ));
        }
        if !location.probe {
            return Ok(source_location_result(
                workspace,
                &location,
                &source,
                Some("source only"),
                false,
            ));
        }
        let Some((start, end, in_tactic, indent)) = goal_probe(&source, location.line) else {
            return Ok(source_location_result(
                workspace,
                &location,
                &source,
                Some("source only"),
                false,
            ));
        };
        let mut probe = source.clone();
        probe.replace_range(
            start..end,
            &goal_probe_replacement(
                in_tactic,
                &indent,
                "first | exact? | aesop? | simp? | apply? | rw?",
            ),
        );
        let (_, rendered) = match self
            .checker
            .probe_source(workspace, &location.path, &probe)
        {
            Ok(result) => result,
            Err(error) => {
                return Ok(source_location_result(
                    workspace,
                    &location,
                    &source,
                    Some(&format!("goal unavailable: {error:#}")),
                    false,
                ));
            }
        };
        let goal_state = traced_goal_state(&rendered);
        let mut suggestions = Vec::new();
        if let Some(state) = &goal_state {
            for candidate in local_method_candidates(state) {
                probe = source.clone();
                probe.replace_range(
                    start..end,
                    &goal_probe_replacement(in_tactic, &indent, &candidate),
                );
                if self
                    .checker
                    .probe_source(workspace, &location.path, &probe)
                    .is_ok_and(|(ok, _)| ok)
                {
                    suggestions.push(candidate);
                    break;
                }
            }
        }
        for suggestion in try_this_suggestions(&rendered) {
            push_suggestion(&mut suggestions, &suggestion);
        }
        if suggestions.is_empty() && goal_state.is_none() {
            let detail = rendered
                .lines()
                .rev()
                .find(|line| !line.trim().is_empty())
                .map(|line| {
                    format!(
                        "goal search returned no tactic suggestion: {}",
                        clean_line(line)
                    )
                })
                .unwrap_or_else(|| "goal search returned no tactic suggestion".into());
            return Ok(source_location_result(
                workspace,
                &location,
                &source,
                Some(&detail),
                false,
            ));
        }
        let relative = location
            .path
            .strip_prefix(&workspace.path)
            .unwrap_or(&location.path)
            .to_string_lossy()
            .into_owned();
        let mut hits = Vec::new();
        if let Some(goal_state) = goal_state {
            hits.push(SearchHit {
                name: "goal".into(),
                kind: "goal-state".into(),
                signature: None,
                module: String::new(),
                path: relative.clone(),
                line: location.line,
                doc: None,
                source: Some(goal_state),
                usages: Vec::new(),
                applicable: false,
                required_import: None,
            });
        }
        hits.extend(suggestions.into_iter().map(|suggestion| SearchHit {
            name: clean_line(&suggestion),
            kind: "goal".into(),
            signature: None,
            module: String::new(),
            path: relative.clone(),
            line: location.line,
            doc: None,
            source: Some(suggestion),
            usages: Vec::new(),
            applicable: true,
            required_import: None,
        }));
        let has_suggestion = hits.iter().any(|hit| hit.applicable);
        Ok(SearchResult {
            hits,
            inference: "goal".into(),
            note: (!has_suggestion).then(|| "no tactic suggestion".into()),
            ok: true,
        })
    }
}

fn more_search_reference(query: &str) -> Option<&str> {
    let mut terms = query.split_whitespace().rev();
    let modifier = terms.next()?;
    let reference = terms.next()?;
    (modifier.eq_ignore_ascii_case("more")
        && reference
            .strip_prefix('q')
            .is_some_and(|digits| !digits.is_empty() && digits.chars().all(|c| c.is_ascii_digit())))
    .then_some(reference)
}

fn diagnostic_search_query(diagnostic: &str) -> String {
    let lines = diagnostic.lines().collect::<Vec<_>>();
    if diagnostic.contains("unsolved goals")
        && let Some(index) = lines
            .iter()
            .rposition(|line| line.trim_start().starts_with('⊢'))
    {
        let goal = lines[index..]
            .iter()
            .copied()
            .take_while(|line| {
                let trimmed = line.trim_start();
                !trimmed.is_empty()
                    && !trimmed
                        .chars()
                        .next()
                        .is_some_and(|character| character.is_ascii_digit())
            })
            .collect::<Vec<_>>()
            .join(" ");
        let locals = lines[..index]
            .iter()
            .filter_map(|line| line.trim().split_once(':').map(|(names, _)| names))
            .flat_map(str::split_whitespace)
            .filter(|name| declaration_name_query(name))
            .collect::<HashSet<_>>();
        return truncate_line(&single_line(&anonymize_goal(&goal, &locals)), 600);
    }
    static QUOTED: OnceLock<Regex> = OnceLock::new();
    let quoted = QUOTED.get_or_init(|| Regex::new(r"`([^`]+)`").expect("valid diagnostic regex"));
    let terms = quoted
        .captures_iter(diagnostic)
        .filter_map(|capture| capture.get(1).map(|value| value.as_str().trim()))
        .filter(|value| declaration_name_query(value))
        .collect::<Vec<_>>();
    if let Some(qualified) = terms.iter().find(|term| term.contains('.')) {
        return (*qualified).to_owned();
    }
    let mut selected = terms
        .into_iter()
        .map(str::to_owned)
        .collect::<Vec<_>>();
    for token in diagnostic.split(|character: char| {
        character.is_whitespace() || matches!(character, ':' | ',' | '(' | ')' | '[' | ']')
    }) {
        let token = token.trim_matches(|character: char| !character.is_alphanumeric() && character != '_' && character != '.');
        if token.len() >= 4
            && (token.contains(['.', '_'])
                || token.chars().next().is_some_and(char::is_uppercase))
            && !selected.iter().any(|seen| seen == token)
        {
            selected.push(token.to_owned());
        }
        if selected.len() >= 10 {
            break;
        }
    }
    if selected.is_empty() {
        truncate_line(&single_line(diagnostic), 240)
    } else {
        selected.join(" ")
    }
}

fn anonymize_goal(goal: &str, locals: &HashSet<&str>) -> String {
    let mut output = String::with_capacity(goal.len());
    let mut identifier = String::new();
    let flush = |output: &mut String, identifier: &mut String| {
        if !identifier.is_empty() {
            if locals.contains(identifier.as_str()) {
                output.push('_');
            } else {
                output.push_str(identifier);
            }
            identifier.clear();
        }
    };
    for character in goal.chars() {
        if character.is_alphanumeric() || matches!(character, '_' | '\'' | '✝') {
            identifier.push(character);
        } else {
            flush(&mut output, &mut identifier);
            output.push(character);
        }
    }
    flush(&mut output, &mut identifier);
    output
}

fn goal_refinement_query(goal_state: &str, refinement: &str) -> String {
    let target = goal_state
        .lines()
        .find_map(|line| line.trim().strip_prefix('⊢'))
        .map(str::trim)
        .unwrap_or(goal_state);
    let head = target
        .split(|character: char| character.is_whitespace() || character == '(')
        .find(|part| !part.is_empty());
    if declaration_name_query(refinement)
        && !refinement.contains('.')
        && let Some(head) = head
        && declaration_name_query(head)
    {
        format!("{head}.{refinement}")
    } else {
        format!("{target} {refinement}")
    }
}

fn edit_distance(left: &str, right: &str) -> usize {
    let right = right.chars().collect::<Vec<_>>();
    let mut previous = (0..=right.len()).collect::<Vec<_>>();
    for (left_index, left_character) in left.chars().enumerate() {
        let mut current = vec![left_index + 1];
        for (right_index, right_character) in right.iter().enumerate() {
            current.push(
                (previous[right_index + 1] + 1)
                    .min(current[right_index] + 1)
                    .min(previous[right_index] + usize::from(left_character != *right_character)),
            );
        }
        previous = current;
    }
    previous[right.len()]
}

fn search_index_writer_lock(repo: &Repo) -> Result<fs::File> {
    let path = repo.state_dir.join("search-index.lock");
    let file = fs::OpenOptions::new()
        .create(true)
        .truncate(false)
        .read(true)
        .write(true)
        .open(&path)
        .with_context(|| format!("cannot open {}", path.display()))?;
    let result = unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX) };
    if result != 0 {
        bail!(
            "cannot lock {}: {}",
            path.display(),
            std::io::Error::last_os_error()
        );
    }
    Ok(file)
}

fn project_source_hits(
    workspace: &Workspace,
    query: &str,
    query_tokens: &[String],
    scan_all: bool,
) -> Vec<RankedHit> {
    let paths = if scan_all {
        project_lean_files(&workspace.path)
    } else {
        let Ok(paths) = dirty_lean_files(&workspace.path) else {
            return Vec::new();
        };
        paths
    };
    let mut ranked = Vec::new();
    // Small projects should be searchable immediately while their persistent
    // index is still warming. Keep a generous bound so ordinary projects are
    // not silently truncated, while still bounding cold-start filesystem work.
    for path in paths.into_iter().take(256) {
        let absolute = workspace.path.join(&path);
        let Ok(source) = fs::read_to_string(&absolute) else {
            continue;
        };
        let module = project_module_name(&workspace.path, &path);
        for entry in parse_source(&source, &module) {
            let name = entry.name.to_lowercase();
            let searchable = format!("{} {} {}", name, entry.signature, entry.body).to_lowercase();
            let matched_tokens = query_tokens
                .iter()
                .filter(|token| text_matches_token(&searchable, token))
                .collect::<Vec<_>>();
            if matched_tokens.is_empty() {
                continue;
            }
            let relevance = matched_tokens
                .iter()
                .map(|token| token.len().min(20))
                .sum::<usize>();
            let base = name.rsplit('.').next().unwrap_or(&name);
            let exact_name = query_tokens
                .iter()
                .any(|token| token == base || token == &name);
            let named = query_tokens
                .iter()
                .filter(|token| hit_name_matches(&name, token))
                .count();
            let (source, line) = detailed_source_excerpt(
                &entry.body,
                query,
                query_tokens,
                entry.line,
                &entry.kind,
                &entry.name,
            );
            let is_file_like = matches!(entry.kind.as_str(), "file" | "imports");
            let import_query = query_tokens
                .iter()
                .any(|token| matches!(token.as_str(), "import" | "imports"));
            ranked.push(RankedHit {
                hit: SearchHit {
                    name: entry.name,
                    kind: entry.kind,
                    signature: nonempty(entry.signature),
                    module: module.clone(),
                    path: path.to_string_lossy().into_owned(),
                    line,
                    doc: nonempty(entry.docs),
                    source,
                    usages: Vec::new(),
                    applicable: false,
                    required_import: None,
                },
                score: 320.0
                    + relevance as f64 * 4.0
                    + named as f64 * 45.0
                    + if exact_name { 140.0 } else { 0.0 }
                    - if is_file_like && !import_query {
                        300.0
                    } else if is_file_like {
                        60.0
                    } else {
                        0.0
                    },
            });
        }
    }
    ranked
}

const LOOGLE_FILES: &[(&str, &str)] = &[
    (
        "Loogle/BaseIOThunk.lean",
        include_str!("../lean/loogle/Loogle/BaseIOThunk.lean"),
    ),
    (
        "Loogle/BlackListed.lean",
        include_str!("../lean/loogle/Loogle/BlackListed.lean"),
    ),
    (
        "Loogle/Cache.lean",
        include_str!("../lean/loogle/Loogle/Cache.lean"),
    ),
    (
        "Loogle/NameRel.lean",
        include_str!("../lean/loogle/Loogle/NameRel.lean"),
    ),
    (
        "Loogle/TreeMap.lean",
        include_str!("../lean/loogle/Loogle/TreeMap.lean"),
    ),
    (
        "Loogle/Trie.lean",
        include_str!("../lean/loogle/Loogle/Trie.lean"),
    ),
    (
        "Loogle/Find.lean",
        include_str!("../lean/loogle/Loogle/Find.lean"),
    ),
    (
        "MathmuxLoogle.lean",
        include_str!("../lean/loogle/MathmuxLoogle.lean"),
    ),
];

impl LoogleWorker {
    fn start(repo: &Repo, workspace: &Path) -> Result<Self> {
        let root = prepare_loogle(repo, workspace)?;
        let lean_path = loogle_lean_path(repo, workspace, &root)?;
        let runner = root.join("MathmuxLoogle.lean");
        let index = root.join(format!("{}.index", mathlib_artifact_id(workspace)));
        let mut command = lake_command(repo, workspace);
        command
            .args(["env", "lean"])
            .arg("-R")
            .arg(&root)
            .arg("--run")
            .arg(&runner)
            .arg("Mathlib")
            .arg(index)
            .env("LEAN_PATH", lean_path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::from(
                fs::OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open(&repo.log_path)?,
            ));
        command.process_group(0);
        let mut child = command.spawn().context("cannot start Loogle worker")?;
        let stdin = child.stdin.take().context("Loogle worker has no stdin")?;
        let stdout = child.stdout.take().context("Loogle worker has no stdout")?;
        let mut stdout = BufReader::new(stdout);
        let ready = read_line_timeout(&mut stdout, std::time::Duration::from_secs(300));
        let ready = match ready {
            Ok(line) if line.contains("Mathmux Loogle is ready.") => line,
            Ok(line) => {
                kill_child_group(&mut child);
                bail!("unexpected Loogle startup response: {}", clean_line(&line));
            }
            Err(error) => {
                kill_child_group(&mut child);
                return Err(error).context("Loogle startup failed");
            }
        };
        drop(ready);
        Ok(Self {
            child,
            stdin,
            stdout,
            last_used: Instant::now(),
        })
    }

    fn query(&mut self, query: &str) -> Result<Vec<LoogleHit>> {
        self.last_used = Instant::now();
        let query = query.lines().collect::<Vec<_>>().join(" ");
        let mut value = self.query_value(&query)?;
        if value.get("error").is_some()
            && let Some(suggestion) = value
                .get("suggestions")
                .and_then(Value::as_array)
                .and_then(|suggestions| suggestions.first())
                .and_then(Value::as_str)
            && suggestion != query
        {
            value = self.query_value(suggestion)?;
        }
        if value.get("error").is_some() {
            return Ok(Vec::new());
        }
        Ok(value
            .get("hits")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .filter_map(|hit| {
                Some(LoogleHit {
                    name: hit.get("name")?.as_str()?.to_owned(),
                    signature: hit
                        .get("type")
                        .and_then(Value::as_str)
                        .unwrap_or_default()
                        .to_owned(),
                    module: hit
                        .get("module")
                        .and_then(Value::as_str)
                        .unwrap_or_default()
                        .to_owned(),
                    doc: hit.get("doc").and_then(Value::as_str).map(str::to_owned),
                })
            })
            .collect())
    }

    fn query_value(&mut self, query: &str) -> Result<Value> {
        self.stdin.write_all(query.as_bytes())?;
        self.stdin.write_all(b"\n")?;
        self.stdin.flush()?;
        let line = read_line_timeout(&mut self.stdout, std::time::Duration::from_secs(30))?;
        serde_json::from_str(&line)
            .with_context(|| format!("invalid Loogle response: {}", clean_line(&line)))
    }

    fn alive(&mut self) -> bool {
        matches!(self.child.try_wait(), Ok(None))
    }

    fn rss_kib(&self) -> Option<u64> {
        fs::read_to_string(format!("/proc/{}/status", self.child.id()))
            .ok()?
            .lines()
            .find_map(|line| line.strip_prefix("VmRSS:"))?
            .split_whitespace()
            .next()?
            .parse()
            .ok()
    }
}

impl Drop for LoogleWorker {
    fn drop(&mut self) {
        kill_child_group(&mut self.child);
    }
}

fn prepare_loogle(repo: &Repo, workspace: &Path) -> Result<PathBuf> {
    let toolchain = fs::read_to_string(workspace.join("lean-toolchain")).unwrap_or_default();
    let mut material = toolchain.into_bytes();
    for (_, source) in LOOGLE_FILES {
        material.extend_from_slice(source.as_bytes());
    }
    let fingerprint = hash_bytes(&material);
    let root = repo.state_dir.join("loogle").join(&fingerprint[..16]);
    let marker = root.join("built");
    if fs::read_to_string(&marker).ok().as_deref() == Some(fingerprint.as_str()) {
        return Ok(root);
    }
    for (relative, source) in LOOGLE_FILES {
        let path = root.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(path, source)?;
    }
    let order = [
        "Loogle/BaseIOThunk.lean",
        "Loogle/BlackListed.lean",
        "Loogle/Cache.lean",
        "Loogle/NameRel.lean",
        "Loogle/TreeMap.lean",
        "Loogle/Trie.lean",
        "Loogle/Find.lean",
        "MathmuxLoogle.lean",
    ];
    let lean_path = loogle_lean_path(repo, workspace, &root)?;
    for relative in order {
        let source = root.join(relative);
        let output = source.with_extension("olean");
        let result = std::process::Command::new("timeout")
            .args(["--signal=KILL", "180s"])
            .arg(lake_executable())
            .args(["env", "lean"])
            .arg("-R")
            .arg(&root)
            .arg("-o")
            .arg(&output)
            .arg(&source)
            .current_dir(workspace)
            .env("LAKE_ARTIFACT_CACHE", "true")
            .env("LAKE_CACHE_DIR", &repo.cache_dir)
            .env("LEAN_PATH", &lean_path)
            .stdin(Stdio::null())
            .output()
            .with_context(|| format!("cannot compile bundled Loogle module {relative}"))?;
        if !result.status.success() {
            let detail = if result.stderr.is_empty() {
                String::from_utf8_lossy(&result.stdout)
            } else {
                String::from_utf8_lossy(&result.stderr)
            };
            bail!(
                "cannot compile bundled Loogle module {relative}: {}",
                detail.trim()
            );
        }
    }
    fs::write(marker, &fingerprint)?;
    Ok(root)
}

fn loogle_lean_path(repo: &Repo, workspace: &Path, root: &Path) -> Result<String> {
    let output = lake_command(repo, workspace)
        .args(["env", "printenv", "LEAN_PATH"])
        .output()
        .context("cannot read the Lake search path")?;
    ensure!(
        output.status.success(),
        "Lake did not provide a Lean search path"
    );
    Ok(format!(
        "{}:{}",
        root.display(),
        String::from_utf8_lossy(&output.stdout).trim()
    ))
}

fn mathlib_artifact_id(workspace: &Path) -> String {
    let artifact = workspace.join(".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean");
    let material = fs::metadata(&artifact)
        .map(|metadata| format!("{}:{}", modified_ns(&metadata), metadata.len()))
        .unwrap_or_else(|_| "missing".into());
    hash_bytes(material.as_bytes())[..16].to_owned()
}

fn base_input_id(workspace: &Path) -> String {
    let mut material = Vec::new();
    for relative in ["lean-toolchain", "lake-manifest.json"] {
        let path = workspace.join(relative);
        material.extend_from_slice(relative.as_bytes());
        if let Ok(contents) = fs::read(path) {
            material.extend_from_slice(&contents);
        }
    }
    hash_bytes(&material)[..16].to_owned()
}

fn dependency_sources_missing(workspace: &Path) -> bool {
    workspace.join("lake-manifest.json").is_file() && !workspace.join(".lake/packages").is_dir()
}

fn read_line_timeout(
    reader: &mut BufReader<ChildStdout>,
    timeout: std::time::Duration,
) -> Result<String> {
    let mut descriptor = libc::pollfd {
        fd: reader.get_ref().as_raw_fd(),
        events: libc::POLLIN,
        revents: 0,
    };
    let milliseconds = timeout.as_millis().min(i32::MAX as u128) as i32;
    let ready = unsafe { libc::poll(&mut descriptor, 1, milliseconds) };
    if ready == 0 {
        bail!("Loogle response timed out");
    }
    if ready < 0 {
        return Err(std::io::Error::last_os_error().into());
    }
    let mut line = String::new();
    let bytes = reader.read_line(&mut line)?;
    ensure!(bytes > 0, "Loogle worker exited");
    Ok(line)
}

fn kill_child_group(child: &mut Child) {
    let pid = child.id() as i32;
    unsafe {
        libc::kill(-pid, libc::SIGTERM);
    }
    let _ = child.wait();
}

fn append_log(repo: &Repo, detail: &str) {
    if let Ok(mut log) = fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&repo.log_path)
    {
        let _ = writeln!(log, "{detail}");
    }
}

#[derive(Debug)]
struct SourceEntry {
    line: u64,
    name: String,
    kind: String,
    signature: String,
    docs: String,
    body: String,
}

fn parse_source(source: &str, module: &str) -> Vec<SourceEntry> {
    let declaration = declaration_regex();
    let matches = declaration.captures_iter(source).collect::<Vec<_>>();
    let lines = line_starts(source);
    let namespaces = namespaces_by_line(source);
    let contexts = ambient_contexts_by_line(source);
    let mut entries = Vec::new();
    for (index, capture) in matches.iter().enumerate() {
        let complete = capture.get(0).expect("declaration match");
        let kind = capture
            .name("kind")
            .map(|value| value.as_str())
            .unwrap_or("declaration");
        let raw_name = capture.name("name").map(|value| value.as_str());
        if raw_name.is_none() && kind != "instance" {
            continue;
        }
        let line = offset_line(&lines, complete.start());
        let end = matches
            .get(index + 1)
            .and_then(|next| next.get(0))
            .map(|next| next.start())
            .unwrap_or(source.len());
        let block = declaration_block(&source[complete.start()..end]);
        let header_end = declaration_header_end(block);
        let header = block[..header_end].trim();
        let name_end = raw_name
            .and_then(|raw_name| header.find(raw_name).map(|start| start + raw_name.len()))
            .or_else(|| header.find(kind).map(|start| start + kind.len()))
            .unwrap_or(header.len());
        let mut signature = header[name_end..]
            .trim()
            .trim_start_matches(':')
            .trim()
            .to_owned();
        if signature.is_empty()
            && matches!(kind, "abbrev" | "def")
            && let Some(value) = block[header_end..].strip_prefix(":=")
            && let Some(value) = value.lines().next()
        {
            signature = format!(":= {}", value.trim());
        }
        let namespace = namespaces
            .get(line.saturating_sub(1))
            .cloned()
            .unwrap_or_default();
        let name = match raw_name {
            Some(raw_name) if raw_name.contains('.') || namespace.is_empty() => raw_name.to_owned(),
            Some(raw_name) => format!("{}.{}", namespace.join("."), raw_name),
            None if namespace.is_empty() => format!("instance@{line}"),
            None => format!("{}.instance@{line}", namespace.join(".")),
        };
        if matches!(kind, "class" | "structure")
            && let Some(projection) = generated_parent_projection(&name, &signature)
        {
            signature.push_str(&format!("; generated parent projection: {projection}"));
        }
        let context = contexts
            .get(line.saturating_sub(1))
            .cloned()
            .unwrap_or_default();
        let body = if context.is_empty() {
            block.to_owned()
        } else {
            format!("-- ambient context\n{}\n\n{block}", context.join("\n"))
        };
        entries.push(SourceEntry {
            line: line as u64,
            name,
            kind: kind.to_owned(),
            signature: single_line(&signature),
            docs: preceding_doc(source, complete.start()).unwrap_or_default(),
            body: body.chars().take(16_000).collect(),
        });
    }
    let imports = source
        .lines()
        .enumerate()
        .filter(|(_, line)| {
            let line = line.trim_start();
            line.starts_with("import ") || line.starts_with("public import ")
        })
        .collect::<Vec<_>>();
    if let Some((first, _)) = imports.first() {
        entries.push(SourceEntry {
            line: (*first + 1) as u64,
            name: format!("{module}.imports"),
            kind: "imports".into(),
            signature: format!("{} imports", imports.len()),
            docs: String::new(),
            body: imports
                .into_iter()
                .map(|(_, line)| line.trim())
                .collect::<Vec<_>>()
                .join("\n"),
        });
    }
    entries.push(SourceEntry {
        line: 1,
        name: module.to_owned(),
        kind: "file".into(),
        signature: String::new(),
        docs: String::new(),
        body: source.chars().take(256_000).collect(),
    });
    entries
}

fn generated_parent_projection(name: &str, signature: &str) -> Option<String> {
    let parent = signature.split_once("extends ")?.1.trim_start();
    let parent = parent
        .split(|character: char| !(character.is_alphanumeric() || matches!(character, '_' | '.')))
        .next()?;
    if parent.is_empty() {
        return None;
    }
    Some(format!("{name}.to{}", parent.replace('.', "")))
}

fn declaration_regex() -> &'static Regex {
    static REGEX: OnceLock<Regex> = OnceLock::new();
    REGEX.get_or_init(|| {
        Regex::new(
            r"(?m)^[ \t]*(?:@\[[^\n]*\][ \t]*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)[ \t]+)*(?P<kind>theorem|lemma|def|abbrev|opaque|axiom|structure|class|inductive|instance)[ \t]+(?:\([ \t]*priority[ \t]*:=[^\n)]*\)[ \t]+)?(?P<name>[\p{L}_][\p{L}\p{N}\p{M}_'.]*)?",
        )
        .expect("valid declaration regex")
    })
}

fn declaration_header_end(block: &str) -> usize {
    let mut delimiters = Vec::new();
    for (index, character) in block.char_indices() {
        match character {
            '(' | '[' | '{' => delimiters.push(character),
            ')' | ']' | '}' => {
                delimiters.pop();
            }
            ':' if delimiters.is_empty() && block[index..].starts_with(":=") => return index,
            'w' if delimiters.is_empty()
                && block[index..].starts_with("where")
                && block[..index]
                    .chars()
                    .next_back()
                    .is_some_and(char::is_whitespace)
                && block[index + "where".len()..]
                    .chars()
                    .next()
                    .is_none_or(char::is_whitespace) =>
            {
                return index;
            }
            _ => {}
        }
    }
    block.find('\n').unwrap_or(block.len())
}

fn declaration_block(block: &str) -> &str {
    let end = block
        .match_indices('\n')
        .map(|(index, _)| index + 1)
        .find(|start| {
            let line = block[*start..].lines().next().unwrap_or_default();
            let trimmed = line.trim_start();
            line.len() == trimmed.len() && (trimmed == "end" || trimmed.starts_with("end "))
        })
        .unwrap_or(block.len());
    block[..end].trim()
}

fn namespaces_by_line(source: &str) -> Vec<Vec<String>> {
    let mut scopes: Vec<Option<Vec<String>>> = Vec::new();
    let mut result = Vec::new();
    for line in source.lines() {
        result.push(
            scopes
                .iter()
                .filter_map(Option::as_ref)
                .flatten()
                .cloned()
                .collect(),
        );
        let trimmed = line.trim();
        if let Some(name) = trimmed.strip_prefix("namespace ") {
            if let Some(name) = name.split_whitespace().next() {
                scopes.push(Some(name.split('.').map(str::to_owned).collect()));
            }
        } else if trimmed == "section" || trimmed.starts_with("section ") {
            scopes.push(None);
        } else if trimmed == "end" || trimmed.starts_with("end ") {
            scopes.pop();
        }
    }
    result
}

fn ambient_contexts_by_line(source: &str) -> Vec<Vec<String>> {
    let mut scopes = vec![Vec::<String>::new()];
    let mut result = Vec::new();
    for line in source.lines() {
        let flattened = scopes
            .iter()
            .flatten()
            .rev()
            .take(16)
            .cloned()
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect();
        result.push(flattened);
        let trimmed = line.trim();
        if trimmed.starts_with("namespace ") {
            scopes.push(Vec::new());
        } else if trimmed == "section" || trimmed.starts_with("section ") {
            scopes.push(vec![single_line(trimmed)]);
        } else if trimmed == "end" || trimmed.starts_with("end ") {
            if scopes.len() > 1 {
                scopes.pop();
            }
        } else if ["universe ", "variable ", "include ", "omit "]
            .iter()
            .any(|prefix| trimmed.starts_with(prefix))
            && !trimmed.ends_with(" in")
        {
            scopes
                .last_mut()
                .expect("root context scope")
                .push(single_line(trimmed));
        }
    }
    result
}

fn preceding_doc(source: &str, offset: usize) -> Option<String> {
    let prefix = &source[..offset];
    let end = prefix.rfind("-/")? + 2;
    let suffix = prefix[end..].trim();
    let separated_only_by_attributes = suffix.chars().all(|character| character == ']')
        || (suffix.starts_with("@[") && suffix.ends_with(']'));
    if !suffix.is_empty() && !separated_only_by_attributes {
        return None;
    }
    let start = prefix[..end].rfind("/--")?;
    Some(
        prefix[start + 3..end - 2]
            .lines()
            .map(|line| line.trim().trim_start_matches('*').trim())
            .collect::<Vec<_>>()
            .join(" "),
    )
}

fn line_starts(source: &str) -> Vec<usize> {
    std::iter::once(0)
        .chain(source.match_indices('\n').map(|(index, _)| index + 1))
        .collect()
}

fn offset_line(lines: &[usize], offset: usize) -> usize {
    lines.partition_point(|start| *start <= offset).max(1)
}

fn source_entry(path: &Path, kind: SourceKind) -> bool {
    let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
        return true;
    };
    match kind {
        SourceKind::Project => !matches!(name, ".git" | ".lake" | "target"),
        SourceKind::Dependency => !matches!(name, ".git" | ".lake" | "target"),
        SourceKind::Stdlib => !matches!(name, ".git" | "build"),
    }
}

fn display_path(path: &Path, workspace: &Path, root: &Path, kind: SourceKind) -> String {
    match kind {
        SourceKind::Project | SourceKind::Dependency => path
            .strip_prefix(workspace)
            .or_else(|_| path.strip_prefix(root))
            .unwrap_or(path)
            .to_string_lossy()
            .into_owned(),
        SourceKind::Stdlib => format!(
            "<stdlib>/{}",
            path.strip_prefix(root).unwrap_or(path).display()
        ),
    }
}

fn module_name(path: &Path, root: &Path, kind: SourceKind) -> String {
    let relative = path.strip_prefix(root).unwrap_or(path);
    let relative = if matches!(kind, SourceKind::Dependency) {
        let components = relative.components().collect::<Vec<_>>();
        components
            .iter()
            .position(|component| {
                matches!(
                    component.as_os_str().to_str(),
                    Some("Mathlib" | "Batteries" | "Cli" | "Qq" | "Plausible")
                )
            })
            .map(|index| components[index..].iter().collect::<PathBuf>())
            .unwrap_or_else(|| relative.to_path_buf())
    } else {
        relative.to_path_buf()
    };
    let mut module = relative;
    module.set_extension("");
    module
        .components()
        .filter_map(|component| component.as_os_str().to_str())
        .collect::<Vec<_>>()
        .join(".")
}

fn shared_owner(label: &str, root: &Path) -> String {
    format!("{label}:{}", hash_bytes(root.to_string_lossy().as_bytes()))
}

fn package_scopes(workspace: &Path) -> HashSet<String> {
    let Ok(packages) = fs::canonicalize(workspace.join(".lake/packages")) else {
        return HashSet::new();
    };
    [
        shared_owner("packages", &packages),
        shared_owner("artifact-packages", &packages),
    ]
    .into_iter()
    .collect()
}

fn lean_source_root(repo: &Repo, root: &Path) -> Option<PathBuf> {
    let output = lake_command(repo, root)
        .args(["env", "lean", "--print-prefix"])
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let prefix = PathBuf::from(String::from_utf8_lossy(&output.stdout).trim());
    [prefix.join("src/lean"), prefix.join("src/lean4")]
        .into_iter()
        .find(|path| path.is_dir())
}

fn modified_ns(metadata: &fs::Metadata) -> i64 {
    metadata
        .modified()
        .ok()
        .and_then(|time| time.duration_since(std::time::UNIX_EPOCH).ok())
        .map(|duration| duration.as_nanos().min(i64::MAX as u128) as i64)
        .unwrap_or(0)
}

fn delete_search_origin(connection: &Connection, owner: &str, origin: &str) -> Result<()> {
    connection.execute(
        "DELETE FROM search_fts WHERE rowid IN (
            SELECT rowid FROM search_origins WHERE owner = ?1 AND origin = ?2
         )",
        params![owner, origin],
    )?;
    connection.execute(
        "DELETE FROM search_origins WHERE owner = ?1 AND origin = ?2",
        params![owner, origin],
    )?;
    Ok(())
}

fn record_file(
    transaction: &rusqlite::Transaction<'_>,
    owner: &str,
    path: &Path,
    kind: &str,
) -> Result<()> {
    let metadata = fs::metadata(path)?;
    transaction.execute(
        "INSERT INTO search_files(owner, path, kind, modified_ns, size)
         VALUES (?1, ?2, ?3, ?4, ?5)
         ON CONFLICT(owner, path, kind) DO UPDATE SET
            modified_ns = excluded.modified_ns, size = excluded.size",
        params![
            owner,
            path.to_string_lossy(),
            kind,
            modified_ns(&metadata),
            metadata.len() as i64,
        ],
    )?;
    Ok(())
}

fn reference_name(encoded: &str) -> Option<String> {
    serde_json::from_str::<Value>(encoded)
        .ok()?
        .get("c")?
        .get("n")?
        .as_str()
        .map(str::to_owned)
}

fn reference_display_path(module: &str, workspace: &Workspace) -> String {
    let relative = PathBuf::from(format!("{}.lean", module.replace('.', "/")));
    if workspace.path.join(&relative).is_file() {
        relative.to_string_lossy().into_owned()
    } else {
        format!("<dependency>/{}", relative.display())
    }
}

fn fts_query(query: &str) -> String {
    meaningful_query_tokens(query)
        .into_iter()
        .filter(|token| token != "_")
        .map(|token| format!("\"{}\"*", token.replace('"', "\"\"")))
        .collect::<Vec<_>>()
        .join(" OR ")
}

fn query_tokens(query: &str) -> Vec<String> {
    query
        .split(|character: char| {
            !character.is_alphanumeric() && character != '_' && character != '.'
        })
        .map(|token| token.trim_matches('.').to_lowercase())
        .filter(|token| !token.is_empty())
        .collect()
}

fn declaration_name_query(query: &str) -> bool {
    let query = query.trim();
    !query.is_empty()
        && !query.starts_with('.')
        && !query.ends_with('.')
        && query
            .chars()
            .all(|character| character.is_alphanumeric() || matches!(character, '_' | '.' | '\''))
}

fn explicit_declaration_name(query: &str) -> Option<&str> {
    let mut terms = query.split_whitespace();
    let kind = terms.next()?;
    if !matches!(kind.to_ascii_lowercase().as_str(), "def" | "lemma" | "theorem") {
        return None;
    }
    let name = terms.next()?;
    if !declaration_name_query(name)
        || !terms.all(|term| {
            matches!(
                term.to_ascii_lowercase().as_str(),
                "body" | "implementation" | "proof" | "source"
            )
        })
    {
        return None;
    }
    Some(name)
}

fn declaration_glob_query(query: &str) -> bool {
    query.contains('*')
        && query.chars().filter(|character| character.is_alphanumeric()).count() >= 2
        && query.chars().all(|character| {
            character.is_alphanumeric() || matches!(character, '_' | '.' | '\'' | '*')
        })
}

fn declaration_glob_matches(name: &str, query: &str) -> bool {
    let characters = query.chars().collect::<Vec<_>>();
    let pattern = characters
        .iter()
        .enumerate()
        .map(|(index, character)| match character {
            '*' => ".*".to_owned(),
            '.' if index.checked_sub(1).is_some_and(|prior| characters[prior] == '*')
                || characters.get(index + 1) == Some(&'*') =>
            {
                "[._]?".to_owned()
            }
            '.' => "[._]".to_owned(),
            character => regex::escape(&character.to_string()),
        })
        .collect::<String>();
    let prefix = if query.starts_with('*') {
        ""
    } else {
        r"(?:^|\.)"
    };
    Regex::new(&format!(r"(?i){prefix}{pattern}$"))
        .is_ok_and(|pattern| pattern.is_match(name))
}

fn qualified_name_matches(name: &str, query: &str) -> bool {
    let name = name.to_lowercase();
    let query = query.trim().to_lowercase();
    name == query
        || name
            .strip_suffix(&query)
            .is_some_and(|prefix| prefix.ends_with('.'))
}

fn unique_qualified_hit_name<'a>(
    hits: impl Iterator<Item = &'a SearchHit>,
    query: &str,
) -> Option<String> {
    let names = hits
        .filter(|hit| qualified_name_matches(&hit.name, query))
        .map(|hit| hit.name.to_lowercase())
        .collect::<HashSet<_>>();
    if names.len() == 1 {
        names.into_iter().next()
    } else {
        None
    }
}

fn merge_exact_candidates(mut candidates: Vec<RankedHit>) -> RankedHit {
    candidates.sort_by(|left, right| {
        right
            .score
            .partial_cmp(&left.score)
            .unwrap_or(Ordering::Equal)
            .then_with(|| left.hit.name.cmp(&right.hit.name))
    });
    let mut resolved = candidates.remove(0);
    for mut candidate in candidates {
        merge_duplicate_hit(&mut resolved.hit, &mut candidate.hit);
    }
    resolved
}

fn specific_query_tokens(query: &str) -> Vec<String> {
    query
        .split(|character: char| {
            !character.is_alphanumeric() && character != '_' && character != '.'
        })
        .map(|token| token.trim_matches('.'))
        .filter(|token| token.len() >= 8)
        .filter(|token| token.contains(['.', '_']) || token.chars().skip(1).any(char::is_uppercase))
        .map(str::to_lowercase)
        .collect()
}

fn source_specific_query_tokens(query: &str) -> Vec<String> {
    query
        .split(|character: char| {
            !character.is_alphanumeric() && character != '_' && character != '.'
        })
        .map(|token| token.trim_matches('.'))
        .filter(|token| token.len() >= 8)
        .filter(|token| {
            token.contains(['.', '_'])
                || (token.chars().next().is_some_and(char::is_lowercase)
                    && token.chars().skip(1).any(char::is_uppercase))
        })
        .map(str::to_lowercase)
        .collect()
}

fn meaningful_query_tokens(query: &str) -> Vec<String> {
    let mut tokens = query_tokens(query);
    let generic = [
        "class",
        "constructor",
        "constructors",
        "def",
        "instance",
        "lemma",
        "structure",
        "theorem",
    ];
    if tokens.len() > 1
        && tokens
            .iter()
            .any(|token| !generic.contains(&token.as_str()))
    {
        tokens.retain(|token| !generic.contains(&token.as_str()));
    }
    if tokens.len() > 1 {
        tokens.retain(|token| token.chars().count() >= 2);
        tokens.retain(|token| {
            !matches!(
                token.as_str(),
                "all" | "and" | "for" | "from" | "in" | "of" | "on" | "or" | "the" | "to" | "with"
            )
        });
    }
    if query_requests_proof_body(query) {
        tokens.retain(|token| {
            !matches!(
                token.as_str(),
                "body" | "implementation" | "proof" | "source"
            )
        });
    }
    let aliases = tokens
        .iter()
        .filter_map(|token| match token.as_str() {
            "addition" => Some("add"),
            "continuity" => Some("continuous"),
            "multiplication" => Some("mul"),
            "projection" => Some("proj"),
            "scaling" => Some("smul"),
            _ => None,
        })
        .map(str::to_owned)
        .collect::<Vec<_>>();
    tokens.extend(aliases);
    let identifier_parts = query
        .split(|character: char| {
            !character.is_alphanumeric() && character != '_' && character != '.'
        })
        // A guessed qualified declaration often gets the namespace right but the
        // leaf wrong. Keep the qualified token for exact lookup, and search the
        // leaf's Lean-style components for nearby members of that namespace.
        .flat_map(|token| identifier_query_parts(token.rsplit('.').next().unwrap_or(token)))
        .filter(|part| {
            part.chars().count() >= 3
                && !matches!(
                    part.as_str(),
                    "all" | "and" | "for" | "from" | "the" | "with"
                )
        })
        .collect::<Vec<_>>();
    tokens.extend(identifier_parts);
    let mut seen = HashSet::new();
    tokens.retain(|token| seen.insert(token.clone()));
    tokens
}

fn identifier_query_parts(token: &str) -> Vec<String> {
    let mut parts = Vec::new();
    for segment in token.split(['.', '_']) {
        let mut start = 0;
        let characters = segment.char_indices().collect::<Vec<_>>();
        for index in 1..characters.len() {
            let (_, previous) = characters[index - 1];
            let (offset, current) = characters[index];
            let next_is_lower = characters
                .get(index + 1)
                .is_some_and(|(_, next)| next.is_lowercase());
            if current.is_uppercase()
                && (previous.is_lowercase() || previous.is_numeric() || next_is_lower)
            {
                parts.push(segment[start..offset].to_lowercase());
                start = offset;
            }
        }
        if start > 0 || segment != token {
            parts.push(segment[start..].to_lowercase());
        }
    }
    parts
}

fn qualified_member_score(query: &str, name: &str) -> f64 {
    if !declaration_name_query(query) {
        return 0.0;
    }
    let Some((query_owner, query_leaf_raw)) = query.trim().rsplit_once('.') else {
        return 0.0;
    };
    let Some((name_owner, name_leaf_raw)) = name.rsplit_once('.') else {
        return 0.0;
    };
    let query_owner = query_owner.to_lowercase();
    let name_owner = name_owner.to_lowercase();
    if name_owner != query_owner && !name_owner.ends_with(&format!(".{query_owner}")) {
        return 0.0;
    }

    let query_parts = identifier_query_parts(query_leaf_raw)
        .into_iter()
        .filter(|part| part.len() >= 3)
        .collect::<HashSet<_>>();
    let name_parts = identifier_query_parts(name_leaf_raw)
        .into_iter()
        .filter(|part| part.len() >= 3)
        .collect::<HashSet<_>>();
    let shared_parts = query_parts.intersection(&name_parts).count();
    let query_leaf = query_leaf_raw.to_lowercase();
    let name_leaf = name_leaf_raw.to_lowercase();
    let common_prefix = query_leaf
        .chars()
        .zip(name_leaf.chars())
        .take_while(|(left, right)| left == right)
        .count();
    let common_suffix = query_leaf
        .chars()
        .rev()
        .zip(name_leaf.chars().rev())
        .take_while(|(left, right)| left == right)
        .count();
    300.0 + shared_parts as f64 * 250.0
        + common_prefix.saturating_sub(3).min(10) as f64 * 4.0
        + common_suffix.saturating_sub(3).min(10) as f64 * 4.0
}

fn promote_query_coverage(ranked: &mut Vec<RankedHit>, tokens: &[String]) {
    if ranked.len() <= 1 || tokens.len() <= 1 {
        return;
    }
    let mut remaining = std::mem::take(ranked);
    let mut promoted: Vec<RankedHit> = Vec::new();
    let qualified = tokens.iter().filter(|token| token.contains('.')).count();
    if qualified >= 2 {
        for token in tokens.iter().filter(|token| token.contains('.')) {
            if let Some(position) = remaining
                .iter()
                .position(|candidate| candidate.hit.name.eq_ignore_ascii_case(token))
            {
                promoted.push(remaining.remove(position));
            }
        }
    }
    if promoted.len() < SUMMARY_LIMIT && !remaining.is_empty() {
        promoted.push(remaining.remove(0));
    }
    for token in tokens.iter().filter(|token| token.len() >= 3) {
        if promoted
            .iter()
            .any(|candidate| hit_name_matches(&candidate.hit.name, token))
        {
            continue;
        }
        let eligible = |candidate: &RankedHit| {
            !matches!(candidate.hit.kind.as_str(), "file" | "imports")
                || matches!(token.as_str(), "import" | "imports")
        };
        if let Some(position) = remaining
            .iter()
            .enumerate()
            .filter(|(_, candidate)| {
                eligible(candidate) && hit_name_matches(&candidate.hit.name, token)
            })
            .max_by_key(|(_, candidate)| {
                candidate
                    .hit
                    .name
                    .split(['.', '_'])
                    .filter(|segment| tokens.iter().any(|facet| words_match(segment, facet)))
                    .count()
            })
            .map(|(position, _)| position)
        {
            promoted.push(remaining.remove(position));
        } else if token.len() >= 6
            && !promoted
                .iter()
                .any(|candidate| hit_matches_token(&candidate.hit, token))
            && let Some(position) = remaining.iter().position(|candidate| {
                eligible(candidate) && hit_matches_token(&candidate.hit, token)
            })
        {
            promoted.push(remaining.remove(position));
        }
        if promoted.len() == SUMMARY_LIMIT {
            break;
        }
    }
    promoted.extend(remaining);
    *ranked = promoted;
}

fn hit_name_matches(name: &str, token: &str) -> bool {
    if name.eq_ignore_ascii_case(token) {
        return true;
    }
    let leaf = token.rsplit('.').next().unwrap_or(token);
    name.split(['.', '_'])
        .any(|segment| words_match(segment, leaf))
}

fn hit_matches_token(hit: &SearchHit, token: &str) -> bool {
    hit_name_matches(&hit.name, token)
        || hit
            .source
            .as_deref()
            .is_some_and(|source| text_matches_token(&source.to_lowercase(), token))
}

fn text_matches_token(text: &str, token: &str) -> bool {
    text.contains(token)
        || token
            .strip_suffix('s')
            .filter(|singular| singular.len() >= 4)
            .is_some_and(|singular| text.contains(singular))
}

fn words_match(left: &str, right: &str) -> bool {
    left.eq_ignore_ascii_case(right)
        || right
            .strip_suffix('s')
            .filter(|singular| singular.len() >= 4)
            .is_some_and(|singular| left.eq_ignore_ascii_case(singular))
        || left
            .strip_suffix('s')
            .filter(|singular| singular.len() >= 4)
            .is_some_and(|singular| singular.eq_ignore_ascii_case(right))
}

fn declaration_leaf_matches(name: &str, query: &str) -> bool {
    let leaf = name.rsplit('.').next().unwrap_or(name);
    query_tokens(query).iter().any(|token| {
        let token = token.rsplit('.').next().unwrap_or(token);
        words_match(leaf, token)
    })
}

fn lexical_score(query: &str, tokens: &[String], row: &IndexedRow) -> f64 {
    let exact_case_name = row.name == query;
    let exact_case_leaf = row.name.rsplit('.').next() == Some(query);
    let query = query.to_lowercase();
    let name = row.name.to_lowercase();
    let base = name.rsplit('.').next().unwrap_or(&name);
    let body = format!(
        "{} {} {} {}",
        row.signature.to_lowercase(),
        row.docs.to_lowercase(),
        row.body.to_lowercase(),
        row.path.to_lowercase()
    );
    let mut score = if name == query {
        600.0
    } else if base == query {
        105.0
    } else if name.ends_with(&format!(".{query}")) {
        95.0
    } else if name.starts_with(&query) || base.starts_with(&query) {
        75.0
    } else if name.contains(&query) {
        55.0
    } else {
        0.0
    };
    if row.kind != "file"
        && tokens.iter().any(|token| {
            token == &name || (token.len() >= 12 && !token.contains('.') && token.as_str() == base)
        })
    {
        score += 100.0;
    }
    if exact_case_name {
        score += 200.0;
    } else if exact_case_leaf {
        score += 160.0;
    }
    for token in tokens {
        if name.contains(token) {
            score += 12.0;
        } else if body.contains(token) {
            score += 3.0;
        }
    }
    let name_segments = name.split('.').collect::<HashSet<_>>();
    score += tokens
        .iter()
        .flat_map(|token| token.split('.'))
        .filter(|segment| name_segments.contains(segment))
        .count() as f64
        * 30.0;
    if row.kind != "file" {
        score += 20.0;
    } else {
        score -= 40.0;
    }
    score += qualified_member_score(&query, &row.name);
    score
}

fn type_shaped(query: &str) -> bool {
    query_tokens(query).iter().any(|token| token == "_")
        || query.contains('→')
        || query.contains("->")
        || query.contains('⊢')
        || query.contains("∀")
        || query.contains("fun ")
}

fn conclusion_query(query: &str) -> bool {
    let query = query.trim_start();
    query.starts_with('⊢') || query.starts_with("|-")
}

fn apply_import_context(candidate: &mut RankedHit, context: &ImportContext) {
    if candidate.hit.module.is_empty() {
        return;
    }
    if context.accessible.contains(&candidate.hit.module) {
        candidate.score += 30.0;
        candidate.hit.required_import = None;
    } else if context.complete {
        candidate.score -= 10.0;
        candidate.hit.required_import = Some(candidate.hit.module.clone());
    }
}

fn merge_duplicate_hit(existing: &mut SearchHit, candidate: &mut SearchHit) {
    if existing.kind == "declaration" && !matches!(candidate.kind.as_str(), "declaration" | "file")
    {
        existing.kind = candidate.kind.clone();
    }
    if existing.signature.is_none() {
        existing.signature = candidate.signature.take();
    }
    if existing.doc.is_none() {
        existing.doc = candidate.doc.take();
    }
    if existing.source.is_none() {
        existing.source = candidate.source.take();
    }
    if existing.usages.is_empty() {
        existing.usages = std::mem::take(&mut candidate.usages);
    }
    existing.applicable |= candidate.applicable;
    if existing.required_import.is_none() {
        existing.required_import = candidate.required_import.take();
    }
}

fn exact_search_result(hits: Vec<SearchHit>, base_warming: bool) -> SearchResult {
    SearchResult {
        hits,
        inference: if type_search_enabled() {
            "hybrid".into()
        } else {
            "hybrid(type-off)".into()
        },
        note: base_warming.then(|| "source index warming".into()),
        ok: true,
    }
}

fn structural_type_score(pattern: &str, signature: &str) -> f64 {
    if signature.is_empty() {
        return 0.0;
    }
    let pattern_tokens = query_tokens(pattern)
        .into_iter()
        .filter(|token| token != "_")
        .collect::<Vec<_>>();
    let signature_lower = signature.to_lowercase();
    if !pattern_tokens
        .iter()
        .all(|token| signature_lower.contains(token))
    {
        return 0.0;
    }
    let explicit_conclusion = conclusion_query(pattern);
    let pattern_without_turnstile = pattern
        .trim_start()
        .strip_prefix('⊢')
        .or_else(|| pattern.trim_start().strip_prefix("|-"))
        .unwrap_or(pattern)
        .trim_start();
    let conclusion_head = pattern_without_turnstile
        .split(|character: char| character.is_whitespace() || character == '(')
        .find(|part| !part.is_empty());
    let conclusion_score = if explicit_conclusion
        && conclusion_head.is_some_and(|head| signature.contains(&format!(": {head}")))
    {
        80.0
    } else {
        0.0
    };
    let shape_score = ["∘", "→L", "≃L", "↔", "∈", "⊆"]
        .into_iter()
        .filter(|shape| pattern.contains(shape) && signature.contains(shape))
        .count() as f64
        * 50.0;
    let arrows = pattern.matches('→').count() + pattern.matches("->").count();
    let signature_arrows = signature.matches('→').count() + signature.matches("->").count();
    let arrow_score = if arrows == 0 {
        0.0
    } else if arrows == signature_arrows {
        24.0
    } else if arrows < signature_arrows {
        10.0
    } else {
        0.0
    };
    20.0
        + arrow_score
        + conclusion_score
        + shape_score
        + pattern_tokens.len() as f64 * 5.0
}

fn type_search_enabled() -> bool {
    let opted_out = std::env::var("MATHMUX_LOOGLE")
        .ok()
        .is_some_and(|value| matches!(value.to_ascii_lowercase().as_str(), "0" | "false" | "off"));
    let memory_limited = std::env::var("MATHMUX_SEARCH_MEMORY_MB")
        .ok()
        .and_then(|value| value.parse::<u64>().ok())
        .is_some_and(|limit| limit < 16_384);
    !opted_out && !memory_limited
}

fn nonempty(value: String) -> Option<String> {
    (!value.trim().is_empty()).then_some(value)
}

fn source_excerpt_with_limit(
    source: &str,
    query: &str,
    tokens: &[String],
    declaration_line: u64,
    file_hit: bool,
    line_limit: usize,
) -> (Option<String>, u64) {
    if source.trim().is_empty() {
        return (None, declaration_line);
    }
    let lines = source.lines().collect::<Vec<_>>();
    let query = query.to_lowercase();
    let matched = lines
        .iter()
        .position(|line| line.to_lowercase().contains(&query))
        .or_else(|| best_source_match(&lines, tokens))
        .unwrap_or(0);
    let start = matched.saturating_sub(2);
    let excerpt = lines[start..lines.len().min(start + line_limit)].join("\n");
    let line = if file_hit {
        matched as u64 + 1
    } else {
        declaration_line
    };
    (nonempty(excerpt), line)
}

fn best_source_match(lines: &[&str], tokens: &[String]) -> Option<usize> {
    const MATCH_CONTEXT_LINES: usize = 16;
    let lowered = lines
        .iter()
        .map(|line| line.to_lowercase())
        .collect::<Vec<_>>();
    let mut best = None;
    for (index, line) in lowered.iter().enumerate() {
        if !tokens.iter().any(|token| line.contains(token)) {
            continue;
        }
        let start = index.saturating_sub(2);
        let end = lowered.len().min(start + MATCH_CONTEXT_LINES);
        let score = tokens
            .iter()
            .filter(|token| lowered[start..end].iter().any(|line| line.contains(*token)))
            .count();
        if best.is_none_or(|(_, best_score)| score > best_score) {
            best = Some((index, score));
        }
    }
    best.map(|(index, _)| index)
}

fn detailed_source_excerpt(
    body: &str,
    query: &str,
    tokens: &[String],
    declaration_line: u64,
    kind: &str,
    name: &str,
) -> (Option<String>, u64) {
    if matches!(kind, "class" | "inductive" | "structure") {
        let declaration = body
            .split("\n\n/--")
            .next()
            .unwrap_or(body)
            .split("\n\n/-!")
            .next()
            .unwrap_or(body);
        let excerpt = declaration
            .lines()
            .take(DECLARATION_DETAIL_LINES)
            .collect::<Vec<_>>()
            .join("\n");
        return (nonempty(excerpt), declaration_line);
    }
    if kind == "imports" {
        let excerpt = body.lines().take(64).collect::<Vec<_>>().join("\n");
        return (nonempty(excerpt), declaration_line);
    }
    let name = name.to_lowercase();
    let leaf = name.rsplit('.').next().unwrap_or(&name);
    let focused_tokens = tokens
        .iter()
        .filter(|token| token.as_str() != name && token.as_str() != leaf)
        .cloned()
        .collect::<Vec<_>>();
    let body_lines = body.lines().collect::<Vec<_>>();
    let focused_tokens =
        if focused_tokens.is_empty() || best_source_match(&body_lines, &focused_tokens).is_none() {
            tokens
        } else {
            &focused_tokens
        };
    source_excerpt_with_limit(
        body,
        query,
        focused_tokens,
        declaration_line,
        kind == "file",
        DECLARATION_DETAIL_LINES,
    )
}

fn fallback_source_hits(
    workspace: &Path,
    query: &str,
    query_tokens: &[String],
) -> Result<Vec<RankedHit>> {
    let workspace = fs::canonicalize(workspace)?;
    let packages = fs::canonicalize(workspace.join(".lake/packages")).ok();
    let generic = [
        "class",
        "constructor",
        "constructors",
        "def",
        "instance",
        "lemma",
        "structure",
        "theorem",
    ];
    let symbolic_term = symbolic_source_term(query);
    let mut terms = symbolic_term.iter().cloned().collect::<Vec<_>>();
    if symbolic_term.is_none() {
        terms.extend(
            query_tokens
                .iter()
                .flat_map(|token| std::iter::once(token.as_str()).chain(token.split(['.', '_'])))
                .map(str::to_lowercase)
                .filter(|term| term.len() >= 3 && !generic.contains(&term.as_str())),
        );
    }
    let named_argument_terms = named_argument_terms(query);
    terms.extend(named_argument_terms.iter().cloned());
    let generated_suffixes = ["_symm_apply", "_apply"];
    for term in terms.clone() {
        for suffix in generated_suffixes {
            if let Some(stem) = term.strip_suffix(suffix)
                && stem.len() >= 3
            {
                terms.push(stem.to_owned());
            }
        }
    }
    for term in terms.clone() {
        let synonym = match term.as_str() {
            "addition" => Some("add"),
            "continuity" => Some("continuous"),
            "islinear" => Some("linear"),
            "positive" => Some("pos"),
            "projection" => Some("proj"),
            "scaling" => Some("smul"),
            "trivializationat" => Some("trivialization"),
            "weighted" => Some("weight"),
            _ => None,
        };
        if let Some(synonym) = synonym {
            terms.push(synonym.to_owned());
        }
    }
    terms.sort();
    terms.dedup();
    if terms.is_empty() {
        return Ok(Vec::new());
    }
    let mut strong_terms = query
        .split('|')
        .map(str::trim)
        .filter(|term| term.len() >= 3)
        .map(str::to_lowercase)
        .collect::<Vec<_>>();
    strong_terms.extend(
        query_tokens
            .iter()
            .filter_map(|token| token.rsplit_once('.').map(|(_, base)| base.to_lowercase())),
    );
    let mut declaration_terms = Vec::new();
    if symbolic_term.is_none()
        && query_tokens.len() <= 2
        && let Some(token) = query_tokens.last()
    {
        for name in token.split('.').filter(|name| name.len() >= 3) {
            for kind in [
                "abbrev",
                "class",
                "def",
                "instance",
                "lemma",
                "structure",
                "theorem",
            ] {
                declaration_terms.push(format!("{kind} {name}"));
            }
        }
    }
    let mut rare_terms = terms.clone();
    rare_terms.sort_by(|left, right| right.len().cmp(&left.len()).then_with(|| left.cmp(right)));
    strong_terms.extend(rare_terms.iter().take(2).cloned());
    strong_terms.sort();
    strong_terms.dedup();
    let declaration_paths = source_scan_paths(&workspace, packages.as_deref(), &declaration_terms)?;
    let strong_paths = source_scan_paths(&workspace, packages.as_deref(), &strong_terms)?;
    let named_argument_paths =
        source_scan_paths(&workspace, packages.as_deref(), &named_argument_terms)?;
    let mut balanced_paths = if symbolic_term.is_some() {
        strong_paths
            .iter()
            .cloned()
            .map(|path| (path, 1))
            .collect()
    } else {
        source_scan_path_counts(
            &workspace,
            packages.as_deref(),
            &rare_terms.into_iter().take(12).collect::<Vec<_>>(),
        )?
    };
    balanced_paths.sort_by(|(left_path, left_score), (right_path, right_score)| {
        right_score.cmp(left_score).then_with(|| {
            let left_dependency = packages
                .as_ref()
                .is_some_and(|packages| left_path.starts_with(packages));
            let right_dependency = packages
                .as_ref()
                .is_some_and(|packages| right_path.starts_with(packages));
            left_dependency
                .cmp(&right_dependency)
                .then_with(|| left_path.cmp(right_path))
        })
    });
    let balanced_paths = balanced_paths
        .into_iter()
        .map(|(path, _)| path)
        .collect::<Vec<_>>();
    let strong_set = strong_paths.iter().collect::<HashSet<_>>();
    let named_argument_set = named_argument_paths.iter().collect::<HashSet<_>>();
    let preferred_set = if named_argument_set.is_empty() {
        &strong_set
    } else {
        &named_argument_set
    };
    let direct_paths = direct_module_paths(&workspace, packages.as_deref(), query);
    let direct_path_set = direct_paths.iter().cloned().collect::<HashSet<_>>();
    let specific_paths = if symbolic_term.is_some() {
        Vec::new()
    } else {
        source_scan_paths(
            &workspace,
            packages.as_deref(),
            &source_specific_query_tokens(query),
        )?
    };
    let mut paths = direct_paths
        .into_iter()
        .chain(specific_paths)
        .chain(
            declaration_paths
                .iter()
                .filter(|path| preferred_set.contains(path))
                .cloned(),
        )
        .collect::<Vec<_>>();
    let mut seen_paths = paths.iter().cloned().collect::<HashSet<_>>();
    let remaining_paths = if terms == strong_terms {
        strong_paths.clone()
    } else {
        source_scan_paths(&workspace, packages.as_deref(), &terms)?
    };
    for candidates in [
        declaration_paths,
        balanced_paths,
        strong_paths,
        remaining_paths,
    ] {
        for path in candidates {
            if seen_paths.insert(path.clone()) {
                paths.push(path);
            }
        }
    }
    let mut ranked = Vec::new();
    let class_query = query
        .split('|')
        .map(str::trim)
        .any(|part| part.to_lowercase().starts_with("class "));
    let imports_query = query_tokens
        .iter()
        .any(|token| matches!(token.as_str(), "import" | "imports"));
    for path in paths.into_iter().take(96) {
        let path = if path.is_absolute() {
            path
        } else {
            workspace.join(path)
        };
        let source = fs::read_to_string(&path)?;
        let source_lower = source.to_lowercase();
        let file_coverage = terms
            .iter()
            .filter(|term| source_lower.contains(*term))
            .count();
        let (root, kind) = packages
            .as_ref()
            .filter(|packages| path.starts_with(packages))
            .map(|packages| (packages.as_path(), SourceKind::Dependency))
            .unwrap_or((workspace.as_path(), SourceKind::Project));
        let module = module_name(&path, root, kind);
        for entry in parse_source(&source, &module) {
            let searchable =
                format!("{} {} {}", entry.name, entry.signature, entry.body).to_lowercase();
            let score = terms
                .iter()
                .filter(|term| searchable.contains(*term))
                .count();
            if score == 0 {
                continue;
            }
            let (excerpt, matched_line) = detailed_source_excerpt(
                &entry.body,
                query,
                &terms,
                entry.line,
                &entry.kind,
                &entry.name,
            );
            let name_score = terms
                .iter()
                .filter(|term| entry.name.to_lowercase().contains(*term))
                .map(|term| if term.len() >= 12 { 3 } else { 1 })
                .sum::<usize>();
            let named_argument_score = named_argument_terms
                .iter()
                .filter(|term| entry.signature.to_lowercase().contains(*term))
                .count();
            let name = entry.name.to_lowercase();
            let symbolic_name_match = symbolic_term
                .as_ref()
                .is_some_and(|term| name.contains(term));
            let base = name.rsplit('.').next().unwrap_or(&name);
            let name_segments = name.split('.').collect::<HashSet<_>>();
            let segment_score = terms
                .iter()
                .filter(|term| name_segments.contains(term.as_str()))
                .count();
            let is_file = entry.kind == "file";
            let is_direct_path = direct_path_set.contains(&path);
            let exact_name = query_tokens.iter().any(|token| {
                (token.contains('.') && token == &name)
                    || (!is_file
                        && token.len() >= 4
                        && !token.contains('.')
                        && token.as_str() == base)
            });
            let qualified_leaf = query_tokens.iter().any(|token| {
                token
                    .rsplit_once('.')
                    .is_some_and(|(_, leaf)| name_segments.contains(leaf))
            });
            let is_class = entry.kind == "class";
            let is_owner = matches!(entry.kind.as_str(), "structure" | "class");
            let qualified_member_query = declaration_name_query(query) && query.contains('.');
            let qualified_owner_score = if qualified_member_query {
                0
            } else {
                query_tokens
                    .iter()
                    .enumerate()
                    .filter_map(|(index, token)| {
                        token.rsplit_once('.').map(|(owner, _)| (index, owner))
                    })
                    .filter(|(_, owner)| *owner == name || name.ends_with(&format!(".{owner}")))
                    .map(|(index, _)| if index == 0 { 2 } else { 1 })
                    .sum::<usize>()
            };
            let qualified_member_score = qualified_member_score(query, &entry.name);
            let member_owner_score = if is_owner && !qualified_member_query {
                query_tokens
                    .iter()
                    .filter(|token| {
                        token.len() >= 8
                            && !text_matches_token(&name, token)
                            && text_matches_token(&searchable, token)
                    })
                    .count()
            } else {
                0
            };
            let is_imports = entry.kind == "imports";
            ranked.push(RankedHit {
                hit: SearchHit {
                    name: entry.name,
                    kind: entry.kind,
                    signature: nonempty(entry.signature),
                    module: module.clone(),
                    path: display_path(&path, &workspace, root, kind),
                    line: matched_line,
                    doc: nonempty(entry.docs),
                    source: excerpt,
                    usages: Vec::new(),
                    applicable: false,
                    required_import: None,
                },
                score: 35.0
                    + score as f64 * 8.0
                    + name_score as f64 * 20.0
                    + named_argument_score as f64 * 200.0
                    + segment_score as f64 * 30.0
                    + if exact_name { 80.0 } else { 0.0 }
                    + if symbolic_name_match { 600.0 } else { 0.0 }
                    + if qualified_leaf { 60.0 } else { 0.0 }
                    + qualified_owner_score as f64 * 250.0
                    + qualified_member_score
                    + member_owner_score as f64 * 160.0
                    + if is_direct_path { 400.0 } else { 0.0 }
                    + if is_imports && imports_query {
                        200.0
                    } else {
                        0.0
                    }
                    + if is_class && class_query { 40.0 } else { 0.0 }
                    + if is_file {
                        -220.0
                    } else {
                        20.0 + file_coverage as f64 * 4.0
                    },
            });
        }
    }
    ranked.sort_by(|left, right| {
        right
            .score
            .partial_cmp(&left.score)
            .unwrap_or(Ordering::Equal)
    });
    promote_query_coverage(&mut ranked, query_tokens);
    ranked.truncate(RESULT_LIMIT);
    Ok(ranked)
}

fn symbolic_source_term(query: &str) -> Option<String> {
    let query = query.trim();
    (!query.is_empty()
        && !query.chars().any(char::is_whitespace)
        && (query.chars().count() > 1 || !query.is_ascii())
        && query.chars().any(|character| !character.is_alphanumeric()))
    .then(|| query.to_lowercase())
}

fn named_argument_terms(query: &str) -> Vec<String> {
    static REGEX: OnceLock<Regex> = OnceLock::new();
    let regex = REGEX.get_or_init(|| {
        Regex::new(r"\(([\p{L}_][\p{L}\p{N}\p{M}_']*)\s*:=").expect("valid named argument regex")
    });
    regex
        .captures_iter(query)
        .filter_map(|capture| capture.get(1))
        .map(|name| format!("({} :", name.as_str().to_lowercase()))
        .collect()
}

fn direct_module_paths(workspace: &Path, packages: Option<&Path>, query: &str) -> Vec<PathBuf> {
    let mut roots = vec![workspace.to_path_buf()];
    if let Some(packages) = packages
        && let Ok(entries) = fs::read_dir(packages)
    {
        roots.extend(entries.flatten().map(|entry| entry.path()));
    }
    let mut paths = Vec::new();
    let tokens = query
        .split(|character: char| {
            !character.is_alphanumeric() && character != '_' && character != '.'
        })
        .filter(|token| !token.is_empty())
        .collect::<Vec<_>>();
    for token in tokens.iter().filter(|token| token.contains('.')) {
        let relative = if token.ends_with(".lean") {
            PathBuf::from(token)
        } else {
            PathBuf::from(format!("{}.lean", token.replace('.', "/")))
        };
        for root in &roots {
            let candidate = root.join(&relative);
            if candidate.is_file()
                && let Ok(candidate) = fs::canonicalize(candidate)
                && !paths.contains(&candidate)
            {
                paths.push(candidate);
            }
        }
    }
    for path in project_lean_files(workspace) {
        let Some(stem) = path.file_stem().and_then(|stem| stem.to_str()) else {
            continue;
        };
        if tokens.iter().any(|token| stem.eq_ignore_ascii_case(token)) {
            let candidate = workspace.join(path);
            if let Ok(candidate) = fs::canonicalize(candidate)
                && !paths.contains(&candidate)
            {
                paths.push(candidate);
            }
        }
    }
    paths
}

fn source_scan_paths(
    workspace: &Path,
    packages: Option<&Path>,
    terms: &[String],
) -> Result<Vec<PathBuf>> {
    if terms.is_empty() {
        return Ok(Vec::new());
    }
    let mut command = std::process::Command::new("timeout");
    command.args([
        "--signal=KILL",
        "2s",
        "rg",
        "-l",
        "-i",
        "-F",
        "--glob",
        "*.lean",
    ]);
    for term in terms {
        command.args(["-e", term]);
    }
    command.arg(workspace);
    if let Some(packages) = packages {
        command.arg(packages);
    }
    let output = command.stdin(Stdio::null()).output()?;
    if !output.status.success() && !matches!(output.status.code(), Some(1 | 124 | 137)) {
        bail!(
            "local source scan failed: {}",
            clean_line(&String::from_utf8_lossy(&output.stderr))
        );
    }
    Ok(String::from_utf8_lossy(&output.stdout)
        .lines()
        .map(PathBuf::from)
        .collect())
}

fn source_scan_path_counts(
    workspace: &Path,
    packages: Option<&Path>,
    terms: &[String],
) -> Result<Vec<(PathBuf, usize)>> {
    if terms.is_empty() {
        return Ok(Vec::new());
    }
    let mut command = std::process::Command::new("timeout");
    command.args([
        "--signal=KILL",
        "2s",
        "rg",
        "-c",
        "-i",
        "-F",
        "--glob",
        "*.lean",
    ]);
    for term in terms {
        command.args(["-e", term]);
    }
    command.arg(workspace);
    if let Some(packages) = packages {
        command.arg(packages);
    }
    let output = command.stdin(Stdio::null()).output()?;
    if !output.status.success() && !matches!(output.status.code(), Some(1 | 124 | 137)) {
        bail!(
            "local source coverage scan failed: {}",
            clean_line(&String::from_utf8_lossy(&output.stderr))
        );
    }
    Ok(String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| {
            let (path, count) = line.rsplit_once(':')?;
            Some((PathBuf::from(path), count.parse().ok()?))
        })
        .collect())
}

fn render_summary(run: &SearchRun) -> String {
    let mut output = run.reference.clone();
    let proof_body_requested = query_requests_proof_body(&run.query);
    if run.hits.is_empty() {
        output.push_str(" no results");
    }
    for (index, hit) in run.hits.iter().take(SUMMARY_LIMIT).enumerate() {
        output.push('\n');
        output.push_str(&hit.name);
        if let Some(signature) = &hit.signature {
            output.push_str(" : ");
            output.push_str(&truncate_line(&single_line(signature), 240));
        }
        output.push_str(&format!("  {}:{}", hit.path, hit.line));
        if hit.applicable {
            output.push_str("  applicable");
        }
        if let Some(module) = &hit.required_import {
            output.push_str(&format!("\n  import {module}"));
        }
        let explicitly_named = !matches!(hit.kind.as_str(), "file" | "imports")
            && declaration_leaf_matches(&hit.name, &run.query);
        if (index == 0
            || (!proof_body_requested
                && (explicitly_named
                    || (index < 3
                        && matches!(
                            hit.kind.as_str(),
                            "class" | "inductive" | "structure"
                        )))))
            && let Some(source) = &hit.source
        {
            let source_lines = if index == 0 && proof_body_requested {
                DECLARATION_DETAIL_LINES
            } else {
                match hit.kind.as_str() {
                    "class" | "inductive" | "structure" => 16,
                    "imports" => 64,
                    "location" => LOCATION_PREVIEW_LINES,
                    "location-more" => LOCATION_MORE_LINES,
                    _ => SOURCE_PREVIEW_LINES,
                }
            };
            for line in source.lines().take(source_lines) {
                output.push_str(&format!("\n  | {}", truncate_line(line.trim(), 200)));
            }
        }
    }
    if run.hits.len() > SUMMARY_LIMIT {
        output.push_str(&format!(
            "\n+{} results; show {}",
            run.hits.len() - SUMMARY_LIMIT,
            run.reference
        ));
    }
    if let Some(note) = &run.note {
        output.push_str(&format!("\n{note}"));
    }
    output
}

struct GoalLocation {
    path: PathBuf,
    display_path: Option<String>,
    line: u64,
    tail: bool,
    more: bool,
    probe: bool,
}

fn parse_goal_location(root: &Path, cwd: &Path, query: &str) -> Result<Option<GoalLocation>> {
    let (query, more) = query
        .rsplit_once(char::is_whitespace)
        .filter(|(_, modifier)| modifier.eq_ignore_ascii_case("more"))
        .map_or((query, false), |(query, _)| (query.trim_end(), true));
    if let Some((path, suffix)) = query.rsplit_once(':')
        && suffix.eq_ignore_ascii_case("tail")
    {
        let Some((path, display_path, probe)) = resolve_goal_path(root, cwd, path)? else {
            return Ok(None);
        };
        let line = fs::read_to_string(&path)?.lines().count().max(1) as u64;
        return Ok(Some(GoalLocation {
            path,
            display_path,
            line,
            tail: true,
            more,
            probe,
        }));
    }
    let mut parts = query.rsplitn(3, ':');
    let Some(last) = parts.next() else {
        return Ok(None);
    };
    let Ok(last_number) = last.parse::<u64>() else {
        return Ok(None);
    };
    let Some(second) = parts.next() else {
        return Ok(None);
    };
    let (path, line) = if let Ok(line) = second.parse::<u64>() {
        let Some(path) = parts.next() else {
            return Ok(None);
        };
        (path, line)
    } else {
        (second, last_number)
    };
    let Some((path, display_path, probe)) = resolve_goal_path(root, cwd, path)? else {
        return Ok(None);
    };
    ensure!(line > 0, "goal line starts at 1");
    Ok(Some(GoalLocation {
        path,
        display_path,
        line,
        tail: false,
        more,
        probe,
    }))
}

fn resolve_goal_path(
    root: &Path,
    cwd: &Path,
    path: &str,
) -> Result<Option<(PathBuf, Option<String>, bool)>> {
    let display = path.strip_prefix("<dependency>/").unwrap_or(path);
    let requested = PathBuf::from(display);
    if requested
        .extension()
        .is_none_or(|extension| extension != "lean")
    {
        return Ok(None);
    }
    let direct = if requested.is_absolute() {
        requested.clone()
    } else {
        cwd.join(&requested)
    };
    if direct.is_file() {
        let direct = fs::canonicalize(direct)?;
        if direct.starts_with(root) {
            return Ok(Some((direct, None, true)));
        }
    }

    let packages = root.join(".lake/packages");
    let Ok(packages) = fs::canonicalize(packages) else {
        return Ok(None);
    };
    let mut candidates = Vec::new();
    let direct_package = packages.join(&requested);
    if direct_package.is_file() {
        candidates.push(fs::canonicalize(direct_package)?);
    }
    for package in fs::read_dir(&packages)?.flatten() {
        let candidate = package.path().join(&requested);
        if candidate.is_file() {
            candidates.push(fs::canonicalize(candidate)?);
        }
    }
    candidates.sort();
    candidates.dedup();
    candidates.retain(|candidate| candidate.starts_with(&packages));
    let [resolved] = candidates.as_slice() else {
        return Ok(None);
    };
    Ok(Some((
        resolved.clone(),
        Some(display.to_owned()),
        false,
    )))
}

fn source_location_result(
    workspace: &Workspace,
    location: &GoalLocation,
    source: &str,
    note: Option<&str>,
    ok: bool,
) -> SearchResult {
    let relative = location.display_path.clone().unwrap_or_else(|| {
        location
            .path
            .strip_prefix(&workspace.path)
            .unwrap_or(&location.path)
            .to_string_lossy()
            .into_owned()
    });
    SearchResult {
        hits: vec![SearchHit {
            name: "source".into(),
            kind: if location.more {
                "location-more"
            } else {
                "location"
            }
            .into(),
            signature: None,
            module: String::new(),
            path: relative,
            line: location.line,
            doc: None,
            source: nonempty(location_source_excerpt(
                source,
                location.line,
                if location.more {
                    LOCATION_MORE_LINES
                } else if location.tail {
                    SOURCE_PREVIEW_LINES
                } else {
                    LOCATION_PREVIEW_LINES
                },
            )),
            usages: Vec::new(),
            applicable: false,
            required_import: None,
        }],
        inference: if ok { "source" } else { "source-only" }.into(),
        note: note.map(Into::into),
        ok,
    }
}

fn location_source_excerpt(source: &str, requested_line: u64, line_limit: usize) -> String {
    let lines = source.lines().collect::<Vec<_>>();
    if lines.is_empty() {
        return String::new();
    }
    let target = requested_line
        .saturating_sub(1)
        .min(lines.len().saturating_sub(1) as u64) as usize;
    let start = target
        .saturating_sub(6)
        .min(lines.len().saturating_sub(line_limit));
    let end = lines.len().min(start + line_limit);
    lines[start..end]
        .iter()
        .enumerate()
        .map(|(offset, line)| format!("{:>5} | {line}", start + offset + 1))
        .collect::<Vec<_>>()
        .join("\n")
}

fn goal_probe(source: &str, requested_line: u64) -> Option<(usize, usize, bool, String)> {
    let lines = line_starts(source);
    let requested = requested_line.saturating_sub(1) as usize;
    for distance in 0..=2 {
        for line in [requested.saturating_sub(distance), requested + distance] {
            let start = *lines.get(line)?;
            let end = lines.get(line + 1).copied().unwrap_or(source.len());
            let text = &source[start..end];
            for placeholder in ["sorry", "admit"] {
                if let Some(local) = text.find(placeholder) {
                    let absolute = start + local;
                    let indent = text[..local]
                        .chars()
                        .take_while(|character| character.is_whitespace())
                        .collect();
                    let preceding = &source[..absolute];
                    let in_tactic = preceding
                        .lines()
                        .rev()
                        .find(|line| !line.trim().is_empty())
                        .is_some_and(|line| line.trim_end().ends_with("by"));
                    return Some((absolute, absolute + placeholder.len(), in_tactic, indent));
                }
            }
        }
    }
    None
}

fn goal_probe_replacement(in_tactic: bool, indent: &str, tactic: &str) -> String {
    if in_tactic {
        format!(
            "run_tac\n{indent}  let goal ← Lean.Elab.Tactic.getMainGoal\n{indent}  let state ← Lean.Meta.ppGoal goal\n{indent}  Lean.logInfo m!\"{GOAL_STATE_BEGIN}\\n{{state}}\\n{GOAL_STATE_END}\"\n{indent}{tactic}"
        )
    } else {
        format!(
            "by\n{indent}  run_tac\n{indent}    let goal ← Lean.Elab.Tactic.getMainGoal\n{indent}    let state ← Lean.Meta.ppGoal goal\n{indent}    Lean.logInfo m!\"{GOAL_STATE_BEGIN}\\n{{state}}\\n{GOAL_STATE_END}\"\n{indent}  {tactic}"
        )
    }
}

fn try_this_suggestions(output: &str) -> Vec<String> {
    let mut suggestions = Vec::new();
    let mut next_is_suggestion = false;
    for line in output.lines() {
        if let Some(suggestion) = line.split("Try this:").nth(1) {
            let suggestion = suggestion.trim();
            if suggestion.is_empty() {
                next_is_suggestion = true;
            } else {
                push_suggestion(&mut suggestions, suggestion);
            }
        } else if next_is_suggestion && !line.trim().is_empty() {
            push_suggestion(&mut suggestions, line.trim());
            next_is_suggestion = false;
        }
    }
    suggestions
}

fn traced_goal_state(output: &str) -> Option<String> {
    let lines = output.lines().collect::<Vec<_>>();
    let start = lines
        .iter()
        .position(|line| line.contains(GOAL_STATE_BEGIN))?
        + 1;
    let end = lines[start..]
        .iter()
        .position(|line| line.contains(GOAL_STATE_END))?
        + start;
    let state = lines[start..end]
        .iter()
        .map(|line| line.trim_end())
        .filter(|line| !line.trim().is_empty())
        .collect::<Vec<_>>();
    if state.is_empty() {
        return None;
    }
    let omitted = state.len().saturating_sub(SOURCE_PREVIEW_LINES);
    let mut rendered = state[state.len().saturating_sub(SOURCE_PREVIEW_LINES)..].join("\n");
    if omitted > 0 {
        rendered = format!("+{omitted} context lines omitted\n{rendered}");
    }
    Some(rendered)
}

fn local_method_candidates(goal_state: &str) -> Vec<String> {
    let Some(goal) = goal_state
        .lines()
        .find_map(|line| line.trim().strip_prefix('⊢'))
        .map(str::trim)
    else {
        return Vec::new();
    };
    let Some(goal_head) = goal
        .split(|character: char| character.is_whitespace() || character == '(')
        .find(|part| !part.is_empty())
    else {
        return Vec::new();
    };
    let hypotheses = goal_state
        .lines()
        .filter_map(|line| line.trim().split_once(':'))
        .filter_map(|(name, ty)| {
            let head = ty
                .trim()
                .split(|character: char| character.is_whitespace() || character == '(')
                .find(|part| !part.is_empty())?;
            (head == goal_head)
                .then(|| name.split_whitespace().last().map(str::to_owned))
                .flatten()
        })
        .take(6)
        .collect::<Vec<_>>();
    let mut candidates = Vec::new();
    for left in &hypotheses {
        for right in &hypotheses {
            if left == right {
                continue;
            }
            candidates.push(format!("exact {left}.comp {right}"));
            candidates.push(format!("exact {left}.trans {right}"));
            if candidates.len() >= 8 {
                return candidates;
            }
        }
    }
    candidates
}

fn push_suggestion(suggestions: &mut Vec<String>, suggestion: &str) {
    let suggestion = suggestion
        .strip_prefix("[apply] ")
        .or_else(|| suggestion.strip_prefix("[exact] "))
        .unwrap_or(suggestion);
    if !suggestions.iter().any(|seen| seen == suggestion) {
        suggestions.push(suggestion.to_owned());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_parser_qualifies_names_and_keeps_types() {
        let source = r#"namespace Demo
/-- Converts a hypothesis. -/
theorem useful (h : P) : Q := by
  sorry
def pairValue (value : α × β) : α × β := value
end Demo
"#;
        let entries = parse_source(source, "Demo");
        let theorem = entries
            .iter()
            .find(|entry| entry.kind == "theorem")
            .unwrap();
        assert_eq!(theorem.name, "Demo.useful");
        assert_eq!(theorem.signature, "(h : P) : Q");
        assert_eq!(theorem.docs, "Converts a hypothesis.");
        assert!(
            entries
                .iter()
                .any(|entry| entry.name == "Demo.pairValue" && entry.signature.contains('×'))
        );
        let named_argument = parse_source(
            "theorem configured (x : α) : f (R := 𝕜) x = x := by simp\n",
            "Demo",
        );
        assert_eq!(named_argument[0].signature, "(x : α) : f (R := 𝕜) x = x");
        let inferred_abbrev =
            parse_source("abbrev ZeroFiber := EuclideanSpace ℂ (Fin 0)\n", "Demo");
        assert_eq!(inferred_abbrev[0].signature, ":= EuclideanSpace ℂ (Fin 0)");

        let sectioned = parse_source(
            "namespace Outer\nsection First\ndef before := 1\nend First\nsection Second\ndef after := 2\nend Second\nend Outer\n",
            "Outer",
        );
        assert!(sectioned.iter().any(|entry| entry.name == "Outer.before"));
        assert!(sectioned.iter().any(|entry| entry.name == "Outer.after"));

        let unicode = parse_source(
            "namespace LinearMap\ndef mkContinuous₂ (f : α) := f\nend LinearMap\n",
            "LinearMap",
        );
        assert!(
            unicode
                .iter()
                .any(|entry| entry.name == "LinearMap.mkContinuous₂")
        );

        let additive_doc = parse_source(
            "/-- Multiplicative support. -/\n@[to_additive /-- Additive support around zero. -/]\ntheorem mulSupportFact : True := trivial\n",
            "Demo",
        );
        assert_eq!(additive_doc[0].docs, "Additive support around zero.");

        let priority_instance = parse_source(
            "namespace VectorBundle\ninstance (priority := 100) trivialization_linear [VectorBundle R F E] : e.IsLinear R := inferInstance\nend VectorBundle\n",
            "VectorBundle",
        );
        assert!(priority_instance.iter().any(|entry| {
            entry.kind == "instance" && entry.name == "VectorBundle.trivialization_linear"
        }));

        let anonymous_instance = parse_source(
            "namespace ComplexVectorBundle\ninstance (V : ComplexVectorBundle B) : NormedAddCommGroup V.F := V.normedAddCommGroup\nend ComplexVectorBundle\n",
            "ComplexVectorBundle",
        );
        assert!(anonymous_instance.iter().any(|entry| {
            entry.kind == "instance"
                && entry.name.starts_with("ComplexVectorBundle.instance@")
                && entry.signature.contains("NormedAddCommGroup V.F")
        }));

        let structure = parse_source(
            "structure InnerProductSpace.Core extends PreInnerProductSpace.Core where\n  definite : True\n",
            "InnerProductSpace",
        );
        assert!(structure[0].signature.contains(
            "generated parent projection: InnerProductSpace.Core.toPreInnerProductSpaceCore"
        ));

        let contextual = parse_source(
            "namespace Demo\nuniverse u\nvariable {α : Type u} [Group α]\nsection Closed\nvariable [TopologicalSpace α]\nend Closed\nstructure Box where\n  value : α\nend Demo\n",
            "Demo",
        );
        let boxed = contextual
            .iter()
            .find(|entry| entry.name == "Demo.Box")
            .unwrap();
        assert!(boxed.body.contains("universe u"));
        assert!(boxed.body.contains("variable {α : Type u} [Group α]"));
        assert!(!boxed.body.contains("variable [TopologicalSpace α]"));

        let grouped = parse_source(
            "namespace Demo\nsection Adapter\nvariable {α : Type} [Group α]\ntheorem useful : True := by trivial\nend Adapter\nend Demo\n",
            "Demo",
        );
        let useful = grouped
            .iter()
            .find(|entry| entry.name == "Demo.useful")
            .unwrap();
        assert!(useful.body.contains("section Adapter"));
        assert!(!useful.body.contains("end Adapter"));
    }

    #[test]
    fn inference_reserves_positions_and_recognizes_type_patterns() {
        assert!(type_shaped("_ → Injective _"));
        assert!(!type_shaped("injective function"));
        assert!(!type_shaped("norm_inner_le_norm"));
        assert!(structural_type_score("_ → Injective _", "Bijective f → Injective f") > 0.0);
        assert!(
            structural_type_score(
                "⊢ Continuous (_ ∘ _)",
                "{f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f)",
            ) > structural_type_score(
                "⊢ Continuous (_ ∘ _)",
                "(e : LocalTrivialization F E) [e.IsLinear 𝕜]",
            )
        );
        assert!(conclusion_query("⊢ _ → Injective _"));
        assert!(!conclusion_query("_ → Injective _"));
        assert_eq!(fts_query("List.map"), "\"list.map\"*");
        assert!(declaration_name_query("Finsupp.sum_add_index"));
        assert!(declaration_name_query("Ring.inverse_eq_inv'"));
        assert!(declaration_name_query("transportAmbient"));
        assert!(!declaration_name_query("Finsupp.sum add"));
        assert_eq!(
            explicit_declaration_name("theorem Bundle.Trivialization.apply_mk_symm"),
            Some("Bundle.Trivialization.apply_mk_symm")
        );
        assert_eq!(
            explicit_declaration_name("def Demo.useful proof body"),
            Some("Demo.useful")
        );
        assert_eq!(explicit_declaration_name("theorem search terms"), None);
        assert_eq!(more_search_reference("q4246 MORE"), Some("q4246"));
        assert_eq!(
            more_search_reference("projectionRangeInclusionHom q4246 MORE"),
            Some("q4246")
        );
        assert_eq!(more_search_reference("q4246 comp"), None);
        assert_eq!(symbolic_source_term("*ᵥ"), Some("*ᵥ".to_owned()));
        assert_eq!(symbolic_source_term("≤"), Some("≤".to_owned()));
        assert_eq!(symbolic_source_term("*"), None);
        assert_eq!(symbolic_source_term("ordinary"), None);
        assert_eq!(symbolic_source_term("A *ᵥ x"), None);
        assert!(declaration_glob_query("FiberBundle.*equiv"));
        assert!(!declaration_glob_query("*ᵥ"));
        assert!(declaration_glob_matches(
            "Demo.FiberBundle.local_equiv",
            "FiberBundle.*equiv"
        ));
        assert!(declaration_glob_matches(
            "Demo.matrixToEuclideanCLM_mul",
            "matrixToEuclideanCLM.*mul"
        ));
        assert!(declaration_glob_matches(
            "Demo.projectionRangePretrivializationAt_totalSpaceMk_isInducing",
            "projectionRange.*IsInducing"
        ));
        assert!(declaration_glob_matches(
            "Demo.projectionRangeInclusionHom",
            "projectionRange.*Inclusion*"
        ));
        assert!(!declaration_glob_matches(
            "Demo.FiberBundle.local_equiv_apply",
            "FiberBundle.*equiv"
        ));
        assert!(qualified_name_matches(
            "AtiyahSinger.ComplexVectorSubbundle.transportAmbient",
            "ComplexVectorSubbundle.transportAmbient"
        ));
        assert!(!qualified_name_matches(
            "AtiyahSinger.ComplexVectorSubbundle.transportAmbient",
            "VectorSubbundle.transportAmbient"
        ));
        assert_eq!(meaningful_query_tokens("precomp (L :=)"), vec!["precomp"]);
        assert_eq!(
            meaningful_query_tokens("LinearEquiv.ofFinrankEq --all"),
            vec!["linearequiv.offinrankeq", "finrank"]
        );
        assert_eq!(
            meaningful_query_tokens("LinearMap.rangeEquiv"),
            vec!["linearmap.rangeequiv", "range", "equiv"]
        );
        assert!(
            qualified_member_score("LinearMap.rangeEquiv", "LinearMap.quotKerEquivRange")
                > qualified_member_score("LinearMap.rangeEquiv", "Algebra.linearMap")
        );
        assert!(
            qualified_member_score("LinearMap.rangeEquiv", "LinearMap.kerComplementEquivRange")
                > qualified_member_score("LinearMap.rangeEquiv", "LinearMap.range")
        );
        assert!(
            qualified_member_score("LinearEquiv.ofSurjective", "LinearEquiv.ofBijective") > 90.0
        );
        assert_eq!(
            meaningful_query_tokens("finite_trivialization_cover proof body"),
            vec![
                "finite_trivialization_cover",
                "finite",
                "trivialization",
                "cover"
            ]
        );
        assert_eq!(
            meaningful_query_tokens("elementaryTransvectionLoop_homotopic_one"),
            vec![
                "elementarytransvectionloop_homotopic_one",
                "elementary",
                "transvection",
                "loop",
                "homotopic",
                "one"
            ]
        );
        assert_eq!(
            meaningful_query_tokens("adapter weights to complex"),
            vec!["adapter", "weights", "complex"]
        );
        assert_eq!(
            source_specific_query_tokens("ContinuousMap IsUnit unitsLift"),
            vec!["unitslift"]
        );
        assert!(words_match("weight", "weights"));
        assert!(hit_name_matches(
            "Matrix.conjTranspose_mul",
            "matrix.conjtranspose_mul"
        ));
        assert!(declaration_leaf_matches(
            "AtiyahSinger.ContinuousLinearBundleHom.matrixEquiv",
            "ContinuousLinearBundleHom matrixEquiv"
        ));
        assert!(!declaration_leaf_matches(
            "AtiyahSinger.ContinuousLinearBundleHom.matrixEquiv_apply",
            "ContinuousLinearBundleHom matrixEquiv"
        ));
        let named_row = |name: &str| IndexedRow {
            owner: "workspace:w1".into(),
            path: "Demo.lean".into(),
            module: "Demo".into(),
            line: 1,
            name: name.into(),
            kind: "structure".into(),
            signature: String::new(),
            docs: String::new(),
            body: String::new(),
            rank: 0.0,
        };
        let tokens = meaningful_query_tokens("HermitianBundleMetric");
        assert!(
            lexical_score(
                "HermitianBundleMetric",
                &tokens,
                &named_row("AtiyahSinger.HermitianBundleMetric")
            ) > lexical_score(
                "HermitianBundleMetric",
                &tokens,
                &named_row("AtiyahSinger.Bundle.Trivial.hermitianBundleMetric")
            )
        );
        let summary = render_summary(&SearchRun {
            reference: "q1".into(),
            workspace_ref: "w1".into(),
            query: "demo".into(),
            inference: "hybrid".into(),
            hits: Vec::new(),
            note: None,
            duration_ms: 123,
            created_at: 0,
        });
        assert_eq!(summary, "q1 no results");
    }

    #[test]
    fn search_summary_keeps_definition_body_after_ambient_context() {
        let summary = render_summary(&SearchRun {
            reference: "q2".into(),
            workspace_ref: "w1".into(),
            query: "matrixLaurentShift".into(),
            inference: "hybrid".into(),
            hits: vec![SearchHit {
                name: "Demo.matrixLaurentShift".into(),
                kind: "def".into(),
                signature: Some("Nat → Nat".into()),
                module: "Demo".into(),
                path: "Demo.lean".into(),
                line: 10,
                doc: None,
                source: Some(
                    "-- ambient context\nuniverse u\nvariable {B : Type u}\nsection\nvariable (n : Nat)\n\ndef matrixLaurentShift : Nat :=\n  n + 1"
                        .into(),
                ),
                usages: Vec::new(),
                applicable: false,
                required_import: None,
            }],
            note: None,
            duration_ms: 1,
            created_at: 0,
        });
        assert!(summary.contains("  | n + 1"));
    }

    #[test]
    fn explicit_body_query_keeps_alternatives_compact() {
        let hit = |name: &str, source: &str| SearchHit {
            name: name.into(),
            kind: "theorem".into(),
            signature: Some("True".into()),
            module: "Demo".into(),
            path: "Demo.lean".into(),
            line: 1,
            doc: None,
            source: Some(source.into()),
            usages: Vec::new(),
            applicable: false,
            required_import: None,
        };
        let summary = render_summary(&SearchRun {
            reference: "q3".into(),
            workspace_ref: "w1".into(),
            query: "theorem proof".into(),
            inference: "hybrid".into(),
            hits: vec![
                hit("Demo.proof", "requested body"),
                hit("Other.proof", "alternative body"),
            ],
            note: None,
            duration_ms: 1,
            created_at: 0,
        });
        assert!(summary.contains("requested body"));
        assert!(summary.contains("Other.proof : True"));
        assert!(!summary.contains("alternative body"));
    }

    #[test]
    fn import_context_marks_only_unavailable_results() {
        let hit = |module: &str| RankedHit {
            hit: SearchHit {
                name: format!("{module}.useful"),
                kind: "theorem".into(),
                signature: Some("True".into()),
                module: module.into(),
                path: format!("{}.lean", module.replace('.', "/")),
                line: 1,
                doc: None,
                source: None,
                usages: Vec::new(),
                applicable: false,
                required_import: None,
            },
            score: 10.0,
        };
        let context = ImportContext {
            accessible: HashSet::from(["Demo.Available".into()]),
            complete: true,
        };
        let mut available = hit("Demo.Available");
        apply_import_context(&mut available, &context);
        assert_eq!(available.score, 40.0);
        assert!(available.hit.required_import.is_none());

        let mut unavailable = hit("Demo.Extra");
        apply_import_context(&mut unavailable, &context);
        assert_eq!(
            unavailable.hit.required_import.as_deref(),
            Some("Demo.Extra")
        );
    }

    #[test]
    fn references_decode_from_ilean_keys() {
        let key = r#"{"c":{"m":"Demo","n":"Demo.useful"}}"#;
        assert_eq!(reference_name(key).as_deref(), Some("Demo.useful"));
    }

    #[test]
    fn goal_suggestions_accept_leans_multiline_output() {
        assert_eq!(
            try_this_suggestions("Try this:\n  [apply] exact useful h\n"),
            vec!["exact useful h"]
        );
        assert_eq!(
            traced_goal_state(
                "MATHMUX_GOAL_BEGIN\nX : Type\nh : True\n⊢ True\nMATHMUX_GOAL_END\nTry this: exact h"
            )
            .as_deref(),
            Some("X : Type\nh : True\n⊢ True")
        );
        assert_eq!(
            local_method_candidates(
                "f g : X → X\nhf : Continuous f\nhg : Continuous g\n⊢ Continuous (f ∘ g)"
            )
            .first()
            .map(String::as_str),
            Some("exact hf.comp hg")
        );
        assert_eq!(
            goal_refinement_query("hf : Continuous f\n⊢ Continuous (f ∘ g)", "comp"),
            "Continuous.comp"
        );
        assert_eq!(edit_distance("compp", "comp"), 1);
        assert_eq!(
            diagnostic_search_query(
                "error: unsolved goals\nX : Type\nf g : X → X\nhf : Continuous f\n⊢ Continuous (f ∘ g)\n   3 | example"
            ),
            "⊢ Continuous (_ ∘ _)"
        );
        let source = (1..=30)
            .map(|line| format!("line {line}"))
            .collect::<Vec<_>>()
            .join("\n");
        let excerpt = location_source_excerpt(&source, 15, LOCATION_PREVIEW_LINES);
        assert!(excerpt.contains("   15 | line 15"));
        assert_eq!(excerpt.lines().count(), 30);

        let directory = tempfile::tempdir().unwrap();
        fs::write(directory.path().join("Demo.lean"), &source).unwrap();
        let location = parse_goal_location(directory.path(), directory.path(), "Demo.lean:tail")
            .unwrap()
            .unwrap();
        assert_eq!(location.line, 30);
        assert!(location.tail);
        assert!(!location.more);
        assert!(location.probe);
        assert!(location.display_path.is_none());
        let tail = location_source_excerpt(&source, location.line, SOURCE_PREVIEW_LINES);
        assert_eq!(tail.lines().count(), 16);
        assert!(tail.contains("   30 | line 30"));

        let more = parse_goal_location(
            directory.path(),
            directory.path(),
            "Demo.lean:15 MORE",
        )
        .unwrap()
        .unwrap();
        assert_eq!(more.line, 15);
        assert!(!more.tail);
        assert!(more.more);

        let dependency = directory
            .path()
            .join(".lake/packages/mathlib/Mathlib/Topology");
        fs::create_dir_all(&dependency).unwrap();
        fs::write(dependency.join("Basic.lean"), &source).unwrap();
        let dependency = parse_goal_location(
            directory.path(),
            directory.path(),
            "Mathlib/Topology/Basic.lean:15 MORE",
        )
        .unwrap()
        .unwrap();
        assert_eq!(dependency.line, 15);
        assert!(dependency.more);
        assert!(!dependency.probe);
        assert_eq!(
            dependency.display_path.as_deref(),
            Some("Mathlib/Topology/Basic.lean")
        );
    }

    #[test]
    fn missing_dependency_sources_are_detected_from_the_manifest() {
        let directory = tempfile::tempdir().unwrap();
        fs::write(directory.path().join("lake-manifest.json"), "{}").unwrap();
        assert!(dependency_sources_missing(directory.path()));
        fs::create_dir_all(directory.path().join(".lake/packages")).unwrap();
        assert!(!dependency_sources_missing(directory.path()));
    }

    #[test]
    fn source_excerpts_center_the_match_and_report_file_lines() {
        let source = (1..=20)
            .map(|line| {
                if line == 12 {
                    "theorem exact_match := by simp".to_owned()
                } else {
                    format!("-- line {line}")
                }
            })
            .collect::<Vec<_>>()
            .join("\n");
        let (excerpt, line) =
            source_excerpt_with_limit(&source, "exact_match", &["exact_match".into()], 1, true, 8);
        let excerpt = excerpt.unwrap();
        assert_eq!(line, 12);
        assert!(excerpt.starts_with("-- line 10"));
        assert!(excerpt.contains("theorem exact_match"));
        assert_eq!(excerpt.lines().count(), 8);

        let structure = "structure Config where\n  first : Nat\n  second : String\n  third : Bool\n\n/-- The next declaration. -/\ndef next := 1\n";
        let (excerpt, line) = detailed_source_excerpt(
            structure,
            "Config",
            &["config".into()],
            10,
            "structure",
            "Demo.Config",
        );
        assert_eq!(line, 10);
        let excerpt = excerpt.unwrap();
        assert!(excerpt.contains("third : Bool"));
        assert!(!excerpt.contains("next declaration"));

        let proof = (1..=20)
            .map(|line| format!("proof line {line}"))
            .collect::<Vec<_>>()
            .join("\n");
        let (excerpt, _) = detailed_source_excerpt(
            &proof,
            "proof line 1",
            &["proof".into()],
            1,
            "theorem",
            "Demo.proof",
        );
        assert_eq!(excerpt.unwrap().lines().count(), 20);
    }

    #[test]
    fn source_excerpts_prefer_local_context_covering_the_query() {
        let source = "rw [Finsupp.sum_add_index]\nsimp [smul_eq_mul]\ntheorem Demo.outer : True := by\n  step 1\n  step 2\n  step 3\n  step 4\n  step 5\n  step 6\n  step 7\n  step 8\n  step 9\n  step 10\n  step 11\n  step 12\n  step 13\n  step 14\n  step 15\n  step 16\n  have hpush (q : α) : True := by\n    rw [Finsupp.sum_add_index]\n    simp\n    simp [smul_eq_mul]\n  exact hpush q\n  simp_rw [hpush]\n";
        let query = "Demo.outer hpush Finsupp.sum_add_index smul_eq_mul";
        let tokens = meaningful_query_tokens(query);
        let (excerpt, _) =
            detailed_source_excerpt(source, query, &tokens, 1, "theorem", "Demo.outer");
        let excerpt = excerpt.unwrap();
        assert!(excerpt.contains("have hpush"));
        assert!(excerpt.contains("Finsupp.sum_add_index"));
        assert!(excerpt.contains("smul_eq_mul"));

        let ambient = (1..=20)
            .map(|line| format!("variable (ambient{line} : Nat)"))
            .collect::<Vec<_>>()
            .join("\n");
        let source =
            format!("-- ambient context\n{ambient}\n\ndef requestedDefinition : Nat :=\n  42");
        let query = "missingLocalTerm requestedDefinition";
        let tokens = meaningful_query_tokens(query);
        let (excerpt, _) = detailed_source_excerpt(
            &source,
            query,
            &tokens,
            1,
            "def",
            "Demo.requestedDefinition",
        );
        let excerpt = excerpt.unwrap();
        assert!(excerpt.contains("def requestedDefinition"));
        assert!(excerpt.contains("42"));
    }

    #[test]
    fn warming_fallback_finds_local_dependency_declarations() {
        let directory = tempfile::tempdir().unwrap();
        let package = directory.path().join(".lake/packages/demo/Demo");
        fs::create_dir_all(&package).unwrap();
        fs::write(
            package.join("Api.lean"),
            "namespace Bundle.ContinuousLinearMap\n\nclass topologicalSpaceTotalSpace : Prop where\n  value : True\n\nend Bundle.ContinuousLinearMap\n",
        )
        .unwrap();
        let hits = fallback_source_hits(
            directory.path(),
            "Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace",
            &["bundle.continuouslinearmap.topologicalspacetotalspace".into()],
        )
        .unwrap();
        assert!(hits.iter().any(|hit| {
            hit.hit.name == "Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace"
        }));
    }

    #[test]
    fn fallback_finds_symbolic_notation_literally() {
        let directory = tempfile::tempdir().unwrap();
        fs::write(
            directory.path().join("Notation.lean"),
            "def vectorAction (a : α) (v : β) := a *ᵥ v\n",
        )
        .unwrap();
        let query = "*ᵥ";
        let hits = fallback_source_hits(
            directory.path(),
            query,
            &meaningful_query_tokens(query),
        )
        .unwrap();
        assert!(hits.iter().any(|hit| hit.hit.name == "vectorAction"));
    }

    #[test]
    fn fallback_prefers_declarations_over_whole_file_matches() {
        let directory = tempfile::tempdir().unwrap();
        fs::write(
            directory.path().join("Support.lean"),
            "theorem continuous_of_support (f : α → β) : Continuous f := by sorry\n-- closure support zero neighborhood\n",
        )
        .unwrap();
        let tokens = meaningful_query_tokens("continuous support closure zero neighborhood");
        let hits = fallback_source_hits(
            directory.path(),
            "continuous support closure zero neighborhood",
            &tokens,
        )
        .unwrap();
        assert_eq!(hits[0].hit.name, "continuous_of_support");
    }

    #[test]
    fn fallback_opens_an_explicit_module_before_broad_matches() {
        let directory = tempfile::tempdir().unwrap();
        let package = directory
            .path()
            .join(".lake/packages/demo/Mathlib/Topology");
        fs::create_dir_all(&package).unwrap();
        fs::write(
            package.join("Support.lean"),
            "theorem support_fact : True := trivial\n",
        )
        .unwrap();
        let query = "Mathlib.Topology.Support Function.support";
        let hits =
            fallback_source_hits(directory.path(), query, &meaningful_query_tokens(query)).unwrap();
        assert!(hits.iter().any(|hit| hit.hit.name == "support_fact"));
    }

    #[test]
    fn fallback_keeps_lower_camel_declarations_in_broad_queries() {
        let directory = tempfile::tempdir().unwrap();
        let package = directory
            .path()
            .join(".lake/packages/mathlib/Mathlib/Topology/ContinuousMap");
        fs::create_dir_all(&package).unwrap();
        fs::write(
            package.join("Units.lean"),
            "namespace ContinuousMap\ndef unitsLift : True := trivial\ntheorem isUnit_iff_forall_isUnit : True := trivial\nend ContinuousMap\n",
        )
        .unwrap();
        let query = "ContinuousMap pointwise IsUnit iff global IsUnit and unitsLift construction";
        let hits =
            fallback_source_hits(directory.path(), query, &meaningful_query_tokens(query)).unwrap();
        assert!(
            hits.iter()
                .take(5)
                .any(|hit| hit.hit.name == "ContinuousMap.unitsLift")
        );
        assert!(
            hits.iter()
                .take(5)
                .any(|hit| hit.hit.name == "ContinuousMap.isUnit_iff_forall_isUnit")
        );
    }

    #[test]
    fn fallback_opens_explicit_lean_file_import_lists() {
        let directory = tempfile::tempdir().unwrap();
        fs::write(
            directory.path().join("Root.lean"),
            "import Demo.One\nimport Demo.Two\n",
        )
        .unwrap();
        let query = "root Root.lean import list";
        let hits =
            fallback_source_hits(directory.path(), query, &meaningful_query_tokens(query)).unwrap();
        assert_eq!(hits[0].hit.name, "Root.imports");
        assert_eq!(
            hits[0].hit.source.as_deref(),
            Some("import Demo.One\nimport Demo.Two")
        );
    }

    #[test]
    fn fallback_reserves_tied_coverage_for_project_sources() {
        let directory = tempfile::tempdir().unwrap();
        let dependencies = directory.path().join(".lake/packages/demo/Mathlib");
        fs::create_dir_all(&dependencies).unwrap();
        for index in 0..100 {
            fs::write(
                dependencies.join(format!("Noise{index}.lean")),
                format!("theorem noise{index} : True := by trivial\n-- finite continuous sum\n"),
            )
            .unwrap();
        }
        fs::write(
            directory.path().join("Metric.lean"),
            "theorem project_weightedSum : True := by trivial\n-- finite continuous sum\n",
        )
        .unwrap();
        let query = "finite continuous sum";
        let hits =
            fallback_source_hits(directory.path(), query, &meaningful_query_tokens(query)).unwrap();
        assert!(hits.iter().any(|hit| hit.hit.name == "project_weightedSum"));
    }

    #[test]
    fn fallback_connects_trivialization_at_to_linearity_instance() {
        let directory = tempfile::tempdir().unwrap();
        fs::write(
            directory.path().join("Basic.lean"),
            "namespace VectorBundle\ninstance (priority := 100) trivialization_linear : e.IsLinear R := inferInstance\nend VectorBundle\n",
        )
        .unwrap();
        let query =
            "linear_trivializationAt isLinear_trivializationAt VectorBundle.trivializationAt";
        let hits =
            fallback_source_hits(directory.path(), query, &meaningful_query_tokens(query)).unwrap();
        assert!(
            hits.iter()
                .any(|hit| hit.hit.name == "VectorBundle.trivialization_linear")
        );
    }

    #[test]
    fn fallback_connects_conceptual_inner_product_api_terms() {
        let directory = tempfile::tempdir().unwrap();
        fs::write(
            directory.path().join("Inner.lean"),
            "namespace InnerProductSpace\ndef ofCore (c : Core K E) : InnerProductSpace K E := by sorry\nend InnerProductSpace\nnamespace Submodule\ntheorem sup_orthogonal_of_hasOrthogonalProjection [K.HasOrthogonalProjection] : K ⊔ Kᗮ = ⊤ := by sorry\nend Submodule\n",
        )
        .unwrap();
        for (query, expected) in [
            (
                "InnerProductSpace.Core.toInnerProductSpace constructor",
                "InnerProductSpace.ofCore",
            ),
            (
                "orthogonal complement finite dimensional sup top",
                "Submodule.sup_orthogonal_of_hasOrthogonalProjection",
            ),
        ] {
            let hits =
                fallback_source_hits(directory.path(), query, &meaningful_query_tokens(query))
                    .unwrap();
            assert!(hits.iter().any(|hit| hit.hit.name == expected));
        }
    }

    #[test]
    fn fallback_respects_qualified_member_owner_order() {
        let directory = tempfile::tempdir().unwrap();
        fs::write(
            directory.path().join("Core.lean"),
            "structure PreInnerProductSpace.Core where\n  conj_inner_symm : True\nstructure InnerProductSpace.Core extends PreInnerProductSpace.Core where\n  definite : True\n",
        )
        .unwrap();
        let query = "InnerProductSpace.Core.definite PreInnerProductSpace.Core.conj_inner_symm";
        let hits =
            fallback_source_hits(directory.path(), query, &meaningful_query_tokens(query)).unwrap();
        assert_eq!(hits[0].hit.name, "InnerProductSpace.Core");
        assert!(
            hits[0]
                .hit
                .signature
                .as_deref()
                .unwrap()
                .contains("InnerProductSpace.Core.toPreInnerProductSpaceCore")
        );
    }

    #[test]
    fn fallback_includes_root_qualified_member_owner_structure() {
        let directory = tempfile::tempdir().unwrap();
        fs::write(
            directory.path().join("Metric.lean"),
            "namespace AtiyahSinger\nstructure HermitianBundleMetric where\n  inner : True\n  continuous : True\nnamespace HermitianBundleMetric\ntheorem pos_inner : True := trivial\nend HermitianBundleMetric\nend AtiyahSinger\n",
        )
        .unwrap();
        let query = "HermitianBundleMetric.pos_inner continuity WhitneySquare";
        let hits =
            fallback_source_hits(directory.path(), query, &meaningful_query_tokens(query)).unwrap();
        assert_eq!(hits[0].hit.name, "AtiyahSinger.HermitianBundleMetric");
        assert!(
            hits[0]
                .hit
                .source
                .as_deref()
                .unwrap()
                .contains("continuous : True")
        );
    }

    #[test]
    fn fallback_honors_named_argument_queries() {
        let directory = tempfile::tempdir().unwrap();
        fs::write(
            directory.path().join("Precomp.lean"),
            "namespace CategoryTheory\ndef precomp (α : X) := α\nend CategoryTheory\nnamespace ContinuousLinearMap\ndef precomp (G) (L : E → F) := L\nend ContinuousLinearMap\n",
        )
        .unwrap();
        let query = "precomp (L :=)";
        let hits =
            fallback_source_hits(directory.path(), query, &meaningful_query_tokens(query)).unwrap();
        assert_eq!(hits[0].hit.name, "ContinuousLinearMap.precomp");
        assert!(
            hits[0]
                .hit
                .signature
                .as_deref()
                .unwrap()
                .contains("(L : E → F)")
        );
    }
}
