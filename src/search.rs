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

use crate::git::{lake_command, lake_executable};
use crate::issue::{TelemetryOperation, TelemetryStore, development_enabled};
use crate::repo::Repo;
use crate::state::{SearchHit, SearchRun, SearchUsage, State, Workspace};
use crate::util::{clean_line, hash_bytes, now_unix_ms};

const RESULT_LIMIT: usize = 24;
const SUMMARY_LIMIT: usize = 5;
const GOAL_TIMEOUT_MS: u64 = 2_000;
const SEARCH_INDEX_VERSION: i64 = 6;
const DECLARATION_DETAIL_LINES: usize = 48;

pub struct Searcher {
    repo: Repo,
    state: State,
    index_lock: Mutex<()>,
    base_lock: Arc<Mutex<()>>,
    loogle: Mutex<LoogleState>,
    base: Mutex<HashMap<String, BaseState>>,
}

struct SearchResult {
    hits: Vec<SearchHit>,
    inference: String,
    note: Option<String>,
}

#[derive(Debug)]
struct RankedHit {
    hit: SearchHit,
    score: f64,
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
    pub fn new(repo: Repo, state: State) -> Result<Self> {
        let searcher = Self {
            repo,
            state,
            index_lock: Mutex::new(()),
            base_lock: Arc::new(Mutex::new(())),
            loogle: Mutex::new(LoogleState::Empty),
            base: Mutex::new(HashMap::new()),
        };
        searcher.migrate()?;
        Ok(searcher)
    }

    pub fn search(&self, workspace: &Workspace, cwd: &Path, query: &str) -> Result<String> {
        let query = query.trim();
        ensure!(!query.is_empty(), "search query is empty");
        let reference = self.state.next_ref('q')?;
        let started = Instant::now();
        let result = if let Some(location) = parse_goal_location(&workspace.path, cwd, query)? {
            self.goal_search(workspace, location)?
        } else {
            let _guard = self
                .index_lock
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            let (scopes, base_warming) = self.refresh(workspace)?;
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
        self.state.add_search(&run)?;
        self.state.touch_workspace(&workspace.reference)?;
        Ok(render_summary(&run))
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
                 DELETE FROM search_references;",
            )?;
            connection.execute(
                "INSERT INTO search_meta(key, value) VALUES ('version', ?1)
                 ON CONFLICT(key) DO UPDATE SET value = excluded.value",
                [SEARCH_INDEX_VERSION],
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
        if let Ok(_base_guard) = self.base_lock.try_lock() {
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
                let workspace = workspace.clone();
                let base_lock = self.base_lock.clone();
                let partial = package_scopes(&workspace.path);
                std::thread::spawn(move || {
                    let started = Instant::now();
                    let result = {
                        let _guard = base_lock
                            .lock()
                            .unwrap_or_else(std::sync::PoisonError::into_inner);
                        Searcher::new(repo.clone(), state)
                            .and_then(|searcher| searcher.refresh_base(&workspace))
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
        self.remove_missing(&source_root.owner, "source", &files)?;
        for path in files {
            if !self.file_changed(&source_root.owner, &path, "source")? {
                continue;
            }
            let source = fs::read_to_string(&path)
                .with_context(|| format!("cannot index {}", path.display()))?;
            let display = display_path(&path, workspace_root, &source_root.root, source_root.kind);
            let module = module_name(&path, &source_root.root, source_root.kind);
            let entries = parse_source(&source, &module);
            let mut connection = self.open()?;
            let transaction = connection.transaction()?;
            transaction.execute(
                "DELETE FROM search_fts WHERE owner = ?1 AND origin = ?2",
                params![source_root.owner, path.to_string_lossy()],
            )?;
            for entry in entries {
                transaction.execute(
                    "INSERT INTO search_fts(
                        owner, origin, file, module, line, name, kind, signature, docs, body
                     ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10)",
                    params![
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
                    ],
                )?;
            }
            record_file(&transaction, &source_root.owner, &path, "source")?;
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
        for path in files {
            if !self.file_changed(owner, &path, "ilean")? {
                continue;
            }
            let value: Value = serde_json::from_slice(&fs::read(&path)?)
                .with_context(|| format!("cannot index {}", path.display()))?;
            let module = value
                .get("module")
                .and_then(Value::as_str)
                .unwrap_or_default();
            let source_path = format!("{}.lean", module.replace('.', "/"));
            let mut connection = self.open()?;
            let transaction = connection.transaction()?;
            let artifact = path.to_string_lossy();
            transaction.execute(
                "DELETE FROM search_fts WHERE owner = ?1 AND origin = ?2",
                params![owner, artifact],
            )?;
            transaction.execute(
                "DELETE FROM search_references WHERE owner = ?1 AND file = ?2",
                params![owner, artifact],
            )?;
            if let Some(declarations) = value.get("decls").and_then(Value::as_object) {
                for (name, range) in declarations {
                    let line = range
                        .as_array()
                        .and_then(|range| range.get(4).or_else(|| range.first()))
                        .and_then(Value::as_u64)
                        .unwrap_or(0)
                        + 1;
                    transaction.execute(
                        "INSERT INTO search_fts(
                            owner, origin, file, module, line, name, kind, signature, docs, body
                         ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, 'declaration', '', '', '')",
                        params![owner, artifact, source_path, module, line, name],
                    )?;
                }
            }
            if let Some(references) = value.get("references").and_then(Value::as_object) {
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
                        transaction.execute(
                            "INSERT INTO search_references(
                                owner, file, target, source_module, line, context
                             ) VALUES (?1, ?2, ?3, ?4, ?5, ?6)",
                            params![owner, artifact, target, module, line, context],
                        )?;
                    }
                }
            }
            record_file(&transaction, owner, &path, "ilean")?;
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
            connection.execute(
                "DELETE FROM search_fts WHERE owner = ?1 AND origin = ?2",
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

    fn file_changed(&self, owner: &str, path: &Path, kind: &str) -> Result<bool> {
        let metadata = fs::metadata(path)?;
        let modified = modified_ns(&metadata);
        let size = metadata.len() as i64;
        let prior = self
            .open()?
            .query_row(
                "SELECT modified_ns, size FROM search_files
                 WHERE owner = ?1 AND path = ?2 AND kind = ?3",
                params![owner, path.to_string_lossy(), kind],
                |row| Ok((row.get::<_, i64>(0)?, row.get::<_, i64>(1)?)),
            )
            .optional()?;
        Ok(prior != Some((modified, size)))
    }

    fn combined_search(
        &self,
        workspace: &Workspace,
        query: &str,
        scopes: &HashSet<String>,
        base_warming: bool,
    ) -> Result<SearchResult> {
        let type_search = type_search_enabled() && type_shaped(query);
        let rows = self.candidates(query, type_search)?;
        let query_lower = query.to_lowercase();
        let query_tokens = meaningful_query_tokens(query);
        let mut ranked = Vec::new();
        let mut warming = false;
        if type_search {
            let (loogle_hits, is_warming) = self.loogle_hits(workspace, query);
            warming = is_warming;
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
                    },
                    score: 180.0 - position as f64,
                });
            }
        }
        for row in rows.into_iter().filter(|row| scopes.contains(&row.owner)) {
            let type_score = if type_search {
                structural_type_score(query, &row.signature)
            } else {
                0.0
            };
            let lexical = lexical_score(&query_lower, &query_tokens, &row);
            if type_search && row.kind == "file" && type_score == 0.0 {
                continue;
            }
            if lexical <= 0.0 && type_score <= 0.0 {
                continue;
            }
            let usages = self.usages(&row.name, scopes, workspace)?;
            let (source, matched_line) =
                detailed_source_excerpt(&row.body, query, &query_tokens, row.line, &row.kind);
            let score = lexical
                + type_score
                + (usages.len() as f64 + 1.0).ln()
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
                    usages,
                },
                score,
            });
        }
        if base_warming || ranked.len() < 3 || query.contains('|') || query_tokens.len() > 1 {
            match fallback_source_hits(&workspace.path, query, &query_tokens) {
                Ok(hits) => ranked.extend(hits),
                Err(error) => append_log(
                    &self.repo,
                    &format!("source fallback unavailable: {error:#}"),
                ),
            }
        }
        ranked.sort_by(|left, right| {
            right
                .score
                .partial_cmp(&left.score)
                .unwrap_or(Ordering::Equal)
                .then_with(|| left.hit.name.cmp(&right.hit.name))
        });
        let mut seen = HashSet::new();
        ranked.retain(|candidate| seen.insert(candidate.hit.name.clone()));
        ranked.truncate(RESULT_LIMIT);
        let no_hits = ranked.is_empty();
        let dependency_sources_missing = dependency_sources_missing(&workspace.path);
        Ok(SearchResult {
            hits: ranked.into_iter().map(|candidate| candidate.hit).collect(),
            inference: if type_search {
                "hybrid+type".into()
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
        })
    }

    fn candidates(&self, query: &str, include_all_signatures: bool) -> Result<Vec<IndexedRow>> {
        let connection = self.open()?;
        let fts_query = fts_query(query);
        let sql = if fts_query.is_empty() && include_all_signatures {
            "SELECT owner, file, module, line, name, kind, signature, docs, body, 0.0
             FROM search_fts WHERE signature <> '' LIMIT 20000"
        } else {
            "SELECT owner, file, module, line, name, kind, signature, docs, body,
                    bm25(search_fts, 0.0, 0.0, 0.0, 0.0, 0.0, 12.0, 0.0, 7.0, 3.0, 1.0)
             FROM search_fts WHERE search_fts MATCH ?1 LIMIT 1000"
        };
        let mut statement = connection.prepare(sql)?;
        let map = |row: &rusqlite::Row<'_>| {
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
        };
        if fts_query.is_empty() && include_all_signatures {
            statement
                .query_map([], map)?
                .collect::<rusqlite::Result<Vec<_>>>()
                .map_err(Into::into)
        } else if fts_query.is_empty() {
            Ok(Vec::new())
        } else {
            statement
                .query_map([fts_query], map)?
                .collect::<rusqlite::Result<Vec<_>>>()
                .map_err(Into::into)
        }
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
        let Some((start, end, replacement)) = goal_probe(&source, location.line) else {
            return Ok(SearchResult {
                hits: Vec::new(),
                inference: "goal".into(),
                note: Some("no sorry or admit placeholder near that position".into()),
            });
        };
        let mut probe = source;
        probe.replace_range(start..end, replacement);
        let directory = self.repo.state_dir.join("search-goals");
        fs::create_dir_all(&directory)?;
        let id = hash_bytes(
            format!(
                "{}:{}:{}:{}",
                workspace.reference,
                location.path.display(),
                location.line,
                now_unix_ms()
            )
            .as_bytes(),
        );
        let temporary = directory.join(format!("GoalProbe-{}.lean", &id[..16]));
        fs::write(&temporary, probe)?;
        let timeout = format!("{:.3}s", GOAL_TIMEOUT_MS as f64 / 1000.0);
        let mut command = std::process::Command::new("timeout");
        command
            .args(["--signal=KILL", &timeout])
            .arg(lake_executable())
            .args(["env", "lean"])
            .arg(&temporary)
            .current_dir(&workspace.path)
            .env("LAKE_ARTIFACT_CACHE", "true")
            .env("LAKE_CACHE_DIR", &self.repo.cache_dir)
            .stdin(Stdio::null());
        let output = command.output();
        let _ = fs::remove_file(&temporary);
        let output = output?;
        let timed_out = matches!(output.status.code(), None | Some(124 | 137));
        let rendered = format!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let suggestions = try_this_suggestions(&rendered);
        let relative = location
            .path
            .strip_prefix(&workspace.path)
            .unwrap_or(&location.path)
            .to_string_lossy()
            .into_owned();
        let hits: Vec<SearchHit> = suggestions
            .into_iter()
            .map(|suggestion| SearchHit {
                name: clean_line(&suggestion),
                kind: "goal".into(),
                signature: None,
                module: String::new(),
                path: relative.clone(),
                line: location.line,
                doc: None,
                source: Some(suggestion),
                usages: Vec::new(),
            })
            .collect();
        let note = if timed_out {
            Some(format!("goal search timed out after {GOAL_TIMEOUT_MS}ms"))
        } else if hits.is_empty() && !output.status.success() {
            rendered
                .lines()
                .rev()
                .find(|line| !line.trim().is_empty())
                .map(|line| format!("goal search unavailable: {}", clean_line(line)))
        } else {
            None
        };
        Ok(SearchResult {
            hits,
            inference: "goal".into(),
            note,
        })
    }
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
        self.stdin.write_all(query.as_bytes())?;
        self.stdin.write_all(b"\n")?;
        self.stdin.flush()?;
        let line = read_line_timeout(&mut self.stdout, std::time::Duration::from_secs(30))?;
        let value: Value = serde_json::from_str(&line)
            .with_context(|| format!("invalid Loogle response: {}", clean_line(&line)))?;
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
    let mut entries = Vec::new();
    for (index, capture) in matches.iter().enumerate() {
        let complete = capture.get(0).expect("declaration match");
        let Some(raw_name) = capture.name("name").map(|value| value.as_str()) else {
            continue;
        };
        let line = offset_line(&lines, complete.start());
        let end = matches
            .get(index + 1)
            .and_then(|next| next.get(0))
            .map(|next| next.start())
            .unwrap_or(source.len());
        let block = source[complete.start()..end].trim();
        let header_end = declaration_header_end(block);
        let header = block[..header_end].trim();
        let name_end = header
            .find(raw_name)
            .map(|start| start + raw_name.len())
            .unwrap_or(header.len());
        let signature = header[name_end..].trim().trim_start_matches(':').trim();
        let namespace = namespaces
            .get(line.saturating_sub(1))
            .cloned()
            .unwrap_or_default();
        let name = if raw_name.contains('.') || namespace.is_empty() {
            raw_name.to_owned()
        } else {
            format!("{}.{}", namespace.join("."), raw_name)
        };
        entries.push(SourceEntry {
            line: line as u64,
            name,
            kind: capture
                .name("kind")
                .map(|value| value.as_str().to_owned())
                .unwrap_or_else(|| "declaration".into()),
            signature: single_line(signature),
            docs: preceding_doc(source, complete.start()).unwrap_or_default(),
            body: block.chars().take(16_000).collect(),
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
    tokens
}

fn lexical_score(query: &str, tokens: &[String], row: &IndexedRow) -> f64 {
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
        120.0
    } else if base == query {
        105.0
    } else if name.ends_with(&format!(".{query}")) {
        95.0
    } else if name.starts_with(query) || base.starts_with(query) {
        75.0
    } else if name.contains(query) {
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
    20.0 + arrow_score + pattern_tokens.len() as f64 * 5.0
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

fn source_excerpt(
    source: &str,
    query: &str,
    tokens: &[String],
    declaration_line: u64,
    file_hit: bool,
) -> (Option<String>, u64) {
    if source.trim().is_empty() {
        return (None, declaration_line);
    }
    let lines = source.lines().collect::<Vec<_>>();
    let query = query.to_lowercase();
    let matched = lines
        .iter()
        .position(|line| line.to_lowercase().contains(&query))
        .or_else(|| {
            lines
                .iter()
                .enumerate()
                .map(|(index, line)| {
                    let line = line.to_lowercase();
                    let score = tokens.iter().filter(|token| line.contains(*token)).count();
                    (index, score)
                })
                .filter(|(_, score)| *score > 0)
                .max_by_key(|(_, score)| *score)
                .map(|(index, _)| index)
        })
        .unwrap_or(0);
    let start = matched.saturating_sub(2);
    let excerpt = lines[start..lines.len().min(start + 8)].join("\n");
    let line = if file_hit {
        matched as u64 + 1
    } else {
        declaration_line
    };
    (nonempty(excerpt), line)
}

fn detailed_source_excerpt(
    body: &str,
    query: &str,
    tokens: &[String],
    declaration_line: u64,
    kind: &str,
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
    source_excerpt(body, query, tokens, declaration_line, kind == "file")
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
    let mut terms = query_tokens
        .iter()
        .flat_map(|token| std::iter::once(token.as_str()).chain(token.split(['.', '_'])))
        .map(str::to_lowercase)
        .filter(|term| term.len() >= 3 && !generic.contains(&term.as_str()))
        .collect::<Vec<_>>();
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
    if query_tokens.len() <= 2
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
    let mut path_coverage = HashMap::<PathBuf, usize>::new();
    for term in rare_terms.iter().take(12) {
        for path in source_scan_paths(&workspace, packages.as_deref(), std::slice::from_ref(term))?
        {
            *path_coverage.entry(path).or_default() += 1;
        }
    }
    let mut balanced_paths = path_coverage.into_iter().collect::<Vec<_>>();
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
    let direct_paths = direct_module_paths(&workspace, packages.as_deref(), query);
    let mut paths = direct_paths
        .into_iter()
        .chain(
            declaration_paths
                .iter()
                .filter(|path| strong_set.contains(path))
                .cloned(),
        )
        .collect::<Vec<_>>();
    let mut seen_paths = paths.iter().cloned().collect::<HashSet<_>>();
    for candidates in [
        declaration_paths,
        balanced_paths,
        strong_paths,
        source_scan_paths(&workspace, packages.as_deref(), &terms)?,
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
            let (excerpt, matched_line) =
                detailed_source_excerpt(&entry.body, query, &terms, entry.line, &entry.kind);
            let name_score = terms
                .iter()
                .filter(|term| entry.name.to_lowercase().contains(*term))
                .count();
            let name = entry.name.to_lowercase();
            let base = name.rsplit('.').next().unwrap_or(&name);
            let name_segments = name.split('.').collect::<HashSet<_>>();
            let segment_score = terms
                .iter()
                .filter(|term| name_segments.contains(term.as_str()))
                .count();
            let is_file = entry.kind == "file";
            let exact_name = query_tokens.iter().any(|token| {
                (token.contains('.') && token == &name)
                    || (!is_file
                        && token.len() >= 12
                        && !token.contains('.')
                        && token.as_str() == base)
                    || (query_tokens.len() == 1 && token.as_str() == base)
            });
            let qualified_leaf = query_tokens.iter().any(|token| {
                token
                    .rsplit_once('.')
                    .is_some_and(|(_, leaf)| name_segments.contains(leaf))
            });
            let is_class = entry.kind == "class";
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
                },
                score: 35.0
                    + score as f64 * 8.0
                    + name_score as f64 * 20.0
                    + segment_score as f64 * 30.0
                    + if exact_name { 80.0 } else { 0.0 }
                    + if qualified_leaf { 60.0 } else { 0.0 }
                    + if is_class && class_query { 40.0 } else { 0.0 }
                    + if is_file {
                        -40.0
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
    ranked.truncate(RESULT_LIMIT);
    Ok(ranked)
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
        .filter(|token| token.contains('.'));
    for token in tokens {
        let relative = PathBuf::from(format!("{}.lean", token.replace('.', "/")));
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

fn render_summary(run: &SearchRun) -> String {
    let mut output = run.reference.clone();
    if run.hits.is_empty() {
        output.push_str(" no results");
    }
    for hit in run.hits.iter().take(SUMMARY_LIMIT) {
        output.push('\n');
        output.push_str(&hit.name);
        if let Some(signature) = &hit.signature {
            output.push_str(" : ");
            output.push_str(&truncate_line(&single_line(signature), 240));
        }
        output.push_str(&format!("  {}:{}", hit.path, hit.line));
        if run.hits.first().is_some_and(|first| first.name == hit.name)
            && let Some(source) = &hit.source
        {
            for line in source.lines().take(3) {
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
    output.push_str(&format!("\n{}ms", run.duration_ms));
    output
}

fn single_line(value: &str) -> String {
    value.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn truncate_line(value: &str, limit: usize) -> String {
    if value.chars().count() <= limit {
        return value.to_owned();
    }
    let mut output = value
        .chars()
        .take(limit.saturating_sub(1))
        .collect::<String>();
    output.push('…');
    output
}

struct GoalLocation {
    path: PathBuf,
    line: u64,
}

fn parse_goal_location(root: &Path, cwd: &Path, query: &str) -> Result<Option<GoalLocation>> {
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
    let requested = PathBuf::from(path);
    let absolute = if requested.is_absolute() {
        requested
    } else {
        cwd.join(requested)
    };
    if absolute
        .extension()
        .is_none_or(|extension| extension != "lean")
        || !absolute.is_file()
    {
        return Ok(None);
    }
    let absolute = fs::canonicalize(absolute)?;
    ensure!(
        absolute.starts_with(root),
        "goal position is outside the workspace"
    );
    ensure!(line > 0, "goal line starts at 1");
    Ok(Some(GoalLocation {
        path: absolute,
        line,
    }))
}

fn goal_probe(source: &str, requested_line: u64) -> Option<(usize, usize, &'static str)> {
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
                    let preceding = &source[..absolute];
                    let in_tactic = preceding
                        .lines()
                        .rev()
                        .find(|line| !line.trim().is_empty())
                        .is_some_and(|line| line.trim_end().ends_with("by"));
                    let replacement = if in_tactic {
                        "first | exact? | apply? | rw?"
                    } else {
                        "by first | exact? | apply? | rw?"
                    };
                    return Some((absolute, absolute + placeholder.len(), replacement));
                }
            }
        }
    }
    None
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
    }

    #[test]
    fn inference_reserves_positions_and_recognizes_type_patterns() {
        assert!(type_shaped("_ → Injective _"));
        assert!(!type_shaped("injective function"));
        assert!(!type_shaped("norm_inner_le_norm"));
        assert!(structural_type_score("_ → Injective _", "Bijective f → Injective f") > 0.0);
        assert_eq!(fts_query("List.map"), "\"list.map\"*");
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
            source_excerpt(&source, "exact_match", &["exact_match".into()], 1, true);
        let excerpt = excerpt.unwrap();
        assert_eq!(line, 12);
        assert!(excerpt.starts_with("-- line 10"));
        assert!(excerpt.contains("theorem exact_match"));
        assert_eq!(excerpt.lines().count(), 8);

        let structure = "structure Config where\n  first : Nat\n  second : String\n  third : Bool\n\n/-- The next declaration. -/\ndef next := 1\n";
        let (excerpt, line) =
            detailed_source_excerpt(structure, "Config", &["config".into()], 10, "structure");
        assert_eq!(line, 10);
        let excerpt = excerpt.unwrap();
        assert!(excerpt.contains("third : Bool"));
        assert!(!excerpt.contains("next declaration"));
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
}
