use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::os::fd::AsRawFd;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::{Arc, Mutex, OnceLock};
use std::time::{Duration, Instant};

use anyhow::{Context, Result, bail, ensure};
use regex::Regex;
use rusqlite::{Connection, OptionalExtension, params, params_from_iter};
use serde_json::Value;
use walkdir::WalkDir;

use crate::check::{Checker, parse_imports, project_module_name};
use crate::git::{dirty_lean_files, lake_command, lake_executable, project_lean_files};
use crate::issue::{TelemetryOperation, TelemetryStore, development_enabled};
use crate::repo::Repo;
use crate::state::{SEARCH_USAGE_LIMIT, SearchHit, SearchRun, SearchUsage, State, Workspace};
use crate::util::{
    SOURCE_PREVIEW_LINES, clean_line, hash_bytes, now_unix_ms, query_requests_proof_body,
    single_line, truncate_line, truncate_middle,
};

mod goal;
mod query;
mod source;
#[cfg(test)]
mod tests;

use goal::*;
use query::*;
use source::*;

const RESULT_LIMIT: usize = 24;
const SUMMARY_LIMIT: usize = 5;
const LOCATION_PREVIEW_LINES: usize = 32;
const LOCATION_MORE_LINES: usize = 96;
const SOURCE_OCCURRENCE_LIMIT: usize = 64;
const SOURCE_RANGE_LIMIT: usize = 120;
const SOURCE_OCCURRENCE_ALL_LIMIT: usize = 200;
const OUTLINE_PREVIEW_LINES: usize = 64;
const OUTLINE_LINE_CHARS: usize = 120;
const RELATED_RESULT_LIMIT: usize = 8;
const GOAL_STATE_BEGIN: &str = "MATHMUX_GOAL_BEGIN";
const GOAL_STATE_END: &str = "MATHMUX_GOAL_END";
const SEARCH_INDEX_VERSION: i64 = 7;
const SOURCE_INDEX_KIND: &str = "source-v9";
const DECLARATION_DETAIL_LINES: usize = 48;
const INDEX_COMMIT_BATCH: usize = 64;
const SEARCH_REFRESH_INTERVAL: std::time::Duration = std::time::Duration::from_millis(500);
const DIAGNOSTIC_PROBE_MAX_CHECK_MS: u64 = 2_000;
const DIAGNOSTIC_PROBE_BUDGET: Duration = Duration::from_millis(750);
const SOURCE_SCAN_BUDGET: Duration = Duration::from_millis(300);
const SOURCE_FALLBACK_BUDGET: Duration = Duration::from_millis(750);

pub struct Searcher {
    repo: Repo,
    state: State,
    checker: Arc<Checker>,
    index_lock: Mutex<()>,
    last_refresh: Mutex<HashMap<String, Instant>>,
    dirty_cache: Mutex<HashMap<String, (Instant, Vec<PathBuf>)>>,
    source_cache: Mutex<HashMap<PathBuf, CachedSource>>,
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

struct ExpandedQuery {
    query: String,
    context: Vec<SearchHit>,
    import_target: Option<PathBuf>,
}

impl ExpandedQuery {
    fn plain(query: impl Into<String>) -> Self {
        Self {
            query: query.into(),
            context: Vec::new(),
            import_target: None,
        }
    }
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

fn delete_search_references(connection: &Connection, owner: &str, file: &str) -> Result<()> {
    connection.execute(
        "DELETE FROM search_references
         WHERE file_id IN (
            SELECT id FROM search_reference_files WHERE owner = ?1 AND file = ?2
         )",
        params![owner, file],
    )?;
    connection.execute(
        "DELETE FROM search_reference_files WHERE owner = ?1 AND file = ?2",
        params![owner, file],
    )?;
    Ok(())
}

fn migrate_reference_schema(connection: &Connection) -> Result<bool> {
    let normalized = connection
        .prepare("PRAGMA table_info(search_references)")?
        .query_map([], |row| row.get::<_, String>(1))?
        .collect::<rusqlite::Result<Vec<_>>>()?
        .iter()
        .any(|column| column == "file_id");
    if !normalized {
        connection.execute_batch(
            "DROP INDEX IF EXISTS search_references_target;
             DROP INDEX IF EXISTS search_references_file;
             DROP TABLE IF EXISTS search_references;",
        )?;
    }
    connection.execute_batch(
        "CREATE TABLE IF NOT EXISTS search_reference_files (
            id INTEGER PRIMARY KEY,
            owner TEXT NOT NULL,
            file TEXT NOT NULL,
            source_module TEXT NOT NULL,
            UNIQUE(owner, file)
         );
         CREATE TABLE IF NOT EXISTS search_references (
            file_id INTEGER NOT NULL,
            target TEXT NOT NULL,
            line INTEGER NOT NULL,
            context TEXT
         );
         CREATE INDEX IF NOT EXISTS search_references_target
            ON search_references(target);
         CREATE INDEX IF NOT EXISTS search_references_file
            ON search_references(file_id);",
    )?;
    Ok(!normalized)
}

fn name_contains_candidates(
    connection: &Connection,
    tokens: &[String],
) -> Result<Vec<IndexedRow>> {
    if tokens.is_empty() {
        return Ok(Vec::new());
    }
    let conditions = vec!["name LIKE ? COLLATE NOCASE"; tokens.len()].join(" OR ");
    let sql = format!(
        "SELECT owner, file, module, line, name, kind, signature, docs, body, 0.0
         FROM search_fts WHERE ({conditions})
           AND owner IN (SELECT owner FROM active_search_scopes)
         ORDER BY CASE
           WHEN owner LIKE 'workspace:%' OR owner LIKE 'artifacts:%' THEN 0
           ELSE 1
         END
         LIMIT 128"
    );
    let patterns = tokens
        .iter()
        .map(|token| format!("%{token}%"))
        .collect::<Vec<_>>();
    let mut statement = connection.prepare(&sql)?;
    statement
        .query_map(params_from_iter(&patterns), indexed_row_from_row)?
        .collect::<rusqlite::Result<Vec<_>>>()
        .map_err(Into::into)
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

#[derive(Clone)]
struct CachedSource {
    modified_ns: i64,
    size: u64,
    source: Arc<str>,
    entries: Arc<Vec<SourceEntry>>,
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
            source_cache: Mutex::new(HashMap::new()),
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
        let query = query.trim();
        if let Some(reference) = more_search_reference(query) {
            return self.state.show(reference, true);
        }
        let started = Instant::now();
        let query = normalize_lean_inspection_query(query);
        let expanded = self.expand_reference_query(workspace, &query)?;
        let location = parse_goal_location(
            &workspace.path,
            cwd,
            Some(&self.repo.root),
            &expanded.query,
        )?;
        let show_all = all || (location.is_none() && search_more_requested(&expanded.query));
        let query = strip_search_modifiers(&expanded.query);
        let query = query.as_str();
        ensure!(!query.is_empty(), "search query is empty");
        let reference = self.state.next_ref('q')?;
        let result = if let Some(location) = location {
            self.goal_search(workspace, location)?
        } else if let Some(location) =
            parse_source_occurrence_query(
                &workspace.path,
                cwd,
                Some(&self.repo.root),
                query,
            )?
        {
            source_occurrence_result(workspace, location, show_all)?
        } else {
            let (scopes, base_warming) = match self.index_lock.try_lock() {
                Ok(_guard) => self.refresh(workspace)?,
                Err(std::sync::TryLockError::Poisoned(error)) => {
                    let _guard = error.into_inner();
                    self.refresh(workspace)?
                }
                Err(std::sync::TryLockError::WouldBlock) => {
                    self.current_scopes(workspace)
                }
            };
            self.combined_search(
                workspace,
                query,
                &scopes,
                base_warming,
                expanded.import_target.as_deref(),
                show_all,
            )?
        };
        let mut result = result;
        if !expanded.context.is_empty() {
            result.hits.splice(0..0, expanded.context);
        }
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
        let rendered = if show_all {
            self.state.show(&run.reference, true)
        } else {
            Ok(render_summary(&run))
        }?;
        if ok { Ok(rendered) } else { bail!(rendered) }
    }

    fn expand_reference_query(&self, workspace: &Workspace, query: &str) -> Result<ExpandedQuery> {
        let mut parts = query.splitn(2, char::is_whitespace);
        let reference = parts.next().unwrap_or_default();
        let refinement = parts.next().unwrap_or_default().trim();
        if reference
            .strip_prefix('s')
            .is_some_and(|digits| !digits.is_empty() && digits.chars().all(|c| c.is_ascii_digit()))
        {
            let submission = self
                .state
                .submission(reference)?
                .with_context(|| format!("unknown submission reference {reference}"))?;
            let (subject, context) = self.submission_search_context(&submission, refinement)?;
            return Ok(ExpandedQuery {
                query: [subject.as_str(), refinement]
                    .into_iter()
                    .filter(|part| !part.is_empty())
                    .collect::<Vec<_>>()
                    .join(" "),
                context,
                import_target: None,
            });
        }
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
                return Ok(ExpandedQuery::plain(goal_refinement_query(
                    goal, refinement,
                )));
            }
            let base = if search_refinement_facet(refinement) {
                prior
                    .hits
                    .iter()
                    .find(|hit| !matches!(hit.kind.as_str(), "goal-state" | "diagnostic-context"))
                    .map(|hit| hit.name.as_str())
                    .unwrap_or(&prior.query)
            } else {
                &prior.query
            };
            return Ok(ExpandedQuery::plain(refined_search_query(base, refinement)));
        }
        if reference
            .strip_prefix('c')
            .is_some_and(|digits| !digits.is_empty() && digits.chars().all(|c| c.is_ascii_digit()))
        {
            let repair_requested = refinement
                .split_whitespace()
                .any(|term| term.eq_ignore_ascii_case("repair"));
            let refinement = refinement
                .split_whitespace()
                .filter(|term| !term.eq_ignore_ascii_case("repair"))
                .collect::<Vec<_>>()
                .join(" ");
            let run = self
                .state
                .check_run(reference)?
                .with_context(|| format!("unknown check reference {reference}"))?;
            let diagnostic = run
                .diagnostics
                .first()
                .or_else(|| run.warnings.first())
                .or_else(|| run.suggestions.first());
            let diagnostic_text = diagnostic.map(|value| value.text.as_str()).unwrap_or_default();
            let mut diagnostic_query = diagnostic_search_query(diagnostic_text);
            if diagnostic_text.contains("Invalid field")
                && let Some(nearest) = self.nearest_field_declaration(&diagnostic_query)?
            {
                diagnostic_query = nearest;
            }
            ensure!(
                !diagnostic_query.is_empty() || !refinement.is_empty(),
                "{reference} has no diagnostic to search"
            );
            let target = run
                .failed
                .as_deref()
                .or_else(|| run.files.first().map(String::as_str))
                .map(PathBuf::from);
            let mut context = diagnostic.into_iter().map(|diagnostic| {
                let fallback = target.as_deref().and_then(Path::to_str);
                let (path, line) = diagnostic_position(&diagnostic.text, fallback);
                SearchHit {
                    name: "diagnostic context".into(),
                    kind: "diagnostic-context".into(),
                    signature: None,
                    module: String::new(),
                    path: path.unwrap_or_else(|| {
                        target
                            .as_ref()
                            .map(|path| path.to_string_lossy().into_owned())
                            .unwrap_or_default()
                    }),
                    line,
                    doc: None,
                    source: Some(diagnostic_context(
                        &diagnostic.text,
                        diagnostic.context.as_deref(),
                    )),
                    usages: Vec::new(),
                    applicable: false,
                    required_import: None,
                }
            }).collect::<Vec<_>>();
            if repair_requested
                && diagnostic_text.contains("unsolved goals")
                && run.duration_ms <= DIAGNOSTIC_PROBE_MAX_CHECK_MS
                && let Some(target) = target.as_deref()
            {
                context.extend(self.diagnostic_probe_hits(
                    workspace,
                    target,
                    diagnostic_text,
                ));
            }
            return Ok(ExpandedQuery {
                query: [diagnostic_query.as_str(), refinement.as_str()]
                    .into_iter()
                    .filter(|part| !part.is_empty())
                    .collect::<Vec<_>>()
                    .join(" "),
                context,
                import_target: target.filter(|path| workspace.path.join(path).is_file()),
            });
        }
        Ok(ExpandedQuery::plain(query))
    }

    fn submission_search_context(
        &self,
        submission: &crate::state::Submission,
        refinement: &str,
    ) -> Result<(String, Vec<SearchHit>)> {
        let subject = git_text(
            &self.repo.root,
            &["show", "-s", "--format=%s", &submission.main_commit],
        )?
        .trim()
        .to_owned();
        let changed = git_text(
            &self.repo.root,
            &[
                "diff",
                "--name-only",
                "--diff-filter=ACMR",
                &submission.base_commit,
                &submission.main_commit,
            ],
        )?;
        let mut added = Vec::new();
        for path in changed.lines().filter(|path| path.ends_with(".lean")) {
            let module = project_module_name(&self.repo.root, Path::new(path));
            let before = git_file_at(&self.repo.root, &submission.base_commit, path)?;
            let after = git_file_at(&self.repo.root, &submission.main_commit, path)?
                .with_context(|| format!("submission file unavailable: {path}"))?;
            let prior = before
                .as_deref()
                .map(|source| {
                    parse_source(source, &module)
                        .into_iter()
                        .map(|entry| (entry.name, entry.kind))
                        .collect::<HashSet<_>>()
                })
                .unwrap_or_default();
            added.extend(
                parse_source(&after, &module)
                    .into_iter()
                    .filter(|entry| !matches!(entry.kind.as_str(), "file" | "imports" | "notation"))
                    .filter(|entry| !prior.contains(&(entry.name.clone(), entry.kind.clone())))
                    .map(|entry| (path.to_owned(), module.clone(), entry)),
            );
        }
        let has_public = added
            .iter()
            .any(|(_, _, entry)| !source_entry_is_private(entry));
        let refinement_tokens = meaningful_query_tokens(refinement);
        added.sort_by(|(_, _, left), (_, _, right)| {
            submission_entry_score(right, &refinement_tokens)
                .cmp(&submission_entry_score(left, &refinement_tokens))
        });
        let context = added
            .into_iter()
            .filter(|(_, _, entry)| !has_public || !source_entry_is_private(entry))
            .take(8)
            .map(|(path, module, entry)| SearchHit {
                name: entry.name,
                kind: entry.kind,
                signature: nonempty(entry.signature),
                module,
                path,
                line: entry.line,
                doc: nonempty(entry.docs),
                source: None,
                usages: Vec::new(),
                applicable: false,
                required_import: None,
            })
            .collect();
        Ok((subject, context))
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

    fn diagnostic_probe_hits(
        &self,
        workspace: &Workspace,
        target: &Path,
        diagnostic: &str,
    ) -> Vec<SearchHit> {
        let (_, line) = diagnostic_position(diagnostic, target.to_str());
        let absolute = workspace.path.join(target);
        let Ok(source) = fs::read_to_string(&absolute) else {
            return Vec::new();
        };
        let started = Instant::now();
        let mut suggestions = Vec::new();
        if let Some(probe) = append_goal_tactic(
            &source,
            line,
            "first | exact? | simp? | apply? | rw?",
        ) && let Ok(Some((_, rendered))) = self.checker.probe_source_if_ready(
            workspace,
            &absolute,
            &probe,
            DIAGNOSTIC_PROBE_BUDGET,
        )
        {
            suggestions.extend(try_this_suggestions(&rendered));
        }
        if suggestions.is_empty() {
            for candidate in local_method_candidates(diagnostic).into_iter().take(3) {
                let Some(remaining) = DIAGNOSTIC_PROBE_BUDGET.checked_sub(started.elapsed()) else {
                    break;
                };
                if remaining.is_zero() {
                    break;
                }
                let Some(probe) = append_goal_tactic(&source, line, &candidate) else {
                    break;
                };
                if self
                    .checker
                    .probe_source_if_ready(workspace, &absolute, &probe, remaining)
                    .is_ok_and(|result| result.is_some_and(|(ok, _)| ok))
                {
                    suggestions.push(candidate);
                    break;
                }
            }
        }
        suggestions
            .into_iter()
            .filter(|suggestion| {
                suggestion.len() <= 500
                    && !suggestion
                        .split_whitespace()
                        .any(|term| term == "sorry")
            })
            .take(3)
            .map(|suggestion| SearchHit {
                name: clean_line(&suggestion),
                kind: "diagnostic-repair".into(),
                signature: None,
                module: String::new(),
                path: target.to_string_lossy().into_owned(),
                line,
                doc: Some("verified in the checked file context".into()),
                source: Some(suggestion),
                usages: Vec::new(),
                applicable: true,
                required_import: None,
            })
            .collect()
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
                if development_enabled()
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
        // Daemon generations can overlap briefly during a live upgrade. Keep
        // schema repair and origin-map reconstruction atomic across processes.
        connection.execute_batch("BEGIN IMMEDIATE")?;
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
        if migrate_reference_schema(&connection)? {
            connection.execute("DELETE FROM search_files WHERE kind = 'ilean'", [])?;
        }
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
                 DELETE FROM search_reference_files;
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
                "DELETE FROM search_imports
                 WHERE EXISTS (
                    SELECT 1 FROM search_files
                    WHERE search_files.owner = search_imports.owner
                      AND search_files.path = search_imports.origin
                      AND (search_files.kind = 'source' OR search_files.kind LIKE 'source-v%')
                      AND search_files.kind <> ?1
                 )",
                [SOURCE_INDEX_KIND],
            )?;
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
                "DELETE FROM search_origins
                 WHERE EXISTS (
                    SELECT 1 FROM search_files
                    WHERE search_files.owner = search_origins.owner
                      AND search_files.path = search_origins.origin
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
        let active_workspaces = self
            .state
            .list_workspaces()?
            .into_iter()
            .flat_map(|workspace| {
                [
                    format!("workspace:{}", workspace.reference),
                    format!("artifacts:{}", workspace.reference),
                ]
            })
            .collect::<HashSet<_>>();
        let mut statement = connection.prepare(
            "SELECT owner FROM search_files
             WHERE owner LIKE 'workspace:%' OR owner LIKE 'artifacts:%'
             UNION
             SELECT owner FROM search_reference_files
             WHERE owner LIKE 'workspace:%' OR owner LIKE 'artifacts:%'",
        )?;
        let stale_owners = statement
            .query_map([], |row| row.get::<_, String>(0))?
            .collect::<rusqlite::Result<Vec<_>>>()?
            .into_iter()
            .filter(|owner| !active_workspaces.contains(owner))
            .collect::<Vec<_>>();
        drop(statement);
        for owner in stale_owners {
            connection.execute(
                "DELETE FROM search_references WHERE file_id IN (
                    SELECT id FROM search_reference_files WHERE owner = ?1
                 )",
                [&owner],
            )?;
            connection.execute("DELETE FROM search_reference_files WHERE owner = ?1", [&owner])?;
            connection.execute("DELETE FROM search_fts WHERE owner = ?1", [&owner])?;
            connection.execute("DELETE FROM search_origins WHERE owner = ?1", [&owner])?;
            connection.execute("DELETE FROM search_imports WHERE owner = ?1", [&owner])?;
            connection.execute("DELETE FROM search_files WHERE owner = ?1", [&owner])?;
        }
        connection.execute_batch("COMMIT")?;
        Ok(())
    }

    fn open(&self) -> Result<Connection> {
        let connection = Connection::open(&self.repo.search_db_path)?;
        connection.busy_timeout(std::time::Duration::from_secs(60))?;
        Ok(connection)
    }

    fn refresh(&self, workspace: &Workspace) -> Result<(HashSet<String>, bool)> {
        let roots = vec![SourceRoot {
            owner: format!("workspace:{}", workspace.reference),
            root: workspace.path.clone(),
            kind: SourceKind::Project,
        }];

        let project_artifacts = workspace.path.join(".lake/build/lib/lean");
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
        Ok(self.current_scopes(workspace))
    }

    fn current_scopes(&self, workspace: &Workspace) -> (HashSet<String>, bool) {
        let mut scopes = HashSet::from([format!("workspace:{}", workspace.reference)]);
        if workspace.path.join(".lake/build/lib/lean").is_dir() {
            scopes.insert(format!("artifacts:{}", workspace.reference));
        }
        let (base_scopes, warming) = self.base_scopes(workspace);
        scopes.extend(base_scopes);
        (scopes, warming)
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
                    if development_enabled()
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
            let transaction =
                connection.transaction_with_behavior(rusqlite::TransactionBehavior::Immediate)?;
            let mut next_rowid = Self::next_search_rowid(&transaction)?;
            for path in batch {
                let display =
                    display_path(path, workspace_root, &source_root.root, source_root.kind);
                let module = module_name(path, &source_root.root, source_root.kind);
                let cached = if matches!(source_root.kind, SourceKind::Project) {
                    Some(self.project_source(path, &module)?)
                } else {
                    None
                };
                let source = match &cached {
                    Some(cached) => cached.source.clone(),
                    None => Arc::from(
                        fs::read_to_string(path)
                            .with_context(|| format!("cannot index {}", path.display()))?,
                    ),
                };
                let entries = match &cached {
                    Some(cached) => cached.entries.clone(),
                    None => Arc::new(parse_source(&source, &module)),
                };
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
                            rowid, owner, origin, file, module, line, name, kind, signature, docs, body
                         ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11)",
                    )?;
                    let mut map_origin = transaction.prepare_cached(
                        "INSERT INTO search_origins(rowid, owner, origin)
                         VALUES (?1, ?2, ?3)
                         ON CONFLICT(rowid) DO UPDATE SET
                            owner = excluded.owner, origin = excluded.origin",
                    )?;
                    for entry in entries.iter() {
                        insert.execute(params![
                            next_rowid,
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
                            next_rowid,
                            source_root.owner,
                            path.to_string_lossy(),
                        ])?;
                        next_rowid = next_rowid
                            .checked_add(1)
                            .context("search index rowid overflow")?;
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
            let transaction =
                connection.transaction_with_behavior(rusqlite::TransactionBehavior::Immediate)?;
            let mut next_rowid = Self::next_search_rowid(&transaction)?;
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
                delete_search_references(&transaction, owner, artifact.as_ref())?;
                if let Some(declarations) = value.get("decls").and_then(Value::as_object) {
                    let mut insert = transaction.prepare_cached(
                        "INSERT INTO search_fts(
                            rowid, owner, origin, file, module, line, name, kind, signature, docs, body
                         ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, 'declaration', '', '', '')",
                    )?;
                    let mut map_origin = transaction.prepare_cached(
                        "INSERT INTO search_origins(rowid, owner, origin)
                         VALUES (?1, ?2, ?3)
                         ON CONFLICT(rowid) DO UPDATE SET
                            owner = excluded.owner, origin = excluded.origin",
                    )?;
                    for (name, range) in declarations {
                        let line = range
                            .as_array()
                            .and_then(|range| range.get(4).or_else(|| range.first()))
                            .and_then(Value::as_u64)
                            .unwrap_or(0)
                            + 1;
                        insert.execute(params![
                            next_rowid,
                            owner,
                            artifact,
                            source_path,
                            module,
                            line,
                            name
                        ])?;
                        map_origin.execute(params![next_rowid, owner, artifact])?;
                        next_rowid = next_rowid
                            .checked_add(1)
                            .context("search index rowid overflow")?;
                    }
                }
                if let Some(references) = value.get("references").and_then(Value::as_object) {
                    transaction.execute(
                        "INSERT INTO search_reference_files(owner, file, source_module)
                         VALUES (?1, ?2, ?3)
                         ON CONFLICT(owner, file) DO UPDATE SET
                            source_module = excluded.source_module",
                        params![owner, artifact, module],
                    )?;
                    let file_id = transaction.query_row(
                        "SELECT id FROM search_reference_files
                         WHERE owner = ?1 AND file = ?2",
                        params![owner, artifact],
                        |row| row.get::<_, i64>(0),
                    )?;
                    let mut insert = transaction.prepare_cached(
                        "INSERT INTO search_references(
                            file_id, target, line, context
                         ) VALUES (?1, ?2, ?3, ?4)",
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
                            insert.execute(params![file_id, target, line, context])?;
                        }
                    }
                }
                record_file(&transaction, owner, path, "ilean")?;
            }
            transaction.commit()?;
        }
        Ok(())
    }

    fn next_search_rowid(connection: &Connection) -> Result<i64> {
        connection
            .query_row(
                "SELECT max(
                    coalesce((SELECT max(rowid) FROM search_fts), 0),
                    coalesce((SELECT max(rowid) FROM search_origins), 0)
                 ) + 1",
                [],
                |row| row.get(0),
            )
            .map_err(Into::into)
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
                delete_search_references(&connection, owner, &missing)?;
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
        import_target: Option<&Path>,
        show_all: bool,
    ) -> Result<SearchResult> {
        let search_started = Instant::now();
        let field_inventory = field_inventory_query(query);
        let explicit_declaration = explicit_declaration_name(query);
        let query = explicit_declaration.unwrap_or(query);
        let type_search = type_search_enabled() && type_shaped(query);
        let query_tokens = meaningful_query_tokens(query);
        let import_context = self.import_context(workspace, scopes, base_warming, import_target);
        let import_ms = search_started.elapsed().as_millis() as u64;
        if let Some(structure) = field_inventory
            && let Some(result) = self.field_inventory_result(
                structure,
                scopes,
                workspace,
                import_context.as_ref(),
                base_warming,
            )?
        {
            return Ok(result);
        }
        if !type_search
            && let Some((anchor, refinement_tokens, requested_terms)) = anchored_api_query(query)
        {
            let exact_rows = self.exact_candidates(anchor, scopes)?;
            if exact_rows.is_empty()
                && let Some(mut result) = self.generated_exact_result(
                    workspace,
                    anchor,
                    scopes,
                    import_context.as_ref(),
                    base_warming,
                )?
                && !result.hits.is_empty()
            {
                let exact = result.hits.remove(0);
                let mut hits = vec![exact];
                hits.extend(self.api_neighborhood(
                    &hits[0],
                    scopes,
                    workspace,
                    import_context.as_ref(),
                    &refinement_tokens,
                )?);
                result.hits = hits;
                annotate_missing_hit_terms(&mut result, &requested_terms);
                return Ok(result);
            }
            let exact = ranked_exact_candidates(exact_rows, anchor, workspace);
            if let Some(exact) = resolved_exact_candidates(exact, anchor) {
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
                    &refinement_tokens,
                )?);
                let mut result = exact_search_result(hits, base_warming);
                annotate_missing_hit_terms(&mut result, &requested_terms);
                return Ok(result);
            }
        }
        if !type_search && declaration_name_query(query) {
            let mut exact_query = query.to_owned();
            let mut exact_rows = self.exact_candidates(query, scopes)?;
            if exact_rows.is_empty()
                && let Some(result) = self.generated_exact_result(
                    workspace,
                    query,
                    scopes,
                    import_context.as_ref(),
                    base_warming,
                )?
            {
                return Ok(result);
            }
            let continuations = if exact_rows.is_empty() {
                self.direct_continuations(query, scopes)?
            } else {
                Vec::new()
            };
            if let [continuation] = continuations.as_slice() {
                exact_query = continuation.clone();
                exact_rows = self.exact_candidates(continuation, scopes)?;
            }
            let has_qualified_match = exact_rows
                .iter()
                .any(|row| qualified_name_matches(&row.name, query));
            if !has_qualified_match
                && let Some(base) = declaration_suffix_base(query)
                && continuations.is_empty()
            {
                let base_rows = self.exact_candidates(base, scopes)?;
                if !base_rows.is_empty() {
                    exact_query = base.to_owned();
                    exact_rows = base_rows;
                } else if let Some(mut result) = self.generated_exact_result(
                    workspace,
                    base,
                    scopes,
                    import_context.as_ref(),
                    base_warming,
                )? {
                    let recovery = format!("closest name: {base}");
                    result.note = Some(match result.note {
                        Some(note) => format!("{recovery}; {note}"),
                        None => recovery,
                    });
                    return Ok(result);
                }
            }
            let exact = ranked_exact_candidates(exact_rows, &exact_query, workspace);
            if let Some(exact) = resolved_exact_candidates(exact, &exact_query) {
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
                    &[],
                )?);
                let mut result = exact_search_result(hits, base_warming);
                if exact_query != query {
                    let recovery = format!("closest name: {exact_query}");
                    result.note = Some(match result.note {
                        Some(note) => format!("{recovery}; {note}"),
                        None => recovery,
                    });
                }
                return Ok(result);
            }
        }
        let candidates_started = Instant::now();
        let rows = self.candidates(query, &query_tokens, type_search, scopes)?;
        let candidates_ms = candidates_started.elapsed().as_millis() as u64;
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
            let symbolic_name_score = symbolic_source_term(query)
                .filter(|term| row.name.to_lowercase().contains(term))
                .map_or(0.0, |_| 600.0);
            let score = lexical
                + type_score
                + symbolic_name_score
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
        let project_started = Instant::now();
        ranked.extend(self.project_source_hits(workspace, query, &query_tokens));
        let project_ms = project_started.elapsed().as_millis() as u64;
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
                    &[],
                )?);
                return Ok(exact_search_result(hits, base_warming || warming));
            }
        }
        let resolved_declaration_head = declaration_list_terms(query)
            .and_then(|terms| terms.first().copied())
            .is_some_and(|term| {
                ranked.iter().any(|candidate| {
                    !matches!(candidate.hit.kind.as_str(), "file" | "imports")
                        && qualified_name_matches(&candidate.hit.name, term)
                })
            });
        let missing_specific_term = specific_query_tokens(query).iter().any(|token| {
            !ranked.iter().any(|candidate| {
                !matches!(candidate.hit.kind.as_str(), "file" | "imports")
                    && (text_matches_token(&candidate.hit.name.to_lowercase(), token)
                        || candidate.hit.signature.as_deref().is_some_and(|signature| {
                            text_matches_token(&signature.to_lowercase(), token)
                        })
                        || qualified_leaf_path_match(
                            token,
                            &candidate.hit.name,
                            &candidate.hit.module,
                            &candidate.hit.path,
                        ))
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
                } else if token.contains('.') {
                    name.contains(token)
                        || qualified_leaf_path_match(
                            token,
                            &candidate.hit.name,
                            &candidate.hit.module,
                            &candidate.hit.path,
                        )
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
        let pipe_alternative_covered = query.contains('|')
            && pipe_alternative_covered(query, ranked.iter().map(|candidate| &candidate.hit));
        let fallback_started = Instant::now();
        let mut fallback_used = false;
        if !resolved_declaration_head
            && !warm_name_coverage
            && !pipe_alternative_covered
            && (ranked.len() < 3
                || missing_specific_term
                || missing_source_identifier
                || missing_named_detail
                || symbolic_source_term(query).is_some()
                || (!base_warming
                    && !type_search
                    && (query.contains('|') || !named_argument_terms(query).is_empty())))
        {
            fallback_used = true;
            match fallback_source_hits(&workspace.path, query, &query_tokens) {
                Ok(hits) => ranked.extend(hits),
                Err(error) => append_log(
                    &self.repo,
                    &format!("source fallback unavailable: {error:#}"),
                ),
            }
        }
        let fallback_ms = fallback_started.elapsed().as_millis() as u64;
        let finish_started = Instant::now();
        let glob_name_miss = apply_declaration_glob(&mut ranked, query);
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
        let exact_name_miss = name_search
            && !ranked.iter().any(|candidate| {
                !matches!(candidate.hit.kind.as_str(), "file" | "imports")
                    && qualified_name_matches(&candidate.hit.name, query)
            });
        ranked.truncate(result_limit(exact_name_miss, show_all));
        for candidate in &mut ranked {
            if candidate.hit.usages.is_empty()
                && !matches!(candidate.hit.kind.as_str(), "file" | "imports")
            {
                candidate.hit.usages = self.usages(&candidate.hit.name, scopes, workspace)?;
            }
        }
        let no_hits = ranked.is_empty();
        let dependency_sources_missing = dependency_sources_missing(&workspace.path);
        let mut note = match (base_warming, warming, no_hits && dependency_sources_missing) {
            (_, _, true) => {
                Some("dependency sources unavailable: .lake/packages is missing".into())
            }
            (true, true, _) => Some("source and type indexes warming".into()),
            (true, false, _) => Some("source index warming".into()),
            (false, true, _) => Some("type index warming".into()),
            (false, false, false) => None,
        };
        if glob_name_miss {
            let detail = "related results (no name match)";
            note = Some(match note {
                Some(existing) => format!("{detail}; {existing}"),
                None => detail.into(),
            });
        }
        if exact_name_miss {
            let detail = "related results (no exact match)";
            note = Some(match note {
                Some(existing) => format!("{detail}; {existing}"),
                None => detail.into(),
            });
        }
        let result = SearchResult {
            hits: ranked.into_iter().map(|candidate| candidate.hit).collect(),
            inference: if type_search {
                "hybrid+applicability".into()
            } else if !type_search_enabled() {
                "hybrid(type-off)".into()
            } else {
                "hybrid".into()
            },
            note,
            ok: true,
        };
        let total_ms = search_started.elapsed().as_millis() as u64;
        if total_ms >= 2_000
            && development_enabled()
            && let Ok(store) = TelemetryStore::global()
        {
            let detail = format!(
                "import={import_ms}ms candidates={candidates_ms}ms project={project_ms}ms fallback={fallback_ms}ms used={fallback_used} finish={}ms hits={}",
                finish_started.elapsed().as_millis(),
                result.hits.len(),
            );
            let _ = store.record_operation(
                &self.repo,
                &TelemetryOperation {
                    workspace: Some(&workspace.reference),
                    verb: "search_profile",
                    reference: None,
                    ok: true,
                    duration_ms: total_ms,
                    detail: &detail,
                    rss_kib: None,
                },
            );
        }
        Ok(result)
    }

    fn generated_exact_result(
        &self,
        workspace: &Workspace,
        query: &str,
        scopes: &HashSet<String>,
        import_context: Option<&ImportContext>,
        base_warming: bool,
    ) -> Result<Option<SearchResult>> {
        if let Some(base) = query.strip_suffix(".mk") {
            let structures = self
                .exact_candidates(base, scopes)?
                .into_iter()
                .filter(|row| matches!(row.kind.as_str(), "class" | "structure"))
                .collect::<Vec<_>>();
            if let [row] = structures.as_slice() {
                let tokens = meaningful_query_tokens(query);
                let (source, _) = detailed_source_excerpt(
                    &row.body,
                    query,
                    &tokens,
                    row.line,
                    &row.kind,
                    &row.name,
                );
                let mut resolved = RankedHit {
                    hit: SearchHit {
                        name: format!("{}.mk", row.name),
                        kind: "constructor".into(),
                        signature: nonempty(row.signature.clone()),
                        module: row.module.clone(),
                        path: row.path.clone(),
                        line: row.line,
                        doc: nonempty(row.docs.clone()),
                        source,
                        usages: Vec::new(),
                        applicable: false,
                        required_import: None,
                    },
                    score: 900.0,
                };
                if let Some(context) = import_context {
                    apply_import_context(&mut resolved, context);
                }
                let mut hits = vec![resolved.hit];
                hits.extend(self.api_neighborhood(
                    &hits[0],
                    scopes,
                    workspace,
                    import_context,
                    &[],
                )?);
                return Ok(Some(exact_search_result(hits, base_warming)));
            }
        }
        let name_pattern = format!("\"{}\"", query.replace('"', "\\\""));
        let (mut hits, warming) = self.loogle_hits(workspace, &name_pattern);
        let positions = hits
            .iter()
            .enumerate()
            .filter(|(_, hit)| qualified_name_matches(&hit.name, query))
            .map(|(position, _)| position)
            .collect::<Vec<_>>();
        let [position] = positions.as_slice() else {
            let Some((_, leaf)) = query.rsplit_once('.') else {
                return Ok(None);
            };
            let leaf_pattern = format!("\"{}\"", leaf.replace('"', "\\\""));
            let (leaf_hits, leaf_warming) = self.loogle_hits(workspace, &leaf_pattern);
            let mut leaf_hits = leaf_hits
                .into_iter()
                .filter(|hit| hit.name.rsplit('.').next() == Some(leaf))
                .map(|hit| {
                    let score = qualified_leaf_path_score(
                        query,
                        &hit.name,
                        &hit.module,
                        &format!("{}.lean", hit.module.replace('.', "/")),
                    );
                    (score, hit)
                })
                .collect::<Vec<_>>();
            leaf_hits.sort_by(|(left_score, left), (right_score, right)| {
                right_score
                    .total_cmp(left_score)
                    .then_with(|| left.name.cmp(&right.name))
            });
            let mut related = Vec::new();
            for (_, hit) in leaf_hits.into_iter().take(SUMMARY_LIMIT) {
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
                    score: 0.0,
                };
                self.enrich_exact_source(&mut resolved.hit, scopes)?;
                if let Some(context) = import_context {
                    apply_import_context(&mut resolved, context);
                }
                related.push(resolved.hit);
            }
            if related.is_empty() {
                return Ok(None);
            }
            return Ok(Some(SearchResult {
                hits: related,
                inference: "generated-member".into(),
                note: Some(if base_warming || warming || leaf_warming {
                    "related generated members (no exact match); source index warming".into()
                } else {
                    "related generated members (no exact match)".into()
                }),
                ok: true,
            }));
        };
        let hit = hits.remove(*position);
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
        if let Some(context) = import_context {
            apply_import_context(&mut resolved, context);
        }
        let mut hits = vec![resolved.hit];
        hits.extend(self.api_neighborhood(
            &hits[0],
            scopes,
            workspace,
            import_context,
            &[],
        )?);
        Ok(Some(exact_search_result(
            hits,
            base_warming || warming,
        )))
    }

    fn import_context(
        &self,
        workspace: &Workspace,
        scopes: &HashSet<String>,
        base_warming: bool,
        requested: Option<&Path>,
    ) -> Option<ImportContext> {
        if base_warming {
            return None;
        }
        let dirty = self.dirty_lean_files(workspace)?;
        let nested = dirty
            .iter()
            .filter(|path| path.components().count() > 1)
            .collect::<Vec<_>>();
        let target = requested.or_else(|| {
            if nested.len() == 1 {
                Some(nested[0].as_path())
            } else if dirty.len() == 1 {
                Some(dirty[0].as_path())
            } else {
                None
            }
        })?;
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
               AND owner IN (SELECT owner FROM active_search_scopes)
             ORDER BY CASE
               WHEN owner LIKE 'workspace:%' OR owner LIKE 'artifacts:%' THEN 0
               ELSE 1
             END, bm25(search_fts, 0.0, 0.0, 0.0, 0.0, 0.0, 12.0, 0.0, 7.0, 3.0, 1.0)
             LIMIT 128",
        )?;
        let mut qualified = connection.prepare(
            "SELECT owner, file, module, line, name, kind, signature, docs, body,
                    bm25(search_fts, 0.0, 0.0, 0.0, 0.0, 0.0, 12.0, 0.0, 7.0, 3.0, 1.0)
             FROM search_fts WHERE search_fts MATCH ?1
               AND owner IN (SELECT owner FROM active_search_scopes) LIMIT 256",
        )?;
        let mut exact_leaf = connection.prepare(
            "SELECT owner, file, module, line, name, kind, signature, docs, body, 0.0
             FROM search_fts
             WHERE search_fts MATCH ?1
               AND (lower(name) = lower(?2)
                    OR lower(substr(name, -(length(?2) + 1))) = ('.' || lower(?2)))
               AND owner IN (SELECT owner FROM active_search_scopes)
             ORDER BY CASE WHEN kind = 'file' THEN 1 ELSE 0 END,
                      length(name),
                      CASE
                        WHEN owner LIKE 'workspace:%' OR owner LIKE 'artifacts:%' THEN 0
                        ELSE 1
                      END
             LIMIT 128",
        )?;
        let mut contains_tokens = Vec::new();
        for token in tokens
            .iter()
            .filter(|token| token.len() >= 4 && token.as_str() != "_")
        {
            let exact_query = format!("name : \"{}\"", token.replace('"', "\"\""));
            rows.extend(
                exact_leaf
                    .query_map(params![exact_query, token], indexed_row_from_row)?
                    .collect::<rusqlite::Result<Vec<_>>>()?,
            );
            let name_query = format!("name : \"{}\"*", token.replace('"', "\"\""));
            let named_rows = named
                .query_map([name_query], indexed_row_from_row)?
                .collect::<rusqlite::Result<Vec<_>>>()?;
            let found = !named_rows.is_empty();
            rows.extend(named_rows);
            let compound_query = token.eq_ignore_ascii_case(query)
                && identifier_query_parts(query).len() >= 2;
            if !found
                && !compound_query
                && (token.len() >= 8 || token.contains(['.', '_']))
            {
                contains_tokens.push(token.clone());
            }
        }
        rows.extend(name_contains_candidates(&connection, &contains_tokens)?);
        if name_query && let Some((owner, leaf)) = query.rsplit_once('.')
        {
            let owner = owner.rsplit('.').next().unwrap_or(owner).to_lowercase();
            let namespace_query = format!("name : \"{}\"", owner.replace('"', "\"\""));
            rows.extend(
                qualified
                    .query_map([namespace_query], indexed_row_from_row)?
                    .collect::<rusqlite::Result<Vec<_>>>()?,
            );
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
            if leaf.chars().count() >= 3 {
                let query = format!("name : \"{}\"", leaf.replace('"', "\"\""));
                rows.extend(
                    named
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
               AND (lower(name) = lower(?2)
                    OR lower(substr(name, -(length(?2) + 1))) = ('.' || lower(?2)))
               AND owner IN (SELECT owner FROM active_search_scopes)
             LIMIT 128",
        )?;
        let exact = format!("name : \"{}\"", query.replace('"', "\"\""));
        statement
            .query_map(params![exact, query], indexed_row_from_row)?
            .collect::<rusqlite::Result<Vec<_>>>()
            .map(|rows| {
                rows.into_iter()
                    .filter(|row| qualified_name_matches(&row.name, query))
                    .collect()
            })
            .map_err(anyhow::Error::from)
    }

    fn field_inventory_result(
        &self,
        structure: &str,
        scopes: &HashSet<String>,
        workspace: &Workspace,
        import_context: Option<&ImportContext>,
        base_warming: bool,
    ) -> Result<Option<SearchResult>> {
        let miss = |detail: String| {
            let mut result = exact_search_result(Vec::new(), base_warming);
            result.note = Some(match result.note {
                Some(note) => format!("{detail}; {note}"),
                None => detail,
            });
            result
        };
        let exact = ranked_exact_candidates(
            self.exact_candidates(structure, scopes)?,
            structure,
            workspace,
        );
        let Some(exact) = resolved_exact_candidates(exact, structure) else {
            return Ok(Some(miss(format!(
                "no unique class or structure named {structure}; qualify the name"
            ))));
        };
        let resolved_name = exact
            .first()
            .map(|candidate| candidate.hit.name.clone())
            .unwrap_or_else(|| structure.to_owned());
        let resolved_kind = exact
            .iter()
            .find(|candidate| candidate.hit.kind != "declaration")
            .map(|candidate| candidate.hit.kind.clone())
            .unwrap_or_else(|| "declaration".into());
        let structural = exact
            .into_iter()
            .filter(|candidate| matches!(candidate.hit.kind.as_str(), "class" | "structure"))
            .collect::<Vec<_>>();
        if structural.is_empty() {
            return Ok(Some(miss(format!(
                "{resolved_name} is {resolved_kind}, not a class or structure"
            ))));
        }
        let mut parent = merge_exact_candidates(structural);
        if let Some(context) = import_context {
            apply_import_context(&mut parent, context);
        }
        let indexed_parent_name = parent.hit.name.clone();
        parent.hit.name = canonical_declaration_name(&parent.hit.name).to_owned();

        let connection = self.open()?;
        install_active_scopes(&connection, scopes)?;
        let mut statement = connection.prepare(
            "SELECT owner, file, module, line, name, kind, signature, docs, body, 0.0
             FROM search_fts WHERE search_fts MATCH ?1 AND kind = 'field'
               AND owner IN (SELECT owner FROM active_search_scopes)
             ORDER BY line, name LIMIT 256",
        )?;
        let query = format!(
            "name : \"{}\"*",
            indexed_parent_name.replace('"', "\"\"")
        );
        let prefix = format!("{}.", parent.hit.name);
        let rows = statement
            .query_map([query], indexed_row_from_row)?
            .collect::<rusqlite::Result<Vec<_>>>()?;
        let mut seen = HashSet::new();
        let fields = rows
            .into_iter()
            .filter_map(|mut row| {
                row.name = canonical_declaration_name(&row.name).to_owned();
                (row.module == parent.hit.module
                    && row
                        .name
                        .strip_prefix(&prefix)
                        .is_some_and(|leaf| !leaf.contains('.'))
                    && seen.insert(row.name.clone()))
                .then_some(row)
            })
            .collect::<Vec<_>>();
        if fields.is_empty() {
            return Ok(Some(miss(format!(
                "{} has no indexed fields",
                parent.hit.name
            ))));
        }
        let source = fields
            .iter()
            .map(|field| {
                let leaf = field.name.strip_prefix(&prefix).unwrap_or(&field.name);
                if field.signature.is_empty() {
                    leaf.to_owned()
                } else {
                    format!("{leaf} : {}", field.signature)
                }
            })
            .collect::<Vec<_>>()
            .join("\n");
        let hit = SearchHit {
            name: format!("{} fields", parent.hit.name),
            kind: "fields".into(),
            signature: None,
            module: parent.hit.module,
            path: parent.hit.path,
            line: parent.hit.line,
            doc: parent.hit.doc,
            source: Some(source),
            usages: Vec::new(),
            applicable: false,
            required_import: parent.hit.required_import,
        };
        Ok(Some(exact_search_result(vec![hit], base_warming)))
    }

    fn direct_continuations(
        &self,
        query: &str,
        scopes: &HashSet<String>,
    ) -> Result<Vec<String>> {
        let connection = self.open()?;
        install_active_scopes(&connection, scopes)?;
        let mut statement = connection.prepare(
            "SELECT name FROM search_fts
             WHERE search_fts MATCH ?1
               AND owner IN (SELECT owner FROM active_search_scopes)
             LIMIT 128",
        )?;
        let fts = format!("name : \"{}\"*", query.replace('"', "\"\""));
        let names = statement
            .query_map([fts], |row| row.get::<_, String>(0))?
            .collect::<rusqlite::Result<Vec<_>>>()?;
        let mut names = names
            .into_iter()
            .filter(|name| direct_continuation_name_matches(name, query))
            .collect::<Vec<_>>();
        names.sort();
        names.dedup();
        Ok(names)
    }

    fn api_neighborhood(
        &self,
        exact: &SearchHit,
        scopes: &HashSet<String>,
        workspace: &Workspace,
        import_context: Option<&ImportContext>,
        refinement_tokens: &[String],
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
                let searchable = format!("{} {}", row.name, row.signature).to_lowercase();
                let refinement_score = refinement_tokens
                    .iter()
                    .filter(|token| searchable.contains(token.as_str()))
                    .map(|token| token.chars().count())
                    .sum::<usize>();
                (refinement_score, priority, row)
            })
            .collect::<Vec<_>>();
        ranked.sort_by(
            |(left_score, left_priority, left),
             (right_score, right_priority, right)| {
                right_score
                    .cmp(left_score)
                    .then_with(|| left_priority.cmp(right_priority))
                    .then_with(|| left.name.cmp(&right.name))
            },
        );
        ranked
            .into_iter()
            .take(4)
            .map(|(_, _, row)| {
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
        if hit
            .source
            .as_deref()
            .is_some_and(|source| source.starts_with("-- ambient context"))
            && hit.signature.is_some()
        {
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
        let candidate_has_context = source_hit
            .source
            .as_deref()
            .is_some_and(|source| source.starts_with("-- ambient context"));
        let existing_has_context = hit
            .source
            .as_deref()
            .is_some_and(|source| source.starts_with("-- ambient context"));
        if candidate_has_context && !existing_has_context
            || !hit
                .source
                .as_deref()
                .is_some_and(|source| source_has_complete_declaration_header(hit, source))
                && source_hit.source.as_deref().is_some_and(|source| {
                    source_has_complete_declaration_header(&source_hit, source)
                })
        {
            hit.source = source_hit.source.take();
        }
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
        install_active_scopes(&connection, scopes)?;
        let mut statement = connection.prepare(
            "SELECT files.owner, files.source_module, refs.line, refs.context
             FROM search_references refs
             JOIN search_reference_files files ON files.id = refs.file_id
             WHERE refs.target = ?1
               AND files.owner IN (SELECT owner FROM active_search_scopes)
             ORDER BY (files.owner = ?2) DESC, files.source_module, refs.line
             LIMIT ?3",
        )?;
        let workspace_owner = format!("workspace:{}", workspace.reference);
        let rows = statement.query_map(
            params![name, workspace_owner, SEARCH_USAGE_LIMIT as i64],
            |row| {
                Ok((
                    row.get::<_, String>(0)?,
                    row.get::<_, String>(1)?,
                    row.get::<_, i64>(2)? as u64,
                    row.get::<_, Option<String>>(3)?,
                ))
            },
        )?;
        let mut usages = Vec::new();
        for row in rows {
            let (owner, module, line, context) = row?;
            debug_assert!(scopes.contains(&owner));
            usages.push(SearchUsage {
                path: reference_display_path(&module, workspace),
                module,
                line,
                context,
            });
        }
        Ok(usages)
    }
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

impl Searcher {
    fn project_source(&self, path: &Path, module: &str) -> Result<CachedSource> {
        let metadata = fs::metadata(path)
            .with_context(|| format!("cannot inspect {}", path.display()))?;
        let stamp = modified_ns(&metadata);
        let size = metadata.len();
        let mut cache = self
            .source_cache
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if let Some(cached) = cache.get(path)
            && cached.modified_ns == stamp
            && cached.size == size
        {
            return Ok(cached.clone());
        }
        let source: Arc<str> = fs::read_to_string(path)
            .with_context(|| format!("cannot read {}", path.display()))?
            .into();
        let cached = CachedSource {
            modified_ns: stamp,
            size,
            entries: Arc::new(parse_source(&source, module)),
            source,
        };
        cache.insert(path.to_path_buf(), cached.clone());
        Ok(cached)
    }

    fn project_source_hits(
        &self,
        workspace: &Workspace,
        query: &str,
        query_tokens: &[String],
    ) -> Vec<RankedHit> {
        let Ok(paths) = dirty_lean_files(&workspace.path) else {
            return Vec::new();
        };
        let mut ranked = Vec::new();
        // Dirty source must override the persistent index immediately. Cold clean
        // workspaces use the targeted source fallback while indexing completes.
        for path in paths.into_iter().take(256) {
            let absolute = workspace.path.join(&path);
            let module = project_module_name(&workspace.path, &path);
            let Ok(cached) = self.project_source(&absolute, &module) else {
                continue;
            };
            for entry in cached.entries.iter() {
                let name = entry.name.to_lowercase();
                let searchable =
                    format!("{} {} {}", name, entry.signature, entry.body).to_lowercase();
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
                        name: entry.name.clone(),
                        kind: entry.kind.clone(),
                        signature: nonempty(entry.signature.clone()),
                        module: module.clone(),
                        path: path.to_string_lossy().into_owned(),
                        line,
                        doc: nonempty(entry.docs.clone()),
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

fn git_text(root: &Path, args: &[&str]) -> Result<String> {
    let output = Command::new("git")
        .args(args)
        .current_dir(root)
        .stdin(Stdio::null())
        .output()
        .context("cannot inspect submission commit")?;
    ensure!(
        output.status.success(),
        "cannot inspect submission commit: {}",
        clean_line(&String::from_utf8_lossy(&output.stderr))
    );
    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
}

fn git_file_at(root: &Path, commit: &str, path: &str) -> Result<Option<String>> {
    let spec = format!("{commit}:{path}");
    let output = Command::new("git")
        .args(["show", &spec])
        .current_dir(root)
        .stdin(Stdio::null())
        .output()
        .context("cannot inspect submission source")?;
    Ok(output
        .status
        .success()
        .then(|| String::from_utf8_lossy(&output.stdout).into_owned()))
}

fn render_summary(run: &SearchRun) -> String {
    let mut output = run.reference.clone();
    let proof_body_requested = query_requests_proof_body(&run.query);
    let related_results = run
        .note
        .as_deref()
        .is_some_and(|note| note.contains("related results"));
    if run.hits.is_empty() {
        output.push_str(" no results");
    }
    for (index, hit) in run.hits.iter().take(SUMMARY_LIMIT).enumerate() {
        output.push('\n');
        output.push_str(&hit.name);
        let displayed_source = hit.source.as_deref().filter(|_| {
            !related_results
                && (index == 0
                || (!proof_body_requested
                    && (declaration_leaf_matches(&hit.name, &run.query)
                        || (index < 3
                            && matches!(
                                hit.kind.as_str(),
                                "class" | "inductive" | "structure"
                            )))))
        });
        if let Some(signature) = &hit.signature
            && !displayed_source
                .is_some_and(|source| source_has_complete_declaration_header(hit, source))
        {
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
        if let Some(source) = displayed_source {
            if !matches!(
                hit.kind.as_str(),
                "file"
                    | "fields"
                    | "imports"
                    | "location"
                    | "location-more"
                    | "outline"
                    | "source-occurrences"
                    | "source-range"
            ) {
                output.push_str("\nsource:");
            }
            let source_lines = if index == 0 && proof_body_requested {
                DECLARATION_DETAIL_LINES
            } else {
                match hit.kind.as_str() {
                    "class" | "inductive" | "structure" => 16,
                    "fields" => SOURCE_OCCURRENCE_ALL_LIMIT,
                    "imports" => 64,
                    "outline" => OUTLINE_PREVIEW_LINES,
                    "location" => LOCATION_PREVIEW_LINES,
                    "location-more" => LOCATION_MORE_LINES,
                    "diagnostic-context" => source.lines().count(),
                    "source-range" => SOURCE_OCCURRENCE_ALL_LIMIT,
                    "source-occurrences" => SOURCE_OCCURRENCE_LIMIT,
                    _ => SOURCE_PREVIEW_LINES,
                }
            };
            for line in source.lines().take(source_lines) {
                output.push('\n');
                if hit.kind == "diagnostic-context" {
                    output.push_str(line.trim_end());
                } else {
                    output.push_str(&truncate_line(line.trim_end(), 200));
                }
            }
            let omitted = source.lines().count().saturating_sub(source_lines);
            if omitted > 0 {
                match hit.kind.as_str() {
                    "class" | "structure" => output.push_str(&format!(
                        "\n+{omitted} lines; search {} fields",
                        hit.name
                    )),
                    "outline" => output.push_str(&format!(
                        "\n+{omitted} declarations; show {} --all",
                        run.reference
                    )),
                    _ => {}
                }
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

fn source_has_complete_declaration_header(hit: &SearchHit, source: &str) -> bool {
    let Some(leaf) = hit.name.rsplit('.').next() else {
        return false;
    };
    let declaration = source.lines().skip_while(|line| {
        let line = line.trim_start();
        !line.contains(leaf) || !line.split_whitespace().any(|word| word == hit.kind)
    });
    let header = declaration.collect::<Vec<_>>().join("\n");
    if header.is_empty() {
        return false;
    }
    header.contains(":=")
        || matches!(hit.kind.as_str(), "class" | "inductive" | "instance" | "structure")
            && header.split_whitespace().any(|word| word == "where")
}
