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

mod api;
mod source_query;
mod plan;
mod probe;
mod query;
mod source;
mod tuning;
#[cfg(test)]
mod tests;

use source_query::*;
use api::*;
use plan::*;
use query::*;
use source::*;
use tuning::*;

const RESULT_LIMIT: usize = SEARCH_TUNING.presentation.result_limit;
const SUMMARY_LIMIT: usize = SEARCH_TUNING.presentation.summary_limit;
const LOCATION_PREVIEW_LINES: usize = 32;
const LOCATION_EXPANDED_LINES: usize = 96;
const SOURCE_OCCURRENCE_LIMIT: usize = 64;
const SOURCE_RANGE_LIMIT: usize = 120;
const SOURCE_RANGE_ALL_LIMIT: usize = SEARCH_TUNING.presentation.source_range_all_lines;
const SOURCE_OCCURRENCE_ALL_LIMIT: usize = 200;
const OUTLINE_PREVIEW_LINES: usize = 64;
const OUTLINE_LINE_CHARS: usize = 120;
const RELATED_RESULT_LIMIT: usize = SEARCH_TUNING.presentation.related_result_limit;
const SEARCH_INDEX_VERSION: i64 = 7;
const SOURCE_INDEX_KIND: &str = "source-v12";
const DECLARATION_DETAIL_LINES: usize = SEARCH_TUNING.presentation.declaration_detail_lines;
const INDEX_COMMIT_BATCH: usize = 64;
const SEARCH_REFRESH_INTERVAL: std::time::Duration = std::time::Duration::from_millis(500);
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
    auxiliary_query: Option<String>,
}

impl ExpandedQuery {
    fn plain(query: impl Into<String>) -> Self {
        Self {
            query: query.into(),
            context: Vec::new(),
            import_target: None,
            auxiliary_query: None,
        }
    }
}

#[derive(Debug)]
struct Candidate {
    hit: SearchHit,
    score: f64,
    origins: u8,
}

#[derive(Clone, Copy)]
enum CandidateOrigin {
    Index = 1,
    Loogle = 2,
    ProjectSource = 4,
    FallbackSource = 8,
}

struct ImportContext {
    accessible: HashSet<String>,
    complete: bool,
}

struct TextSearchContext<'a> {
    scopes: &'a HashSet<String>,
    base_warming: bool,
    import_target: Option<&'a Path>,
    show_all: bool,
}

struct ExactPlan {
    anchor: String,
    refinement_tokens: Vec<String>,
    requested_terms: Vec<String>,
    recover_continuation: bool,
}

struct ExactMatch {
    candidate: Candidate,
    matched: String,
    warming: bool,
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

fn compact_ranked_hit(row: IndexedRow) -> Candidate {
    Candidate {
        hit: SearchHit {
            name: row.name,
            kind: row.kind,
            signature: nonempty(row.signature),
            module: row.module,
            path: row.path,
            line: row.line,
            doc: nonempty(row.docs),
            source: None,
            usages: Vec::new(),
            applicable: false,
            required_import: None,
        },
        score: 0.0,
        origins: CandidateOrigin::Index as u8,
    }
}

fn indexed_candidate(
    row: IndexedRow,
    query: &str,
    query_tokens: &[String],
    score: f64,
) -> Candidate {
    let (source, line) = detailed_source_excerpt(
        &row.body,
        query,
        query_tokens,
        row.line,
        &row.kind,
        &row.name,
    );
    Candidate {
        hit: SearchHit {
            name: row.name,
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
        },
        score,
        origins: CandidateOrigin::Index as u8,
    }
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

fn ensure_reference_schema(connection: &Connection) -> Result<bool> {
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
    let sql = indexed_rows_sql(&format!(
        "WHERE ({conditions})
         AND owner IN (SELECT owner FROM active_search_scopes)
         ORDER BY CASE
           WHEN owner LIKE 'workspace:%' OR owner LIKE 'artifacts:%' THEN 0
           ELSE 1
         END
         LIMIT {limit}",
        conditions = conditions,
        limit = SEARCH_TUNING.retrieval.name_contains_rows,
    ));
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

fn module_context_candidates(
    connection: &Connection,
    query: &str,
    tokens: &[String],
    rows: &[IndexedRow],
) -> Result<Vec<IndexedRow>> {
    if tokens.len() < 2 {
        return Ok(Vec::new());
    }
    let mut modules = rows
        .iter()
        .filter(|row| !matches!(row.kind.as_str(), "file" | "imports"))
        .map(|row| (lexical_score(query, tokens, row), row.module.clone()))
        .filter(|(score, module)| *score > 0.0 && !module.is_empty())
        .collect::<Vec<_>>();
    modules.sort_by(|left, right| right.0.total_cmp(&left.0));
    let mut seen = HashSet::new();
    modules.retain(|(_, module)| seen.insert(module.clone()));
    modules.truncate(SEARCH_TUNING.retrieval.module_count);
    if modules.is_empty() {
        return Ok(Vec::new());
    }
    let placeholders = (2..=modules.len() + 1)
        .map(|index| format!("?{index}"))
        .collect::<Vec<_>>()
        .join(", ");
    let sql = ranked_rows_sql(&format!(
        "WHERE search_fts MATCH ?1 AND module IN ({placeholders})
         AND owner IN (SELECT owner FROM active_search_scopes)
         LIMIT {limit}",
        placeholders = placeholders,
        limit = SEARCH_TUNING.retrieval.module_rows,
    ));
    let mut parameters = vec![fts_query(&tokens.join(" "))];
    parameters.extend(modules.into_iter().map(|(_, module)| module));
    connection
        .prepare(&sql)?
        .query_map(params_from_iter(&parameters), indexed_row_from_row)?
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
        limit: Option<usize>,
        all: bool,
    ) -> Result<String> {
        reject_colon_attached_source_facet(query)?;
        let request = SearchRequest::parse(query, limit, all)?;
        let started = Instant::now();
        let requested_query = request.displayed_query.clone();
        let (query, forced_plan, exact_names) = match &request.expression {
            SearchExpression::ExactNames(names) => (names[0].clone(), Some(TextSearchPlan::ExactFirst), Some(names)),
            SearchExpression::Type(pattern) => (pattern.clone(), Some(TextSearchPlan::ForcedType), None),
            SearchExpression::Regex(query) | SearchExpression::Query(query) => (query.clone(), None, None),
        };
        let expanded = self.expand_reference_query(&query)?;
        let planned = plan_search(
            workspace,
            cwd,
            &self.repo.root,
            &expanded.query,
            !expanded.context.is_empty(),
        )?;
        let source_show_all = request.all;
        let query = planned.query.as_str();
        let reference = self.state.next_ref('q')?;
        let result = if let Some(names) = exact_names {
            self.exact_name_batch(workspace, names, request.all)?
        } else { match planned.plan {
            SearchPlan::StoredContext => SearchResult {
                hits: Vec::new(),
                inference: "stored-context".into(),
                note: Some("stored context only; declaration search skipped".into()),
                ok: true,
            },
            SearchPlan::Location(mut location) => {
                location.expanded = request.all;
                self.source_location_search(workspace, location)?
            }
            SearchPlan::SourceRegex(source) => {
                source_regex_result(workspace, source, source_show_all)?
            }
            SearchPlan::Source(source) => {
                if source.terms.len() == 1 && source.terms[0].eq_ignore_ascii_case("dependents") {
                    self.source_dependents(workspace, &source)?
                } else {
                    source_occurrence_result(workspace, source, source_show_all)?
                }
            }
            SearchPlan::Text(text_plan) => self.planned_text_search(
                workspace,
                query,
                forced_plan.unwrap_or(text_plan),
                expanded.import_target.as_deref(),
                expanded.auxiliary_query.as_deref(),
                request.all,
            )?,
        }};
        let mut result = result;
        if !expanded.context.is_empty() && requested_query.split_whitespace().count() == 1 {
            suppress_inferred_missing_note(&mut result.note);
        }
        if !expanded.context.is_empty() {
            result.hits.splice(0..0, expanded.context);
        }
        if let Some(limit) = request.limit {
            result.hits.truncate(limit);
        }
        let run = SearchRun {
            reference: reference.clone(),
            workspace_ref: workspace.reference.clone(),
            query: if query.is_empty() {
                requested_query
            } else {
                query.to_owned()
            },
            inference: result.inference,
            hits: result.hits,
            note: result.note,
            duration_ms: started.elapsed().as_millis() as u64,
            created_at: now_unix_ms(),
        };
        let ok = result.ok;
        self.state.add_search(&run)?;
        self.state.touch_workspace(&workspace.reference)?;
        let rendered = if request.all {
            self.state.show(&run.reference, true)
        } else {
            Ok(render_summary(&run))
        }?;
        if ok { Ok(rendered) } else { bail!(rendered) }
    }

    fn exact_name_batch(
        &self,
        workspace: &Workspace,
        names: &[String],
        all: bool,
    ) -> Result<SearchResult> {
        let mut hits = Vec::new();
        let mut missing = Vec::new();
        let mut warming = false;
        for name in names {
            let result = self.planned_text_search(
                workspace,
                name,
                TextSearchPlan::ExactFirst,
                None,
                None,
                all,
            )?;
            warming |= result.note.as_deref().is_some_and(|note| note.contains("warming"));
            if let Some(hit) = result.hits.into_iter().find(|hit| qualified_name_matches(&hit.name, name)) {
                hits.push(hit);
            } else {
                missing.push(name.clone());
            }
        }
        Ok(SearchResult {
            hits,
            inference: "exact-batch".into(),
            note: (!missing.is_empty()).then(|| format!("not found: {}", missing.join(", ")))
                .or_else(|| warming.then(|| "search indexes warming".into())),
            ok: missing.is_empty(),
        })
    }

    fn source_dependents(
        &self,
        workspace: &Workspace,
        query: &SourceOccurrenceQuery,
    ) -> Result<SearchResult> {
        let relative = query.path.strip_prefix(&workspace.path).unwrap_or(&query.path);
        let module = project_module_name(&workspace.path, relative);
        let (scopes, warming) = self.search_scopes(workspace)?;
        let connection = self.open()?;
        install_active_scopes(&connection, &scopes)?;
        let mut statement = connection.prepare(
            "SELECT DISTINCT search_imports.origin, search_imports.module
             FROM search_imports
             JOIN active_search_scopes ON active_search_scopes.owner = search_imports.owner
             WHERE search_imports.imported = ?1
             ORDER BY search_imports.module, search_imports.origin",
        )?;
        let rows = statement.query_map([&module], |row| {
            Ok((row.get::<_, String>(0)?, row.get::<_, String>(1)?))
        })?;
        let mut hits = Vec::new();
        for row in rows {
            let (path, dependent) = row?;
            hits.push(SearchHit {
                name: dependent.clone(),
                kind: "dependent".into(),
                signature: Some(format!("imports {module}")),
                module: dependent,
                path,
                line: 1,
                doc: None,
                source: None,
                usages: Vec::new(),
                applicable: false,
                required_import: None,
            });
        }
        Ok(SearchResult {
            note: if warming {
                Some("source index warming".into())
            } else if hits.is_empty() {
                Some("no indexed dependents".into())
            } else {
                None
            },
            hits,
            inference: "dependents".into(),
            ok: true,
        })
    }

    fn expand_reference_query(&self, query: &str) -> Result<ExpandedQuery> {
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
            require_submission_refinement(reference, refinement)?;
            let (subject, context) = self.submission_search_context(&submission, refinement)?;
            return Ok(ExpandedQuery {
                query: [subject.as_str(), refinement]
                    .into_iter()
                    .filter(|part| !part.is_empty())
                    .collect::<Vec<_>>()
                    .join(" "),
                context,
                import_target: None,
                auxiliary_query: None,
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
            let base = if search_refinement_facet(refinement) {
                prior
                    .hits
                    .first()
                    .map(|hit| hit.name.as_str())
                    .unwrap_or(&prior.query)
            } else {
                &prior.query
            };
            return Ok(ExpandedQuery::plain(refined_search_query(base, refinement)));
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

    fn loogle_hits(
        &self,
        workspace: &Workspace,
        query: &str,
        accept_suggestions: bool,
    ) -> (Vec<LoogleHit>, bool, Option<String>) {
        self.loogle_hits_with_suggestions(workspace, query, accept_suggestions)
    }

    fn loogle_exact_name_hits(
        &self,
        workspace: &Workspace,
        query: &str,
    ) -> (Vec<LoogleHit>, bool, Option<String>) {
        self.loogle_hits_with_suggestions(workspace, query, false)
    }

    fn loogle_hits_with_suggestions(
        &self,
        workspace: &Workspace,
        query: &str,
        accept_suggestions: bool,
    ) -> (Vec<LoogleHit>, bool, Option<String>) {
        if !type_search_enabled() || !workspace.path.join(".lake/packages/mathlib").is_dir() {
            return (Vec::new(), false, None);
        }
        let mut state = match self.loogle.try_lock() {
            Ok(state) => state,
            Err(std::sync::TryLockError::Poisoned(error)) => error.into_inner(),
            Err(std::sync::TryLockError::WouldBlock) => return (Vec::new(), true, None),
        };
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
            return (Vec::new(), true, None);
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
                Err(std::sync::mpsc::TryRecvError::Empty) => return (Vec::new(), true, None),
            }
        }
        let LoogleState::Running(worker) = &mut *state else {
            return (Vec::new(), false, None);
        };
        match worker.query(query, accept_suggestions) {
            Ok((hits, error)) => (hits, false, error),
            Err(error) => {
                append_log(&self.repo, &format!("Loogle query failed: {error:#}"));
                *state = LoogleState::Unavailable;
                (Vec::new(), false, None)
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
        if ensure_reference_schema(&connection)? {
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

    fn search_scopes(&self, workspace: &Workspace) -> Result<(HashSet<String>, bool)> {
        match self.index_lock.try_lock() {
            Ok(_guard) => self.refresh(workspace),
            Err(std::sync::TryLockError::Poisoned(error)) => {
                let _guard = error.into_inner();
                self.refresh(workspace)
            }
            Err(std::sync::TryLockError::WouldBlock) => Ok(self.current_scopes(workspace)),
        }
    }

    fn planned_text_search(
        &self,
        workspace: &Workspace,
        query: &str,
        plan: TextSearchPlan,
        import_target: Option<&Path>,
        auxiliary_query: Option<&str>,
        show_all: bool,
    ) -> Result<SearchResult> {
        let (scopes, base_warming) = self.search_scopes(workspace)?;
        let mut result = self.execute_text_search(
            workspace,
            query,
            plan,
            TextSearchContext {
                scopes: &scopes,
                base_warming,
                import_target,
                show_all,
            },
        )?;
        if let Some(auxiliary_query) = auxiliary_query {
            let existing = result
                .hits
                .iter()
                .map(|hit| hit.name.clone())
                .collect::<HashSet<_>>();
            let hints = self
                .execute_text_search(
                    workspace,
                    auxiliary_query,
                    text_search_plan(auxiliary_query),
                    TextSearchContext {
                        scopes: &scopes,
                        base_warming,
                        import_target,
                        show_all: false,
                    },
                )?
                .hits
                .into_iter()
                .filter(|hit| {
                    hit.name
                        .rsplit('.')
                        .next()
                        .is_some_and(|leaf| leaf.eq_ignore_ascii_case(auxiliary_query))
                        && !existing.contains(&hit.name)
                })
                .take(3)
                .collect::<Vec<_>>();
            result.hits.splice(0..0, hints);
        }
        Ok(result)
    }

    fn execute_text_search(
        &self,
        workspace: &Workspace,
        query: &str,
        plan: TextSearchPlan,
        context: TextSearchContext<'_>,
    ) -> Result<SearchResult> {
        let TextSearchContext {
            scopes,
            base_warming,
            import_target,
            show_all,
        } = context;
        let search_started = Instant::now();
        let field_inventory = field_inventory_query(query);
        let explicit_declaration = explicit_declaration_name(query);
        let query = explicit_declaration.unwrap_or(query);
        let type_search = matches!(plan, TextSearchPlan::Type | TextSearchPlan::ForcedType);
        let strict_type = matches!(plan, TextSearchPlan::ForcedType);
        let query_tokens = meaningful_query_tokens(query);
        let import_context = self.import_context(workspace, scopes, base_warming, import_target);
        let import_ms = search_started.elapsed().as_millis() as u64;
        if matches!(plan, TextSearchPlan::ExactFirst)
            && let Some(structure) = field_inventory
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
        if !matches!(plan, TextSearchPlan::Discovery)
            && let Some(plan) = exact_plan(query, type_search)
            && let Some(result) = self.resolve_exact(
                workspace,
                scopes,
                import_context.as_ref(),
                base_warming,
                &plan,
            )?
        {
            return Ok(result);
        }
        let candidates_started = Instant::now();
        let rows = self.candidates(query, &query_tokens, type_search, scopes)?;
        let candidates_ms = candidates_started.elapsed().as_millis() as u64;
        let name_search = !type_search && declaration_name_query(query);
        let mut ranked = Vec::new();
        let mut warming = false;
        let loogle_started = Instant::now();
        if type_search {
            let explicit_conclusion = conclusion_query(query);
            let applicability_query = if explicit_conclusion {
                query.to_owned()
            } else {
                format!("⊢ {query}")
            };
            let (applicable_hits, applicable_warming, applicable_error) =
                self.loogle_hits(workspace, &applicability_query, !strict_type);
            if strict_type && let Some(error) = applicable_error {
                bail!("invalid type pattern: {}", clean_line(&error));
            }
            warming |= applicable_warming;
            let has_full_applicability_page = applicable_hits.len() >= RESULT_LIMIT;
            let applicable = self.ranked_loogle_hits(
                applicable_hits,
                scopes,
                workspace,
                true,
                SEARCH_TUNING.type_score.loogle_applicable,
            )?;
            ranked.extend(applicable);
            if !explicit_conclusion && !has_full_applicability_page {
                let (loogle_hits, is_warming, related_error) =
                    self.loogle_hits(workspace, query, !strict_type);
                if strict_type && let Some(error) = related_error {
                    bail!("invalid type pattern: {}", clean_line(&error));
                }
                warming |= is_warming;
                let loogle = self.ranked_loogle_hits(
                    loogle_hits,
                    scopes,
                    workspace,
                    false,
                    SEARCH_TUNING.type_score.loogle_related,
                )?;
                ranked.extend(loogle);
            }
        }
        let loogle_ms = loogle_started.elapsed().as_millis() as u64;
        let ranking_started = Instant::now();
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
            let symbolic_name_score = symbolic_source_term(query)
                .filter(|term| row.name.to_lowercase().contains(term))
                .map_or(0.0, |_| SEARCH_TUNING.lexical.symbolic_name);
            let score = lexical
                + type_score
                + symbolic_name_score
                + if row.owner == format!("workspace:{}", workspace.reference) {
                    SEARCH_TUNING.lexical.workspace
                } else {
                    0.0
                }
                - row.rank.max(0.0);
            ranked.push(indexed_candidate(row, query, &query_tokens, score));
        }
        let ranking_ms = ranking_started.elapsed().as_millis() as u64;
        let project_started = Instant::now();
        let project = self.project_source_hits(workspace, query, &query_tokens);
        ranked.extend(project);
        let project_ms = project_started.elapsed().as_millis() as u64;
        if name_search
            && let Some(exact_name) = unique_qualified_hit_name(
                ranked
                    .iter()
                    .map(|candidate| &candidate.hit)
                    .filter(|hit| !matches!(hit.kind.as_str(), "file" | "imports")),
                query,
            )
        {
            let candidate = merge_exact_candidates(
                ranked
                    .into_iter()
                    .filter(|candidate| candidate.hit.name.to_lowercase() == exact_name)
                    .collect(),
            );
            return self.finish_exact(
                ExactMatch {
                    candidate,
                    matched: query.to_owned(),
                    warming,
                },
                &exact_plan(query, false).expect("name queries have an exact plan"),
                workspace,
                scopes,
                import_context.as_ref(),
                base_warming,
            );
        }
        let fallback_started = Instant::now();
        let mut fallback_used = false;
        if base_warming
            || symbolic_source_term(query).is_some()
            || !named_argument_terms(query).is_empty()
        {
            fallback_used = true;
            match fallback_source_candidates(&workspace.path, query, &query_tokens) {
                Ok(hits) => ranked.extend(hits),
                Err(error) => append_log(
                    &self.repo,
                    &format!("source fallback unavailable: {error:#}"),
                ),
            }
        }
        let fallback_ms = fallback_started.elapsed().as_millis() as u64;
        let finish_started = Instant::now();
        let (mut ranked, glob_name_miss) = rank_discovery_candidates(
            ranked,
            query,
            &query_tokens,
            explicit_declaration.is_some(),
            import_context.as_ref(),
        );
        let exact_name_miss = name_search
            && !ranked.iter().any(|candidate| {
                !matches!(candidate.hit.kind.as_str(), "file" | "imports")
                    && qualified_name_matches(&candidate.hit.name, query)
            });
        ranked.truncate(result_limit(exact_name_miss, show_all));
        let fallback_top = ranked
            .iter()
            .filter(|candidate| candidate.origins & CandidateOrigin::FallbackSource as u8 != 0)
            .count();
        let fallback_unique_top = ranked
            .iter()
            .filter(|candidate| candidate.origins == CandidateOrigin::FallbackSource as u8)
            .count();
        if exact_name_miss {
            // A near declaration-name match should be useful without a follow-up
            // source-range read. Keep this bounded: summaries show these three
            // signatures, while ambiguous related source bodies stay hidden.
            for candidate in ranked
                .iter_mut()
                .take(SEARCH_TUNING.promotion.exact_source_enrichment)
            {
                self.enrich_exact_source(&mut candidate.hit, scopes)?;
            }
        }
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
            prepend_search_note(&mut note, "no name match".into());
        }
        if exact_name_miss {
            prepend_search_note(&mut note, "related results (no exact match)".into());
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
        let finish_ms = finish_started.elapsed().as_millis() as u64;
        let accounted_ms = import_ms
            + candidates_ms
            + loogle_ms
            + ranking_ms
            + project_ms
            + fallback_ms
            + finish_ms;
        let unaccounted_ms = total_ms.saturating_sub(accounted_ms);
        let sampled_fallback = fallback_used
            && query.bytes().fold(0_u8, |hash, byte| {
                hash.wrapping_mul(31).wrapping_add(byte)
            }) % 8 == 0;
        if (total_ms >= 2_000 || sampled_fallback)
            && development_enabled()
            && let Ok(store) = TelemetryStore::global()
        {
            let detail = format!(
                "import={import_ms}ms candidates={candidates_ms}ms loogle={loogle_ms}ms rank={ranking_ms}ms project={project_ms}ms fallback={fallback_ms}ms used={fallback_used} top={fallback_top} unique_top={fallback_unique_top} finish={finish_ms}ms other={unaccounted_ms}ms hits={}",
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

    fn ranked_loogle_hits(
        &self,
        hits: Vec<LoogleHit>,
        scopes: &HashSet<String>,
        workspace: &Workspace,
        applicable: bool,
        base_score: f64,
    ) -> Result<Vec<Candidate>> {
        hits.into_iter()
            .enumerate()
            .map(|(position, hit)| {
                let usages = self.usages(&hit.name, scopes, workspace)?;
                Ok(Candidate {
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
                        applicable,
                        required_import: None,
                    },
                    score: base_score - position as f64,
                    origins: CandidateOrigin::Loogle as u8,
                })
            })
            .collect()
    }

    fn resolve_exact(
        &self,
        workspace: &Workspace,
        scopes: &HashSet<String>,
        import_context: Option<&ImportContext>,
        base_warming: bool,
        plan: &ExactPlan,
    ) -> Result<Option<SearchResult>> {
        let mut names = vec![plan.anchor.clone()];
        if let Some(base) = declaration_predicate_base(&plan.anchor) {
            names.push(base);
        }
        if plan.recover_continuation {
            let continuations = self.direct_continuations(&plan.anchor, scopes)?;
            if let [continuation] = continuations.as_slice() {
                names.push(continuation.clone());
            }
        }
        if let Some(base) = declaration_suffix_base(&plan.anchor) {
            names.push(base.to_owned());
        }
        names.dedup();

        for name in names {
            let rows = self.exact_candidates(&name, scopes)?;
            let ranked = ranked_exact_candidates(rows, &name, workspace);
            let matched = if let Some(candidates) = resolved_exact_candidates(ranked, &name) {
                Some(ExactMatch {
                    candidate: merge_exact_candidates(candidates),
                    matched: name.clone(),
                    warming: false,
                })
            } else {
                self.generated_exact_match(workspace, &name, scopes)?
            };
            if let Some(matched) = matched {
                return self
                    .finish_exact(
                        matched,
                        plan,
                        workspace,
                        scopes,
                        import_context,
                        base_warming,
                    )
                    .map(Some);
            }
        }
        Ok(None)
    }

    fn finish_exact(
        &self,
        mut matched: ExactMatch,
        plan: &ExactPlan,
        workspace: &Workspace,
        scopes: &HashSet<String>,
        import_context: Option<&ImportContext>,
        base_warming: bool,
    ) -> Result<SearchResult> {
        self.enrich_exact_source(&mut matched.candidate.hit, scopes)?;
        if matched.candidate.hit.usages.is_empty() {
            matched.candidate.hit.usages =
                self.usages(&matched.candidate.hit.name, scopes, workspace)?;
        }
        if let Some(context) = import_context {
            apply_import_context(&mut matched.candidate, context);
        }
        let mut hits = vec![matched.candidate.hit];
        hits.extend(self.context_pack(
            &hits[0],
            scopes,
            workspace,
            import_context,
            &plan.refinement_tokens,
        )?);
        let mut result = exact_search_result(hits, base_warming || matched.warming);
        annotate_missing_hit_terms(&mut result, &plan.requested_terms);
        if matched.matched != plan.anchor {
            prepend_search_note(
                &mut result.note,
                format!("closest name: {}", matched.matched),
            );
        }
        Ok(result)
    }

    fn generated_exact_match(
        &self,
        workspace: &Workspace,
        query: &str,
        scopes: &HashSet<String>,
    ) -> Result<Option<ExactMatch>> {
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
                return Ok(Some(ExactMatch {
                    candidate: Candidate {
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
                        score: SEARCH_TUNING.lexical.exact_resolution,
                        origins: CandidateOrigin::Index as u8,
                    },
                    matched: query.to_owned(),
                    warming: false,
                }));
            }
        }
        let name_pattern = format!("\"{}\"", query.replace('"', "\\\""));
        let (mut hits, warming, _) = self.loogle_exact_name_hits(workspace, &name_pattern);
        let positions = hits
            .iter()
            .enumerate()
            .filter(|(_, hit)| qualified_name_matches(&hit.name, query))
            .map(|(position, _)| position)
            .collect::<Vec<_>>();
        let [position] = positions.as_slice() else {
            return Ok(None);
        };
        let hit = hits.remove(*position);
        Ok(Some(ExactMatch {
            candidate: Candidate {
                hit: SearchHit {
                    path: format!("{}.lean", hit.module.replace('.', "/")),
                    line: 1,
                    kind: "declaration".into(),
                    signature: nonempty(hit.signature),
                    doc: hit.doc,
                    source: None,
                    usages: Vec::new(),
                    name: hit.name,
                    module: hit.module,
                    applicable: false,
                    required_import: None,
                },
                score: SEARCH_TUNING.lexical.exact_resolution,
                origins: CandidateOrigin::Loogle as u8,
            },
            matched: query.to_owned(),
            warming,
        }))
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
            indexed_rows_sql(&format!(
                "WHERE signature <> ''
                 AND owner IN (SELECT owner FROM active_search_scopes) LIMIT {}",
                SEARCH_TUNING.retrieval.type_rows
            ))
        } else if name_query {
            ranked_rows_sql(&format!(
                "WHERE search_fts MATCH ?1
                 AND owner IN (SELECT owner FROM active_search_scopes) LIMIT {}",
                SEARCH_TUNING.retrieval.name_query_rows
            ))
        } else {
            ranked_rows_sql(&format!(
                "WHERE search_fts MATCH ?1
                 AND owner IN (SELECT owner FROM active_search_scopes) LIMIT {}",
                SEARCH_TUNING.retrieval.discovery_rows
            ))
        };
        let mut statement = connection.prepare(&sql)?;
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
        if let Some(glob_query) = declaration_glob_fts_query(query) {
            let sql = ranked_rows_sql(&format!(
                "WHERE search_fts MATCH ?1
                 AND owner IN (SELECT owner FROM active_search_scopes) LIMIT {}",
                SEARCH_TUNING.retrieval.discovery_rows
            ));
            rows.extend(
                connection
                    .prepare(&sql)?
                    .query_map([glob_query], indexed_row_from_row)?
                    .collect::<rusqlite::Result<Vec<_>>>()?,
            );
        }
        let named_sql = ranked_rows_sql(&format!(
            "WHERE search_fts MATCH ?1
             AND owner IN (SELECT owner FROM active_search_scopes)
             ORDER BY CASE
               WHEN owner LIKE 'workspace:%' OR owner LIKE 'artifacts:%' THEN 0
               ELSE 1
             END, {}
             LIMIT {}",
            fts_rank_sql(),
            SEARCH_TUNING.retrieval.name_rows,
        ));
        let mut named = connection.prepare(&named_sql)?;
        let qualified_sql = ranked_rows_sql(&format!(
            "WHERE search_fts MATCH ?1
             AND owner IN (SELECT owner FROM active_search_scopes) LIMIT {}",
            SEARCH_TUNING.retrieval.qualified_rows,
        ));
        let mut qualified = connection.prepare(&qualified_sql)?;
        let exact_leaf_sql = indexed_rows_sql(&format!(
            "WHERE search_fts MATCH ?1
             AND (lower(name) = lower(?2)
                  OR lower(substr(name, -(length(?2) + 1))) = ('.' || lower(?2)))
             AND owner IN (SELECT owner FROM active_search_scopes)
             ORDER BY CASE WHEN kind = 'file' THEN 1 ELSE 0 END,
                      length(name),
                      CASE
                        WHEN owner LIKE 'workspace:%' OR owner LIKE 'artifacts:%' THEN 0
                        ELSE 1
                      END
             LIMIT {}",
            SEARCH_TUNING.retrieval.exact_rows,
        ));
        let mut exact_leaf = connection.prepare(&exact_leaf_sql)?;
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
        if !name_query && !include_all_signatures {
            rows.extend(module_context_candidates(
                &connection,
                query,
                tokens,
                &rows,
            )?);
        }
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
            let parts = identifier_query_parts(leaf)
                .into_iter()
                .filter(|part| part.len() >= 2 && seen.insert(part.clone()))
                .map(|part| {
                    format!(
                        "(name : \"{}\" AND name : \"{}\"*)",
                        owner.replace('"', "\"\""),
                        part.replace('"', "\"\"")
                    )
                })
                .collect::<Vec<_>>()
                .join(" OR ");
            if !parts.is_empty() {
                rows.extend(
                    qualified
                        .query_map([parts], indexed_row_from_row)?
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
        let sql = indexed_rows_sql(&format!(
            "WHERE search_fts MATCH ?1
             AND (lower(name) = lower(?2)
                  OR lower(substr(name, -(length(?2) + 1))) = ('.' || lower(?2)))
             AND owner IN (SELECT owner FROM active_search_scopes)
             LIMIT {}",
            SEARCH_TUNING.retrieval.exact_rows,
        ));
        let mut statement = connection.prepare(&sql)?;
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
            prepend_search_note(&mut result.note, detail);
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
        let sql = indexed_rows_sql(&format!(
            "WHERE search_fts MATCH ?1 AND kind = 'field'
             AND owner IN (SELECT owner FROM active_search_scopes)
             ORDER BY line, name LIMIT {}",
            SEARCH_TUNING.retrieval.field_rows,
        ));
        let mut statement = connection.prepare(&sql)?;
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
        let sql = format!(
            "SELECT name FROM search_fts
             WHERE search_fts MATCH ?1
               AND owner IN (SELECT owner FROM active_search_scopes)
             LIMIT {}",
            SEARCH_TUNING.retrieval.continuation_rows,
        );
        let mut statement = connection.prepare(&sql)?;
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

    fn context_pack(
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
        let query = format!(
            "name : \"{}\"* OR signature : \"{}\"* OR body : \"{}\"",
            exact.name.replace('"', "\"\""),
            leaf.replace('"', "\"\""),
            leaf.replace('"', "\"\"")
        );
        let sql = indexed_rows_sql(&format!(
            "WHERE search_fts MATCH ?1
             AND owner IN (SELECT owner FROM active_search_scopes)
             LIMIT {}",
            SEARCH_TUNING.retrieval.context_rows,
        ));
        let mut statement = connection.prepare(&sql)?;
        let rows = statement
            .query_map([query], indexed_row_from_row)?
            .collect::<rusqlite::Result<Vec<_>>>()?;
        let mut ranked = Vec::new();
        for row in rows {
            if row.name == exact.name || matches!(row.kind.as_str(), "file" | "imports") {
                continue;
            }
            let priority = if row.name == format!("{}.mk", exact.name) {
                0
            } else if row.name.starts_with(&prefix) {
                1
            } else if row.module == exact.module
                && (row.signature.contains(leaf) || row.body.contains(leaf))
            {
                3
            } else {
                continue;
            };
            ranked.push((priority, compact_ranked_hit(row)));
        }
        let mut contexts = exact
            .usages
            .iter()
            .filter_map(|usage| usage.context.as_ref())
            .filter(|name| *name != &exact.name)
            .cloned()
            .collect::<Vec<_>>();
        contexts.sort();
        contexts.dedup();
        for name in contexts {
            let rows = self.exact_candidates(&name, scopes)?;
            let candidates = ranked_exact_candidates(rows, &name, workspace);
            let Some(candidates) = resolved_exact_candidates(candidates, &name) else {
                continue;
            };
            let mut candidate = merge_exact_candidates(candidates);
            candidate.hit.source = None;
            candidate.hit.usages.clear();
            ranked.push((2, candidate));
        }
        for (_, candidate) in &mut ranked {
            if let Some(context) = import_context {
                apply_import_context(candidate, context);
            }
        }
        ranked.sort_by(|left, right| {
            context_refinement_score(&right.1.hit, refinement_tokens)
                .cmp(&context_refinement_score(&left.1.hit, refinement_tokens))
                .then_with(|| left.0.cmp(&right.0))
                .then_with(|| left.1.hit.name.cmp(&right.1.hit.name))
        });
        let mut seen = HashSet::from([exact.name.clone()]);
        Ok(ranked
            .into_iter()
            .filter_map(|(_, candidate)| {
                seen.insert(candidate.hit.name.clone()).then_some(candidate.hit)
            })
            .take(SEARCH_TUNING.promotion.context_group_size)
            .collect())
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
        let sql = indexed_rows_sql(&format!(
            "WHERE search_fts MATCH ?1 LIMIT {}",
            SEARCH_TUNING.retrieval.exact_rows,
        ));
        let mut statement = connection.prepare(&sql)?;
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
        let target = name.strip_prefix("_root_.").unwrap_or(name);
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
            params![target, workspace_owner, SEARCH_USAGE_LIMIT as i64],
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
    ) -> Vec<Candidate> {
        let Ok(paths) = dirty_lean_files(&workspace.path) else {
            return Vec::new();
        };
        let mut ranked = Vec::new();
        // Dirty source must override the persistent index immediately. Cold clean
        // workspaces use the targeted source fallback while indexing completes.
        for path in paths
            .into_iter()
            .take(SEARCH_TUNING.retrieval.dirty_files)
        {
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
                    .map(|token| token.len().min(SEARCH_TUNING.source.dirty_relevance_cap))
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
                ranked.push(Candidate {
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
                    score: SEARCH_TUNING.source.dirty_base
                        + relevance as f64 * SEARCH_TUNING.source.dirty_relevance
                        + named as f64 * SEARCH_TUNING.source.dirty_name
                        + if exact_name {
                            SEARCH_TUNING.source.dirty_exact
                        } else {
                            0.0
                        }
                        - if is_file_like && !import_query {
                            SEARCH_TUNING.source.dirty_file_penalty
                        } else if is_file_like {
                            SEARCH_TUNING.source.dirty_import_file_penalty
                        } else {
                            0.0
                        },
                    origins: CandidateOrigin::ProjectSource as u8,
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

    fn query(
        &mut self,
        query: &str,
        accept_suggestions: bool,
    ) -> Result<(Vec<LoogleHit>, Option<String>)> {
        self.last_used = Instant::now();
        let query = query.lines().collect::<Vec<_>>().join(" ");
        let mut value = self.query_value(&query)?;
        if accept_suggestions
            && value.get("error").is_some()
            && let Some(suggestion) = value
                .get("suggestions")
                .and_then(Value::as_array)
                .and_then(|suggestions| suggestions.first())
                .and_then(Value::as_str)
            && suggestion != query
        {
            value = self.query_value(suggestion)?;
        }
        if let Some(error) = value.get("error").and_then(Value::as_str) {
            return Ok((Vec::new(), Some(error.to_owned())));
        }
        let hits = value
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
            .collect();
        Ok((hits, None))
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
    let summary_limit = if run.inference == "exact-batch" {
        run.hits.len()
    } else {
        SUMMARY_LIMIT
    };
    for (index, hit) in run.hits.iter().take(summary_limit).enumerate() {
        output.push('\n');
        output.push_str(&hit.name);
        let displayed_source = hit.source.as_deref().filter(|_| {
            run.inference == "probe"
                || (!related_results
                && ((index == 0 && proof_body_requested)
                    || (!proof_body_requested
                        && (declaration_leaf_matches(&hit.name, &run.query)
                            || (index < 3
                                && matches!(
                                    hit.kind.as_str(),
                                    "class" | "inductive" | "structure"
                                ))
                            || matches!(
                                hit.kind.as_str(),
                                "fields"
                                    | "file"
                                    | "imports"
                                    | "location"
                                    | "location-expanded"
                                    | "outline"
                                    | "source-occurrences"
                                    | "source-range"
                            )))))
        });
        if let Some(signature) = &hit.signature
            && !displayed_source
                .is_some_and(|source| source_has_complete_declaration_header(hit, source))
        {
            output.push_str(" : ");
            if matches!(run.inference.as_str(), "exact" | "exact-batch") {
                output.push_str(&single_line(signature));
            } else {
                output.push_str(&truncate_line(&single_line(signature), 240));
            }
        }
        if !hit.path.is_empty() {
            output.push_str(&format!("  {}", hit.path));
            if hit.line > 0 {
                output.push_str(&format!(":{}", hit.line));
            }
        }
        if hit.applicable {
            output.push_str("  applicable");
        }
        if let Some(module) = &hit.required_import {
            output.push_str(&format!("\n  import {module}"));
        }
        for usage in hit.usages.iter().take(3) {
            output.push_str(&format!("\n  used: {}:{}", usage.path, usage.line));
            if let Some(context) = &usage.context {
                output.push_str(&format!(" in {context}"));
            }
        }
        if hit.usages.len() > 3 {
            output.push_str(&format!(
                "\n  +{} usages; show {} --all",
                hit.usages.len() - 3,
                run.reference
            ));
        }
        if let Some(source) = displayed_source {
            if run.inference != "probe" && !matches!(
                hit.kind.as_str(),
                "file"
                    | "fields"
                    | "imports"
                    | "location"
                    | "location-expanded"
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
                    "location-expanded" => LOCATION_EXPANDED_LINES,
                    "source-range" => SOURCE_RANGE_ALL_LIMIT,
                    "source-occurrences" => SOURCE_OCCURRENCE_LIMIT,
                    _ => SOURCE_PREVIEW_LINES,
                }
            };
            for line in source.lines().take(source_lines) {
                output.push('\n');
                output.push_str(&truncate_line(line.trim_end(), 200));
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
    if run.hits.len() > summary_limit {
        output.push_str(&format!(
            "\n+{} results; show {} --all",
            run.hits.len() - summary_limit,
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
