use std::collections::BTreeMap;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, ensure};
use rusqlite::types::Type;
use rusqlite::{Connection, OptionalExtension, TransactionBehavior, params};
use serde::{Deserialize, Serialize};

use crate::git::{dirty_paths, head};
use crate::protocol::{Command, Request, Response};
use crate::reference::{Reference, ReferenceKind};
use crate::repo::Repo;
use crate::state::State;
use crate::util::{build_id, format_duration, hash_bytes, now_unix_ms, resident_memory_kib};

const SNAPSHOT_LIMIT: usize = 256 * 1024;
const LOG_LINES: usize = 80;
const TELEMETRY_DAYS: i64 = 30;
const TELEMETRY_LIMIT: i64 = 100_000;

#[derive(Debug, Clone)]
pub struct IssueStore {
    path: PathBuf,
}

#[derive(Debug, Clone)]
pub struct TelemetryStore {
    path: PathBuf,
}

#[derive(Debug, Clone)]
pub struct ContextEvent {
    pub created_at: i64,
    pub client_ms: u64,
    pub workspace: String,
    pub reference: Option<String>,
    pub response_bytes: u64,
}

pub struct TelemetryOperation<'a> {
    pub workspace: Option<&'a str>,
    pub verb: &'a str,
    pub reference: Option<&'a str>,
    pub ok: bool,
    pub duration_ms: u64,
    pub detail: &'a str,
    pub rss_kib: Option<u64>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
struct IssueContext {
    build: String,
    project: Option<String>,
    cwd: String,
    workspace: Option<String>,
    git_head: Option<String>,
    lean_toolchain: Option<String>,
    related_ref: Option<String>,
    related_detail: Option<String>,
    exchange: Option<String>,
    dirty: Vec<String>,
    files: Vec<FileSnapshot>,
    log: Option<String>,
    telemetry: Option<String>,
}

#[derive(Debug)]
struct TelemetryEvent {
    id: i64,
    created_at: i64,
    build: String,
    project: String,
    workspace: Option<String>,
    verb: String,
    reference: Option<String>,
    ok: bool,
    outcome_class: Option<String>,
    query_class: Option<String>,
    response_band: Option<String>,
    follow_up: Option<String>,
    error_class: Option<String>,
    client_ms: u64,
    daemon_ms: u64,
    rss_kib: Option<u64>,
    request_bytes: u64,
    response_bytes: u64,
    request_json: String,
    response_json: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct FileSnapshot {
    path: String,
    text: String,
}

#[derive(Debug, Clone)]
struct Issue {
    id: i64,
    summary: String,
    status: String,
    occurrences: u64,
    context: IssueContext,
    fixed_by: Option<String>,
    note: Option<String>,
    created_at: i64,
    resolved_at: Option<i64>,
}

impl IssueStore {
    pub fn global() -> Result<Self> {
        let override_path = std::env::var_os("MATHMUX_ISSUE_DB");
        let managed = override_path.is_none();
        let path = match override_path {
            Some(path) => PathBuf::from(path),
            None => {
                let base = std::env::var_os("XDG_STATE_HOME")
                    .map(PathBuf::from)
                    .or_else(|| {
                        std::env::var_os("HOME")
                            .map(PathBuf::from)
                            .map(|path| path.join(".local/state"))
                    })
                    .context("cannot locate the local state directory")?;
                base.join("mathmux/development.sqlite3")
            }
        };
        if managed && let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
            fs::set_permissions(parent, fs::Permissions::from_mode(0o700))?;
        }
        Self::new(path)
    }

    pub fn new(path: impl AsRef<Path>) -> Result<Self> {
        let path = path.as_ref().to_path_buf();
        let parent = path.parent().context("issue database has no parent")?;
        fs::create_dir_all(parent)?;
        let store = Self { path };
        store.migrate()?;
        fs::set_permissions(&store.path, fs::Permissions::from_mode(0o600))?;
        Ok(store)
    }

    fn migrate(&self) -> Result<()> {
        let connection = open_db(&self.path)?;
        connection.pragma_update(None, "journal_mode", "WAL")?;
        connection.execute_batch(
            "CREATE TABLE IF NOT EXISTS issues (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                signature TEXT NOT NULL,
                summary TEXT NOT NULL,
                status TEXT NOT NULL CHECK(status IN ('open', 'resolved')),
                occurrences INTEGER NOT NULL,
                context_json TEXT NOT NULL,
                fixed_by TEXT,
                note TEXT,
                created_at INTEGER NOT NULL,
                updated_at INTEGER NOT NULL,
                resolved_at INTEGER,
                resolution TEXT CHECK(resolution IN ('fixed', 'dismissed'))
             );
             CREATE INDEX IF NOT EXISTS issues_status_updated
                ON issues(status, updated_at DESC);
             CREATE INDEX IF NOT EXISTS issues_open_signature
                ON issues(signature) WHERE status = 'open';",
        )?;
        if !table_has_column(&connection, "issues", "resolution")? {
            connection.execute(
                "ALTER TABLE issues ADD COLUMN resolution TEXT
                 CHECK(resolution IN ('fixed', 'dismissed'))",
                [],
            )?;
        }
        Ok(())
    }

    pub fn create(&self, cwd: &Path, summary: &str, related_ref: Option<&str>) -> Result<String> {
        let summary = summary.trim();
        ensure!(!summary.is_empty(), "issue summary is empty");
        ensure!(summary.len() <= 500, "issue summary is too long");
        let context = capture_context(cwd, related_ref)?;
        let signature = hash_bytes(summary.to_ascii_lowercase().as_bytes());
        let now = now_unix_ms();
        let mut connection = open_db(&self.path)?;
        let transaction = connection.transaction_with_behavior(TransactionBehavior::Immediate)?;
        let existing = transaction
            .query_row(
                "SELECT id FROM issues
                 WHERE status = 'open' AND signature = ?1 ORDER BY updated_at DESC LIMIT 1",
                [&signature],
                |row| row.get::<_, i64>(0),
            )
            .optional()?;
        let id = if let Some(id) = existing {
            transaction.execute(
                "UPDATE issues
                 SET occurrences = occurrences + 1, context_json = ?2, updated_at = ?3
                 WHERE id = ?1",
                params![id, serde_json::to_string(&context)?, now],
            )?;
            id
        } else {
            transaction.execute(
                "INSERT INTO issues(
                    signature, summary, status, occurrences, context_json, created_at, updated_at
                 ) VALUES (?1, ?2, 'open', 1, ?3, ?4, ?4)",
                params![signature, summary, serde_json::to_string(&context)?, now],
            )?;
            transaction.last_insert_rowid()
        };
        transaction.commit()?;
        Ok(format!("i{id}"))
    }

    pub fn list(&self, status: &str) -> Result<String> {
        ensure!(
            matches!(status, "open" | "resolved" | "dismissed" | "all"),
            "invalid issue status"
        );
        let connection = open_db(&self.path)?;
        let sql = if status == "all" {
            "SELECT id, summary,
                    CASE WHEN resolution = 'dismissed' THEN 'dismissed' ELSE status END,
                    occurrences FROM issues ORDER BY updated_at DESC"
        } else if status == "dismissed" {
            "SELECT id, summary, 'dismissed', occurrences
             FROM issues WHERE resolution = 'dismissed' ORDER BY updated_at DESC"
        } else if status == "resolved" {
            "SELECT id, summary, status, occurrences
             FROM issues WHERE status = 'resolved'
               AND (resolution IS NULL OR resolution = 'fixed')
             ORDER BY updated_at DESC"
        } else {
            "SELECT id, summary, status, occurrences
             FROM issues WHERE status = ?1 ORDER BY updated_at DESC"
        };
        let mut statement = connection.prepare(sql)?;
        let render = |row: &rusqlite::Row<'_>| {
            let id = row.get::<_, i64>(0)?;
            let summary = row.get::<_, String>(1)?;
            let status = row.get::<_, String>(2)?;
            let occurrences = row.get::<_, u64>(3)?;
            let count = if occurrences > 1 {
                format!(" {occurrences}x")
            } else {
                String::new()
            };
            Ok(format!("i{id} {status}{count} {summary}"))
        };
        let issues: Vec<String> = if matches!(status, "all" | "dismissed" | "resolved") {
            statement
                .query_map([], render)?
                .collect::<rusqlite::Result<Vec<_>>>()?
        } else {
            statement
                .query_map([status], render)?
                .collect::<rusqlite::Result<Vec<_>>>()?
        };
        if issues.is_empty() {
            return Ok(if status == "all" {
                "no issues".into()
            } else {
                format!("no {status} issues")
            });
        }
        Ok(issues.join("\n"))
    }

    pub fn resolve(
        &self,
        reference: &str,
        fixed_by: Option<&str>,
        note: Option<&str>,
    ) -> Result<String> {
        let id = parse_reference(reference)?;
        let changed = open_db(&self.path)?.execute(
            "UPDATE issues SET status = 'resolved', resolution = 'fixed',
                    fixed_by = ?2, note = ?3,
                    updated_at = ?4, resolved_at = ?4
             WHERE id = ?1 AND status = 'open'",
            params![
                id,
                clean_optional(fixed_by),
                clean_optional(note),
                now_unix_ms()
            ],
        )?;
        ensure!(changed == 1, "unknown or resolved issue {reference}");
        Ok(format!("{reference} resolved"))
    }

    pub fn dismiss(&self, reference: &str, reason: &str) -> Result<String> {
        let id = parse_reference(reference)?;
        let reason = reason.trim();
        ensure!(!reason.is_empty(), "dismissal reason is empty");
        let now = now_unix_ms();
        let changed = open_db(&self.path)?.execute(
            "UPDATE issues SET status = 'resolved', resolution = 'dismissed',
                    fixed_by = NULL, note = ?2, updated_at = ?3, resolved_at = ?3
             WHERE id = ?1 AND status = 'open'",
            params![id, reason, now],
        )?;
        ensure!(changed == 1, "unknown or closed issue {reference}");
        Ok(format!("{reference} dismissed"))
    }

    pub fn show(&self, reference: &str, all: bool) -> Result<String> {
        let id = parse_reference(reference)?;
        let issue = open_db(&self.path)?
            .query_row(
                "SELECT id, summary,
                        CASE WHEN resolution = 'dismissed' THEN 'dismissed' ELSE status END,
                        occurrences, context_json, fixed_by, note, created_at, resolved_at
                 FROM issues WHERE id = ?1",
                [id],
                issue_from_row,
            )
            .optional()?
            .with_context(|| format!("unknown reference {reference}"))?;
        Ok(render_issue(&issue, all))
    }
}

impl TelemetryStore {
    pub fn global() -> Result<Self> {
        let issues = IssueStore::global()?;
        Self::new(issues.path)
    }

    pub fn new(path: impl AsRef<Path>) -> Result<Self> {
        let store = Self {
            path: path.as_ref().to_path_buf(),
        };
        store.migrate()?;
        fs::set_permissions(&store.path, fs::Permissions::from_mode(0o600))?;
        Ok(store)
    }

    pub(crate) fn prune_history(&self) -> Result<usize> {
        let mut connection = open_db(&self.path)?;
        let transaction = connection.transaction()?;
        let before: i64 =
            transaction.query_row("SELECT COUNT(*) FROM telemetry_events", [], |row| {
                row.get(0)
            })?;
        prune_telemetry(&transaction, now_unix_ms())?;
        let after: i64 =
            transaction.query_row("SELECT COUNT(*) FROM telemetry_events", [], |row| {
                row.get(0)
            })?;
        transaction.commit()?;
        Ok(before.saturating_sub(after) as usize)
    }

    pub(crate) fn checkpoint(&self) -> Result<()> {
        let connection = open_db(&self.path)?;
        connection.query_row("PRAGMA wal_checkpoint(PASSIVE)", [], |_| Ok(()))?;
        Ok(())
    }

    fn migrate(&self) -> Result<()> {
        if let Some(parent) = self.path.parent() {
            fs::create_dir_all(parent)?;
        }
        let connection = open_db(&self.path)?;
        connection.pragma_update(None, "journal_mode", "WAL")?;
        connection.execute_batch(
            "CREATE TABLE IF NOT EXISTS telemetry_events (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                created_at INTEGER NOT NULL,
                build TEXT NOT NULL,
                project TEXT NOT NULL,
                workspace TEXT,
                verb TEXT NOT NULL,
                reference TEXT,
                ok INTEGER NOT NULL,
                outcome_class TEXT,
                query_class TEXT,
                response_band TEXT,
                follow_up TEXT,
                error_class TEXT,
                client_ms INTEGER NOT NULL,
                daemon_ms INTEGER NOT NULL,
                rss_kib INTEGER,
                request_bytes INTEGER NOT NULL,
                response_bytes INTEGER NOT NULL,
                request_json TEXT NOT NULL,
                response_json TEXT NOT NULL
             );
             CREATE INDEX IF NOT EXISTS telemetry_created
                ON telemetry_events(created_at DESC);
             CREATE INDEX IF NOT EXISTS telemetry_verb_created
                ON telemetry_events(verb, created_at DESC);
             CREATE INDEX IF NOT EXISTS telemetry_project_created
                ON telemetry_events(project, created_at DESC);
             CREATE INDEX IF NOT EXISTS telemetry_project_workspace_id
                ON telemetry_events(project, workspace, id DESC);",
        )?;
        if !table_has_column(&connection, "telemetry_events", "outcome_class")? {
            connection.execute(
                "ALTER TABLE telemetry_events ADD COLUMN outcome_class TEXT",
                [],
            )?;
            connection.execute(
                "UPDATE telemetry_events
                 SET outcome_class = CASE
                     WHEN ok = 0 AND verb = 'check' AND reference GLOB 'c[0-9]*'
                         THEN 'formalization'
                     WHEN ok = 0 THEN 'operational'
                 END",
                [],
            )?;
        }
        for column in ["query_class", "response_band", "follow_up"] {
            if !table_has_column(&connection, "telemetry_events", column)? {
                connection.execute(
                    &format!("ALTER TABLE telemetry_events ADD COLUMN {column} TEXT"),
                    [],
                )?;
            }
        }
        Ok(())
    }

    pub fn record(
        &self,
        repo: &Repo,
        request: &Request,
        response: &Response,
        client_ms: u64,
    ) -> Result<String> {
        let request_json = serde_json::to_string(request)?;
        let response_json = serde_json::to_string(response)?;
        let state = State::existing(&repo.db_path);
        let workspace = state
            .workspace_for_path(Path::new(&request.cwd))
            .ok()
            .map(|workspace| workspace.reference);
        let reference = response_reference(&response.summary);
        let query_class = query_class(request);
        let outcome_class = exchange_outcome_class(
            &state,
            request,
            response,
            reference.as_deref(),
            query_class.as_deref(),
        );
        let response_band = response_band(response_json.len());
        let follow_up = follow_up_kind(request);
        let error_class = (!response.ok).then(|| error_class(&response.summary));
        let now = now_unix_ms();
        let mut connection = open_db(&self.path)?;
        let transaction = connection.transaction()?;
        if let Some(reference) = reference.as_deref()
            && let Some(id) = transaction
                .query_row(
                    "SELECT id FROM telemetry_events
                     WHERE project = ?1 AND verb = ?2 AND reference = ?3
                     LIMIT 1",
                    params![
                        repo.root.to_string_lossy(),
                        request.command.verb(),
                        reference
                    ],
                    |row| row.get::<_, i64>(0),
                )
                .optional()?
        {
            transaction.commit()?;
            return Ok(format!("e{id}"));
        }
        transaction.execute(
            "INSERT INTO telemetry_events(
                created_at, build, project, workspace, verb, reference, ok, outcome_class,
                query_class, response_band, follow_up, error_class,
                client_ms, daemon_ms, rss_kib, request_bytes, response_bytes,
                request_json, response_json
             ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14, ?15, ?16, ?17, ?18, ?19)",
            params![
                now,
                response.build,
                repo.root.to_string_lossy(),
                workspace,
                request.command.verb(),
                reference,
                response.ok,
                outcome_class,
                query_class,
                response_band,
                Option::<String>::None,
                error_class,
                client_ms,
                response.daemon_ms,
                response.rss_kib,
                request_json.len() as u64,
                response_json.len() as u64,
                request_json,
                response_json,
            ],
        )?;
        let id = transaction.last_insert_rowid();
        if let (Some(follow_up), Some(workspace)) = (follow_up, workspace.as_deref()) {
            transaction.execute(
                "UPDATE telemetry_events SET follow_up = ?1
                 WHERE id = (
                    SELECT id FROM telemetry_events
                    WHERE project = ?2 AND workspace = ?3 AND id < ?4
                    ORDER BY id DESC LIMIT 1
                 )
                 AND query_class IS NOT NULL",
                params![follow_up, repo.root.to_string_lossy(), workspace, id],
            )?;
        }
        prune_telemetry(&transaction, now)?;
        transaction.commit()?;
        Ok(format!("e{id}"))
    }

    pub fn context_events(&self, repo: &Repo, since: i64) -> Result<Vec<ContextEvent>> {
        let connection = open_db(&self.path)?;
        let mut statement = connection.prepare(
            "SELECT created_at, client_ms, workspace, reference, response_bytes
             FROM telemetry_events
             WHERE project = ?1 AND created_at >= ?2 AND workspace IS NOT NULL
               AND json_type(request_json, '$.command') = 'object'
             ORDER BY created_at, id",
        )?;
        let rows = statement.query_map(
            params![repo.root.to_string_lossy().as_ref(), since],
            |row| {
                Ok(ContextEvent {
                    created_at: row.get(0)?,
                    client_ms: row.get::<_, i64>(1)?.max(0) as u64,
                    workspace: row.get(2)?,
                    reference: row.get(3)?,
                    response_bytes: row.get::<_, i64>(4)?.max(0) as u64,
                })
            },
        )?;
        rows.collect::<rusqlite::Result<Vec<_>>>()
            .map_err(Into::into)
    }

    pub fn record_operation(
        &self,
        repo: &Repo,
        operation: &TelemetryOperation<'_>,
    ) -> Result<String> {
        ensure!(
            !operation.verb.is_empty()
                && operation.verb.len() <= 64
                && operation
                    .verb
                    .chars()
                    .all(|character| character.is_ascii_alphanumeric() || character == '_'),
            "invalid telemetry verb"
        );
        let response_json = serde_json::json!({ "detail": operation.detail }).to_string();
        let now = now_unix_ms();
        let mut connection = open_db(&self.path)?;
        let transaction = connection.transaction()?;
        transaction.execute(
            "INSERT INTO telemetry_events(
                created_at, build, project, workspace, verb, reference, ok, outcome_class, error_class,
                client_ms, daemon_ms, rss_kib, request_bytes, response_bytes,
                request_json, response_json
             ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?10, ?11, 2, ?12, '{}', ?13)",
            params![
                now,
                build_id(),
                repo.root.to_string_lossy(),
                operation.workspace,
                operation.verb,
                operation.reference,
                operation.ok,
                (!operation.ok).then_some("operational"),
                (!operation.ok).then(|| error_class(operation.detail)),
                operation.duration_ms,
                operation.rss_kib.or_else(resident_memory_kib),
                response_json.len() as u64,
                response_json,
            ],
        )?;
        let id = transaction.last_insert_rowid();
        prune_telemetry(&transaction, now)?;
        transaction.commit()?;
        Ok(format!("e{id}"))
    }

    pub fn summary(&self, since: &str, verb: Option<&str>, slow: Option<usize>) -> Result<String> {
        let cutoff = parse_since(since)?;
        let events = self.events_since(cutoff, verb)?;
        if events.is_empty() {
            return Ok("no telemetry".into());
        }
        if let Some(limit) = slow {
            ensure!(
                (1..=100).contains(&limit),
                "--slow uses a value from 1 to 100"
            );
            let mut events = events;
            events.sort_by_key(|event| std::cmp::Reverse(event.client_ms));
            return Ok(events
                .iter()
                .take(limit)
                .map(render_event_line)
                .collect::<Vec<_>>()
                .join("\n"));
        }
        let mut grouped: BTreeMap<&str, Vec<&TelemetryEvent>> = BTreeMap::new();
        for event in &events {
            grouped.entry(&event.verb).or_default().push(event);
        }
        let mut output = grouped
            .into_iter()
            .map(|(verb, events)| render_aggregate(verb, &events))
            .collect::<Vec<_>>()
            .join("\n");
        append_recent_events(
            &mut output,
            "recent errors",
            events.iter().filter(|event| {
                !event.ok && event.outcome_class.as_deref() != Some("formalization")
            }),
        );
        append_recent_events(
            &mut output,
            "recent formalization failures",
            events
                .iter()
                .filter(|event| event.outcome_class.as_deref() == Some("formalization")),
        );
        Ok(output)
    }

    pub fn show(&self, reference: &str, all: bool) -> Result<String> {
        let id = parse_event_reference(reference)?;
        let event = open_db(&self.path)?
            .query_row(
                "SELECT id, created_at, build, project, workspace, verb, reference, ok,
                        outcome_class, query_class, response_band, follow_up, error_class,
                        client_ms, daemon_ms, rss_kib, request_bytes, response_bytes,
                        request_json, response_json
                 FROM telemetry_events WHERE id = ?1",
                [id],
                telemetry_from_row,
            )
            .optional()?
            .with_context(|| format!("unknown reference {reference}"))?;
        Ok(render_event(&event, all))
    }

    fn events_since(&self, cutoff: i64, verb: Option<&str>) -> Result<Vec<TelemetryEvent>> {
        let connection = open_db(&self.path)?;
        let select = "SELECT id, created_at, build, project, workspace, verb, reference, ok,
                             outcome_class, query_class, response_band, follow_up, error_class,
                             client_ms, daemon_ms, rss_kib, request_bytes, response_bytes,
                             request_json, response_json
                      FROM telemetry_events";
        let (sql, value) = match verb {
            Some(verb) => (
                format!("{select} WHERE created_at >= ?1 AND verb = ?2 ORDER BY created_at DESC"),
                Some(verb),
            ),
            None => (
                format!("{select} WHERE created_at >= ?1 ORDER BY created_at DESC"),
                None,
            ),
        };
        let mut statement = connection.prepare(&sql)?;
        let rows = match value {
            Some(verb) => statement.query_map(params![cutoff, verb], telemetry_from_row)?,
            None => statement.query_map([cutoff], telemetry_from_row)?,
        };
        rows.collect::<rusqlite::Result<Vec<_>>>()
            .map_err(Into::into)
    }

    fn recent(&self, project: &Path, workspace: Option<&str>) -> Result<Option<String>> {
        let connection = open_db(&self.path)?;
        let mut statement = connection.prepare(
            "SELECT id, created_at, build, project, workspace, verb, reference, ok,
                    outcome_class, query_class, response_band, follow_up, error_class,
                    client_ms, daemon_ms, rss_kib, request_bytes, response_bytes,
                    request_json, response_json
             FROM telemetry_events
             WHERE project = ?1 AND (?2 IS NULL OR workspace = ?2)
             ORDER BY created_at DESC LIMIT 10",
        )?;
        let events = statement
            .query_map(
                params![project.to_string_lossy(), workspace],
                telemetry_from_row,
            )?
            .collect::<rusqlite::Result<Vec<_>>>()?;
        Ok((!events.is_empty()).then(|| {
            events
                .iter()
                .map(render_event_line)
                .collect::<Vec<_>>()
                .join("\n")
        }))
    }

    fn latest_exchange(&self, project: &Path, workspace: Option<&str>) -> Result<Option<String>> {
        let row = open_db(&self.path)?
            .query_row(
                "SELECT request_json, response_json
                 FROM telemetry_events
                 WHERE project = ?1 AND (?2 IS NULL OR workspace = ?2)
                   AND request_json <> '{}'
                 ORDER BY created_at DESC, id DESC LIMIT 1",
                params![project.to_string_lossy(), workspace],
                |row| Ok((row.get::<_, String>(0)?, row.get::<_, String>(1)?)),
            )
            .optional()?;
        row.map(|(request, response)| {
            let request = serde_json::from_str::<serde_json::Value>(&request)?;
            let response = serde_json::from_str::<serde_json::Value>(&response)?;
            serde_json::to_string(&serde_json::json!({
                "request": request,
                "response": response,
            }))
            .map_err(Into::into)
        })
        .transpose()
    }
}

pub fn record_exchange(
    repo: &Repo,
    request: &Request,
    response: &Response,
    client_ms: u64,
) -> Result<()> {
    TelemetryStore::global()?.record(repo, request, response, client_ms)?;
    Ok(())
}

fn query_class(request: &Request) -> Option<String> {
    let query = match &request.command {
        Command::Search { query, .. } | Command::Probe { query } => query.trim(),
        _ => return None,
    };
    let class = if query.starts_with("type:") || query.contains("⊢") {
        "type"
    } else if query.starts_with("re:")
        || query.starts_with('/')
        || query.contains(".lean:")
        || query.ends_with(".lean")
    {
        "source"
    } else if query.starts_with("name:")
        || crate::search::is_exact_first_query(query)
        || query
            .split_whitespace()
            .next()
            .is_some_and(is_identifier_query)
            && query.split_whitespace().skip(1).all(is_probe_focus)
    {
        "exact"
    } else {
        "discovery"
    };
    Some(class.into())
}

fn is_identifier_query(value: &str) -> bool {
    !value.is_empty()
        && !value.starts_with('.')
        && !value.ends_with('.')
        && value
            .chars()
            .all(|character| character.is_alphanumeric() || matches!(character, '_' | '.' | '\''))
}

fn is_probe_focus(value: &str) -> bool {
    matches!(
        value.to_ascii_lowercase().as_str(),
        "signature"
            | "source"
            | "apply"
            | "fields"
            | "constructors"
            | "ext"
            | "simp"
            | "instances"
            | "coercions"
            | "usages"
            | "goal"
            | "types"
            | "defeq"
            | "rewrite"
            | "profile"
            | "warnings"
    )
}

fn response_band(bytes: usize) -> String {
    match bytes {
        0..=1024 => "0-1KiB",
        1025..=8192 => "1-8KiB",
        _ => "8KiB+",
    }
    .into()
}

fn exchange_outcome_class(
    state: &State,
    request: &Request,
    response: &Response,
    reference: Option<&str>,
    query_class: Option<&str>,
) -> Option<&'static str> {
    if matches!(
        &request.command,
        Command::Search { .. } | Command::Probe { .. }
    ) {
        if response.summary.contains("source regex scan timed out") {
            return Some("operational_error");
        }
        if response.summary.contains("no regex source matches")
            || response.summary.contains(" no results")
            || response.summary.contains("exact declaration not found")
            || response.summary.contains("not found:")
        {
            return Some("no_result");
        }
        if response.summary.contains("suggestion:")
            || response.summary.contains("suggestions")
            || response.summary.contains("UNMERGED (")
        {
            return Some("near_suggestions");
        }
        if response.ok && query_class.is_some() {
            return Some("exact_hit");
        }
        return Some("operational_error");
    }
    failure_outcome_class(state, request, response, reference)
}

fn follow_up_kind(request: &Request) -> Option<&'static str> {
    match &request.command {
        Command::Probe { .. } => Some("probe"),
        Command::Show { .. } => Some("show"),
        Command::Check { .. } => Some("check"),
        _ => None,
    }
}

pub const fn development_enabled() -> bool {
    cfg!(feature = "development")
}

fn failure_outcome_class(
    state: &State,
    request: &Request,
    response: &Response,
    reference: Option<&str>,
) -> Option<&'static str> {
    if response.ok {
        return None;
    }
    let formalization = matches!(&request.command, Command::Check { .. })
        && reference.is_some_and(|reference| {
            state
                .check_run(reference)
                .ok()
                .flatten()
                .is_some_and(|run| {
                    !run.diagnostics.is_empty()
                        && run
                            .diagnostics
                            .iter()
                            .all(|diagnostic| diagnostic.kind != "mathmux")
                })
        });
    Some(if formalization {
        "formalization"
    } else {
        "operational"
    })
}

fn open_db(path: &Path) -> Result<Connection> {
    let connection = Connection::open(path)?;
    connection.busy_timeout(std::time::Duration::from_secs(10))?;
    Ok(connection)
}

fn prune_telemetry(transaction: &rusqlite::Transaction<'_>, now: i64) -> Result<()> {
    transaction.execute(
        "DELETE FROM telemetry_events WHERE created_at < ?1",
        [now - TELEMETRY_DAYS * 24 * 60 * 60 * 1000],
    )?;
    transaction.execute(
        "DELETE FROM telemetry_events
         WHERE id <= COALESCE((
            SELECT id FROM telemetry_events ORDER BY id DESC LIMIT 1 OFFSET ?1
         ), 0)",
        [TELEMETRY_LIMIT],
    )?;
    Ok(())
}

fn parse_since(value: &str) -> Result<i64> {
    if value == "all" {
        return Ok(0);
    }
    let (number, unit) = value.split_at(value.len().saturating_sub(1));
    let number = number
        .parse::<i64>()
        .with_context(|| format!("invalid --since value {value}"))?;
    ensure!(number > 0, "--since must be positive");
    let milliseconds = match unit {
        "m" => 60 * 1000,
        "h" => 60 * 60 * 1000,
        "d" => 24 * 60 * 60 * 1000,
        "w" => 7 * 24 * 60 * 60 * 1000,
        _ => anyhow::bail!("--since uses m, h, d, w, or all"),
    };
    Ok(now_unix_ms().saturating_sub(number.saturating_mul(milliseconds)))
}

fn telemetry_from_row(row: &rusqlite::Row<'_>) -> rusqlite::Result<TelemetryEvent> {
    Ok(TelemetryEvent {
        id: row.get(0)?,
        created_at: row.get(1)?,
        build: row.get(2)?,
        project: row.get(3)?,
        workspace: row.get(4)?,
        verb: row.get(5)?,
        reference: row.get(6)?,
        ok: row.get(7)?,
        outcome_class: row.get(8)?,
        query_class: row.get(9)?,
        response_band: row.get(10)?,
        follow_up: row.get(11)?,
        error_class: row.get(12)?,
        client_ms: row.get(13)?,
        daemon_ms: row.get(14)?,
        rss_kib: row.get(15)?,
        request_bytes: row.get(16)?,
        response_bytes: row.get(17)?,
        request_json: row.get(18)?,
        response_json: row.get(19)?,
    })
}

fn render_aggregate(verb: &str, events: &[&TelemetryEvent]) -> String {
    let mut durations = events
        .iter()
        .map(|event| event.client_ms)
        .collect::<Vec<_>>();
    durations.sort_unstable();
    let failures = events
        .iter()
        .filter(|event| event.outcome_class.as_deref() == Some("formalization"))
        .count();
    let errors = events
        .iter()
        .filter(|event| !event.ok && event.outcome_class.as_deref() != Some("formalization"))
        .count();
    let rss = events.iter().filter_map(|event| event.rss_kib).max();
    let average = durations.iter().sum::<u64>() / durations.len() as u64;
    let outcome = if failures == 0 {
        format!("err:{errors}")
    } else {
        format!("fail:{failures} err:{errors}")
    };
    let mut output = format!(
        "{} {} avg:{} p50:{} p95:{} {}",
        verb,
        events.len(),
        format_duration(average),
        format_duration(percentile(&durations, 50)),
        format_duration(percentile(&durations, 95)),
        outcome
    );
    if let Some(rss) = rss {
        output.push_str(&format!(" rss:{}", format_memory(rss)));
    }
    output
}

fn percentile(sorted: &[u64], percentile: usize) -> u64 {
    let index = (sorted.len() * percentile).div_ceil(100).saturating_sub(1);
    sorted.get(index).copied().unwrap_or(0)
}

fn render_event_line(event: &TelemetryEvent) -> String {
    let status = if event.ok {
        "ok"
    } else if event.outcome_class.as_deref() == Some("formalization") {
        "failed"
    } else {
        "error"
    };
    let reference = event
        .reference
        .as_deref()
        .map(|reference| format!(" {reference}"))
        .unwrap_or_default();
    format!(
        "e{} {} {} {}{}",
        event.id,
        event.verb,
        format_duration(event.client_ms),
        status,
        reference
    )
}

fn append_recent_events<'a>(
    output: &mut String,
    heading: &str,
    events: impl Iterator<Item = &'a TelemetryEvent>,
) {
    for (index, event) in events.take(5).enumerate() {
        if index == 0 {
            output.push_str(&format!("\n{heading}"));
        }
        output.push('\n');
        output.push_str(&render_event_line(event));
        if let Some(class) = &event.error_class {
            output.push_str(&format!(": {class}"));
        }
    }
}

fn render_event(event: &TelemetryEvent, all: bool) -> String {
    let mut output = render_event_line(event);
    if let Some(error) = &event.error_class {
        output.push_str(&format!("\nerror: {error}"));
    }
    if all {
        output.push_str(&format!(
            "\ncreated: {}\nbuild: {}\nproject: {}\nclient: {}\ndaemon: {}\nio: {}/{} bytes",
            event.created_at,
            event.build,
            event.project,
            format_duration(event.client_ms),
            format_duration(event.daemon_ms),
            event.request_bytes,
            event.response_bytes,
        ));
        if let Some(workspace) = &event.workspace {
            output.push_str(&format!("\nworkspace: {workspace}"));
        }
        if let Some(rss) = event.rss_kib {
            output.push_str(&format!("\nrss: {}", format_memory(rss)));
        }
        if let Some(query_class) = &event.query_class {
            output.push_str(&format!("\nquery-class: {query_class}"));
        }
        if let Some(response_band) = &event.response_band {
            output.push_str(&format!("\nresponse-band: {response_band}"));
        }
        if let Some(follow_up) = &event.follow_up {
            output.push_str(&format!("\nfollow-up: {follow_up}"));
        }
        output.push_str(&format!(
            "\nrequest: {}\nresponse: {}",
            event.request_json, event.response_json
        ));
    }
    output
}

fn format_memory(kib: u64) -> String {
    if kib < 1024 * 1024 {
        format!("{}MiB", kib / 1024)
    } else {
        format!("{:.1}GiB", kib as f64 / 1024.0 / 1024.0)
    }
}

fn response_reference(summary: &str) -> Option<String> {
    summary
        .split_whitespace()
        .map(|token| token.trim_matches(|character: char| !character.is_ascii_alphanumeric()))
        .find(|token| {
            let mut characters = token.chars();
            matches!(
                characters.next(),
                Some('c' | 'e' | 'i' | 'q' | 's' | 'u' | 'w')
            ) && characters.clone().next().is_some()
                && characters.all(|character| character.is_ascii_digit())
        })
        .map(str::to_owned)
}

fn error_class(summary: &str) -> String {
    if summary.contains("malformed search fragment") {
        return "malformed search fragment".into();
    }
    if summary.contains("no tactic context") {
        return "no tactic context".into();
    }
    if summary.contains(" no results")
        || summary.contains("exact declaration not found")
        || summary.contains("not found:")
    {
        return "no results".into();
    }
    if summary.contains("suggestion:")
        || summary.contains("suggestions")
        || summary.contains("UNMERGED (")
    {
        return "near suggestions".into();
    }
    let lines = summary
        .lines()
        .map(str::trim)
        .filter(|line| {
            let mut words = line.split_whitespace();
            let reference = words.next().unwrap_or_default();
            let duration = words.next().unwrap_or_default();
            let run_header = (response_reference(reference).as_deref() == Some(reference)
                && (duration.is_empty() || duration.ends_with("ms"))
                && words.next().is_none())
                || (reference == "error"
                    && response_reference(duration).is_some()
                    && words.next().is_none());
            !run_header
        })
        .collect::<Vec<_>>();
    let value = lines
        .iter()
        .copied()
        .find(|line| {
            line.contains("error(") || line.contains(": error: ") || line.starts_with("error: ")
        })
        .or_else(|| lines.first().copied())
        .unwrap_or("error");
    if let Some(rest) = value.split_once("error(").map(|(_, rest)| rest)
        && let Some((code, _)) = rest.split_once("): ")
    {
        return code.to_owned();
    }
    let value = value
        .split_once(": error: ")
        .map(|(_, message)| message)
        .or_else(|| value.strip_prefix("error: "))
        .unwrap_or(value);
    let lower = value.to_ascii_lowercase();
    for (prefix, class) in [
        ("application type mismatch", "application type mismatch"),
        ("type mismatch", "type mismatch"),
        ("unsolved goals", "unsolved goals"),
        ("failed to synthesize instance", "instance synthesis"),
        ("typeclass instance problem", "instance synthesis"),
        ("unknown identifier", "unknown identifier"),
        ("no goals to be solved", "no goals to be solved"),
        ("fields missing", "fields missing"),
    ] {
        if lower.starts_with(prefix) {
            return class.into();
        }
    }
    let value = value.split_once(':').map_or(value, |(class, _)| class);
    let mut boundary = value.len().min(120);
    while !value.is_char_boundary(boundary) {
        boundary -= 1;
    }
    value[..boundary].to_owned()
}

fn parse_event_reference(reference: &str) -> Result<i64> {
    Ok(Reference::parse_kind(reference, ReferenceKind::Event)?
        .sequence()
        .try_into()?)
}

fn capture_context(cwd: &Path, related_ref: Option<&str>) -> Result<IssueContext> {
    let mut context = IssueContext {
        build: build_id().to_owned(),
        cwd: cwd.to_string_lossy().into_owned(),
        related_ref: related_ref.map(str::to_owned),
        ..IssueContext::default()
    };
    let Ok(repo) = Repo::discover(cwd) else {
        ensure!(related_ref.is_none(), "--ref requires a mathmux repository");
        return Ok(context);
    };
    context.project = Some(repo.root.to_string_lossy().into_owned());
    context.git_head = head(cwd).ok();
    context.lean_toolchain = fs::read_to_string(repo.root.join("lean-toolchain"))
        .ok()
        .map(|value| value.trim().to_owned());
    let mut worktree = repo.root.clone();
    let state = State::existing(&repo.db_path);
    if let Ok(workspace) = state.workspace_for_path(cwd) {
        context.workspace = Some(workspace.reference);
        worktree = workspace.path;
    }
    if let Some(reference) = related_ref {
        context.related_detail = Some(state.show(reference, true)?);
    }
    if let Ok(store) = TelemetryStore::global() {
        context.exchange = store
            .latest_exchange(&repo.root, context.workspace.as_deref())
            .ok()
            .flatten();
        context.telemetry = store
            .recent(&repo.root, context.workspace.as_deref())
            .ok()
            .flatten();
    }
    let dirty = dirty_paths(&worktree).unwrap_or_default();
    context.dirty = dirty
        .iter()
        .map(|path| path.to_string_lossy().into_owned())
        .collect();
    context.files = snapshot_files(&worktree, &dirty);
    context.log = fs::read_to_string(&repo.log_path)
        .ok()
        .map(|log| tail_lines(&log, LOG_LINES));
    Ok(context)
}

fn snapshot_files(root: &Path, paths: &[PathBuf]) -> Vec<FileSnapshot> {
    let mut remaining = SNAPSHOT_LIMIT;
    let mut snapshots = Vec::new();
    for path in paths.iter().filter(|path| relevant_file(path)) {
        let Ok(mut text) = fs::read_to_string(root.join(path)) else {
            continue;
        };
        if remaining == 0 {
            break;
        }
        if text.len() > remaining {
            let mut boundary = remaining;
            while !text.is_char_boundary(boundary) {
                boundary -= 1;
            }
            text.truncate(boundary);
        }
        remaining -= text.len();
        snapshots.push(FileSnapshot {
            path: path.to_string_lossy().into_owned(),
            text,
        });
    }
    snapshots
}

fn relevant_file(path: &Path) -> bool {
    path.extension()
        .and_then(|extension| extension.to_str())
        .is_some_and(|extension| matches!(extension, "lean" | "toml" | "json" | "rs"))
        || path
            .file_name()
            .is_some_and(|name| name == "lean-toolchain")
}

fn tail_lines(value: &str, count: usize) -> String {
    let lines = value.lines().collect::<Vec<_>>();
    lines[lines.len().saturating_sub(count)..].join("\n")
}

fn clean_optional(value: Option<&str>) -> Option<String> {
    value
        .map(str::trim)
        .filter(|value| !value.is_empty())
        .map(str::to_owned)
}

fn table_has_column(connection: &Connection, table: &str, column: &str) -> Result<bool> {
    let mut statement = connection.prepare(&format!("PRAGMA table_info({table})"))?;
    let names = statement
        .query_map([], |row| row.get::<_, String>(1))?
        .collect::<rusqlite::Result<Vec<_>>>()?;
    Ok(names.iter().any(|name| name == column))
}

fn parse_reference(reference: &str) -> Result<i64> {
    Ok(Reference::parse_kind(reference, ReferenceKind::Issue)?
        .sequence()
        .try_into()?)
}

fn issue_from_row(row: &rusqlite::Row<'_>) -> rusqlite::Result<Issue> {
    let context: String = row.get(4)?;
    let context = serde_json::from_str(&context).map_err(|error| {
        rusqlite::Error::FromSqlConversionFailure(4, Type::Text, Box::new(error))
    })?;
    Ok(Issue {
        id: row.get(0)?,
        summary: row.get(1)?,
        status: row.get(2)?,
        occurrences: row.get(3)?,
        context,
        fixed_by: row.get(5)?,
        note: row.get(6)?,
        created_at: row.get(7)?,
        resolved_at: row.get(8)?,
    })
}

fn render_issue(issue: &Issue, all: bool) -> String {
    let occurrences = if issue.occurrences > 1 {
        format!(" {}x", issue.occurrences)
    } else {
        String::new()
    };
    let mut output = format!(
        "i{} {}{}\n{}\nbuild: {}",
        issue.id, issue.status, occurrences, issue.summary, issue.context.build
    );
    if let Some(project) = &issue.context.project {
        let project = if all {
            project.as_str()
        } else {
            Path::new(project)
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or(project)
        };
        output.push_str(&format!("\nproject: {project}"));
    }
    if let Some(reference) = &issue.context.related_ref {
        output.push_str(&format!("\nref: {reference}"));
    }
    if let Some(fixed_by) = &issue.fixed_by {
        output.push_str(&format!("\nfixed by: {fixed_by}"));
    }
    if let Some(note) = &issue.note {
        output.push_str(&format!("\n{note}"));
    }
    if all {
        output.push_str(&format!("\ncwd: {}", issue.context.cwd));
        if let Some(workspace) = &issue.context.workspace {
            output.push_str(&format!("\nworkspace: {workspace}"));
        }
        if let Some(commit) = &issue.context.git_head {
            output.push_str(&format!("\ngit: {commit}"));
        }
        if let Some(toolchain) = &issue.context.lean_toolchain {
            output.push_str(&format!("\ntoolchain: {toolchain}"));
        }
        if !issue.context.dirty.is_empty() {
            output.push_str("\ndirty:");
            for path in &issue.context.dirty {
                output.push_str(&format!("\n  {path}"));
            }
        }
        if let Some(detail) = &issue.context.related_detail {
            output.push_str("\nreference:");
            for line in detail.lines() {
                output.push_str(&format!("\n  {line}"));
            }
        }
        if let Some(exchange) = &issue.context.exchange {
            output.push_str(&format!("\nexchange:\n{exchange}"));
        }
        for file in &issue.context.files {
            output.push_str(&format!("\nfile {}:\n{}", file.path, file.text));
        }
        if let Some(log) = &issue.context.log
            && !log.is_empty()
        {
            output.push_str(&format!("\nlog:\n{log}"));
        }
        if let Some(telemetry) = &issue.context.telemetry
            && !telemetry.is_empty()
        {
            output.push_str(&format!("\ntelemetry:\n{telemetry}"));
        }
        output.push_str(&format!("\ncreated: {}", issue.created_at));
        if let Some(resolved_at) = issue.resolved_at {
            output.push_str(&format!("\nresolved: {resolved_at}"));
        }
    }
    output
}

#[cfg(test)]
mod tests {
    use tempfile::tempdir;

    use super::*;

    #[test]
    fn issues_deduplicate_while_open_and_close_with_a_disposition() {
        let directory = tempdir().unwrap();
        let store = IssueStore::new(directory.path().join("issues.db")).unwrap();
        assert_eq!(
            store.create(directory.path(), "stale check", None).unwrap(),
            "i1"
        );
        assert_eq!(
            store.create(directory.path(), "stale check", None).unwrap(),
            "i1"
        );
        assert!(
            store
                .list("open")
                .unwrap()
                .contains("i1 open 2x stale check")
        );
        assert!(store.show("i1", false).unwrap().contains("i1 open 2x"));
        assert_eq!(
            store.resolve("i1", Some("abc123"), None).unwrap(),
            "i1 resolved"
        );
        assert_eq!(store.list("open").unwrap(), "no open issues");
        assert!(
            store
                .show("i1", false)
                .unwrap()
                .contains("fixed by: abc123")
        );
        assert_eq!(
            store
                .create(directory.path(), "not a tool bug", None)
                .unwrap(),
            "i2"
        );
        assert_eq!(
            store.dismiss("i2", "formalization question").unwrap(),
            "i2 dismissed"
        );
        assert_eq!(
            store.list("dismissed").unwrap(),
            "i2 dismissed not a tool bug"
        );
        assert_eq!(
            store.list("resolved").unwrap(),
            "i1 resolved 2x stale check"
        );
        let dismissed = store.show("i2", false).unwrap();
        assert!(dismissed.contains("i2 dismissed"));
        assert!(dismissed.contains("formalization question"));
    }

    #[test]
    fn telemetry_aggregates_and_exposes_slow_events() {
        let directory = tempdir().unwrap();
        let store = TelemetryStore::new(directory.path().join("development.db")).unwrap();
        let connection = open_db(&store.path).unwrap();
        for (verb, duration, ok, reference, outcome_class) in [
            ("check", 12, true, None, None),
            ("check", 1200, false, Some("c1"), Some("formalization")),
            ("search", 8, false, None, Some("operational")),
        ] {
            connection
                .execute(
                    "INSERT INTO telemetry_events(
                        created_at, build, project, workspace, verb, reference, ok,
                        outcome_class, error_class,
                        client_ms, daemon_ms, rss_kib, request_bytes, response_bytes,
                        request_json, response_json
                     ) VALUES (?1, 'test', '/repo', 'w1', ?2, ?3, ?4, ?5, NULL,
                               ?6, ?6, 1024, 10, 20, '{}', '{}')",
                    params![now_unix_ms(), verb, reference, ok, outcome_class, duration],
                )
                .unwrap();
        }
        let summary = store.summary("24h", None, None).unwrap();
        assert!(summary.contains("check 2 avg:606ms p50:12ms p95:1.2s fail:1 err:0"));
        assert!(summary.contains("search 1 avg:8ms p50:8ms p95:8ms err:1"));
        assert!(summary.contains("recent errors\ne3 search 8ms error"));
        assert!(summary.contains("recent formalization failures\ne2 check 1.2s failed c1"));
        let slow = store.summary("all", None, Some(1)).unwrap();
        assert!(slow.starts_with("e2 check 1.2s failed c1"));
        assert!(store.show("e2", true).unwrap().contains("request: {}"));
        connection
            .execute(
                "UPDATE telemetry_events SET request_json = '{\"cwd\":\"w1\"}' WHERE id = 3",
                [],
            )
            .unwrap();
        connection
            .execute(
                "INSERT INTO telemetry_events(
                    created_at, build, project, workspace, verb, reference, ok, error_class,
                    client_ms, daemon_ms, rss_kib, request_bytes, response_bytes,
                    request_json, response_json
                 ) VALUES (?1, 'test', '/repo', 'w2', 'search', NULL, 1, NULL,
                           1, 1, 1024, 10, 20, '{\"cwd\":\"w2\"}', '{}')",
                [now_unix_ms() + 1],
            )
            .unwrap();
        let exchange = store
            .latest_exchange(Path::new("/repo"), Some("w1"))
            .unwrap()
            .unwrap();
        assert!(exchange.contains("\"cwd\":\"w1\""));
        assert!(!exchange.contains("\"cwd\":\"w2\""));
    }

    #[test]
    fn telemetry_error_classes_ignore_run_specific_headers() {
        assert_eq!(
            error_class("c5364 27639ms\nDemo:12:3: error: No goals to be solved\n  12 | exact h"),
            "no goals to be solved"
        );
        assert_eq!(
            error_class(
                "c5361 421ms\nDemo:9:2: error(lean.synthInstanceFailed): failed to synthesize instance"
            ),
            "lean.synthInstanceFailed"
        );
        assert_eq!(
            error_class("source file is on managed main; run mathmux sync"),
            "source file is on managed main; run mathmux sync"
        );
        assert_eq!(
            error_class(
                "c5365 900ms\nwarning Demo:2:1: warning: unused variable\nDemo:9:2: error: Tactic `rfl` failed"
            ),
            "Tactic `rfl` failed"
        );
        assert_eq!(
            error_class("error q123\nsuggestion: Demo.target : Nat"),
            "near suggestions"
        );
        assert_eq!(error_class("error q124\nq124 no results"), "no results");
        assert_eq!(
            error_class("q128\nUNMERGED (w1:sibling:agent): Demo.target"),
            "near suggestions"
        );
        assert_eq!(
            error_class("q126\n_root_.Demo.target : Nat\nnot found: Demo.missing"),
            "no results"
        );
        assert_eq!(
            error_class(
                "q127\ngoal Demo.lean:45\nno tactic context at line 45; use search for source context"
            ),
            "no tactic context"
        );
        assert_eq!(
            error_class("error q125\nambiguous declaration name: target"),
            "ambiguous declaration name"
        );
    }

    #[test]
    fn telemetry_distinguishes_lean_failures_from_operational_errors() {
        let directory = tempdir().unwrap();
        let state = State::new(directory.path().join("state.db")).unwrap();
        state
            .add_workspace(&crate::state::Workspace {
                reference: "w1".into(),
                name: "worker".into(),
                path: directory.path().to_path_buf(),
                branch: "worker".into(),
                model: None,
            })
            .unwrap();
        state
            .add_check_run(
                &crate::state::CheckRun {
                    reference: "c1".into(),
                    workspace_ref: "w1".into(),
                    status: crate::state::CheckStatus::Failed,
                    files: vec!["Demo.lean".into()],
                    passed: Vec::new(),
                    failed: Some("Demo.lean".into()),
                    not_checked: Vec::new(),
                    warnings: Vec::new(),
                    linters: Vec::new(),
                    suggestions: Vec::new(),
                    diagnostics: vec![crate::state::Diagnostic {
                        kind: "lean.dependency".into(),
                        text: "type mismatch".into(),
                        context: None,
                    }],
                    profile: None,
                    duration_ms: 10,
                    created_at: now_unix_ms(),
                },
                &[],
            )
            .unwrap();
        let request = Request {
            build: String::new(),
            generation: 0,
            cwd: directory.path().to_string_lossy().into_owned(),
            command: Command::Check {
                file: None,
                profile: false,
            },
        };
        assert_eq!(
            failure_outcome_class(&state, &request, &Response::error("c1 10ms"), Some("c1")),
            Some("formalization")
        );
        assert_eq!(
            failure_outcome_class(
                &state,
                &request,
                &Response::error("workspace has no dirty Lean files"),
                None,
            ),
            Some("operational")
        );
    }

    #[test]
    fn search_telemetry_keeps_only_bounded_outcomes_and_follow_up() {
        let directory = tempdir().unwrap();
        let root = directory.path().join("repo");
        let state_dir = directory.path().join("state");
        fs::create_dir_all(&root).unwrap();
        fs::create_dir_all(&state_dir).unwrap();
        let repo = Repo {
            root: root.clone(),
            common_git_dir: directory.path().join("git"),
            state_dir: state_dir.clone(),
            socket_path: state_dir.join("daemon.sock"),
            db_path: state_dir.join("state.sqlite3"),
            search_db_path: state_dir.join("search.sqlite3"),
            log_path: state_dir.join("daemon.log"),
            cache_dir: state_dir.join("cache"),
            integration_lock: state_dir.join("integration.lock"),
            validation_lock: state_dir.join("validation.lock"),
            startup_lock: state_dir.join("startup.lock"),
        };
        State::new(&repo.db_path)
            .unwrap()
            .add_workspace(&crate::state::Workspace {
                reference: "w1".into(),
                name: "worker".into(),
                path: root.clone(),
                branch: "worker".into(),
                model: None,
            })
            .unwrap();
        let store = TelemetryStore::new(directory.path().join("development.db")).unwrap();
        let search = Request {
            build: "test".into(),
            generation: 1,
            cwd: root.to_string_lossy().into_owned(),
            command: Command::Search {
                query: "Demo.target".into(),
                limit: None,
                all: false,
            },
        };
        store
            .record(&repo, &search, &Response::ok("q1\nDemo.target : Nat"), 12)
            .unwrap();
        assert_eq!(
            store
                .record(&repo, &search, &Response::ok("q1\nDemo.target : Nat"), 12)
                .unwrap(),
            "e1"
        );
        let probe = Request {
            command: Command::Probe {
                query: "Demo.target signature".into(),
            },
            ..search.clone()
        };
        store
            .record(&repo, &probe, &Response::ok("q2\nDemo.target : Nat"), 8)
            .unwrap();
        store
            .record(
                &repo,
                &search,
                &Response::error("q3\n_root_.Demo.target : Nat\nnot found: Demo.missing"),
                10,
            )
            .unwrap();
        let source_no_match = Request {
            command: Command::Search {
                query: "re:never_matches".into(),
                limit: None,
                all: false,
            },
            ..search.clone()
        };
        store
            .record(
                &repo,
                &source_no_match,
                &Response::ok("q4\nno regex source matches"),
                8,
            )
            .unwrap();
        let source_timeout = Request {
            command: Command::Search {
                query: "re:slow".into(),
                limit: None,
                all: false,
            },
            ..search.clone()
        };
        store
            .record(
                &repo,
                &source_timeout,
                &Response::ok("q5\nsource regex scan timed out; narrow the scope"),
                8,
            )
            .unwrap();
        let unmerged_miss = Request {
            command: Command::Search {
                query: "CompactlySupportedKZero subtype equiv".into(),
                limit: None,
                all: false,
            },
            ..search.clone()
        };
        store
            .record(
                &repo,
                &unmerged_miss,
                &Response::error(
                    "q6\nUNMERGED (w2:sibling:agent): Demo.target\n".to_owned()
                        + "unmerged sibling declarations (not usable locally):",
                ),
                8,
            )
            .unwrap();

        let connection = open_db(&store.path).unwrap();
        let row = connection
            .query_row(
                "SELECT query_class, outcome_class, response_band, follow_up
                 FROM telemetry_events WHERE id = 1",
                [],
                |row| {
                    Ok((
                        row.get::<_, Option<String>>(0)?,
                        row.get::<_, Option<String>>(1)?,
                        row.get::<_, Option<String>>(2)?,
                        row.get::<_, Option<String>>(3)?,
                    ))
                },
            )
            .unwrap();
        assert_eq!(row.0.as_deref(), Some("exact"));
        assert_eq!(row.1.as_deref(), Some("exact_hit"));
        assert_eq!(row.2.as_deref(), Some("0-1KiB"));
        assert_eq!(row.3.as_deref(), Some("probe"));
        let partial = connection
            .query_row(
                "SELECT outcome_class, error_class FROM telemetry_events WHERE id = 3",
                [],
                |row| {
                    Ok((
                        row.get::<_, Option<String>>(0)?,
                        row.get::<_, Option<String>>(1)?,
                    ))
                },
            )
            .unwrap();
        assert_eq!(partial.0.as_deref(), Some("no_result"));
        assert_eq!(partial.1.as_deref(), Some("no results"));
        let source_outcomes = connection
            .prepare(
                "SELECT outcome_class FROM telemetry_events
                 WHERE id IN (4, 5) ORDER BY id",
            )
            .unwrap()
            .query_map([], |row| row.get::<_, Option<String>>(0))
            .unwrap()
            .collect::<rusqlite::Result<Vec<_>>>()
            .unwrap();
        assert_eq!(
            source_outcomes,
            vec![Some("no_result".into()), Some("operational_error".into())]
        );
        let unmerged_outcome = connection
            .query_row(
                "SELECT outcome_class, error_class FROM telemetry_events WHERE id = 6",
                [],
                |row| {
                    Ok((
                        row.get::<_, Option<String>>(0)?,
                        row.get::<_, Option<String>>(1)?,
                    ))
                },
            )
            .unwrap();
        assert_eq!(unmerged_outcome.0.as_deref(), Some("near_suggestions"));
        assert_eq!(unmerged_outcome.1.as_deref(), Some("near suggestions"));
        assert_eq!(
            connection
                .query_row("SELECT COUNT(*) FROM telemetry_events", [], |row| {
                    row.get::<_, i64>(0)
                })
                .unwrap(),
            6
        );
    }

    #[test]
    fn telemetry_query_class_matches_identifier_boundaries() {
        let request = |query: &str| Request {
            build: String::new(),
            generation: 0,
            cwd: String::new(),
            command: Command::Search {
                query: query.into(),
                limit: None,
                all: false,
            },
        };

        assert_eq!(query_class(&request("Demo.target")), Some("exact".into()));
        assert_eq!(
            query_class(&request("Demo.target usages")),
            Some("exact".into())
        );
        assert_eq!(
            query_class(&request("CompactlySupportedKZero Sum")),
            Some("exact".into())
        );
        assert_eq!(query_class(&request("MatrixGL.")), Some("discovery".into()));
        assert_eq!(query_class(&request(".MatrixGL")), Some("discovery".into()));
    }

    #[test]
    fn follow_up_requires_the_immediate_action_in_the_same_workspace() {
        let directory = tempdir().unwrap();
        let root = directory.path().join("repo");
        let unmapped = directory.path().join("unmapped");
        let state_dir = directory.path().join("state");
        fs::create_dir_all(&root).unwrap();
        fs::create_dir_all(&unmapped).unwrap();
        fs::create_dir_all(&state_dir).unwrap();
        let repo = Repo {
            root: root.clone(),
            common_git_dir: directory.path().join("git"),
            state_dir: state_dir.clone(),
            socket_path: state_dir.join("daemon.sock"),
            db_path: state_dir.join("state.sqlite3"),
            search_db_path: state_dir.join("search.sqlite3"),
            log_path: state_dir.join("daemon.log"),
            cache_dir: state_dir.join("cache"),
            integration_lock: state_dir.join("integration.lock"),
            validation_lock: state_dir.join("validation.lock"),
            startup_lock: state_dir.join("startup.lock"),
        };
        State::new(&repo.db_path)
            .unwrap()
            .add_workspace(&crate::state::Workspace {
                reference: "w1".into(),
                name: "worker".into(),
                path: root.clone(),
                branch: "worker".into(),
                model: None,
            })
            .unwrap();
        let store = TelemetryStore::new(directory.path().join("development.db")).unwrap();

        let search = Request {
            build: "test".into(),
            generation: 1,
            cwd: root.to_string_lossy().into_owned(),
            command: Command::Search {
                query: "Demo.first".into(),
                limit: None,
                all: false,
            },
        };
        store
            .record(&repo, &search, &Response::ok("q1\nDemo.first : Nat"), 12)
            .unwrap();
        let check = Request {
            command: Command::Check {
                file: None,
                profile: false,
            },
            ..search.clone()
        };
        store
            .record(&repo, &check, &Response::ok("c1\nok"), 8)
            .unwrap();
        let probe = Request {
            command: Command::Probe {
                query: "Demo.first signature".into(),
            },
            ..search.clone()
        };
        store
            .record(&repo, &probe, &Response::ok("q2\nDemo.first : Nat"), 8)
            .unwrap();

        let unmapped_probe = Request {
            cwd: unmapped.to_string_lossy().into_owned(),
            command: Command::Probe {
                query: "Demo.first signature".into(),
            },
            ..search
        };
        store
            .record(
                &repo,
                &unmapped_probe,
                &Response::ok("q3\nDemo.first : Nat"),
                8,
            )
            .unwrap();

        let connection = open_db(&store.path).unwrap();
        let follow_up = |reference: &str| {
            connection
                .query_row(
                    "SELECT follow_up FROM telemetry_events WHERE reference = ?1",
                    [reference],
                    |row| row.get::<_, Option<String>>(0),
                )
                .unwrap()
        };
        assert_eq!(follow_up("q1").as_deref(), Some("check"));
        assert_eq!(follow_up("q2"), None);
    }
}
