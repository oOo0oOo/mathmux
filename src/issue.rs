use std::collections::BTreeMap;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, ensure};
use rusqlite::{Connection, OptionalExtension, TransactionBehavior, params};
use serde::{Deserialize, Serialize};

use crate::git::{dirty_paths, head};
use crate::protocol::{Request, Response};
use crate::repo::Repo;
use crate::state::State;
use crate::util::{build_id, hash_bytes, now_unix_ms, resident_memory_kib};

const SNAPSHOT_LIMIT: usize = 256 * 1024;
const LOG_LINES: usize = 80;
const TELEMETRY_DAYS: i64 = 30;
const TELEMETRY_LIMIT: i64 = 50_000;

#[derive(Debug, Clone)]
pub struct IssueStore {
    path: PathBuf,
}

#[derive(Debug, Clone)]
pub struct TelemetryStore {
    path: PathBuf,
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

    fn open_db(&self) -> Result<Connection> {
        let connection = Connection::open(&self.path)?;
        connection.busy_timeout(std::time::Duration::from_secs(10))?;
        Ok(connection)
    }

    fn migrate(&self) -> Result<()> {
        let connection = self.open_db()?;
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
                resolved_at INTEGER
             );
             CREATE INDEX IF NOT EXISTS issues_status_updated
                ON issues(status, updated_at DESC);
             CREATE INDEX IF NOT EXISTS issues_open_signature
                ON issues(signature) WHERE status = 'open';",
        )?;
        Ok(())
    }

    pub fn create(&self, cwd: &Path, summary: &str, related_ref: Option<&str>) -> Result<String> {
        let summary = summary.trim();
        ensure!(!summary.is_empty(), "issue summary is empty");
        ensure!(summary.len() <= 500, "issue summary is too long");
        let context = capture_context(cwd, related_ref)?;
        let signature = hash_bytes(summary.to_ascii_lowercase().as_bytes());
        let now = now_unix_ms();
        let mut connection = self.open_db()?;
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
            matches!(status, "open" | "resolved" | "all"),
            "invalid issue status"
        );
        let connection = self.open_db()?;
        let sql = if status == "all" {
            "SELECT id, summary, status, occurrences FROM issues ORDER BY updated_at DESC"
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
        let issues: Vec<String> = if status == "all" {
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
        let changed = self.open_db()?.execute(
            "UPDATE issues SET status = 'resolved', fixed_by = ?2, note = ?3,
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

    pub fn show(&self, reference: &str, all: bool) -> Result<String> {
        let id = parse_reference(reference)?;
        let issue = self
            .open_db()?
            .query_row(
                "SELECT id, summary, status, occurrences, context_json, fixed_by, note,
                        created_at, resolved_at FROM issues WHERE id = ?1",
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

    fn open_db(&self) -> Result<Connection> {
        let connection = Connection::open(&self.path)?;
        connection.busy_timeout(std::time::Duration::from_secs(10))?;
        Ok(connection)
    }

    fn migrate(&self) -> Result<()> {
        if let Some(parent) = self.path.parent() {
            fs::create_dir_all(parent)?;
        }
        let connection = self.open_db()?;
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
                ON telemetry_events(project, created_at DESC);",
        )?;
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
        let workspace = State::new(&repo.db_path)
            .ok()
            .and_then(|state| state.workspace_for_path(Path::new(&request.cwd)).ok())
            .map(|workspace| workspace.reference);
        let reference = response_reference(&response.summary);
        let error_class = (!response.ok).then(|| error_class(&response.summary));
        let now = now_unix_ms();
        let mut connection = self.open_db()?;
        let transaction = connection.transaction()?;
        transaction.execute(
            "INSERT INTO telemetry_events(
                created_at, build, project, workspace, verb, reference, ok, error_class,
                client_ms, daemon_ms, rss_kib, request_bytes, response_bytes,
                request_json, response_json
             ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14, ?15)",
            params![
                now,
                response.build,
                repo.root.to_string_lossy(),
                workspace,
                request.command.verb(),
                reference,
                response.ok,
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
        prune_telemetry(&transaction, now)?;
        transaction.commit()?;
        Ok(format!("e{id}"))
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
        let mut connection = self.open_db()?;
        let transaction = connection.transaction()?;
        transaction.execute(
            "INSERT INTO telemetry_events(
                created_at, build, project, workspace, verb, reference, ok, error_class,
                client_ms, daemon_ms, rss_kib, request_bytes, response_bytes,
                request_json, response_json
             ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?9, ?10, 2, ?11, '{}', ?12)",
            params![
                now,
                build_id(),
                repo.root.to_string_lossy(),
                operation.workspace,
                operation.verb,
                operation.reference,
                operation.ok,
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
        Ok(grouped
            .into_iter()
            .map(|(verb, events)| render_aggregate(verb, &events))
            .collect::<Vec<_>>()
            .join("\n"))
    }

    pub fn show(&self, reference: &str, all: bool) -> Result<String> {
        let id = parse_event_reference(reference)?;
        let event = self
            .open_db()?
            .query_row(
                "SELECT id, created_at, build, project, workspace, verb, reference, ok,
                        error_class, client_ms, daemon_ms, rss_kib, request_bytes,
                        response_bytes, request_json, response_json
                 FROM telemetry_events WHERE id = ?1",
                [id],
                telemetry_from_row,
            )
            .optional()?
            .with_context(|| format!("unknown reference {reference}"))?;
        Ok(render_event(&event, all))
    }

    fn events_since(&self, cutoff: i64, verb: Option<&str>) -> Result<Vec<TelemetryEvent>> {
        let connection = self.open_db()?;
        let select = "SELECT id, created_at, build, project, workspace, verb, reference, ok,
                             error_class, client_ms, daemon_ms, rss_kib, request_bytes,
                             response_bytes, request_json, response_json
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
        let connection = self.open_db()?;
        let mut statement = connection.prepare(
            "SELECT id, created_at, build, project, workspace, verb, reference, ok,
                    error_class, client_ms, daemon_ms, rss_kib, request_bytes,
                    response_bytes, request_json, response_json
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
}

pub fn record_exchange(
    repo: &Repo,
    request: &Request,
    response: &Response,
    client_ms: u64,
) -> Result<()> {
    #[derive(Serialize)]
    struct Exchange<'a> {
        request: &'a Request,
        response: &'a Response,
    }

    let path = repo.state_dir.join("development-last-command.json");
    fs::write(&path, serde_json::to_vec(&Exchange { request, response })?)?;
    fs::set_permissions(path, fs::Permissions::from_mode(0o600))?;
    TelemetryStore::global()?.record(repo, request, response, client_ms)?;
    Ok(())
}

pub fn development_enabled() -> bool {
    std::env::var("MATHMUX_DEVELOPMENT")
        .ok()
        .is_some_and(|value| matches!(value.as_str(), "1" | "true" | "yes"))
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
        error_class: row.get(8)?,
        client_ms: row.get(9)?,
        daemon_ms: row.get(10)?,
        rss_kib: row.get(11)?,
        request_bytes: row.get(12)?,
        response_bytes: row.get(13)?,
        request_json: row.get(14)?,
        response_json: row.get(15)?,
    })
}

fn render_aggregate(verb: &str, events: &[&TelemetryEvent]) -> String {
    let mut durations = events
        .iter()
        .map(|event| event.client_ms)
        .collect::<Vec<_>>();
    durations.sort_unstable();
    let errors = events.iter().filter(|event| !event.ok).count();
    let rss = events.iter().filter_map(|event| event.rss_kib).max();
    let average = durations.iter().sum::<u64>() / durations.len() as u64;
    let mut output = format!(
        "{} {} avg:{} p50:{} p95:{} err:{}",
        verb,
        events.len(),
        format_milliseconds(average),
        format_milliseconds(percentile(&durations, 50)),
        format_milliseconds(percentile(&durations, 95)),
        errors
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
    let status = if event.ok { "ok" } else { "error" };
    let reference = event
        .reference
        .as_deref()
        .map(|reference| format!(" {reference}"))
        .unwrap_or_default();
    format!(
        "e{} {} {} {}{}",
        event.id,
        event.verb,
        format_milliseconds(event.client_ms),
        status,
        reference
    )
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
            format_milliseconds(event.client_ms),
            format_milliseconds(event.daemon_ms),
            event.request_bytes,
            event.response_bytes,
        ));
        if let Some(workspace) = &event.workspace {
            output.push_str(&format!("\nworkspace: {workspace}"));
        }
        if let Some(rss) = event.rss_kib {
            output.push_str(&format!("\nrss: {}", format_memory(rss)));
        }
        output.push_str(&format!(
            "\nrequest: {}\nresponse: {}",
            event.request_json, event.response_json
        ));
    }
    output
}

fn format_milliseconds(milliseconds: u64) -> String {
    if milliseconds < 1000 {
        format!("{milliseconds}ms")
    } else {
        format!("{:.1}s", milliseconds as f64 / 1000.0)
    }
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
    let value = summary.lines().next().unwrap_or("error").trim();
    let mut boundary = value.len().min(120);
    while !value.is_char_boundary(boundary) {
        boundary -= 1;
    }
    value[..boundary].to_owned()
}

fn parse_event_reference(reference: &str) -> Result<i64> {
    let value = reference
        .strip_prefix('e')
        .filter(|value| !value.is_empty())
        .filter(|value| value.chars().all(|character| character.is_ascii_digit()))
        .with_context(|| format!("malformed telemetry reference {reference}"))?;
    Ok(value.parse()?)
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
    context.exchange =
        fs::read_to_string(repo.state_dir.join("development-last-command.json")).ok();
    let mut worktree = repo.root.clone();
    if let Ok(state) = State::new(&repo.db_path) {
        if let Ok(workspace) = state.workspace_for_path(cwd) {
            context.workspace = Some(workspace.reference);
            worktree = workspace.path;
        }
        if let Some(reference) = related_ref {
            context.related_detail = Some(state.show(reference, true)?);
        }
    }
    context.telemetry = TelemetryStore::global()
        .ok()
        .and_then(|store| store.recent(&repo.root, context.workspace.as_deref()).ok())
        .flatten();
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

fn parse_reference(reference: &str) -> Result<i64> {
    let value = reference
        .strip_prefix('i')
        .filter(|value| !value.is_empty())
        .filter(|value| value.chars().all(|character| character.is_ascii_digit()))
        .with_context(|| format!("malformed issue reference {reference}"))?;
    Ok(value.parse()?)
}

fn issue_from_row(row: &rusqlite::Row<'_>) -> rusqlite::Result<Issue> {
    let context: String = row.get(4)?;
    Ok(Issue {
        id: row.get(0)?,
        summary: row.get(1)?,
        status: row.get(2)?,
        occurrences: row.get(3)?,
        context: serde_json::from_str(&context).unwrap_or_default(),
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
    fn issues_deduplicate_while_open_and_resolve_without_claiming() {
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
    }

    #[test]
    fn telemetry_aggregates_and_exposes_slow_events() {
        let directory = tempdir().unwrap();
        let store = TelemetryStore::new(directory.path().join("development.db")).unwrap();
        let connection = store.open_db().unwrap();
        for (verb, duration, ok) in [
            ("check", 12, true),
            ("check", 1200, false),
            ("search", 8, true),
        ] {
            connection
                .execute(
                    "INSERT INTO telemetry_events(
                        created_at, build, project, workspace, verb, reference, ok, error_class,
                        client_ms, daemon_ms, rss_kib, request_bytes, response_bytes,
                        request_json, response_json
                     ) VALUES (?1, 'test', '/repo', 'w1', ?2, NULL, ?3, NULL,
                               ?4, ?4, 1024, 10, 20, '{}', '{}')",
                    params![now_unix_ms(), verb, ok, duration],
                )
                .unwrap();
        }
        let summary = store.summary("24h", None, None).unwrap();
        assert!(summary.contains("check 2 avg:606ms p50:12ms p95:1.2s err:1"));
        assert!(summary.contains("search 1 avg:8ms p50:8ms"));
        let slow = store.summary("all", None, Some(1)).unwrap();
        assert!(slow.starts_with("e2 check 1.2s error"));
        assert!(store.show("e2", true).unwrap().contains("request: {}"));
    }

    #[test]
    fn telemetry_windows_are_narrow() {
        assert_eq!(parse_since("all").unwrap(), 0);
        assert!(parse_since("24h").unwrap() < now_unix_ms());
        assert!(parse_since("soon").is_err());
    }
}
