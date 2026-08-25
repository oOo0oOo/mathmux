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
use crate::util::{build_id, hash_bytes, now_unix_ms};

const SNAPSHOT_LIMIT: usize = 256 * 1024;
const LOG_LINES: usize = 80;

#[derive(Debug, Clone)]
pub struct IssueStore {
    path: PathBuf,
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
        let path = if let Some(path) = override_path {
            PathBuf::from(path)
        } else {
            let base = std::env::var_os("XDG_STATE_HOME")
                .map(PathBuf::from)
                .or_else(|| {
                    std::env::var_os("HOME")
                        .map(PathBuf::from)
                        .map(|path| path.join(".local/state"))
                })
                .context("cannot locate the local state directory")?;
            base.join("mathmux/development.sqlite3")
        };
        if std::env::var_os("MATHMUX_ISSUE_DB").is_none()
            && let Some(parent) = path.parent()
        {
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
            "SELECT id, summary, status, occurrences, context_json, fixed_by, note,
                    created_at, resolved_at FROM issues ORDER BY updated_at DESC"
        } else {
            "SELECT id, summary, status, occurrences, context_json, fixed_by, note,
                    created_at, resolved_at FROM issues WHERE status = ?1 ORDER BY updated_at DESC"
        };
        let mut statement = connection.prepare(sql)?;
        let issues = if status == "all" {
            statement
                .query_map([], issue_from_row)?
                .collect::<rusqlite::Result<Vec<_>>>()?
        } else {
            statement
                .query_map([status], issue_from_row)?
                .collect::<rusqlite::Result<Vec<_>>>()?
        };
        if issues.is_empty() {
            return Ok(if status == "all" {
                "no issues".into()
            } else {
                format!("no {status} issues")
            });
        }
        Ok(issues
            .iter()
            .map(|issue| {
                let occurrences = if issue.occurrences > 1 {
                    format!(" {}x", issue.occurrences)
                } else {
                    String::new()
                };
                format!(
                    "i{} {}{} {}",
                    issue.id, issue.status, occurrences, issue.summary
                )
            })
            .collect::<Vec<_>>()
            .join("\n"))
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

pub fn record_exchange(repo: &Repo, request: &Request, response: &Response) -> Result<()> {
    #[derive(Serialize)]
    struct Exchange<'a> {
        request: &'a Request,
        response: &'a Response,
    }

    let path = repo.state_dir.join("development-last-command.json");
    fs::write(&path, serde_json::to_vec(&Exchange { request, response })?)?;
    fs::set_permissions(path, fs::Permissions::from_mode(0o600))?;
    Ok(())
}

fn capture_context(cwd: &Path, related_ref: Option<&str>) -> Result<IssueContext> {
    let build = current_build();
    let mut context = IssueContext {
        build,
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
    if let Ok(state) = State::new(&repo.db_path) {
        context.workspace = state
            .workspace_for_path(cwd)
            .ok()
            .map(|workspace| workspace.reference);
        if let Some(reference) = related_ref {
            context.related_detail = Some(state.show(reference, true)?);
        }
    }
    let worktree = context
        .workspace
        .as_ref()
        .and_then(|_| State::new(&repo.db_path).ok())
        .and_then(|state| state.workspace_for_path(cwd).ok())
        .map(|workspace| workspace.path)
        .unwrap_or_else(|| repo.root.clone());
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
            text.truncate(remaining);
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

fn current_build() -> String {
    build_id().to_owned()
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
}
