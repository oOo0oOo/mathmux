use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};
use rusqlite::{Connection, OptionalExtension, params};
use serde::{Deserialize, Serialize};

use crate::util::now_unix_ms;

#[derive(Debug, Clone)]
pub struct State {
    path: PathBuf,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Workspace {
    pub reference: String,
    pub name: String,
    pub path: PathBuf,
    pub branch: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckRecord {
    pub reference: String,
    pub workspace_ref: String,
    pub target: String,
    pub fingerprint: String,
    pub dependencies: Vec<String>,
    pub source_version: u64,
    pub created_at: i64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Submission {
    pub reference: String,
    pub workspace_ref: String,
    pub workspace_commit: String,
    pub main_commit: String,
    pub base_commit: String,
    pub checks: Vec<String>,
    pub validation_status: String,
    pub validation_detail: Option<String>,
    pub validated_by: Option<String>,
    pub created_at: i64,
}

impl State {
    pub fn new(path: impl AsRef<Path>) -> Result<Self> {
        let state = Self {
            path: path.as_ref().to_path_buf(),
        };
        state.migrate()?;
        Ok(state)
    }

    fn open(&self) -> Result<Connection> {
        let connection = Connection::open(&self.path)
            .with_context(|| format!("cannot open {}", self.path.display()))?;
        connection.pragma_update(None, "foreign_keys", "ON")?;
        connection.busy_timeout(std::time::Duration::from_secs(10))?;
        Ok(connection)
    }

    fn migrate(&self) -> Result<()> {
        let connection = self.open()?;
        connection.pragma_update(None, "journal_mode", "WAL")?;
        connection.execute_batch(
            "CREATE TABLE IF NOT EXISTS counters (
                kind TEXT PRIMARY KEY,
                value INTEGER NOT NULL
             );
             CREATE TABLE IF NOT EXISTS workspaces (
                ref TEXT PRIMARY KEY,
                name TEXT NOT NULL UNIQUE,
                path TEXT NOT NULL UNIQUE,
                branch TEXT NOT NULL,
                created_at INTEGER NOT NULL,
                last_active INTEGER NOT NULL,
                deleted_at INTEGER
             );
             CREATE TABLE IF NOT EXISTS checks (
                ref TEXT PRIMARY KEY,
                workspace_ref TEXT NOT NULL REFERENCES workspaces(ref) ON DELETE CASCADE,
                target TEXT NOT NULL,
                fingerprint TEXT NOT NULL,
                dependencies_json TEXT NOT NULL,
                source_version INTEGER NOT NULL DEFAULT 1,
                created_at INTEGER NOT NULL
             );
             CREATE INDEX IF NOT EXISTS checks_workspace_target
                ON checks(workspace_ref, target, created_at DESC);
             CREATE TABLE IF NOT EXISTS syncs (
                ref TEXT PRIMARY KEY,
                workspace_ref TEXT NOT NULL REFERENCES workspaces(ref) ON DELETE CASCADE,
                status TEXT NOT NULL,
                detail TEXT NOT NULL,
                created_at INTEGER NOT NULL
             );
             CREATE TABLE IF NOT EXISTS submissions (
                ref TEXT PRIMARY KEY,
                workspace_ref TEXT NOT NULL REFERENCES workspaces(ref),
                workspace_commit TEXT NOT NULL,
                main_commit TEXT NOT NULL,
                base_commit TEXT NOT NULL,
                checks_json TEXT NOT NULL,
                validation_status TEXT NOT NULL,
                validation_detail TEXT,
                validated_by TEXT,
                created_at INTEGER NOT NULL
             );
             CREATE INDEX IF NOT EXISTS submissions_validation
                ON submissions(validation_status, created_at);",
        )?;
        let _ = connection.execute("ALTER TABLE workspaces ADD COLUMN deleted_at INTEGER", []);
        let _ = connection.execute(
            "ALTER TABLE checks ADD COLUMN source_version INTEGER NOT NULL DEFAULT 1",
            [],
        );
        Ok(())
    }

    pub fn next_ref(&self, kind: char) -> Result<String> {
        let mut connection = self.open()?;
        let transaction =
            connection.transaction_with_behavior(rusqlite::TransactionBehavior::Immediate)?;
        transaction.execute(
            "INSERT INTO counters(kind, value) VALUES (?1, 1)
             ON CONFLICT(kind) DO UPDATE SET value = value + 1",
            [kind.to_string()],
        )?;
        let value: i64 = transaction.query_row(
            "SELECT value FROM counters WHERE kind = ?1",
            [kind.to_string()],
            |row| row.get(0),
        )?;
        transaction.commit()?;
        Ok(format!("{kind}{value}"))
    }

    pub fn add_workspace(&self, workspace: &Workspace) -> Result<()> {
        let now = now_unix_ms();
        self.open()?.execute(
            "INSERT INTO workspaces(ref, name, path, branch, created_at, last_active)
             VALUES (?1, ?2, ?3, ?4, ?5, ?5)",
            params![
                workspace.reference,
                workspace.name,
                workspace.path.to_string_lossy(),
                workspace.branch,
                now
            ],
        )?;
        Ok(())
    }

    pub fn remove_workspace(&self, reference: &str) -> Result<()> {
        let mut connection = self.open()?;
        let transaction = connection.transaction()?;
        transaction.execute("DELETE FROM checks WHERE workspace_ref = ?1", [reference])?;
        transaction.execute(
            "UPDATE workspaces
             SET name = name || '#deleted#' || ref,
                 path = '<deleted:' || ref || '>',
                 branch = '<deleted>',
                 deleted_at = ?2
             WHERE ref = ?1 AND deleted_at IS NULL",
            params![reference, now_unix_ms()],
        )?;
        transaction.commit()?;
        Ok(())
    }

    pub fn list_workspaces(&self) -> Result<Vec<Workspace>> {
        let connection = self.open()?;
        let mut statement = connection.prepare(
            "SELECT ref, name, path, branch FROM workspaces
                 WHERE deleted_at IS NULL ORDER BY created_at",
        )?;
        let rows = statement.query_map([], workspace_from_row)?;
        rows.collect::<rusqlite::Result<Vec<_>>>()
            .map_err(Into::into)
    }

    pub fn workspace_named(&self, name: &str) -> Result<Option<Workspace>> {
        self.open()?
            .query_row(
                "SELECT ref, name, path, branch FROM workspaces
                 WHERE name = ?1 AND deleted_at IS NULL",
                [name],
                workspace_from_row,
            )
            .optional()
            .map_err(Into::into)
    }

    pub fn workspace_for_path(&self, cwd: &Path) -> Result<Workspace> {
        let cwd = std::fs::canonicalize(cwd)
            .with_context(|| format!("cannot resolve {}", cwd.display()))?;
        self.list_workspaces()?
            .into_iter()
            .filter(|workspace| cwd.starts_with(&workspace.path))
            .max_by_key(|workspace| workspace.path.as_os_str().len())
            .context("current directory is not inside a mathmux workspace")
    }

    pub fn touch_workspace(&self, reference: &str) -> Result<()> {
        self.open()?.execute(
            "UPDATE workspaces SET last_active = ?2 WHERE ref = ?1",
            params![reference, now_unix_ms()],
        )?;
        Ok(())
    }

    pub fn add_check(&self, check: &CheckRecord) -> Result<()> {
        self.open()?.execute(
            "INSERT INTO checks(
                ref, workspace_ref, target, fingerprint, dependencies_json, source_version, created_at
             ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7)",
            params![
                check.reference,
                check.workspace_ref,
                check.target,
                check.fingerprint,
                serde_json::to_string(&check.dependencies)?,
                check.source_version,
                check.created_at
            ],
        )?;
        Ok(())
    }

    pub fn latest_check(&self, workspace_ref: &str, target: &str) -> Result<Option<CheckRecord>> {
        self.open()?
            .query_row(
                "SELECT ref, workspace_ref, target, fingerprint, dependencies_json,
                        source_version, created_at
                 FROM checks WHERE workspace_ref = ?1 AND target = ?2
                 ORDER BY created_at DESC LIMIT 1",
                params![workspace_ref, target],
                check_from_row,
            )
            .optional()
            .map_err(Into::into)
    }

    pub fn checks_for_workspace(&self, workspace_ref: &str) -> Result<Vec<CheckRecord>> {
        let connection = self.open()?;
        let mut statement = connection.prepare(
            "SELECT ref, workspace_ref, target, fingerprint, dependencies_json,
                    source_version, created_at
             FROM checks WHERE workspace_ref = ?1 ORDER BY created_at DESC",
        )?;
        let rows = statement.query_map([workspace_ref], check_from_row)?;
        rows.collect::<rusqlite::Result<Vec<_>>>()
            .map_err(Into::into)
    }

    pub fn delete_checks(&self, workspace_ref: &str) -> Result<()> {
        self.open()?.execute(
            "DELETE FROM checks WHERE workspace_ref = ?1",
            [workspace_ref],
        )?;
        Ok(())
    }

    pub fn add_sync(&self, workspace_ref: &str, status: &str, detail: &str) -> Result<String> {
        let reference = self.next_ref('u')?;
        self.open()?.execute(
            "INSERT INTO syncs(ref, workspace_ref, status, detail, created_at)
             VALUES (?1, ?2, ?3, ?4, ?5)",
            params![reference, workspace_ref, status, detail, now_unix_ms()],
        )?;
        Ok(reference)
    }

    pub fn add_submission(&self, submission: &Submission) -> Result<()> {
        self.open()?.execute(
            "INSERT INTO submissions(
                ref, workspace_ref, workspace_commit, main_commit, base_commit, checks_json,
                validation_status, validation_detail, validated_by, created_at
             ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10)",
            params![
                submission.reference,
                submission.workspace_ref,
                submission.workspace_commit,
                submission.main_commit,
                submission.base_commit,
                serde_json::to_string(&submission.checks)?,
                submission.validation_status,
                submission.validation_detail,
                submission.validated_by,
                submission.created_at
            ],
        )?;
        Ok(())
    }

    pub fn submission(&self, reference: &str) -> Result<Option<Submission>> {
        self.open()?
            .query_row(
                "SELECT ref, workspace_ref, workspace_commit, main_commit, base_commit, checks_json,
                        validation_status, validation_detail, validated_by, created_at
                 FROM submissions WHERE ref = ?1",
                [reference],
                submission_from_row,
            )
            .optional()
            .map_err(Into::into)
    }

    pub fn next_validation(&self) -> Result<Option<Submission>> {
        let connection = self.open()?;
        let running: bool = connection.query_row(
            "SELECT EXISTS(SELECT 1 FROM submissions WHERE validation_status = 'running')",
            [],
            |row| row.get(0),
        )?;
        if running {
            return Ok(None);
        }
        let newest = connection
            .query_row(
                "SELECT ref, workspace_ref, workspace_commit, main_commit, base_commit, checks_json,
                        validation_status, validation_detail, validated_by, created_at
                 FROM submissions WHERE validation_status = 'queued'
                 ORDER BY created_at DESC LIMIT 1",
                [],
                submission_from_row,
            )
            .optional()?;
        let Some(newest): Option<Submission> = newest else {
            return Ok(None);
        };
        connection.execute(
            "UPDATE submissions SET validation_status = 'skipped', validated_by = ?1
             WHERE validation_status = 'queued' AND ref <> ?1",
            [&newest.reference],
        )?;
        connection.execute(
            "UPDATE submissions SET validation_status = 'running' WHERE ref = ?1",
            [&newest.reference],
        )?;
        Ok(Some(Submission {
            validation_status: "running".into(),
            ..newest
        }))
    }

    pub fn finish_validation(&self, reference: &str, passed: bool, detail: &str) -> Result<()> {
        let status = if passed { "passed" } else { "failed" };
        self.open()?.execute(
            "UPDATE submissions SET validation_status = ?2, validation_detail = ?3 WHERE ref = ?1",
            params![reference, status, detail],
        )?;
        Ok(())
    }

    pub fn recover_validation(&self) -> Result<()> {
        self.open()?.execute(
            "UPDATE submissions SET validation_status = 'queued' WHERE validation_status = 'running'",
            [],
        )?;
        Ok(())
    }

    pub fn has_validation_work(&self) -> Result<bool> {
        self.open()?
            .query_row(
                "SELECT EXISTS(SELECT 1 FROM submissions
                 WHERE validation_status IN ('queued', 'running'))",
                [],
                |row| row.get(0),
            )
            .map_err(Into::into)
    }

    pub fn show(&self, reference: &str) -> Result<String> {
        let mut characters = reference.chars();
        let Some(kind) = characters.next() else {
            bail!("empty reference");
        };
        let sequence = characters.collect::<String>();
        if sequence.is_empty() || !sequence.chars().all(|value| value.is_ascii_digit()) {
            bail!("malformed reference {reference}");
        }
        let connection = self.open()?;
        match kind {
            'w' => connection
                .query_row(
                    "SELECT ref,
                            CASE WHEN deleted_at IS NULL THEN name
                                 ELSE substr(name, 1, instr(name, '#deleted#') - 1) END,
                            path, branch, created_at, last_active, deleted_at
                     FROM workspaces WHERE ref = ?1",
                    [reference],
                    |row| Ok(format!(
                        "{} workspace {}\npath: {}\nbranch: {}\ncreated: {}\nlast active: {}\nstatus: {}",
                        row.get::<_, String>(0)?, row.get::<_, String>(1)?, row.get::<_, String>(2)?,
                        row.get::<_, String>(3)?, row.get::<_, i64>(4)?, row.get::<_, i64>(5)?,
                        if row.get::<_, Option<i64>>(6)?.is_some() { "deleted" } else { "active" }
                    )),
                )
                .optional()?,
            'c' => connection
                .query_row(
                    "SELECT ref, workspace_ref, target, fingerprint, dependencies_json,
                            source_version, created_at
                     FROM checks WHERE ref = ?1",
                    [reference],
                    |row| Ok(format!(
                        "{} check passed\nworkspace: {}\ntarget: {}\nsource version: {}\nfingerprint: {}\ndependencies: {}\ncreated: {}",
                        row.get::<_, String>(0)?, row.get::<_, String>(1)?, row.get::<_, String>(2)?,
                        row.get::<_, u64>(5)?, row.get::<_, String>(3)?, row.get::<_, String>(4)?,
                        row.get::<_, i64>(6)?
                    )),
                )
                .optional()?,
            's' => connection
                .query_row(
                    "SELECT ref, workspace_ref, workspace_commit, main_commit, base_commit, checks_json,
                            validation_status, validation_detail, validated_by, created_at
                     FROM submissions WHERE ref = ?1",
                    [reference],
                    |row| Ok(format!(
                        "{} submission\nworkspace: {}\nworkspace commit: {}\nmain commit: {}\nbase: {}\nchecks: {}\nvalidation: {}\ndetail: {}\nvalidated by: {}\ncreated: {}",
                        row.get::<_, String>(0)?, row.get::<_, String>(1)?, row.get::<_, String>(2)?,
                        row.get::<_, String>(3)?, row.get::<_, String>(4)?, row.get::<_, String>(5)?,
                        row.get::<_, String>(6)?, row.get::<_, Option<String>>(7)?.unwrap_or_default(),
                        row.get::<_, Option<String>>(8)?.unwrap_or_default(), row.get::<_, i64>(9)?
                    )),
                )
                .optional()?,
            'u' => connection
                .query_row(
                    "SELECT ref, workspace_ref, status, detail, created_at FROM syncs WHERE ref = ?1",
                    [reference],
                    |row| Ok(format!(
                        "{} sync {}\nworkspace: {}\ndetail: {}\ncreated: {}",
                        row.get::<_, String>(0)?, row.get::<_, String>(2)?, row.get::<_, String>(1)?,
                        row.get::<_, String>(3)?, row.get::<_, i64>(4)?
                    )),
                )
                .optional()?,
            _ => bail!("unknown reference type {kind}"),
        }
        .with_context(|| format!("unknown reference {reference}"))
    }
}

fn workspace_from_row(row: &rusqlite::Row<'_>) -> rusqlite::Result<Workspace> {
    Ok(Workspace {
        reference: row.get(0)?,
        name: row.get(1)?,
        path: PathBuf::from(row.get::<_, String>(2)?),
        branch: row.get(3)?,
    })
}

fn check_from_row(row: &rusqlite::Row<'_>) -> rusqlite::Result<CheckRecord> {
    let dependencies: String = row.get(4)?;
    Ok(CheckRecord {
        reference: row.get(0)?,
        workspace_ref: row.get(1)?,
        target: row.get(2)?,
        fingerprint: row.get(3)?,
        dependencies: serde_json::from_str(&dependencies).unwrap_or_default(),
        source_version: row.get(5)?,
        created_at: row.get(6)?,
    })
}

fn submission_from_row(row: &rusqlite::Row<'_>) -> rusqlite::Result<Submission> {
    let checks: String = row.get(5)?;
    Ok(Submission {
        reference: row.get(0)?,
        workspace_ref: row.get(1)?,
        workspace_commit: row.get(2)?,
        main_commit: row.get(3)?,
        base_commit: row.get(4)?,
        checks: serde_json::from_str(&checks).unwrap_or_default(),
        validation_status: row.get(6)?,
        validation_detail: row.get(7)?,
        validated_by: row.get(8)?,
        created_at: row.get(9)?,
    })
}

#[cfg(test)]
mod tests {
    use tempfile::tempdir;

    use super::*;

    #[test]
    fn references_persist_and_show_requires_a_typed_reference() {
        let directory = tempdir().unwrap();
        let path = directory.path().join("state.db");
        let state = State::new(&path).unwrap();
        assert_eq!(state.next_ref('c').unwrap(), "c1");
        assert_eq!(State::new(&path).unwrap().next_ref('c').unwrap(), "c2");
        assert!(state.show("check:c2").is_err());
        assert!(state.show("").is_err());
    }

    #[test]
    fn queued_submissions_coalesce_to_the_newest_revision() {
        let directory = tempdir().unwrap();
        let state = State::new(directory.path().join("state.db")).unwrap();
        state
            .add_workspace(&Workspace {
                reference: "w1".into(),
                name: "agent".into(),
                path: directory.path().join("agent"),
                branch: "mathmux/agent".into(),
            })
            .unwrap();
        for (reference, created_at) in [("s1", 1), ("s2", 2)] {
            state
                .add_submission(&Submission {
                    reference: reference.into(),
                    workspace_ref: "w1".into(),
                    workspace_commit: format!("workspace-{reference}"),
                    main_commit: format!("main-{reference}"),
                    base_commit: "base".into(),
                    checks: vec!["c1".into()],
                    validation_status: "queued".into(),
                    validation_detail: None,
                    validated_by: None,
                    created_at,
                })
                .unwrap();
        }
        assert_eq!(state.next_validation().unwrap().unwrap().reference, "s2");
        let skipped = state.submission("s1").unwrap().unwrap();
        assert_eq!(skipped.validation_status, "skipped");
        assert_eq!(skipped.validated_by.as_deref(), Some("s2"));
    }
}
