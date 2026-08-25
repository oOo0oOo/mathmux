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

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct Diagnostic {
    pub kind: String,
    pub text: String,
    #[serde(default)]
    pub context: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckRun {
    pub reference: String,
    pub workspace_ref: String,
    pub status: String,
    pub files: Vec<String>,
    pub passed: Vec<String>,
    pub failed: Option<String>,
    pub not_checked: Vec<String>,
    pub warnings: Vec<Diagnostic>,
    pub linters: Vec<Diagnostic>,
    pub diagnostics: Vec<Diagnostic>,
    pub profile: Option<CheckProfile>,
    pub duration_ms: u64,
    pub created_at: i64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckProfile {
    pub planning_ms: u64,
    pub files: Vec<FileCheckProfile>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileCheckProfile {
    pub target: String,
    pub mode: String,
    pub dependencies_ms: u64,
    pub cache_ms: u64,
    pub setup_ms: u64,
    pub elaborate_ms: u64,
    pub total_ms: u64,
}

impl CheckProfile {
    pub fn render(&self) -> String {
        let mut output = format!("profile:\n  planning {}ms", self.planning_ms);
        for file in self.files.iter().take(32) {
            output.push_str(&format!(
                "\n  {} {} {}ms (dependencies {}ms, cache {}ms, setup {}ms, elaborate {}ms)",
                file.target,
                file.mode,
                file.total_ms,
                file.dependencies_ms,
                file.cache_ms,
                file.setup_ms,
                file.elaborate_ms,
            ));
        }
        if self.files.len() > 32 {
            output.push_str(&format!("\n  +{} files", self.files.len() - 32));
        }
        output
    }
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
    pub build_output: Option<String>,
    pub axioms: Vec<String>,
    pub sorries: Vec<String>,
    pub validation_duration_ms: Option<u64>,
    pub validated_by: Option<String>,
    pub created_at: i64,
}

#[derive(Debug, Clone)]
pub struct ValidationReport {
    pub passed: bool,
    pub detail: String,
    pub build_output: String,
    pub axioms: Vec<String>,
    pub sorries: Vec<String>,
    pub duration_ms: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchUsage {
    pub module: String,
    pub path: String,
    pub line: u64,
    pub context: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchHit {
    pub name: String,
    pub kind: String,
    pub signature: Option<String>,
    pub module: String,
    pub path: String,
    pub line: u64,
    pub doc: Option<String>,
    pub source: Option<String>,
    pub usages: Vec<SearchUsage>,
    #[serde(default)]
    pub applicable: bool,
    #[serde(default)]
    pub required_import: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchRun {
    pub reference: String,
    pub workspace_ref: String,
    pub query: String,
    pub inference: String,
    pub hits: Vec<SearchHit>,
    pub note: Option<String>,
    pub duration_ms: u64,
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
            "CREATE TABLE IF NOT EXISTS state_meta (
                key TEXT PRIMARY KEY,
                value INTEGER NOT NULL
             );
             CREATE TABLE IF NOT EXISTS counters (
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
             CREATE TABLE IF NOT EXISTS check_runs (
                ref TEXT PRIMARY KEY,
                workspace_ref TEXT NOT NULL REFERENCES workspaces(ref),
                status TEXT NOT NULL,
                files_json TEXT NOT NULL,
                passed_json TEXT NOT NULL,
                failed TEXT,
                not_checked_json TEXT NOT NULL,
                warnings_json TEXT NOT NULL,
                linters_json TEXT NOT NULL,
                diagnostics_json TEXT NOT NULL,
                profile_json TEXT,
                duration_ms INTEGER NOT NULL,
                created_at INTEGER NOT NULL
             );
             CREATE TABLE IF NOT EXISTS certificates (
                check_ref TEXT NOT NULL REFERENCES check_runs(ref),
                workspace_ref TEXT NOT NULL REFERENCES workspaces(ref),
                target TEXT NOT NULL,
                fingerprint TEXT NOT NULL,
                dependencies_json TEXT NOT NULL,
                source_version INTEGER NOT NULL,
                PRIMARY KEY(check_ref, target)
             );
             CREATE INDEX IF NOT EXISTS certificates_workspace_target
                ON certificates(workspace_ref, target);
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
                build_output TEXT,
                axioms_json TEXT NOT NULL DEFAULT '[]',
                sorries_json TEXT NOT NULL DEFAULT '[]',
                validation_duration_ms INTEGER,
                validated_by TEXT,
                created_at INTEGER NOT NULL
             );
             CREATE INDEX IF NOT EXISTS submissions_validation
                ON submissions(validation_status, created_at);
             CREATE TABLE IF NOT EXISTS searches (
                ref TEXT PRIMARY KEY,
                workspace_ref TEXT NOT NULL REFERENCES workspaces(ref),
                query TEXT NOT NULL,
                inference TEXT NOT NULL,
                hits_json TEXT NOT NULL,
                note TEXT,
                duration_ms INTEGER NOT NULL,
                created_at INTEGER NOT NULL
             );",
        )?;
        let _ = connection.execute("ALTER TABLE workspaces ADD COLUMN deleted_at INTEGER", []);
        let _ = connection.execute(
            "ALTER TABLE checks ADD COLUMN source_version INTEGER NOT NULL DEFAULT 1",
            [],
        );
        let _ = connection.execute("ALTER TABLE check_runs ADD COLUMN profile_json TEXT", []);
        for statement in [
            "ALTER TABLE submissions ADD COLUMN build_output TEXT",
            "ALTER TABLE submissions ADD COLUMN axioms_json TEXT NOT NULL DEFAULT '[]'",
            "ALTER TABLE submissions ADD COLUMN sorries_json TEXT NOT NULL DEFAULT '[]'",
            "ALTER TABLE submissions ADD COLUMN validation_duration_ms INTEGER",
        ] {
            let _ = connection.execute(statement, []);
        }
        migrate_legacy_checks(&connection)?;
        let legacy_search_removed: bool = connection.query_row(
            "SELECT EXISTS(SELECT 1 FROM state_meta WHERE key = 'legacy_search_removed')",
            [],
            |row| row.get(0),
        )?;
        if !legacy_search_removed {
            // Search indexing moved to its own database. Remove legacy index
            // tables so queue state no longer shares pages with stale FTS data.
            connection.execute_batch(
                "DROP TABLE IF EXISTS search_fts;
                 DROP TABLE IF EXISTS search_references;
                 DROP TABLE IF EXISTS search_imports;
                 DROP TABLE IF EXISTS search_files;
                 DROP TABLE IF EXISTS search_meta;
                 INSERT INTO state_meta(key, value)
                 VALUES ('legacy_search_removed', 1);",
            )?;
        }
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

    pub fn add_check_run(&self, run: &CheckRun, certificates: &[CheckRecord]) -> Result<()> {
        let mut connection = self.open()?;
        let transaction = connection.transaction()?;
        transaction.execute(
            "INSERT INTO check_runs(
                ref, workspace_ref, status, files_json, passed_json, failed, not_checked_json,
                warnings_json, linters_json, diagnostics_json, profile_json, duration_ms, created_at
             ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13)",
            params![
                run.reference,
                run.workspace_ref,
                run.status,
                serde_json::to_string(&run.files)?,
                serde_json::to_string(&run.passed)?,
                run.failed,
                serde_json::to_string(&run.not_checked)?,
                serde_json::to_string(&run.warnings)?,
                serde_json::to_string(&run.linters)?,
                serde_json::to_string(&run.diagnostics)?,
                run.profile
                    .as_ref()
                    .map(serde_json::to_string)
                    .transpose()?,
                run.duration_ms,
                run.created_at,
            ],
        )?;
        for certificate in certificates {
            transaction.execute(
                "INSERT INTO certificates(
                    check_ref, workspace_ref, target, fingerprint, dependencies_json, source_version
                 ) VALUES (?1, ?2, ?3, ?4, ?5, ?6)",
                params![
                    run.reference,
                    run.workspace_ref,
                    certificate.target,
                    certificate.fingerprint,
                    serde_json::to_string(&certificate.dependencies)?,
                    certificate.source_version,
                ],
            )?;
        }
        transaction.commit()?;
        Ok(())
    }

    pub fn check_run(&self, reference: &str) -> Result<Option<CheckRun>> {
        self.open()?
            .query_row(
                "SELECT ref, workspace_ref, status, files_json, passed_json, failed,
                        not_checked_json, warnings_json, linters_json, diagnostics_json,
                        profile_json, duration_ms, created_at
                 FROM check_runs WHERE ref = ?1",
                [reference],
                check_run_from_row,
            )
            .optional()
            .map_err(Into::into)
    }

    pub fn latest_check_run(&self, workspace_ref: &str) -> Result<Option<CheckRun>> {
        self.open()?
            .query_row(
                "SELECT ref, workspace_ref, status, files_json, passed_json, failed,
                        not_checked_json, warnings_json, linters_json, diagnostics_json,
                        profile_json, duration_ms, created_at
                 FROM check_runs WHERE workspace_ref = ?1
                 ORDER BY created_at DESC, CAST(substr(ref, 2) AS INTEGER) DESC
                 LIMIT 1",
                [workspace_ref],
                check_run_from_row,
            )
            .optional()
            .map_err(Into::into)
    }

    pub fn checks_for_workspace(&self, workspace_ref: &str) -> Result<Vec<CheckRecord>> {
        let connection = self.open()?;
        let mut statement = connection.prepare(
            "SELECT c.check_ref, c.workspace_ref, c.target, c.fingerprint, c.dependencies_json,
                    c.source_version, r.created_at
             FROM certificates c JOIN check_runs r ON r.ref = c.check_ref
             WHERE c.workspace_ref = ?1 ORDER BY r.created_at DESC",
        )?;
        let rows = statement.query_map([workspace_ref], check_from_row)?;
        rows.collect::<rusqlite::Result<Vec<_>>>()
            .map_err(Into::into)
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
                validation_status, validation_detail, build_output, axioms_json, sorries_json,
                validation_duration_ms, validated_by, created_at
             ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14)",
            params![
                submission.reference,
                submission.workspace_ref,
                submission.workspace_commit,
                submission.main_commit,
                submission.base_commit,
                serde_json::to_string(&submission.checks)?,
                submission.validation_status,
                submission.validation_detail,
                submission.build_output,
                serde_json::to_string(&submission.axioms)?,
                serde_json::to_string(&submission.sorries)?,
                submission.validation_duration_ms,
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
                        validation_status, validation_detail, build_output, axioms_json,
                        sorries_json, validation_duration_ms, validated_by, created_at
                 FROM submissions WHERE ref = ?1",
                [reference],
                submission_from_row,
            )
            .optional()
            .map_err(Into::into)
    }

    pub fn recent_submissions(&self, limit: usize) -> Result<Vec<Submission>> {
        let connection = self.open()?;
        let mut statement = connection.prepare(
            "SELECT ref, workspace_ref, workspace_commit, main_commit, base_commit, checks_json,
                    validation_status, validation_detail, build_output, axioms_json,
                    sorries_json, validation_duration_ms, validated_by, created_at
             FROM submissions
             ORDER BY created_at DESC, CAST(substr(ref, 2) AS INTEGER) DESC
             LIMIT ?1",
        )?;
        let rows = statement.query_map([limit as i64], submission_from_row)?;
        rows.collect::<rusqlite::Result<Vec<_>>>()
            .map_err(Into::into)
    }

    pub fn pending_submissions(&self) -> Result<Vec<Submission>> {
        let connection = self.open()?;
        let mut statement = connection.prepare(
            "SELECT ref, workspace_ref, workspace_commit, main_commit, base_commit, checks_json,
                    validation_status, validation_detail, build_output, axioms_json,
                    sorries_json, validation_duration_ms, validated_by, created_at
             FROM submissions WHERE validation_status IN ('queued', 'running')
             ORDER BY CASE validation_status WHEN 'running' THEN 0 ELSE 1 END,
                      created_at, CAST(substr(ref, 2) AS INTEGER)",
        )?;
        let rows = statement.query_map([], submission_from_row)?;
        rows.collect::<rusqlite::Result<Vec<_>>>()
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
                        validation_status, validation_detail, build_output, axioms_json,
                        sorries_json, validation_duration_ms, validated_by, created_at
                 FROM submissions WHERE validation_status = 'queued'
                 ORDER BY created_at DESC,
                          CAST(substr(ref, 2) AS INTEGER) DESC
                 LIMIT 1",
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

    pub fn finish_validation(&self, reference: &str, report: &ValidationReport) -> Result<()> {
        let status = if report.passed { "passed" } else { "failed" };
        self.open()?.execute(
            "UPDATE submissions
             SET validation_status = ?2, validation_detail = ?3, build_output = ?4,
                 axioms_json = ?5, sorries_json = ?6, validation_duration_ms = ?7
             WHERE ref = ?1",
            params![
                reference,
                status,
                report.detail,
                report.build_output,
                serde_json::to_string(&report.axioms)?,
                serde_json::to_string(&report.sorries)?,
                report.duration_ms,
            ],
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

    pub fn has_running_validation(&self) -> Result<bool> {
        self.open()?
            .query_row(
                "SELECT EXISTS(SELECT 1 FROM submissions WHERE validation_status = 'running')",
                [],
                |row| row.get(0),
            )
            .map_err(Into::into)
    }

    pub fn add_search(&self, run: &SearchRun) -> Result<()> {
        self.open()?.execute(
            "INSERT INTO searches(
                ref, workspace_ref, query, inference, hits_json, note, duration_ms, created_at
             ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8)",
            params![
                run.reference,
                run.workspace_ref,
                run.query,
                run.inference,
                serde_json::to_string(&run.hits)?,
                run.note,
                run.duration_ms,
                run.created_at,
            ],
        )?;
        Ok(())
    }

    pub fn search_run(&self, reference: &str) -> Result<Option<SearchRun>> {
        self.open()?
            .query_row(
                "SELECT ref, workspace_ref, query, inference, hits_json, note,
                        duration_ms, created_at
                 FROM searches WHERE ref = ?1",
                [reference],
                |row| {
                    let hits: String = row.get(4)?;
                    Ok(SearchRun {
                        reference: row.get(0)?,
                        workspace_ref: row.get(1)?,
                        query: row.get(2)?,
                        inference: row.get(3)?,
                        hits: serde_json::from_str(&hits).unwrap_or_default(),
                        note: row.get(5)?,
                        duration_ms: row.get(6)?,
                        created_at: row.get(7)?,
                    })
                },
            )
            .optional()
            .map_err(Into::into)
    }

    pub fn show(&self, reference: &str, all: bool) -> Result<String> {
        let kind = validate_reference(reference)?;
        match kind {
            'c' => self
                .check_run(reference)?
                .map(|run| render_check_run(&run, all))
                .with_context(|| format!("unknown reference {reference}")),
            's' => self
                .submission(reference)?
                .map(|submission| render_submission(&submission, all))
                .with_context(|| format!("unknown reference {reference}")),
            'w' => self.show_workspace(reference, all),
            'u' => self.show_sync(reference, all),
            'q' => self
                .search_run(reference)?
                .map(|run| render_search_run(&run, all))
                .with_context(|| format!("unknown reference {reference}")),
            _ => bail!("unknown reference type {kind}"),
        }
    }

    fn show_workspace(&self, reference: &str, all: bool) -> Result<String> {
        self.open()?
            .query_row(
                "SELECT ref,
                        CASE WHEN deleted_at IS NULL THEN name
                             ELSE substr(name, 1, instr(name, '#deleted#') - 1) END,
                        path, branch, created_at, last_active, deleted_at
                 FROM workspaces WHERE ref = ?1",
                [reference],
                |row| {
                    let status = if row.get::<_, Option<i64>>(6)?.is_some() {
                        "deleted"
                    } else {
                        "active"
                    };
                    let mut output = format!(
                        "{} {} {}\npath: {}",
                        row.get::<_, String>(0)?,
                        row.get::<_, String>(1)?,
                        status,
                        row.get::<_, String>(2)?
                    );
                    if all {
                        output.push_str(&format!(
                            "\nbranch: {}\ncreated: {}\nlast active: {}",
                            row.get::<_, String>(3)?,
                            row.get::<_, i64>(4)?,
                            row.get::<_, i64>(5)?
                        ));
                    }
                    Ok(output)
                },
            )
            .optional()?
            .with_context(|| format!("unknown reference {reference}"))
    }

    fn show_sync(&self, reference: &str, all: bool) -> Result<String> {
        self.open()?
            .query_row(
                "SELECT ref, workspace_ref, status, detail, created_at FROM syncs WHERE ref = ?1",
                [reference],
                |row| {
                    let mut output = format!(
                        "{} {}\nworkspace: {}",
                        row.get::<_, String>(0)?,
                        row.get::<_, String>(2)?,
                        row.get::<_, String>(1)?
                    );
                    let detail = row.get::<_, String>(3)?;
                    if !detail.is_empty() {
                        output.push_str(&format!("\n{detail}"));
                    }
                    if all {
                        output.push_str(&format!("\ncreated: {}", row.get::<_, i64>(4)?));
                    }
                    Ok(output)
                },
            )
            .optional()?
            .with_context(|| format!("unknown reference {reference}"))
    }
}

fn render_search_run(run: &SearchRun, all: bool) -> String {
    let mut output = format!("{} {}\nquery: {}", run.reference, run.inference, run.query);
    if let Some(note) = &run.note {
        output.push_str(&format!("\n{note}"));
    }
    if run.hits.is_empty() {
        output.push_str("\nno results");
        return output;
    }
    let hit_limit = if all { 8 } else { 5 };
    for (index, hit) in run.hits.iter().take(hit_limit).enumerate() {
        output.push_str(&format!("\n{}. {}", index + 1, hit.name));
        if let Some(signature) = &hit.signature {
            output.push_str(&format!(
                " : {}",
                truncate_line(&single_line(signature), 300)
            ));
        }
        output.push_str(&format!("\n   {}:{}", hit.path, hit.line));
        if hit.applicable {
            output.push_str("  applicable");
        }
        if !hit.usages.is_empty() {
            output.push_str(&format!("  refs:{}", hit.usages.len()));
        }
        if let Some(module) = &hit.required_import {
            output.push_str(&format!("\n   import {module}"));
        }
        if all || index < 3 {
            if let Some(doc) = &hit.doc {
                for line in doc.trim().lines().take(3) {
                    output.push_str(&format!("\n   doc: {}", truncate_line(line.trim(), 240)));
                }
            }
            if let Some(source) = &hit.source {
                output.push_str("\n   source:");
                let source_lines =
                    if matches!(hit.kind.as_str(), "class" | "inductive" | "structure")
                        || (index == 0 && query_requests_proof_body(&run.query))
                    {
                        48
                    } else {
                        8
                    };
                for line in source.trim().lines().take(source_lines) {
                    output.push_str(&format!("\n     {}", truncate_line(line, 240)));
                }
            }
            for usage in hit.usages.iter().take(5) {
                output.push_str(&format!("\n   used: {}:{}", usage.path, usage.line));
                if let Some(context) = &usage.context {
                    output.push_str(&format!(" in {context}"));
                }
            }
        }
    }
    if run.hits.len() > hit_limit {
        output.push_str(&format!(
            "\n+{} results omitted; refine the query",
            run.hits.len() - hit_limit
        ));
    }
    output
}

fn query_requests_proof_body(query: &str) -> bool {
    let normalized = query
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
        .to_lowercase();
    normalized.contains(":= by")
        || normalized.contains("proof body")
        || normalized.contains("implementation body")
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

fn validate_reference(reference: &str) -> Result<char> {
    let mut characters = reference.chars();
    let Some(kind) = characters.next() else {
        bail!("empty reference");
    };
    let sequence = characters.collect::<String>();
    if sequence.is_empty() || !sequence.chars().all(|value| value.is_ascii_digit()) {
        bail!("malformed reference {reference}");
    }
    Ok(kind)
}

fn render_check_run(run: &CheckRun, all: bool) -> String {
    let mut output = format!("{} {} {}ms", run.reference, run.status, run.duration_ms);
    output.push_str(&format!("\nworkspace: {}", run.workspace_ref));
    if !run.files.is_empty() {
        output.push_str("\nfiles:");
        for file in &run.files {
            output.push_str(&format!("\n  {file}"));
        }
    }
    if let Some(failed) = &run.failed {
        output.push_str(&format!("\nfailed: {failed}"));
    }
    if all && !run.not_checked.is_empty() {
        output.push_str("\nnot checked:");
        for file in &run.not_checked {
            output.push_str(&format!("\n  {file}"));
        }
    }
    append_diagnostics(&mut output, "warnings", &run.warnings);
    if all {
        append_diagnostics(&mut output, "linters", &run.linters);
    } else if !run.linters.is_empty() {
        output.push_str(&format!("\nlinters: {}", run.linters.len()));
    }
    append_diagnostics(&mut output, "diagnostics", &run.diagnostics);
    if let Some(profile) = &run.profile {
        output.push('\n');
        output.push_str(&profile.render());
    }
    output
}

fn render_submission(submission: &Submission, all: bool) -> String {
    if submission.validation_status == "skipped" {
        return format!(
            "{} covered-by:{}",
            submission.reference,
            submission.validated_by.as_deref().unwrap_or("pending")
        );
    }
    let mut output = format!("{} {}", submission.reference, submission.validation_status);
    if !submission.checks.is_empty() {
        output.push_str(&format!("\ncheck: {}", submission.checks.join(" ")));
    }
    if let Some(duration) = submission.validation_duration_ms {
        output.push_str(&format!("\nbuild: {}", format_duration(duration)));
    }
    if matches!(submission.validation_status.as_str(), "passed" | "failed") {
        if !submission.axioms.is_empty() {
            output.push_str("\naxioms: failed");
            for axiom in &submission.axioms {
                output.push_str(&format!("\n  {axiom}"));
            }
        } else if submission.validation_status == "passed" {
            output.push_str("\naxioms: clean");
        } else if submission
            .validation_detail
            .as_deref()
            .is_some_and(|detail| detail.starts_with("build failed"))
        {
            output.push_str("\naxioms: not run");
        } else {
            output.push_str("\naxioms: error");
        }
        output.push_str(&format!("\nsorries: {}", submission.sorries.len()));
        if all {
            for location in &submission.sorries {
                output.push_str(&format!("\n  {location}"));
            }
        }
    }
    if let Some(detail) = &submission.validation_detail
        && !detail.is_empty()
    {
        output.push_str(&format!("\n{detail}"));
    }
    if let Some(build_output) = &submission.build_output
        && !build_output.trim().is_empty()
    {
        if !all && submission.validation_status == "passed" {
            let warnings = build_output
                .lines()
                .filter(|line| line.trim_start().starts_with("warning:"))
                .count();
            if warnings > 0 {
                output.push_str(&format!(
                    "\nbuild warnings: {warnings}; show {} --all",
                    submission.reference
                ));
            }
        } else {
            let rendered = if all {
                build_output.trim().to_owned()
            } else {
                condense_build_output(build_output)
            };
            if !rendered.is_empty() {
                output.push_str("\noutput:");
                for line in rendered.lines() {
                    output.push_str(&format!("\n  {line}"));
                }
            }
        }
    }
    if all {
        output.push_str(&format!(
            "\nworkspace: {}\nmain: {}",
            submission.workspace_ref,
            short_hash(&submission.main_commit)
        ));
    }
    output
}

fn append_diagnostics(output: &mut String, label: &str, diagnostics: &[Diagnostic]) {
    if diagnostics.is_empty() {
        return;
    }
    output.push_str(&format!("\n{label}:"));
    for diagnostic in diagnostics {
        for line in diagnostic.text.trim().lines() {
            output.push_str(&format!("\n  {line}"));
        }
        if let Some(context) = &diagnostic.context {
            for line in context.lines() {
                output.push_str(&format!("\n  {line}"));
            }
        }
    }
}

fn condense_build_output(output: &str) -> String {
    let mut seen = std::collections::HashSet::new();
    let lines: Vec<_> = output
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .filter(|line| {
            !line.starts_with("trace:")
                && !line.starts_with("info:")
                && !line.contains("Building ")
                && !line.contains("Built ")
                && !line.contains("Replayed ")
                && !line.contains("Build completed successfully")
                && !line.contains("declaration uses `sorry`")
        })
        .filter(|line| seen.insert((*line).to_owned()))
        .take(20)
        .collect();
    lines.join("\n")
}

fn format_duration(milliseconds: u64) -> String {
    if milliseconds < 1000 {
        format!("{milliseconds}ms")
    } else {
        format!("{:.1}s", milliseconds as f64 / 1000.0)
    }
}

fn short_hash(hash: &str) -> &str {
    hash.get(..8).unwrap_or(hash)
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

fn check_run_from_row(row: &rusqlite::Row<'_>) -> rusqlite::Result<CheckRun> {
    Ok(CheckRun {
        reference: row.get(0)?,
        workspace_ref: row.get(1)?,
        status: row.get(2)?,
        files: json_column(row, 3),
        passed: json_column(row, 4),
        failed: row.get(5)?,
        not_checked: json_column(row, 6),
        warnings: json_column(row, 7),
        linters: json_column(row, 8),
        diagnostics: json_column(row, 9),
        profile: row
            .get::<_, Option<String>>(10)?
            .and_then(|value| serde_json::from_str(&value).ok()),
        duration_ms: row.get(11)?,
        created_at: row.get(12)?,
    })
}

fn json_column<T: serde::de::DeserializeOwned + Default>(
    row: &rusqlite::Row<'_>,
    index: usize,
) -> T {
    row.get::<_, String>(index)
        .ok()
        .and_then(|value| serde_json::from_str(&value).ok())
        .unwrap_or_default()
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
        build_output: row.get(8)?,
        axioms: json_column(row, 9),
        sorries: json_column(row, 10),
        validation_duration_ms: row.get(11)?,
        validated_by: row.get(12)?,
        created_at: row.get(13)?,
    })
}

fn migrate_legacy_checks(connection: &Connection) -> Result<()> {
    let legacy = {
        let mut statement = connection.prepare(
            "SELECT ref, workspace_ref, target, fingerprint, dependencies_json,
                    source_version, created_at FROM checks",
        )?;
        let rows = statement.query_map([], check_from_row)?;
        rows.collect::<rusqlite::Result<Vec<_>>>()?
    };
    for check in legacy {
        connection.execute(
            "INSERT OR IGNORE INTO check_runs(
                ref, workspace_ref, status, files_json, passed_json, failed, not_checked_json,
                warnings_json, linters_json, diagnostics_json, duration_ms, created_at
             ) VALUES (?1, ?2, 'passed', ?3, ?3, NULL, '[]', '[]', '[]', '[]', 0, ?4)",
            params![
                check.reference,
                check.workspace_ref,
                serde_json::to_string(&vec![&check.target])?,
                check.created_at,
            ],
        )?;
        connection.execute(
            "INSERT OR IGNORE INTO certificates(
                check_ref, workspace_ref, target, fingerprint, dependencies_json, source_version
             ) VALUES (?1, ?2, ?3, ?4, ?5, ?6)",
            params![
                check.reference,
                check.workspace_ref,
                check.target,
                check.fingerprint,
                serde_json::to_string(&check.dependencies)?,
                check.source_version,
            ],
        )?;
    }
    Ok(())
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
        assert!(state.show("check:c2", false).is_err());
        assert!(state.show("", false).is_err());
    }

    #[test]
    fn explicit_proof_queries_show_the_top_declaration_body() {
        let hit = SearchHit {
            name: "Demo.proof".into(),
            kind: "theorem".into(),
            signature: Some("True".into()),
            module: "Demo".into(),
            path: "Demo.lean".into(),
            line: 1,
            doc: None,
            source: Some(
                (1..=12)
                    .map(|line| format!("proof line {line}"))
                    .collect::<Vec<_>>()
                    .join("\n"),
            ),
            usages: Vec::new(),
            applicable: false,
            required_import: None,
        };
        let run = |query: &str| SearchRun {
            reference: "q1".into(),
            workspace_ref: "w1".into(),
            query: query.into(),
            inference: "hybrid".into(),
            hits: vec![hit.clone()],
            note: None,
            duration_ms: 0,
            created_at: 0,
        };
        assert!(!render_search_run(&run("Demo.proof"), false).contains("proof line 9"));
        assert!(render_search_run(&run("Demo.proof :=   by"), false).contains("proof line 12"));
        assert!(render_search_run(&run("Demo.proof proof body"), false).contains("proof line 12"));
    }

    #[test]
    fn passed_validation_summarizes_build_warnings_by_default() {
        let submission = Submission {
            reference: "s1".into(),
            workspace_ref: "w1".into(),
            workspace_commit: "workspace".into(),
            main_commit: "main".into(),
            base_commit: "base".into(),
            checks: vec!["c1".into()],
            validation_status: "passed".into(),
            validation_detail: Some("build passed; axioms clean (1 modules)".into()),
            build_output: Some(
                "warning: first warning\n  detail\nwarning: second warning\n  detail".into(),
            ),
            axioms: Vec::new(),
            sorries: Vec::new(),
            validation_duration_ms: Some(1000),
            validated_by: None,
            created_at: 0,
        };
        let compact = render_submission(&submission, false);
        assert!(compact.contains("build warnings: 2; show s1 --all"));
        assert!(!compact.contains("first warning"));
        assert!(render_submission(&submission, true).contains("first warning"));
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
        for (reference, created_at) in [("s1", 1), ("s2", 1)] {
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
                    build_output: None,
                    axioms: Vec::new(),
                    sorries: Vec::new(),
                    validation_duration_ms: None,
                    validated_by: None,
                    created_at,
                })
                .unwrap();
        }
        assert_eq!(state.next_validation().unwrap().unwrap().reference, "s2");
        let skipped = state.submission("s1").unwrap().unwrap();
        assert_eq!(skipped.validation_status, "skipped");
        assert_eq!(skipped.validated_by.as_deref(), Some("s2"));
        state
            .finish_validation(
                "s2",
                &ValidationReport {
                    passed: false,
                    detail: "build passed; 1 extra axiom".into(),
                    build_output: "info: Building Proof\nerror detail".into(),
                    axioms: vec!["Unsafe.assume (used by Proof.bad)".into()],
                    sorries: vec!["Proof.lean:12:3".into()],
                    duration_ms: 1250,
                },
            )
            .unwrap();
        let compact = state.show("s2", false).unwrap();
        assert!(compact.contains("Unsafe.assume"));
        assert!(compact.contains("sorries: 1"));
        assert!(!compact.contains("Proof.lean:12:3"));
        assert!(!compact.contains("info: Building"));
        let full = state.show("s2", true).unwrap();
        assert!(full.contains("Proof.lean:12:3"));
        assert!(full.contains("info: Building Proof"));
    }

    #[test]
    fn running_validation_recovers_to_the_queue() {
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
        state
            .add_submission(&Submission {
                reference: "s1".into(),
                workspace_ref: "w1".into(),
                workspace_commit: "workspace".into(),
                main_commit: "main".into(),
                base_commit: "base".into(),
                checks: vec!["c1".into()],
                validation_status: "queued".into(),
                validation_detail: None,
                build_output: None,
                axioms: Vec::new(),
                sorries: Vec::new(),
                validation_duration_ms: None,
                validated_by: None,
                created_at: 1,
            })
            .unwrap();

        assert_eq!(state.next_validation().unwrap().unwrap().reference, "s1");
        assert!(state.has_running_validation().unwrap());
        state.recover_validation().unwrap();
        assert!(!state.has_running_validation().unwrap());
        assert_eq!(state.next_validation().unwrap().unwrap().reference, "s1");
    }
}
