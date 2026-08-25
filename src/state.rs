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
    pub duration_ms: u64,
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
                ON submissions(validation_status, created_at);",
        )?;
        let _ = connection.execute("ALTER TABLE workspaces ADD COLUMN deleted_at INTEGER", []);
        let _ = connection.execute(
            "ALTER TABLE checks ADD COLUMN source_version INTEGER NOT NULL DEFAULT 1",
            [],
        );
        for statement in [
            "ALTER TABLE submissions ADD COLUMN build_output TEXT",
            "ALTER TABLE submissions ADD COLUMN axioms_json TEXT NOT NULL DEFAULT '[]'",
            "ALTER TABLE submissions ADD COLUMN sorries_json TEXT NOT NULL DEFAULT '[]'",
            "ALTER TABLE submissions ADD COLUMN validation_duration_ms INTEGER",
        ] {
            let _ = connection.execute(statement, []);
        }
        migrate_legacy_checks(&connection)?;
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
                warnings_json, linters_json, diagnostics_json, duration_ms, created_at
             ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12)",
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
                        duration_ms, created_at
                 FROM check_runs WHERE ref = ?1",
                [reference],
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
        duration_ms: row.get(10)?,
        created_at: row.get(11)?,
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
}
