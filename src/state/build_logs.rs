use std::collections::HashSet;

use anyhow::Result;
use rusqlite::params;
use serde::{Deserialize, Serialize};

use super::State;

const RAW_LOG_BUDGET: u64 = 256 * 1024 * 1024;
const SUMMARY_BYTES: usize = 8192;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildLogSummary {
    pub original_bytes: u64,
    pub warnings: usize,
    pub diagnostics: String,
}

impl BuildLogSummary {
    pub(super) fn from_output(output: &str) -> Self {
        let warnings = output
            .lines()
            .filter(|line| line.trim_start().starts_with("warning:"))
            .count();
        let lines: Vec<_> = output.lines().collect();
        let start = lines
            .iter()
            .position(|line| line.trim_start().starts_with("error:") || line.contains(" error:"))
            .or_else(|| {
                lines
                    .iter()
                    .position(|line| line.trim_start().starts_with("warning:"))
            })
            .unwrap_or_else(|| lines.len().saturating_sub(10));
        let mut diagnostics = lines
            .iter()
            .skip(start)
            .take(20)
            .copied()
            .collect::<Vec<_>>()
            .join("\n");
        if diagnostics.len() > SUMMARY_BYTES {
            let mut end = SUMMARY_BYTES;
            while !diagnostics.is_char_boundary(end) {
                end -= 1;
            }
            diagnostics.truncate(end);
            diagnostics.push_str("\n[diagnostic excerpt truncated]");
        }
        Self {
            original_bytes: output.len() as u64,
            warnings,
            diagnostics,
        }
    }
}

impl State {
    /// Keep a bounded recent debugging window; durable certification fields are untouched.
    pub(crate) fn prune_build_logs(&self) -> Result<usize> {
        self.prune_build_logs_with_budget(RAW_LOG_BUDGET)
    }

    fn prune_build_logs_with_budget(&self, budget: u64) -> Result<usize> {
        let _guard = self.write_guard();
        let mut connection = self.open()?;
        let mut statement = connection.prepare(
            "SELECT ref, validation_status, length(CAST(build_output AS BLOB))
             FROM submissions WHERE validation_status IN ('passed', 'failed') 
             ORDER BY created_at DESC, ref DESC",
        )?;
        let rows = statement
            .query_map([], |r| {
                Ok((
                    r.get::<_, String>(0)?,
                    r.get::<_, String>(1)?,
                    r.get::<_, Option<u64>>(2)?,
                ))
            })?
            .collect::<rusqlite::Result<Vec<_>>>()?;
        drop(statement);
        let mut keep = HashSet::new();
        let (mut failures, mut bytes) = (0, 0_u64);
        for (index, (reference, status, size)) in rows.iter().enumerate() {
            if status == "failed" {
                failures += 1;
            }
            if (index < 10 || (status == "failed" && failures <= 10))
                && size.is_some_and(|size| size <= budget.saturating_sub(bytes))
            {
                keep.insert(reference.clone());
                bytes += size.unwrap_or(0);
            }
        }
        let mut removed = 0;
        // One transaction per log bounds memory and write-lock duration during legacy cleanup.
        for (reference, _, size) in rows {
            if size.is_none() {
                continue;
            }
            let transaction =
                connection.transaction_with_behavior(rusqlite::TransactionBehavior::Immediate)?;
            let summarized: bool = transaction.query_row(
                "SELECT EXISTS(SELECT 1 FROM build_log_summaries WHERE submission_ref = ?1)",
                [&reference],
                |r| r.get(0),
            )?;
            if !summarized {
                let (output, detail): (Option<String>, Option<String>) = transaction.query_row(
                    "SELECT build_output, validation_detail FROM submissions WHERE ref = ?1",
                    [&reference],
                    |r| Ok((r.get(0)?, r.get(1)?)),
                )?;
                if let Some(output) = output {
                    let summary = BuildLogSummary::from_output(&output);
                    transaction.execute(
                        "INSERT INTO build_log_summaries VALUES (?1, ?2)",
                        params![reference, serde_json::to_string(&summary)?],
                    )?;
                    // Legacy generic failures derived their useful headline from raw output.
                    let enriched =
                        crate::util::enriched_validation_detail(detail.as_deref(), Some(&output));
                    transaction.execute(
                        "UPDATE submissions SET validation_detail = ?2 WHERE ref = ?1",
                        params![reference, enriched],
                    )?;
                }
            }
            if !keep.contains(&reference) {
                removed += transaction.execute("UPDATE submissions SET build_output = NULL WHERE ref = ?1 AND validation_status IN ('passed', 'failed')", [&reference])?;
            }
            transaction.commit()?;
        }
        Ok(removed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::{Submission, ValidationReport, ValidationStatus, Workspace};

    #[test]
    fn retention_keeps_recent_and_failure_windows_and_durable_evidence() {
        let dir = tempfile::tempdir().unwrap();
        let state = State::new(dir.path().join("state.db")).unwrap();
        state
            .add_workspace(&Workspace {
                reference: "w1".into(),
                name: "agent".into(),
                path: dir.path().join("agent"),
                branch: "agent".into(),
                model: None,
            })
            .unwrap();
        for i in 1..=40 {
            state
                .add_submission(&Submission {
                    reference: format!("s{i}"),
                    workspace_ref: "w1".into(),
                    workspace_commit: "work".into(),
                    main_commit: "main".into(),
                    base_commit: "base".into(),
                    checks: vec![],
                    validation_status: if i <= 15 {
                        ValidationStatus::Failed
                    } else {
                        ValidationStatus::Passed
                    },
                    validation_detail: Some("build failed".into()),
                    build_output: Some(
                        "warning: keep count\nerror: useful failure\n  context".into(),
                    ),
                    build_summary: None,
                    axioms: vec!["axiom-evidence".into()],
                    sorries: vec!["sorry-location".into()],
                    validation_duration_ms: Some(12),
                    validated_by: None,
                    created_at: i,
                })
                .unwrap();
        }
        assert_eq!(state.prune_build_logs().unwrap(), 20);
        for i in 1..=40 {
            let submission = state.submission(&format!("s{i}")).unwrap().unwrap();
            assert_eq!(
                submission.build_output.is_some(),
                i >= 31 || (6..=15).contains(&i)
            );
            assert_eq!(submission.build_summary.as_ref().unwrap().warnings, 1);
            assert_eq!(submission.axioms, ["axiom-evidence"]);
            assert_eq!(submission.sorries, ["sorry-location"]);
            assert!(
                submission
                    .validation_detail
                    .unwrap()
                    .contains("useful failure")
            );
        }
        let shown = state.show("s1", true).unwrap();
        assert!(shown.contains("raw build output expired"));
        assert!(shown.contains("useful failure"));
        assert!(shown.contains("build warnings: 1"));
        assert_eq!(state.prune_build_logs().unwrap(), 0);
        state
            .finish_validation(
                "s40",
                &ValidationReport {
                    passed: true,
                    detail: "build passed".into(),
                    build_output: "new output".into(),
                    axioms: vec![],
                    sorries: vec![],
                    sorry_audit: true,
                    duration_ms: 7,
                },
            )
            .unwrap();
        assert_eq!(
            state
                .submission("s40")
                .unwrap()
                .unwrap()
                .build_summary
                .unwrap()
                .original_bytes,
            10
        );
        let mut next = state.submission("s40").unwrap().unwrap();
        next.reference = "s41".into();
        next.created_at = 41;
        next.validation_status = ValidationStatus::Queued;
        next.build_output = None;
        next.build_summary = None;
        state.add_submission(&next).unwrap();
        state
            .finish_validation(
                "s41",
                &ValidationReport {
                    passed: true,
                    detail: "build passed".into(),
                    build_output: "latest".into(),
                    axioms: vec![],
                    sorries: vec![],
                    sorry_audit: true,
                    duration_ms: 8,
                },
            )
            .unwrap();
        assert!(
            state
                .submission("s31")
                .unwrap()
                .unwrap()
                .build_output
                .is_none()
        );
        assert!(
            state
                .submission("s41")
                .unwrap()
                .unwrap()
                .build_output
                .is_some()
        );
        assert_eq!(state.prune_build_logs_with_budget(1).unwrap(), 20);
        assert!(
            state
                .submission("s40")
                .unwrap()
                .unwrap()
                .build_output
                .is_none()
        );
        assert!(
            state
                .submission("s40")
                .unwrap()
                .unwrap()
                .build_summary
                .is_some()
        );
    }

    #[test]
    fn diagnostic_summary_is_bounded_and_prefers_errors_over_build_noise() {
        let output = format!(
            "{}\nwarning: one\nerror: important\n{}",
            "info: Built dependency\n".repeat(500),
            "λ".repeat(10000)
        );
        let summary = BuildLogSummary::from_output(&output);
        assert_eq!(summary.warnings, 1);
        assert!(summary.diagnostics.starts_with("error: important"));
        assert!(summary.diagnostics.len() < SUMMARY_BYTES + 100);
    }
}
