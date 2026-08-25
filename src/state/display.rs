use std::collections::HashSet;

use anyhow::{Result, bail};

use super::{CheckRun, Diagnostic, SearchRun, Submission};
use crate::util::{
    SOURCE_PREVIEW_LINES, format_duration, query_requests_proof_body, short_hash, single_line,
    truncate_line,
};

pub(super) fn render_search_run(run: &SearchRun, all: bool) -> String {
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
                        SOURCE_PREVIEW_LINES
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

pub(super) fn validate_reference(reference: &str) -> Result<char> {
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

pub(super) fn render_check_run(run: &CheckRun, all: bool) -> String {
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

pub(super) fn render_submission(submission: &Submission, all: bool) -> String {
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
    let mut seen = HashSet::new();
    output
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
        .collect::<Vec<_>>()
        .join("\n")
}
