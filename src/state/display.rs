use std::collections::HashSet;

use anyhow::{Result, bail};

use super::{CheckProfile, CheckRun, Diagnostic, SEARCH_USAGE_LIMIT, SearchRun, Submission};
use crate::util::{
    SOURCE_PREVIEW_LINES, format_duration, query_requests_proof_body, short_hash, single_line,
    truncate_line,
};

impl CheckProfile {
    pub fn render(&self, all: bool) -> String {
        let mut output = format!("profile:\n  planning {}ms", self.planning_ms);
        for file in self.files.iter().take(32) {
            let target = if self.files.len() == 1 {
                std::path::Path::new(&file.target)
                    .file_name()
                    .and_then(|name| name.to_str())
                    .unwrap_or(&file.target)
            } else {
                &file.target
            };
            let reuse = file
                .reused_prefix_lines
                .map(|lines| format!(", reused {lines} lines"))
                .unwrap_or_default();
            let queue = if file.queue_ms > 0 {
                format!(", queue {}ms", file.queue_ms)
            } else {
                String::new()
            };
            output.push_str(&format!(
                "\n  {} {} {}ms (deps {}ms, cache {}ms, setup {}ms, Lean {}ms{}{})",
                target,
                file.mode,
                file.total_ms,
                file.dependencies_ms,
                file.cache_ms,
                file.setup_ms,
                file.elaborate_ms,
                reuse,
                queue,
            ));
        }
        if self.files.len() > 32 {
            output.push_str(&format!("\n  +{} files", self.files.len() - 32));
        }
        let mut hotspots = self
            .files
            .iter()
            .flat_map(|file| {
                file.entries
                    .iter()
                    .map(move |entry| (file.target.as_str(), entry))
            })
            .collect::<Vec<_>>();
        hotspots.sort_by(|(_, left), (_, right)| {
            right
                .duration_ms
                .partial_cmp(&left.duration_ms)
                .unwrap_or(std::cmp::Ordering::Equal)
        });
        if !hotspots.is_empty() {
            let limit = if all { hotspots.len() } else { 8 };
            let mut seen = HashSet::new();
            let source = hotspots
                .iter()
                .filter(|(_, entry)| entry.line > 0)
                .filter(|(target, entry)| {
                    seen.insert((*target, entry.line))
                })
                .take(limit)
                .collect::<Vec<_>>();
            if !source.is_empty() {
                output.push_str("\n  source hotspots:");
                for (target, entry) in source {
                    let location = if self.files.len() == 1 {
                        format!("{}:{}", entry.line, entry.column)
                    } else {
                        format!("{}:{}:{}", target, entry.line, entry.column)
                    };
                    let detail = if entry.detail.is_empty() {
                        String::new()
                    } else {
                        format!(" {}", truncate_line(&single_line(&entry.detail), 160))
                    };
                    output.push_str(&format!(
                        "\n    {} {} {}{}",
                        location,
                        format_profile_ms(entry.duration_ms),
                        entry.kind,
                        detail
                    ));
                }
            }
            let named = hotspots
                .iter()
                .filter(|(_, entry)| entry.line == 0 && !entry.detail.is_empty())
                .take(if all { usize::MAX } else { 6 })
                .collect::<Vec<_>>();
            if !named.is_empty() {
                output.push_str("\n  Lean hotspots:");
                for (_, entry) in named {
                    output.push_str(&format!(
                        "\n    {} {} {}",
                        format_profile_ms(entry.duration_ms),
                        entry.kind,
                        truncate_line(&single_line(&entry.detail), if all { 500 } else { 160 }),
                    ));
                }
            }
            let components = hotspots
                .iter()
                .filter(|(_, entry)| entry.line == 0 && entry.detail.is_empty())
                .take(limit)
                .collect::<Vec<_>>();
            if !components.is_empty() {
                output.push_str("\n  Lean components:");
                for (_, entry) in components {
                    output.push_str(&format!(
                        "\n    {} {}",
                        format_profile_ms(entry.duration_ms),
                        entry.kind
                    ));
                }
            }
        } else if self.files.iter().any(|file| file.mode == "profile") {
            output.push_str("\n  hotspots: none captured");
        }
        output
    }
}

fn format_profile_ms(duration_ms: f64) -> String {
    if duration_ms >= 10.0 {
        format!("{duration_ms:.0}ms")
    } else if duration_ms >= 1.0 {
        format!("{duration_ms:.1}ms")
    } else {
        format!("{duration_ms:.2}ms")
    }
}

pub(super) fn render_search_run(run: &SearchRun, all: bool) -> String {
    let mut output = format!("{}\nquery: {}", run.reference, run.query);
    let mut shown_ambient_contexts = HashSet::new();
    if let Some(note) = &run.note {
        output.push_str(&format!("\n{note}"));
    }
    if run.hits.is_empty() {
        output.push_str("\nno results");
        return output;
    }
    let hit_limit = if all { run.hits.len() } else { 5 };
    for (index, hit) in run.hits.iter().take(hit_limit).enumerate() {
        output.push_str(&format!("\n{}. {}", index + 1, hit.name));
        if let Some(signature) = &hit.signature {
            let signature = single_line(signature);
            if all || matches!(run.inference.as_str(), "exact" | "exact-batch") {
                output.push_str(&format!(" : {signature}"));
            } else {
                output.push_str(&format!(" : {}", truncate_line(&signature, 300)));
            }
        }
        if !hit.path.is_empty() {
            output.push_str(&format!("\n   {}", hit.path));
            if hit.line > 0 {
                output.push_str(&format!(":{}", hit.line));
            }
        }
        if hit.applicable {
            output.push_str("  applicable");
        }
        if !hit.usages.is_empty() {
            let suffix = if hit.usages.len() == SEARCH_USAGE_LIMIT {
                "+"
            } else {
                ""
            };
            output.push_str(&format!("  refs:{}{suffix}", hit.usages.len()));
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
            if index < 3 && let Some(source) = &hit.source {
                let source = without_repeated_ambient_context(source, &mut shown_ambient_contexts);
                if !matches!(hit.kind.as_str(), "fields" | "location") {
                    output.push_str("\n   source:");
                }
                let source_lines = match hit.kind.as_str() {
                    "fields" | "outline" | "source-range" | "source-occurrences" => usize::MAX,
                    "class" | "inductive" | "structure" => 48,
                    _ if index == 0 && query_requests_proof_body(&run.query) => 48,
                    _ => SOURCE_PREVIEW_LINES,
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
        let guidance = if all {
            "already at --all detail; refine the query"
        } else {
            "refine the query"
        };
        output.push_str(&format!(
            "\n+{} results omitted; {guidance}",
            run.hits.len() - hit_limit,
        ));
    }
    output
}

fn without_repeated_ambient_context<'a>(source: &'a str, shown: &mut HashSet<String>) -> &'a str {
    let Some((ambient, declaration)) = source.split_once("\n\n") else {
        return source;
    };
    if !ambient.starts_with("-- ambient context") || shown.insert(ambient.to_owned()) {
        source
    } else {
        declaration
    }
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
    append_diagnostics(&mut output, "diagnostics", &run.diagnostics, None, 120);
    append_diagnostics(&mut output, "warnings", &run.warnings, Some(8), 30);
    append_diagnostics(&mut output, "suggestions", &run.suggestions, Some(8), 30);
    if all {
        append_diagnostics(&mut output, "linters", &run.linters, Some(8), 30);
    } else if !run.linters.is_empty() {
        output.push_str(&format!("\nlinters: {}", run.linters.len()));
    }
    if let Some(profile) = &run.profile {
        output.push('\n');
        output.push_str(&profile.render(all));
    }
    output
}

pub(super) fn render_submission(
    submission: &Submission,
    files: &[String],
    later_passing_validation: Option<&str>,
    all: bool,
) -> String {
    if submission.validation_status == "skipped" {
        return format!(
            "{} covered-by:{}",
            submission.reference,
            submission.validated_by.as_deref().unwrap_or("pending")
        );
    }
    let mut output = format!("{} {}", submission.reference, submission.validation_status);
    if submission.validation_status == "failed"
        && let Some(reference) = later_passing_validation
    {
        output.push_str(&format!("\nhistorical: later validation {reference} passed"));
    }
    if !submission.checks.is_empty() {
        output.push_str(&format!("\ncheck: {}", submission.checks.join(" ")));
    }
    if !files.is_empty() {
        output.push_str("\nfiles:");
        let limit = if all { files.len() } else { 12 };
        for file in files.iter().take(limit) {
            output.push_str(&format!("\n  {file}"));
        }
        if files.len() > limit {
            output.push_str(&format!(
                "\n  +{} files; show {} --all",
                files.len() - limit,
                submission.reference
            ));
        }
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
        if submission.validation_status == "passed" {
            let warnings = build_output
                .lines()
                .filter(|line| line.trim_start().starts_with("warning:"))
                .count();
            if warnings > 0 {
                if all {
                    output.push_str(&format!(
                        "\nbuild warnings: {warnings} total; unrelated output omitted"
                    ));
                } else {
                    output.push_str(&format!(
                        "\nbuild warnings: {warnings}; show {} --all",
                        submission.reference
                    ));
                }
            }
            if all {
                let rendered = relevant_passed_build_output(build_output, files);
                if !rendered.is_empty() {
                    output.push_str("\noutput:");
                    for line in rendered.lines() {
                        output.push_str(&format!("\n  {line}"));
                    }
                }
            }
        } else {
            let rendered = if all {
                bounded_build_output(build_output)
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

fn append_diagnostics(
    output: &mut String,
    label: &str,
    diagnostics: &[Diagnostic],
    limit: Option<usize>,
    line_limit: usize,
) {
    if diagnostics.is_empty() {
        return;
    }
    output.push_str(&format!("\n{label}:"));
    let maximum = limit.unwrap_or(diagnostics.len()).min(diagnostics.len());
    let mut remaining = line_limit;
    let mut shown = 0;
    for diagnostic in diagnostics.iter().take(maximum) {
        if remaining == 0 {
            break;
        }
        let lines = diagnostic
            .text
            .trim()
            .lines()
            .chain(
                diagnostic
                    .context
                    .as_deref()
                    .into_iter()
                    .flat_map(str::lines),
            )
            .collect::<Vec<_>>();
        if lines.len() <= remaining {
            for line in &lines {
                output.push_str(&format!("\n  {line}"));
            }
            remaining -= lines.len();
        } else {
            let content = remaining.saturating_sub(1);
            let first = content / 3;
            let last = content - first;
            for line in lines.iter().take(first) {
                output.push_str(&format!("\n  {line}"));
            }
            output.push_str(&format!(
                "\n  ... {} diagnostic lines omitted ...",
                lines.len().saturating_sub(content)
            ));
            for line in lines.iter().skip(lines.len().saturating_sub(last)) {
                output.push_str(&format!("\n  {line}"));
            }
            remaining = 0;
        }
        shown += 1;
    }
    if shown < diagnostics.len() {
        output.push_str(&format!(
            "\n  +{} {label} omitted",
            diagnostics.len() - shown
        ));
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

fn bounded_build_output(output: &str) -> String {
    const LINE_LIMIT: usize = 120;
    const TAIL_LINES: usize = 30;

    let lines = output.trim().lines().collect::<Vec<_>>();
    if lines.len() <= LINE_LIMIT {
        return lines.join("\n");
    }
    let head_lines = LINE_LIMIT - TAIL_LINES;
    let omitted = lines.len() - LINE_LIMIT;
    let mut selected = lines[..head_lines]
        .iter()
        .map(|line| (*line).to_owned())
        .collect::<Vec<_>>();
    selected.push(format!("... {omitted} build lines omitted ..."));
    selected.extend(
        lines[lines.len() - TAIL_LINES..]
            .iter()
            .map(|line| (*line).to_owned()),
    );
    selected.join("\n")
}

fn relevant_passed_build_output(output: &str, files: &[String]) -> String {
    let mut keep = false;
    let mut selected = Vec::new();
    for line in output.lines() {
        let trimmed = line.trim_start();
        if ["warning:", "info:", "error:"]
            .iter()
            .any(|prefix| trimmed.starts_with(prefix))
        {
            keep = files.iter().any(|file| trimmed.contains(file));
        } else if trimmed.starts_with("Build completed")
            || trimmed.starts_with('⚠')
            || trimmed.starts_with("Building ")
            || trimmed.starts_with("Built ")
            || trimmed.starts_with("Replayed ")
        {
            keep = false;
        }
        if keep {
            selected.push(line);
        }
    }
    bounded_build_output(&selected.join("\n"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn long_diagnostics_keep_their_head_and_tail_within_the_budget() {
        let diagnostic = Diagnostic {
            kind: "lean".into(),
            text: (1..=300)
                .map(|line| format!("diagnostic line {line}"))
                .collect::<Vec<_>>()
                .join("\n"),
            context: None,
        };
        let mut output = String::new();
        append_diagnostics(&mut output, "diagnostics", &[diagnostic], None, 12);
        assert_eq!(output.trim().lines().count(), 13);
        assert!(output.contains("diagnostic line 1"));
        assert!(output.contains("diagnostic line 300"));
        assert!(output.contains("289 diagnostic lines omitted"));
    }

    #[test]
    fn expanded_build_output_keeps_head_and_tail_within_the_budget() {
        let output = (1..=300)
            .map(|line| format!("build line {line}"))
            .collect::<Vec<_>>()
            .join("\n");
        let rendered = bounded_build_output(&output);
        assert_eq!(rendered.lines().count(), 121);
        assert!(rendered.contains("build line 1"));
        assert!(rendered.contains("build line 300"));
        assert!(rendered.contains("180 build lines omitted"));
    }

    #[test]
    fn passed_build_output_keeps_only_submitted_file_blocks() {
        let output = "warning: Other.lean:1: unrelated\n  unrelated detail\n\
info: Demo.lean:2: Demo.answer : Nat\n  signature detail\n\
warning: Demo.lean:3: relevant warning\n  relevant detail\n\
Build completed successfully";
        let rendered = relevant_passed_build_output(output, &["Demo.lean".into()]);
        assert!(!rendered.contains("Other.lean"));
        assert!(!rendered.contains("unrelated detail"));
        assert!(rendered.contains("Demo.answer : Nat"));
        assert!(rendered.contains("relevant warning"));
        assert!(rendered.contains("relevant detail"));
    }
}
