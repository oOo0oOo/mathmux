use super::*;

pub(super) fn render_summary(run: &SearchRun) -> String {
    render_summary_inner(run, true)
}

pub(super) fn render_summary_without_hints(run: &SearchRun) -> String {
    render_summary_inner(run, false)
}

fn render_summary_inner(run: &SearchRun, include_hints: bool) -> String {
    let mut output = run.reference.clone();
    let proof_body_requested = query_requests_proof_body(&run.query);
    let related_results = run
        .note
        .as_deref()
        .is_some_and(|note| note.contains("related results"));
    if run.hits.is_empty() {
        output.push_str(" no results");
    }
    let summary_limit = if run.inference == "exact-miss" {
        run.hits.len().min(3)
    } else if proof_body_requested && !related_results {
        1
    } else if run.inference == "exact-batch" {
        run.hits.len()
    } else {
        SUMMARY_LIMIT
    };
    for (index, hit) in run.hits.iter().take(summary_limit).enumerate() {
        output.push('\n');
        if run.inference == "exact-miss" {
            if let Some(provenance) = hit.kind.strip_prefix("unmerged:") {
                output.push_str(&format!("UNMERGED ({provenance}): "));
            } else {
                output.push_str("suggestion: ");
            }
        }
        output.push_str(&hit.name);
        let displayed_source = if run.inference == "exact-miss" {
            None
        } else if run.inference == "probe"
            || (matches!(run.inference.as_str(), "exact" | "exact-batch")
                && (proof_body_requested || hit.kind == "fields"))
        {
            hit.source.as_deref()
        } else {
            hit.source.as_deref().filter(|_| {
                !matches!(run.inference.as_str(), "exact" | "exact-batch")
                    && !related_results
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
                                ))))
            })
        };
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
        if !(proof_body_requested && index == 0) {
            for usage in hit.usages.iter().take(3) {
                output.push_str(&format!("\n  used: {}:{}", usage.path, usage.line));
                if let Some(context) = &usage.context {
                    output.push_str(&format!(" in {context}"));
                }
            }
            if hit.usages.len() > 3 {
                output.push_str(&format!(
                    "\n  +{} usages; probe {} usages",
                    hit.usages.len() - 3,
                    probe_name(&hit.name)
                ));
            }
        }
        if let Some(source) = displayed_source {
            if run.inference != "probe"
                && !matches!(
                    hit.kind.as_str(),
                    "file"
                        | "fields"
                        | "imports"
                        | "location"
                        | "location-expanded"
                        | "outline"
                        | "source-occurrences"
                        | "source-range"
                )
            {
                output.push_str("\nsource:");
            }
            render_source(&mut output, run, hit, source, index, proof_body_requested);
        }
        if run.inference == "exact-miss" {
            let name = probe_name(&hit.name);
            if hit.kind.starts_with("unmerged:") {
                output.push_str(&format!("\n  after sync: mathmux probe {name} signature"));
            } else {
                output.push_str(&format!("\n  next: mathmux probe {name} signature"));
            }
        }
    }
    if run.hits.len() > summary_limit {
        let omitted = run.hits.len() - summary_limit;
        output.push_str(&format!("\n+{omitted} results"));
        if include_hints {
            append_next_hint(&mut output, run, summary_limit, proof_body_requested);
        } else {
            output.push_str(&format!("; show {} --all", run.reference));
        }
    } else if include_hints {
        append_complete_range_hint(&mut output, run);
        append_single_result_hint(&mut output, run, proof_body_requested);
    }
    if let Some(note) = &run.note {
        output.push_str(&format!("\n{note}"));
    }
    output
}

fn append_next_hint(
    output: &mut String,
    run: &SearchRun,
    summary_limit: usize,
    proof_body_requested: bool,
) {
    if run.inference == "exact-miss" {
        return;
    }
    if proof_body_requested {
        output.push_str(&format!("; show {} --all", run.reference));
    } else if run
        .note
        .as_deref()
        .is_some_and(|note| note.contains("related results"))
    {
        output.push_str("; next: refine query");
    } else if let Some(hit) = run.hits.first().filter(|hit| is_probeable_declaration(hit)) {
        output.push_str(&format!(
            "; next: probe {} signature",
            probe_name(&hit.name)
        ));
    } else if run.hits.len() > summary_limit {
        output.push_str("; next: refine query");
    }
}

fn append_complete_range_hint(output: &mut String, run: &SearchRun) {
    let Some(hit) = run.hits.first() else {
        return;
    };
    if hit.kind == "source-range"
        && hit
            .source
            .as_deref()
            .is_some_and(|source| source.lines().count() <= SOURCE_RANGE_LIMIT)
        && run
            .note
            .as_deref()
            .is_none_or(|note| !note.contains("lines omitted"))
    {
        output.push_str("\ncomplete range");
    }
}

fn append_single_result_hint(output: &mut String, run: &SearchRun, proof_body_requested: bool) {
    if proof_body_requested
        || run.hits.len() != 1
        || run
            .note
            .as_deref()
            .is_some_and(|note| note.contains("related results"))
    {
        return;
    }
    if let Some(hit) = run.hits.first().filter(|hit| is_probeable_declaration(hit))
        && matches!(
            run.inference.as_str(),
            "exact" | "exact-batch" | "hybrid" | "hybrid+applicability"
        )
    {
        output.push_str(&format!(
            "\nnext: probe {} signature",
            probe_name(&hit.name)
        ));
    }
}

fn is_probeable_declaration(hit: &SearchHit) -> bool {
    matches!(
        hit.kind.as_str(),
        "abbrev" | "class" | "def" | "inductive" | "instance" | "lemma" | "structure" | "theorem"
    )
}

fn probe_name(name: &str) -> &str {
    name.strip_prefix("_root_.").unwrap_or(name)
}

fn render_source(
    output: &mut String,
    run: &SearchRun,
    hit: &SearchHit,
    source: &str,
    index: usize,
    proof_body_requested: bool,
) {
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
    let lines = source.lines().collect::<Vec<_>>();
    let omitted = lines.len().saturating_sub(source_lines);
    if run.inference == "probe" && omitted > 0 {
        let head = source_lines.div_ceil(2);
        let tail = source_lines - head;
        for line in lines.iter().take(head) {
            output.push('\n');
            output.push_str(&truncate_line(line.trim_end(), 200));
        }
        output.push_str(&format!(
            "\n… {omitted} lines omitted; show {} --all",
            run.reference
        ));
        for line in lines.iter().skip(lines.len() - tail) {
            output.push('\n');
            output.push_str(&truncate_line(line.trim_end(), 200));
        }
    } else {
        for line in lines.iter().take(source_lines) {
            output.push('\n');
            output.push_str(&truncate_line(line.trim_end(), 200));
        }
    }
    if omitted > 0 {
        match hit.kind.as_str() {
            "class" | "structure" => {
                output.push_str(&format!("\n+{omitted} lines; search {} fields", hit.name))
            }
            "outline" => output.push_str(&format!(
                "\n+{omitted} declarations; show {} --all",
                run.reference
            )),
            _ => {}
        }
    }
}

pub(super) fn source_has_complete_declaration_header(hit: &SearchHit, source: &str) -> bool {
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
        || matches!(
            hit.kind.as_str(),
            "class" | "inductive" | "instance" | "structure"
        ) && header.split_whitespace().any(|word| word == "where")
}
