use super::*;

pub(super) fn render_summary(run: &SearchRun) -> String {
    let mut output = run.reference.clone();
    let proof_body_requested = query_requests_proof_body(&run.query);
    let related_results = run
        .note
        .as_deref()
        .is_some_and(|note| note.contains("related results"));
    if run.hits.is_empty() {
        output.push_str(" no results");
    }
    let summary_limit = if proof_body_requested && !related_results {
        1
    } else if run.inference == "exact-batch" {
        run.hits.len()
    } else {
        SUMMARY_LIMIT
    };
    for (index, hit) in run.hits.iter().take(summary_limit).enumerate() {
        output.push('\n');
        output.push_str(&hit.name);
        let displayed_source = hit.source.as_deref().filter(|_| {
            run.inference == "probe"
                || (!related_results
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
                                )))))
        });
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
                    "\n  +{} usages; show {} --all",
                    hit.usages.len() - 3,
                    run.reference
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
    }
    if run.hits.len() > summary_limit {
        output.push_str(&format!(
            "\n+{} results; show {} --all",
            run.hits.len() - summary_limit,
            run.reference
        ));
    }
    if let Some(note) = &run.note {
        output.push_str(&format!("\n{note}"));
    }
    output
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
