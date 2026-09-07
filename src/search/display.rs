use super::*;
use crate::presentation::append_path_location;

pub(super) fn render_summary(run: &SearchRun) -> String {
    render_summary_inner(run, true)
}

pub(super) fn render_summary_without_hints(run: &SearchRun) -> String {
    render_summary_inner(run, false)
}

fn render_summary_inner(run: &SearchRun, include_hints: bool) -> String {
    let (verdict, trailing_note) = split_verdict_and_note(run);
    let mut output = verdict;
    if run.inference == "exact-miss"
        && let Some(note) = trailing_note
    {
        output.push('\n');
        output.push_str(note);
    }
    let proof_body_requested = query_requests_proof_body(&run.query);
    let related_results = run
        .note
        .as_deref()
        .is_some_and(|note| note.contains("related results"));
    let summary_limit = if run.inference == "exact-miss" {
        run.hits.len().min(3)
    } else if proof_body_requested && !related_results {
        1
    } else if run.inference == "exact-batch" {
        run.hits.len()
    } else {
        SUMMARY_LIMIT
    };
    let mut previous_hit_path = None;
    let mut shortened_signature = false;
    for (index, hit) in run.hits.iter().take(summary_limit).enumerate() {
        output.push('\n');
        if run.hits.len() > 1 {
            output.push_str(&format!("{}#{} ", run.reference, index + 1));
        }
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
        } else if matches!(
            run.inference.as_str(),
            "probe" | "probe-source" | "probe-source-excerpt"
        ) || (matches!(run.inference.as_str(), "exact" | "exact-batch")
            && (proof_body_requested || hit.kind == "fields"))
        {
            hit.source.as_deref()
        } else {
            hit.source.as_deref().filter(|_| {
                !matches!(run.inference.as_str(), "exact" | "exact-batch")
                    && !related_results
                    && ((index == 0 && proof_body_requested)
                        || matches!(
                            hit.kind.as_str(),
                            "fields"
                                | "file"
                                | "imports"
                                | "location"
                                | "location-expanded"
                                | "outline"
                                | "proof-outline"
                                | "source-group"
                                | "source-occurrences"
                                | "source-range"
                        ))
            })
        };
        if let Some(signature) = &hit.signature
            && !displayed_source
                .is_some_and(|source| source_has_complete_declaration_header(hit, source))
        {
            output.push_str(" : ");
            if matches!(run.inference.as_str(), "exact" | "exact-batch") {
                output.push_str(&compact_signature_preview(signature));
            } else if run.inference == "signature" {
                let complete = single_line(signature);
                let preview = truncate_line(&compact_signature_preview(signature), 240);
                shortened_signature |= preview != complete;
                output.push_str(&preview);
            } else {
                output.push_str(&truncate_line(&single_line(signature), 240));
            }
        }
        if !hit.path.is_empty() {
            output.push_str("  ");
            append_path_location(&mut output, &hit.path, hit.line, &mut previous_hit_path);
        } else {
            previous_hit_path = None;
        }
        if hit.applicable {
            output.push_str("  applicable");
        }
        if let Some(module) = &hit.required_import {
            output.push_str(&format!("\n  import {module}"));
        }
        if run.inference == "usages" && !(proof_body_requested && index == 0) {
            let mut previous_usage_path = None;
            for usage in hit.usages.iter().take(3) {
                output.push_str("\n  used: ");
                append_path_location(
                    &mut output,
                    &usage.path,
                    usage.line,
                    &mut previous_usage_path,
                );
                if let Some(context) = &usage.context {
                    output.push_str(&format!(" in {context}"));
                }
            }
            if hit.usages.len() > 3 {
                output.push_str(&format!("\n  +{} indexed usages", hit.usages.len() - 3));
            }
        } else if !hit.usages.is_empty() {
            output.push_str(&format!(
                "\n  used in {} place{}",
                hit.usages.len(),
                if hit.usages.len() == 1 { "" } else { "s" }
            ));
        }
        if let Some(source) = displayed_source {
            if !matches!(
                run.inference.as_str(),
                "probe" | "probe-source" | "probe-source-excerpt"
            ) && !matches!(
                hit.kind.as_str(),
                "file"
                    | "fields"
                    | "imports"
                    | "location"
                    | "location-expanded"
                    | "outline"
                    | "proof-outline"
                    | "declaration-outline"
                    | "declaration-neighborhood"
                    | "declaration-dependencies"
                    | "declaration-find"
                    | "source-group"
                    | "source-occurrences"
                    | "source-range"
            ) {
                output.push_str("\nsource:");
            }
            render_source(&mut output, run, hit, source, index, proof_body_requested);
        }
    }
    if run.hits.len() > summary_limit {
        let omitted = run.hits.len() - summary_limit;
        output.push_str(&format!("\n+{omitted} results"));
    } else {
        append_complete_range_hint(&mut output, run);
    }
    if run.inference != "exact-miss"
        && let Some(note) = trailing_note
    {
        output.push('\n');
        output.push_str(note);
    }
    if shortened_signature {
        output.push_str(&format!(
            "\nFull signature/context: mathmux show {} --all",
            run.reference
        ));
    }
    if run.inference == "exact-miss" {
        if !run
            .note
            .as_deref()
            .is_some_and(|n| n.contains("index warming"))
        {
            append_exact_miss_hint(&mut output, run);
        }
    } else if run.hits.len() > summary_limit {
        if include_hints {
            append_next_hint(&mut output, run, summary_limit, proof_body_requested);
        } else {
            output.push_str(&format!("\nnext: mathmux show {} --all", run.reference));
        }
    } else if include_hints {
        append_single_result_hint(&mut output, run, proof_body_requested);
    }
    output.push_str(&format!("\nref: {}", run.reference));
    output
}

fn split_verdict_and_note(run: &SearchRun) -> (String, Option<&str>) {
    if (run.hits.is_empty() || run.inference == "exact-miss")
        && run
            .note
            .as_deref()
            .is_some_and(|n| n.contains("index warming"))
    {
        return ("index still warming; no indexed match yet (absence not established)\nRetry this query after indexing completes".into(), None);
    }
    if run.inference == "exact-miss" {
        let note = run.note.as_deref().unwrap_or("exact declaration not found");
        return note.split_once('\n').map_or_else(
            || (note.to_owned(), None),
            |(head, tail)| (head.to_owned(), Some(tail)),
        );
    }
    let verdict = if run.hits.is_empty() {
        "no results".to_owned()
    } else {
        match run.inference.as_str() {
            "exact" | "exact-batch" => "exact declaration".to_owned(),
            "probe" | "probe-source" | "probe-source-excerpt" | "usages" => {
                "probe result".to_owned()
            }
            "source" | "source-only" | "source-regex" | "source-outline" => {
                "source result".to_owned()
            }
            _ => format!(
                "{} ranked result{}",
                run.hits.len(),
                if run.hits.len() == 1 { "" } else { "s" }
            ),
        }
    };
    (verdict, run.note.as_deref())
}

fn append_exact_miss_hint(output: &mut String, run: &SearchRun) {
    if run.inference != "exact-miss" {
        return;
    }
    if let Some(hit) = run.hits.first() {
        let name = shell_argument(probe_name(&hit.name));
        if hit.kind.starts_with("unmerged:") {
            output.push_str(&format!(
                "\nnext: sync, then mathmux probe {name} signature"
            ));
        } else {
            output.push_str(&format!("\nnext: mathmux probe {name} signature"));
        }
    } else {
        let query = explicit_declaration_name(&run.query).unwrap_or_else(|| {
            run.query
                .split_whitespace()
                .next()
                .unwrap_or(run.query.as_str())
        });
        let query = query.strip_prefix("name:").unwrap_or(query);
        let leaf = query
            .trim_start_matches('@')
            .rsplit('.')
            .next()
            .unwrap_or(query);
        let next = if leaf == query.trim_start_matches('@').trim_start_matches("_root_.") {
            format!("{leaf}*")
        } else {
            leaf.to_owned()
        };
        output.push_str(&format!("\nnext: mathmux search {}", shell_argument(&next)));
    }
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
        output.push_str(&format!("\nnext: mathmux show {} --all", run.reference));
    } else if run
        .note
        .as_deref()
        .is_some_and(|note| note.contains("related results"))
    {
        output.push_str("\nnext: refine query");
    } else if let Some(hit) = run.hits.first().filter(|hit| is_probeable_declaration(hit)) {
        if matches!(hit.kind.as_str(), "structure" | "class") {
            output.push_str(&format!(
                "\ncontract: mathmux probe {} evidence (constructions/obstructions)",
                shell_argument(probe_name(&hit.name))
            ));
        }
        let focus = next_probe_focus(hit);
        output.push_str(&format!(
            "\nnext: mathmux probe {}#1 {focus}",
            run.reference,
        ));
    } else if let Some(hit) = run.hits.first()
        && matches!(
            hit.kind.as_str(),
            "source-group" | "location" | "location-expanded"
        )
    {
        output.push_str(&format!(
            "\nnext: mathmux probe {}#1 outline",
            run.reference
        ));
    } else if run.hits.len() > summary_limit {
        output.push_str("\nnext: refine query");
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
        let focus = next_probe_focus(hit);
        output.push_str(&format!(
            "\nnext: mathmux probe {} {focus}",
            shell_argument(probe_name(&hit.name)),
        ));
    } else if let Some(hit) = run.hits.first() {
        match hit.kind.as_str() {
            "source-group" => output.push_str(&format!(
                "\nnext: mathmux search {}",
                shell_argument(&format!("{}:{}", hit.path, hit.line))
            )),
            "location" | "location-expanded" => output.push_str(&format!(
                "\nnext: mathmux search {} outline",
                shell_argument(&hit.path)
            )),
            "proof-outline" | "declaration-outline" => output.push_str(&format!(
                "\nnext: mathmux probe {} source",
                shell_argument(probe_name(&hit.name))
            )),
            _ => {}
        }
    }
}

fn next_probe_focus(hit: &SearchHit) -> &'static str {
    match hit.kind.as_str() {
        "lemma" | "theorem" | "generated" => "usages",
        "class" | "structure" => "fields",
        "inductive" => "constructors",
        _ => "source",
    }
}

fn compact_signature_preview(signature: &str) -> String {
    let signature = single_line(signature);
    let mut output = String::new();
    let mut context_binders = 0;
    let mut remaining = signature.trim();
    // Only the leading binder sequence is context. Brackets in explicit
    // argument types or the conclusion belong to the mathematical statement.
    while let Some(opening @ ('(' | '{' | '[' | '⦃')) = remaining.chars().next() {
        let mut stack = Vec::new();
        let mut end = None;
        for (index, character) in remaining.char_indices() {
            match character {
                '(' => stack.push(')'),
                '{' => stack.push('}'),
                '[' => stack.push(']'),
                '⦃' => stack.push('⦄'),
                ')' | '}' | ']' | '⦄' => {
                    if stack.pop() != Some(character) {
                        break;
                    }
                    if stack.is_empty() {
                        end = Some(index + character.len_utf8());
                        break;
                    }
                }
                _ => {}
            }
        }
        let Some(end) = end else { break };
        if opening == '(' {
            output.push_str(&remaining[..end]);
            output.push(' ');
        } else {
            context_binders += 1;
        }
        remaining = remaining[end..].trim_start();
    }
    if context_binders > 0 && !remaining.starts_with(':') {
        return signature;
    }
    output.push_str(remaining);
    let output = output.split_whitespace().collect::<Vec<_>>().join(" ");
    if context_binders == 0 {
        output
    } else {
        format!("{output} [context: {context_binders} implicit/typeclass]")
    }
}

fn is_probeable_declaration(hit: &SearchHit) -> bool {
    matches!(
        hit.kind.as_str(),
        "abbrev"
            | "class"
            | "def"
            | "declaration"
            | "generated"
            | "inductive"
            | "instance"
            | "lemma"
            | "structure"
            | "theorem"
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
    if matches!(
        run.inference.as_str(),
        "probe-source" | "probe-source-excerpt"
    ) {
        render_probe_source(output, run, hit, source);
        return;
    }
    if hit.kind == "tactic"
        && source.starts_with("application experiment failed")
        && let Some((focused, _)) = source.split_once("\nFull Lean diagnostic:\n")
    {
        output.push('\n');
        output.push_str(focused);
        output.push_str(&format!(
            "\nFull diagnostic: mathmux show {} --all",
            run.reference
        ));
        return;
    }
    let source_lines = if index == 0 && proof_body_requested {
        DECLARATION_DETAIL_LINES
    } else {
        match hit.kind.as_str() {
            "class" | "inductive" | "structure" => 16,
            "fields" => SOURCE_OCCURRENCE_ALL_LIMIT,
            "contract" => 48,
            "imports" => 64,
            "outline" => OUTLINE_PREVIEW_LINES,
            "location" => LOCATION_PREVIEW_LINES,
            "location-expanded" => LOCATION_EXPANDED_LINES,
            "source-range" => SOURCE_RANGE_ALL_LIMIT,
            "source-occurrences" => SOURCE_OCCURRENCE_LIMIT,
            "source-group" => 3,
            "proof-outline" | "declaration-outline" => 80,
            "declaration-neighborhood" | "declaration-dependencies" | "declaration-find" => 24,
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

// Contiguous previews preserve proof order and never silently cut a long line.
fn render_probe_source(output: &mut String, run: &SearchRun, hit: &SearchHit, source: &str) {
    let lines = source.lines().collect::<Vec<_>>();
    let mut chars = 0;
    let shown = lines
        .iter()
        .take(DECLARATION_DETAIL_LINES)
        .take_while(|line| {
            chars += line.chars().count() + 1;
            chars <= 8_000
        })
        .count();
    let fresh = run.inference == "probe-source";
    output.push_str(if fresh {
        "\nsource snapshot (textual context; not elaborated):"
    } else {
        "\nindexed source excerpt (completeness unavailable):"
    });
    if let Some(doc) = &hit.doc {
        output.push_str(&format!("\nDoc: {}", truncate_line(doc, 400)));
        if doc.chars().count() > 400 {
            output.push_str(&format!("\nFull doc: mathmux show {} --all", run.reference));
        }
    }
    for line in &lines[..shown] {
        output.push('\n');
        output.push_str(line);
    }
    if shown < lines.len() {
        output.push_str(&format!(
            "\n… {} lines not shown; mathmux show {} --all",
            lines.len() - shown,
            run.reference
        ));
        // Synthetic ambient context precedes the first matched declaration line.
        let start = source::declaration_regex()
            .find(source)
            .map(|m| source[..m.start()].lines().count());
        if fresh && let Some(start) = start {
            let next = hit.line + shown.saturating_sub(start) as u64;
            let end = hit.line + lines.len().saturating_sub(start + 1) as u64;
            output.push_str(&format!(
                "\nContinue: mathmux search {}:{}-{}",
                hit.path,
                next,
                end.min(next + 47)
            ));
        }
    } else if fresh {
        output.push_str("\nAll source snapshot lines shown.");
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_previews_bucket_implicit_context() {
        assert_eq!(
            compact_signature_preview(
                "{X : Type u} [TopologicalSpace X] (f : X → X) : Continuous f"
            ),
            "(f : X → X) : Continuous f [context: 2 implicit/typeclass]"
        );
        assert_eq!(compact_signature_preview("Nat → Nat"), "Nat → Nat");
        for signature in [
            "(hf : MemLp f p μ) (hg : MemLp g p μ) : hf.toLp f = hg.toLp g ↔ f =ᵐ[μ] g",
            "(f : E →L[𝕜] F) : f ∈ {g | Continuous g}",
            "(f : {x : Nat // x > 0} → Nat) : f ⟨1, by decide⟩ = 1",
            "E →L[𝕜] F",
            "{x : Nat // x > 0} → Nat",
        ] {
            assert_eq!(compact_signature_preview(signature), signature);
        }
        assert_eq!(
            compact_signature_preview("{X : Type} [Inhabited {x : X // True}] (x : X) : x ∈ {y | True}"),
            "(x : X) : x ∈ {y | True} [context: 2 implicit/typeclass]"
        );
    }

    #[test]
    fn exact_miss_followup_progresses_past_the_failed_name() {
        for (query, next) in [
            ("eLpNorm_two", "\"eLpNorm_two*\""),
            ("eLpNorm_two source", "\"eLpNorm_two*\""),
            ("Demo.missing source", "missing"),
            ("theorem Demo.missing source", "missing"),
            ("declaration theorem missing proof", "\"missing*\""),
            ("name:missing", "\"missing*\""),
            ("@_root_.missing", "\"missing*\""),
            ("missing'", "\"missing'*\""),
        ] {
            let run = SearchRun {
                reference: "q1".into(),
                workspace_ref: "w1".into(),
                query: query.into(),
                inference: "exact-miss".into(),
                hits: vec![],
                note: None,
                duration_ms: 0,
                created_at: 0,
            };
            let mut output = String::new();
            append_exact_miss_hint(&mut output, &run);
            assert_eq!(output, format!("\nnext: mathmux search {next}"), "{query}");
        }
    }

    #[test]
    fn generated_commands_quote_lean_names_with_apostrophes() {
        assert_eq!(
            shell_argument("Demo.changeModelTrivialization'"),
            "\"Demo.changeModelTrivialization'\""
        );
        assert_eq!(shell_argument("Demo.safe_name"), "Demo.safe_name");
    }
}
