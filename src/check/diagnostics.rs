use super::*;

pub(super) fn partition_diagnostics(
    diagnostics: &[WorkerDiagnostic],
) -> (
    Vec<Diagnostic>,
    Vec<Diagnostic>,
    Vec<Diagnostic>,
    Vec<Diagnostic>,
) {
    let mut warnings = Vec::new();
    let mut linters = Vec::new();
    let mut suggestions = Vec::new();
    let mut errors = Vec::new();
    for diagnostic in diagnostics {
        let value = Diagnostic {
            kind: diagnostic.kind.clone(),
            text: enriched_diagnostic_text(diagnostic),
            context: None,
        };
        match diagnostic.severity.as_str() {
            "warning" if is_linter(diagnostic) => linters.push(value),
            "warning" | "information" | "info" if is_tactic_suggestion(diagnostic) => {
                suggestions.push(value)
            }
            "warning" => warnings.push(value),
            "error" => errors.push(value),
            _ => {}
        }
    }
    for values in [&mut warnings, &mut linters, &mut suggestions, &mut errors] {
        deduplicate(values);
    }
    errors.sort_by_key(|diagnostic| !is_syntax_diagnostic(diagnostic));
    if errors.iter().any(|diagnostic| {
        diagnostic
            .text
            .contains("failed to synthesize instance of type class\n  LE Type")
    }) && let Some(syntax) = errors
        .iter_mut()
        .find(|diagnostic| is_syntax_diagnostic(diagnostic))
    {
        syntax.text.push_str(
            "\nhint: a notation may be inactive; open its scope or use its named declaration",
        );
    }
    (warnings, linters, suggestions, errors)
}

fn enriched_diagnostic_text(diagnostic: &WorkerDiagnostic) -> String {
    let mut text = diagnostic.text.clone();
    if diagnostic.severity != "error" {
        return text;
    }
    if text.contains("elaboration function for `Mathlib.Tactic.subscriptTerm` has not been implemented") {
        text.push_str("\nhint: this notation is not active; open its scoped notation or use the named declaration");
    } else if text.contains("failed to synthesize instance of type class\n  DecidableEq ") {
        text.push_str("\nhint: add `classical` locally or provide the `DecidableEq` instance");
    } else if text.contains("synthesized type class instance is not definitionally equal to expression inferred by typing rules") {
        text.push_str("\nhint: construct both expressions under the same local instance; introduce `classical` before either expression when decidability is involved");
    }
    text
}

fn is_syntax_diagnostic(diagnostic: &Diagnostic) -> bool {
    let kind = diagnostic.kind.to_ascii_lowercase();
    kind.contains("parser")
        || kind.contains("syntax")
        || diagnostic.text.lines().next().is_some_and(|line| {
            line.contains("expected token") || line.contains("unexpected token")
        })
}

fn is_tactic_suggestion(diagnostic: &WorkerDiagnostic) -> bool {
    diagnostic.text.contains("Try this:")
}

pub(super) fn attach_source_context(diagnostics: &mut [Diagnostic], target: &Path, source: &str) {
    let target_path = target.to_string_lossy();
    let basename = target_path.rsplit('/').next().unwrap_or(&target_path);
    let module = target
        .with_extension("")
        .components()
        .filter_map(|component| component.as_os_str().to_str())
        .collect::<Vec<_>>()
        .join(".");
    let lines = source.lines().collect::<Vec<_>>();
    for diagnostic in diagnostics {
        let first = diagnostic.text.lines().next().unwrap_or_default();
        let rest = [target_path.as_ref(), basename, module.as_str()]
            .iter()
            .find_map(|prefix| {
                first
                    .strip_prefix(prefix)
                    .and_then(|rest| rest.strip_prefix(':'))
            });
        let Some(line) = rest
            .and_then(|rest| rest.split(':').next())
            .and_then(|line| line.parse::<usize>().ok())
            .filter(|line| *line > 0 && *line <= lines.len())
        else {
            continue;
        };
        let start = line.saturating_sub(2).max(1);
        let end = (line + 2).min(lines.len());
        let ambient = diagnostic
            .text
            .contains("failed to synthesize instance of type class")
            .then(|| {
                let lower = start.saturating_sub(33);
                let nearest = (lower..start.saturating_sub(1))
                    .rev()
                    .find(|index| lines[*index].trim_start().starts_with("variable "))?;
                let first = (lower..=nearest)
                    .rev()
                    .take_while(|index| lines[*index].trim_start().starts_with("variable "))
                    .last()
                    .unwrap_or(nearest);
                Some((first..=nearest).rev().take(4).collect::<Vec<_>>())
            })
            .flatten()
            .unwrap_or_default();
        let render = |current: usize| {
            format!(
                "{} {:>4} | {}",
                if current + 1 == line { ">" } else { " " },
                current + 1,
                lines[current]
            )
        };
        diagnostic.context = Some(
            ambient
                .into_iter()
                .rev()
                .map(render)
                .chain((start - 1..end).map(render))
                .collect::<Vec<_>>()
                .join("\n"),
        );
    }
}

fn is_linter(diagnostic: &WorkerDiagnostic) -> bool {
    let kind = diagnostic.kind.to_ascii_lowercase();
    let text = diagnostic.text.to_ascii_lowercase();
    kind.contains("linter")
        || text.contains("this linter can be disabled")
        || text.contains("declaration uses 'sorry'")
        || text.contains("declaration uses `sorry`")
        || text.contains("unused variable")
        || text.contains("automatically included section variable")
        || text.contains("contains a placeholder")
}

pub(super) fn deduplicate(diagnostics: &mut Vec<Diagnostic>) {
    let mut seen = HashSet::new();
    diagnostics.retain(|diagnostic| seen.insert(diagnostic.clone()));
}
