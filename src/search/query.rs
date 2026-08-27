use super::*;

pub(super) fn more_search_reference(query: &str) -> Option<&str> {
    let mut terms = query.split_whitespace().rev();
    let modifier = terms.next()?;
    let reference = terms.next()?;
    (modifier.eq_ignore_ascii_case("more")
        && reference
            .strip_prefix('q')
            .is_some_and(|digits| !digits.is_empty() && digits.chars().all(|c| c.is_ascii_digit())))
    .then_some(reference)
}

pub(super) fn search_more_requested(query: &str) -> bool {
    query
        .split_whitespace()
        .any(|term| term.eq_ignore_ascii_case("more"))
}

pub(super) fn normalize_lean_inspection_query(query: &str) -> String {
    let escaped_apostrophes = query
        .trim()
        .replace("\\x27", "'")
        .replace("\\X27", "'")
        .replace("\\'", "'");
    let without_file_placeholder = escaped_apostrophes
        .split_whitespace()
        .filter(|term| *term != "FILE")
        .collect::<Vec<_>>()
        .join(" ");
    let mut query = without_file_placeholder.as_str();
    if let Some((directive, rest)) = query.split_once(char::is_whitespace)
        && matches!(
            directive.to_ascii_lowercase().as_str(),
            "#check" | "#print" | "#synth"
        )
    {
        query = rest.trim_start();
    }
    let Some(application) = query.strip_prefix('@') else {
        return query.strip_prefix("_root_.").unwrap_or(query).to_owned();
    };
    let mut terms = application.split_whitespace();
    let Some(name) = terms.next() else {
        return query.to_owned();
    };
    std::iter::once(name.strip_prefix("_root_.").unwrap_or(name))
        .chain(terms.filter(|term| {
            term.eq_ignore_ascii_case("more")
                || matches!(term.to_ascii_lowercase().as_str(), "body" | "proof")
        }))
        .collect::<Vec<_>>()
        .join(" ")
}

pub(super) fn strip_search_modifiers(query: &str) -> String {
    query
        .split_whitespace()
        .filter(|term| {
            !term.eq_ignore_ascii_case("more")
                && !matches!(
                    term.to_ascii_uppercase().as_str(),
                    "FILE:LINE" | "FILE:LINE:COLUMN"
                )
        })
        .collect::<Vec<_>>()
        .join(" ")
}

pub(super) fn refined_search_query(base: &str, refinement: &str) -> String {
    let refinement = refinement.trim();
    let facet = refinement.to_ascii_lowercase();
    if matches!(facet.as_str(), "field" | "fields" | "projection" | "projections") {
        return format!("{base} fields");
    }
    if matches!(facet.as_str(), "constructor" | "constructors") {
        return format!("{base}.mk");
    }
    let refinement = match facet.as_str() {
        "usage" | "usages" | "references" => "",
        "coercion" | "coercions" => "coe",
        "lemma" | "lemmas" => "theorem",
        _ => refinement,
    };
    [base, refinement]
        .into_iter()
        .filter(|part| !part.is_empty())
        .collect::<Vec<_>>()
        .join(" ")
}

pub(super) fn field_inventory_query(query: &str) -> Option<&str> {
    let terms = query.split_whitespace().collect::<Vec<_>>();
    let (name, facet) = match terms.as_slice() {
        [name, facet] => (*name, *facet),
        [kind, name, facet]
            if matches!(
                kind.to_ascii_lowercase().as_str(),
                "class" | "structure"
            ) => (*name, *facet),
        _ => return None,
    };
    (declaration_name_query(name)
        && matches!(
            facet.to_ascii_lowercase().as_str(),
            "field" | "fields" | "projection" | "projections"
        ))
    .then_some(name)
}

pub(super) fn search_refinement_facet(refinement: &str) -> bool {
    matches!(
        refinement.trim().to_ascii_lowercase().as_str(),
        "usage"
            | "usages"
            | "references"
            | "field"
            | "fields"
            | "projection"
            | "projections"
            | "constructor"
            | "constructors"
            | "coercion"
            | "coercions"
            | "lemma"
            | "lemmas"
    )
}

pub(super) fn diagnostic_position(
    diagnostic: &str,
    fallback: Option<&str>,
) -> (Option<String>, u64) {
    static LOCATION: OnceLock<Regex> = OnceLock::new();
    let location = LOCATION.get_or_init(|| {
        Regex::new(r"^(?P<label>.+?):(?P<line>[0-9]+)(?::[0-9]+)?(?::|$)")
            .expect("valid diagnostic location regex")
    });
    let parsed = diagnostic
        .lines()
        .next()
        .and_then(|line| location.captures(line));
    let path = parsed
        .as_ref()
        .and_then(|captures| captures.name("label"))
        .filter(|label| label.as_str().ends_with(".lean"))
        .map(|label| label.as_str().to_owned())
        .or_else(|| fallback.map(str::to_owned));
    let line = parsed
        .as_ref()
        .and_then(|captures| captures.name("line"))
        .and_then(|line| line.as_str().parse().ok())
        .unwrap_or(1);
    (path, line)
}

pub(super) fn diagnostic_context(diagnostic: &str, source_context: Option<&str>) -> String {
    let type_detail = diagnostic_type_detail(diagnostic);
    let goal_detail = diagnostic_goal_detail(diagnostic);
    let mut lines = diagnostic.lines().collect::<Vec<_>>();
    let diagnostic_limit = if type_detail.is_some() || goal_detail.is_some() {
        8
    } else {
        16
    };
    if lines.len() > diagnostic_limit {
        lines.truncate(diagnostic_limit);
    }
    let mut rendered = lines.join("\n");
    if let Some(detail) = type_detail {
        rendered.push('\n');
        rendered.push_str(&detail);
    }
    if let Some(detail) = goal_detail {
        rendered.push('\n');
        rendered.push_str(&detail);
    }
    if let Some(context) = source_context {
        let context = context.lines().take(5).collect::<Vec<_>>().join("\n");
        if !context.is_empty() {
            rendered.push('\n');
            rendered.push_str(&context);
        }
    }
    if diagnostic.contains(
        "synthesized type class instance is not definitionally equal to expression inferred by typing rules",
    ) && !rendered.contains("same local instance")
    {
        rendered.push_str(
            "\nhint: construct both expressions under the same local instance; introduce `classical` before either expression when decidability is involved",
        );
    }
    rendered
}

fn diagnostic_goal_detail(diagnostic: &str) -> Option<String> {
    if !diagnostic.contains("unsolved goals") {
        return None;
    }
    let lines = diagnostic.lines().collect::<Vec<_>>();
    let start = lines
        .iter()
        .rposition(|line| line.trim_start().starts_with('⊢'))?;
    let goal = lines[start..]
        .iter()
        .copied()
        .take_while(|line| {
            let trimmed = line.trim_start().trim_start_matches('>').trim_start();
            !trimmed
                .split_once('|')
                .is_some_and(|(prefix, _)| prefix.trim().chars().all(|c| c.is_ascii_digit()))
        })
        .collect::<Vec<_>>()
        .join("\n");
    (!goal.is_empty()).then(|| format!("goal\n{goal}"))
}

pub(super) fn diagnostic_type_detail(diagnostic: &str) -> Option<String> {
    const SYNTHESIS: &str = "failed to synthesize instance of type class";
    let lines = diagnostic.lines().collect::<Vec<_>>();
    if let Some(index) = lines.iter().position(|line| line.contains(SYNTHESIS)) {
        let mut goal = lines[index]
            .split_once(SYNTHESIS)
            .map(|(_, suffix)| suffix.trim())
            .filter(|suffix| !suffix.is_empty())
            .into_iter()
            .map(str::to_owned)
            .collect::<Vec<_>>();
        goal.extend(
            lines[index + 1..]
                .iter()
                .map(|line| line.trim())
                .take_while(|line| {
                    !line.is_empty() && !line.starts_with("Hint:") && !line.starts_with("Note:")
                })
                .map(str::to_owned),
        );
        let goal = goal.join(" ");
        if !goal.is_empty() {
            return Some(format!("instance goal\n{}", truncate_middle(&goal, 480)));
        }
    }

    let actual_start = lines.iter().position(|line| line.trim() == "has type")? + 1;
    let expected_marker = lines[actual_start..]
        .iter()
        .position(|line| line.trim() == "but is expected to have type")?
        + actual_start;
    let expected_start = expected_marker + 1;
    let expected_end = lines[expected_start..]
        .iter()
        .position(|line| {
            let line = line.trim();
            line.starts_with("in the application")
                || line.starts_with("the following variables")
                || line.starts_with("Hint:")
                || line.starts_with("Note:")
        })
        .map_or(lines.len(), |offset| expected_start + offset);
    let actual = lines[actual_start..expected_marker]
        .iter()
        .flat_map(|line| line.split_whitespace())
        .collect::<Vec<_>>();
    let expected = lines[expected_start..expected_end]
        .iter()
        .flat_map(|line| line.split_whitespace())
        .collect::<Vec<_>>();
    if actual.is_empty() || expected.is_empty() || actual == expected {
        return None;
    }
    let prefix = actual
        .iter()
        .zip(&expected)
        .take_while(|(actual, expected)| actual == expected)
        .count();
    let suffix = actual[prefix..]
        .iter()
        .rev()
        .zip(expected[prefix..].iter().rev())
        .take_while(|(actual, expected)| actual == expected)
        .count();
    let actual_end = actual.len().saturating_sub(suffix).max(prefix);
    let expected_end = expected.len().saturating_sub(suffix).max(prefix);
    let actual_difference = actual[prefix..actual_end].join(" ");
    let expected_difference = expected[prefix..expected_end].join(" ");
    Some(format!(
        "first type difference\nactual: {}\nexpected: {}",
        if actual_difference.is_empty() {
            "<end>".into()
        } else {
            truncate_middle(&actual_difference, 360)
        },
        if expected_difference.is_empty() {
            "<end>".into()
        } else {
            truncate_middle(&expected_difference, 360)
        }
    ))
}

pub(super) fn diagnostic_search_query(
    diagnostic: &str,
    source_context: Option<&str>,
) -> String {
    if diagnostic.contains("(deterministic) timeout at") {
        return String::new();
    }
    if diagnostic.contains(
        "synthesized type class instance is not definitionally equal to expression inferred by typing rules",
    ) {
        return String::new();
    }
    if diagnostic.contains("No goals to be solved") {
        return String::new();
    }
    if (diagnostic.contains("made no progress")
        || diagnostic.contains("Tactic `") && diagnostic.contains(" failed"))
        && let Some(query) = highlighted_tactic_query(source_context)
    {
        return query;
    }
    let lines = diagnostic.lines().collect::<Vec<_>>();
    if diagnostic.contains("unsolved goals")
        && let Some(index) = lines
            .iter()
            .rposition(|line| line.trim_start().starts_with('⊢'))
    {
        let goal = lines[index..]
            .iter()
            .copied()
            .take_while(|line| {
                let trimmed = line.trim_start();
                !trimmed.is_empty()
                    && !trimmed
                        .chars()
                        .next()
                        .is_some_and(|character| character.is_ascii_digit())
            })
            .collect::<Vec<_>>()
            .join(" ");
        let locals = lines[..index]
            .iter()
            .filter_map(|line| line.trim().split_once(':').map(|(names, _)| names))
            .flat_map(str::split_whitespace)
            .filter(|name| declaration_name_query(name))
            .collect::<HashSet<_>>();
        return diagnostic_goal_query(&goal, &locals);
    }
    if let Some(detail) = diagnostic_type_detail(diagnostic)
        && let Some(goal) = detail.strip_prefix("instance goal\n")
    {
        let mut specific = Vec::new();
        let mut structural = Vec::new();
        for token in goal.split(|character: char| {
            !character.is_alphanumeric() && character != '_' && character != '.'
        }) {
            let token = token.trim_matches('.').rsplit('.').next().unwrap_or(token);
            if token.chars().count() < 4 || !declaration_name_query(token) {
                continue;
            }
            let destination = if token.contains('_')
                || token.chars().next().is_some_and(char::is_lowercase)
                    && token.chars().skip(1).any(char::is_uppercase)
            {
                &mut specific
            } else {
                &mut structural
            };
            if !destination
                .iter()
                .any(|seen: &String| seen.eq_ignore_ascii_case(token))
            {
                destination.push(token.to_owned());
            }
        }
        structural.reverse();
        specific.extend(structural);
        if !specific.is_empty() {
            if specific.iter().all(|term| {
                matches!(
                    term.as_str(),
                    "Type" | "Sort" | "Prop" | "OfNat" | "LE" | "LT"
                )
            }) {
                return highlighted_tactic_query(source_context).unwrap_or_default();
            }
            return specific.join(" ");
        }
        return goal.to_owned();
    }
    if let Some(query) = diagnostic_relation_query(diagnostic) {
        return query;
    }
    static QUOTED: OnceLock<Regex> = OnceLock::new();
    let quoted = QUOTED.get_or_init(|| Regex::new(r"`([^`]+)`").expect("valid diagnostic regex"));
    let terms = quoted
        .captures_iter(diagnostic)
        .filter_map(|capture| capture.get(1).map(|value| value.as_str().trim()))
        .filter(|value| declaration_name_query(value))
        .collect::<Vec<_>>();
    if let Some(qualified) = terms.iter().find(|term| term.contains('.')) {
        return (*qualified).to_owned();
    }
    let mut selected = terms.into_iter().map(str::to_owned).collect::<Vec<_>>();
    static LOCATION_PREFIX: OnceLock<Regex> = OnceLock::new();
    let location_prefix = LOCATION_PREFIX.get_or_init(|| {
        Regex::new(r"^[^:\n]+:\d+:\d+:\s*").expect("valid diagnostic location prefix")
    });
    let searchable = location_prefix.replace(diagnostic, "");
    for token in searchable.split(|character: char| {
        character.is_whitespace() || matches!(character, ':' | ',' | '(' | ')' | '[' | ']')
    }) {
        let token = token.trim_matches(|character: char| {
            !character.is_alphanumeric() && character != '_' && character != '.'
        });
        if token.len() >= 4
            && (token.contains(['.', '_']) || token.chars().next().is_some_and(char::is_uppercase))
            && !selected.iter().any(|seen| seen == token)
        {
            selected.push(token.to_owned());
        }
        if selected.len() >= 10 {
            break;
        }
    }
    if selected.is_empty() {
        truncate_line(&single_line(diagnostic), 240)
    } else {
        selected.join(" ")
    }
}

pub(super) fn diagnostic_instance_query(diagnostic: &str) -> Option<String> {
    let goal = diagnostic_type_detail(diagnostic)?
        .strip_prefix("instance goal\n")?
        .to_owned();
    let class = goal
        .split(|character: char| {
            !character.is_alphanumeric() && character != '_' && character != '.'
        })
        .find(|token| !token.is_empty())?
        .rsplit('.')
        .next()?;
    if class.chars().next().is_none_or(|character| !character.is_uppercase())
        || matches!(class, "Type" | "Sort" | "Prop" | "OfNat" | "LE" | "LT")
    {
        return None;
    }
    Some(format!("inst{class}"))
}

fn highlighted_tactic_query(source_context: Option<&str>) -> Option<String> {
    let code = source_context?
        .lines()
        .find_map(|line| line.trim_start().strip_prefix('>'))?
        .split_once('|')?
        .1
        .trim();
    let mut identifiers = code
        .split(|character: char| {
            !character.is_alphanumeric() && !matches!(character, '_' | '.' | '\'')
        })
        .filter(|token| !token.is_empty());
    let tactic = identifiers.next()?;
    if !matches!(
        tactic,
        "apply" | "change" | "exact" | "refine" | "rw" | "simpa" | "simp" | "simp_rw"
    ) {
        return None;
    }
    identifiers
        .find(|token| {
            !matches!(
                *token,
                "at" | "by" | "fun" | "only" | "using" | "with" | "Type" | "Prop"
            ) && token.chars().any(char::is_alphabetic)
                && declaration_name_query(token)
        })
        .map(str::to_owned)
}

pub(super) fn diagnostic_goal_query(goal: &str, locals: &HashSet<&str>) -> String {
    let anonymized = single_line(&anonymize_goal(goal, locals));
    let target = anonymized
        .trim_start()
        .strip_prefix('⊢')
        .unwrap_or(&anonymized)
        .trim();
    let mut focused = Vec::new();
    for token in target.split(|character: char| {
        character.is_whitespace()
            || matches!(
                character,
                '⊢' | '(' | ')' | '[' | ']' | '{' | '}' | ',' | ':' | '='
            )
    }) {
        let token = token.trim_matches(|character: char| {
            !character.is_alphanumeric() && !matches!(character, '_' | '.' | '\'')
        });
        if token.chars().count() >= 4
            && declaration_name_query(token)
            && !token.contains("_proof_")
            && (token.contains(['.', '_'])
                || token.chars().next().is_some_and(char::is_uppercase)
                || token.chars().skip(1).any(char::is_uppercase))
            && !focused
                .iter()
                .any(|seen: &String| seen.eq_ignore_ascii_case(token))
        {
            focused.push(token.to_owned());
        }
        if focused.len() == 6 {
            break;
        }
    }
    if focused.len() >= 2 {
        focused.sort_by_key(|token| {
            let namespace = token.split_once('.').map(|(namespace, _)| namespace);
            let specificity = namespace
                .filter(|namespace| {
                    namespace.chars().next().is_some_and(char::is_uppercase)
                })
                .map(|namespace| namespace.chars().count())
                .or_else(|| {
                    (namespace.is_none() && token.chars().skip(1).any(char::is_uppercase))
                        .then_some(16)
                })
                .unwrap_or_default();
            std::cmp::Reverse((
                specificity,
                token.contains(['.', '_']),
            ))
        });
        focused.join(" ")
    } else {
        truncate_line(&format!("⊢ {target}"), 600)
    }
}

pub(super) fn diagnostic_relation_query(diagnostic: &str) -> Option<String> {
    let lines = diagnostic.lines().map(str::trim).collect::<Vec<_>>();
    let relational = (diagnostic.contains("left-hand side")
        && diagnostic.contains("right-hand side"))
        || (lines.contains(&"has type") && lines.contains(&"but is expected to have type"));
    if !relational {
        return None;
    }
    let message = diagnostic
        .split_once(" error: ")
        .map_or(diagnostic, |(_, message)| message)
        .split("\n\n")
        .next()
        .unwrap_or_default();
    let mut selected = Vec::new();
    for token in message.split(|character: char| {
        character.is_whitespace()
            || matches!(character, ':' | ',' | '(' | ')' | '[' | ']' | '{' | '}')
    }) {
        let token = token.trim_matches(|character: char| {
            !character.is_alphanumeric() && !matches!(character, '_' | '.' | '\'')
        });
        let structured = token.contains(['.', '_'])
            || (token.chars().next().is_some_and(char::is_lowercase)
                && token.chars().skip(1).any(char::is_uppercase));
        if token.len() >= 4
            && structured
            && declaration_name_query(token)
            && !selected.contains(&token)
        {
            selected.push(token);
        }
        if selected.len() == 4 {
            break;
        }
    }
    if let Some(sibling) = related_namespace_sibling(diagnostic, &selected) {
        selected.insert(0, sibling.as_str());
        return Some(selected.join(" "));
    }
    selected.sort_by_key(|token| !token.contains('_'));
    (!selected.is_empty()).then(|| selected.join(" "))
}

fn related_namespace_sibling(diagnostic: &str, selected: &[&str]) -> Option<String> {
    let wrapper = diagnostic
        .split(|character: char| {
            !character.is_alphanumeric() && !matches!(character, '_' | '.' | '\'')
        })
        .filter_map(|token| token.rsplit('.').next())
        .filter_map(|leaf| leaf.strip_prefix("to"))
        .find(|leaf| {
            leaf.chars().count() >= 4
                && leaf.chars().next().is_some_and(char::is_uppercase)
                && declaration_name_query(leaf)
        })?;
    selected.iter().find_map(|name| {
        let (namespace, leaf) = name.rsplit_once('.')?;
        (leaf.contains('_') && namespace.rsplit('.').next() != Some(wrapper))
            .then(|| format!("{wrapper}.{leaf}"))
    })
}

pub(super) fn anonymize_goal(goal: &str, locals: &HashSet<&str>) -> String {
    let mut output = String::with_capacity(goal.len());
    let mut identifier = String::new();
    let flush = |output: &mut String, identifier: &mut String| {
        if !identifier.is_empty() {
            if locals.contains(identifier.as_str()) {
                output.push('_');
            } else {
                output.push_str(identifier);
            }
            identifier.clear();
        }
    };
    for character in goal.chars() {
        if character.is_alphanumeric() || matches!(character, '_' | '\'' | '✝') {
            identifier.push(character);
        } else {
            flush(&mut output, &mut identifier);
            output.push(character);
        }
    }
    flush(&mut output, &mut identifier);
    output
}

pub(super) fn goal_refinement_query(goal_state: &str, refinement: &str) -> String {
    let target = goal_state
        .lines()
        .find_map(|line| line.trim().strip_prefix('⊢'))
        .map(str::trim)
        .unwrap_or(goal_state);
    let head = target
        .split(|character: char| character.is_whitespace() || character == '(')
        .find(|part| !part.is_empty());
    if declaration_name_query(refinement)
        && !refinement.contains('.')
        && let Some(head) = head
        && declaration_name_query(head)
    {
        format!("{head}.{refinement}")
    } else {
        format!("{target} {refinement}")
    }
}

pub(super) fn edit_distance(left: &str, right: &str) -> usize {
    let right = right.chars().collect::<Vec<_>>();
    let mut previous = (0..=right.len()).collect::<Vec<_>>();
    for (left_index, left_character) in left.chars().enumerate() {
        let mut current = vec![left_index + 1];
        for (right_index, right_character) in right.iter().enumerate() {
            current.push(
                (previous[right_index + 1] + 1)
                    .min(current[right_index] + 1)
                    .min(previous[right_index] + usize::from(left_character != *right_character)),
            );
        }
        previous = current;
    }
    previous[right.len()]
}

pub(super) fn fts_query(query: &str) -> String {
    meaningful_query_tokens(query)
        .into_iter()
        .filter(|token| token != "_")
        .map(|token| format!("\"{}\"*", token.replace('"', "\"\"")))
        .collect::<Vec<_>>()
        .join(" OR ")
}

pub(super) fn query_tokens(query: &str) -> Vec<String> {
    query
        .split(|character: char| {
            !character.is_alphanumeric() && character != '_' && character != '.'
        })
        .map(|token| token.trim_matches('.').to_lowercase())
        .filter(|token| !token.is_empty())
        .collect()
}

pub(super) fn declaration_name_query(query: &str) -> bool {
    let query = query.trim();
    !query.is_empty()
        && !query.starts_with('.')
        && !query.ends_with('.')
        && query
            .chars()
            .all(|character| character.is_alphanumeric() || matches!(character, '_' | '.' | '\''))
}

pub(super) fn declaration_suffix_base(query: &str) -> Option<&str> {
    let (base, suffix) = query.rsplit_once('_')?;
    (!suffix.is_empty()
        && suffix.chars().all(char::is_alphanumeric)
        && base
            .rsplit('.')
            .next()
            .is_some_and(|leaf| leaf.chars().count() >= 4)
        && declaration_name_query(base))
    .then_some(base)
}

pub(super) fn declaration_predicate_base(query: &str) -> Option<String> {
    let (owner, leaf) = query
        .rsplit_once('.')
        .map_or((None, query), |(owner, leaf)| (Some(owner), leaf));
    let rest = if let Some(rest) = leaf.strip_prefix("is_") {
        rest.to_owned()
    } else {
        let rest = leaf.strip_prefix("is")?;
        let first = rest.chars().next()?;
        if !first.is_uppercase() {
            return None;
        }
        let mut lowered = first.to_lowercase().collect::<String>();
        lowered.push_str(&rest[first.len_utf8()..]);
        lowered
    };
    (!rest.is_empty()).then(|| owner.map_or(rest.clone(), |owner| format!("{owner}.{rest}")))
}

pub(super) fn explicit_declaration_name(query: &str) -> Option<&str> {
    let mut terms = query.split_whitespace();
    let kind = terms.next()?;
    if !matches!(
        kind.to_ascii_lowercase().as_str(),
        "abbrev"
            | "class"
            | "def"
            | "definition"
            | "inductive"
            | "instance"
            | "lemma"
            | "structure"
            | "theorem"
    ) {
        return None;
    }
    let name = terms.next()?;
    if !declaration_name_query(name)
        || !terms.all(|term| {
            matches!(
                term.to_ascii_lowercase().as_str(),
                "body" | "constructors" | "fields" | "implementation" | "proof" | "source"
            )
        })
    {
        return None;
    }
    Some(name)
}

pub(super) fn declaration_glob_query(query: &str) -> bool {
    query.contains('*')
        && query
            .chars()
            .filter(|character| character.is_alphanumeric())
            .count()
            >= 2
        && query.chars().all(|character| {
            character.is_alphanumeric() || matches!(character, '_' | '.' | '\'' | '*')
        })
}

pub(super) fn apply_declaration_glob(candidates: &mut Vec<Candidate>, query: &str) -> bool {
    if !declaration_glob_query(query) {
        return false;
    }
    if candidates
        .iter()
        .any(|candidate| declaration_glob_matches(&candidate.hit.name, query))
    {
        candidates.retain(|candidate| declaration_glob_matches(&candidate.hit.name, query));
        false
    } else {
        !candidates.is_empty()
    }
}

pub(super) fn declaration_glob_matches(name: &str, query: &str) -> bool {
    let characters = query.chars().collect::<Vec<_>>();
    let pattern = characters
        .iter()
        .enumerate()
        .map(|(index, character)| match character {
            '*' => ".*".to_owned(),
            '.' if index
                .checked_sub(1)
                .is_some_and(|prior| characters[prior] == '*')
                || characters.get(index + 1) == Some(&'*') =>
            {
                "[._]?".to_owned()
            }
            '.' => "[._]".to_owned(),
            character => regex::escape(&character.to_string()),
        })
        .collect::<String>();
    let prefix = if query.starts_with('*') {
        ""
    } else {
        r"(?:^|\.)"
    };
    Regex::new(&format!(r"(?i){prefix}{pattern}$")).is_ok_and(|pattern| pattern.is_match(name))
}

pub(super) fn qualified_name_matches(name: &str, query: &str) -> bool {
    let name = ascii_numeric_spelling(canonical_declaration_name(name)).to_lowercase();
    let query = ascii_numeric_spelling(canonical_declaration_name(query.trim())).to_lowercase();
    name == query
        || name
            .strip_suffix(&query)
            .is_some_and(|prefix| prefix.ends_with('.'))
}

pub(super) fn canonical_declaration_name(name: &str) -> &str {
    name.strip_prefix("_root_.").unwrap_or(name)
}

pub(super) fn result_limit(exact_name_miss: bool, show_all: bool) -> usize {
    if exact_name_miss && !show_all {
        RELATED_RESULT_LIMIT
    } else {
        RESULT_LIMIT
    }
}

pub(super) fn direct_continuation_name_matches(name: &str, query: &str) -> bool {
    let name = name.to_lowercase();
    let query = query.trim().to_lowercase();
    let name_leaf = name.rsplit('.').next().unwrap_or(&name);
    let query_leaf = query.rsplit('.').next().unwrap_or(&query);
    if !name_leaf.starts_with(&format!("{query_leaf}_")) {
        return false;
    }
    let Some((query_owner, _)) = query.rsplit_once('.') else {
        return true;
    };
    let name_owner = name.rsplit_once('.').map_or("", |(owner, _)| owner);
    name_owner == query_owner || name_owner.ends_with(&format!(".{query_owner}"))
}

pub(super) fn unique_qualified_hit_name<'a>(
    hits: impl Iterator<Item = &'a SearchHit>,
    query: &str,
) -> Option<String> {
    let hits = hits.collect::<Vec<_>>();
    let query = canonical_declaration_name(query);
    let exact = hits
        .iter()
        .filter(|hit| canonical_declaration_name(&hit.name).eq_ignore_ascii_case(query))
        .map(|hit| canonical_declaration_name(&hit.name).to_lowercase())
        .collect::<HashSet<_>>();
    if exact.len() == 1 {
        return exact.into_iter().next();
    }
    let names = hits
        .into_iter()
        .filter(|hit| qualified_name_matches(&hit.name, query))
        .map(|hit| canonical_declaration_name(&hit.name).to_lowercase())
        .collect::<HashSet<_>>();
    if names.len() == 1 {
        names.into_iter().next()
    } else {
        None
    }
}

pub(super) fn resolved_exact_candidates(
    candidates: Vec<Candidate>,
    query: &str,
) -> Option<Vec<Candidate>> {
    let name = unique_qualified_hit_name(candidates.iter().map(|candidate| &candidate.hit), query)?;
    Some(
        candidates
            .into_iter()
            .filter(|candidate| {
                canonical_declaration_name(&candidate.hit.name).eq_ignore_ascii_case(&name)
            })
            .collect(),
    )
}

pub(super) fn merge_exact_candidates(mut candidates: Vec<Candidate>) -> Candidate {
    candidates.sort_by(|left, right| {
        right
            .score
            .partial_cmp(&left.score)
            .unwrap_or(Ordering::Equal)
            .then_with(|| left.hit.name.cmp(&right.hit.name))
    });
    let mut resolved = candidates.remove(0);
    for mut candidate in candidates {
        merge_duplicate_hit(&mut resolved.hit, &mut candidate.hit);
        resolved.origins |= candidate.origins;
    }
    resolved
}

pub(super) fn rank_discovery_candidates(
    mut candidates: Vec<Candidate>,
    query: &str,
    query_tokens: &[String],
    explicit_declaration: bool,
    import_context: Option<&ImportContext>,
) -> (Vec<Candidate>, bool) {
    let glob_name_miss = apply_declaration_glob(&mut candidates, query);
    if let Some(context) = import_context {
        for candidate in &mut candidates {
            apply_import_context(candidate, context);
        }
    }
    candidates.sort_by(|left, right| {
        right
            .score
            .partial_cmp(&left.score)
            .unwrap_or(Ordering::Equal)
            .then_with(|| left.hit.name.cmp(&right.hit.name))
    });
    let mut positions: HashMap<String, usize> = HashMap::new();
    let mut deduplicated: Vec<Candidate> = Vec::new();
    for mut candidate in candidates {
        if let Some(index) = positions.get(&candidate.hit.name).copied() {
            merge_duplicate_hit(&mut deduplicated[index].hit, &mut candidate.hit);
            deduplicated[index].origins |= candidate.origins;
        } else {
            positions.insert(candidate.hit.name.clone(), deduplicated.len());
            deduplicated.push(candidate);
        }
    }
    if explicit_declaration {
        deduplicated.sort_by_key(|candidate| !qualified_name_matches(&candidate.hit.name, query));
    } else {
        promote_query_coverage(&mut deduplicated, query_tokens);
        promote_result_context(&mut deduplicated, query_tokens);
    }
    (deduplicated, glob_name_miss)
}

pub(super) fn ranked_exact_candidates(
    rows: Vec<IndexedRow>,
    query: &str,
    workspace: &Workspace,
) -> Vec<Candidate> {
    let tokens = meaningful_query_tokens(query);
    rows.into_iter()
        .map(|row| {
            let score = lexical_score(query, &tokens, &row)
                + if row.owner == format!("workspace:{}", workspace.reference) {
                    8.0
                } else {
                    0.0
                }
                - row.rank.max(0.0);
            indexed_candidate(row, query, &tokens, score)
        })
        .collect()
}

pub(super) fn anchored_api_query(query: &str) -> Option<(&str, Vec<String>, Vec<String>)> {
    let (anchor, refinement) = query.trim().split_once(char::is_whitespace)?;
    let specific_anchor =
        anchor.contains(['.', '_']) || anchor.chars().skip(1).any(char::is_uppercase);
    if anchor.chars().count() < 6 || !specific_anchor || !declaration_name_query(anchor) {
        return None;
    }
    let refinement_lower = refinement.trim().to_ascii_lowercase();
    if refinement_lower == "declarations"
        || matches!(
            refinement_lower.as_str(),
            "body" | "implementation" | "implementation body" | "proof" | "proof body" | "source"
        )
    {
        return Some((anchor, Vec::new(), Vec::new()));
    }
    let tokens = meaningful_query_tokens(refinement);
    let mut requested = query_tokens(refinement)
        .into_iter()
        .filter(|token| token.chars().count() >= 3)
        .collect::<Vec<_>>();
    requested.sort();
    requested.dedup();
    (!tokens.is_empty() && tokens.len() <= 24).then_some((anchor, tokens, requested))
}

pub(super) fn exact_plan(query: &str, type_search: bool) -> Option<ExactPlan> {
    if type_search {
        return None;
    }
    if let Some((anchor, refinement_tokens, requested_terms)) = anchored_api_query(query) {
        return Some(ExactPlan {
            anchor: anchor.to_owned(),
            refinement_tokens,
            requested_terms,
            recover_continuation: false,
        });
    }
    declaration_name_query(query).then(|| ExactPlan {
        anchor: query.to_owned(),
        refinement_tokens: Vec::new(),
        requested_terms: Vec::new(),
        recover_continuation: true,
    })
}

pub(super) fn missing_hit_terms(hits: &[SearchHit], terms: &[String]) -> Vec<String> {
    let searchable = hits
        .iter()
        .map(|hit| {
            format!(
                "{} {} {} {}",
                hit.name,
                hit.signature.as_deref().unwrap_or_default(),
                hit.doc.as_deref().unwrap_or_default(),
                hit.source.as_deref().unwrap_or_default()
            )
        })
        .collect::<Vec<_>>()
        .join(" ")
        .to_lowercase();
    terms
        .iter()
        .filter(|term| !searchable.contains(term.as_str()))
        .take(4)
        .cloned()
        .collect()
}

pub(super) fn context_refinement_score(hit: &SearchHit, tokens: &[String]) -> usize {
    let searchable = format!(
        "{} {}",
        hit.name,
        hit.signature.as_deref().unwrap_or_default()
    )
    .to_lowercase();
    tokens
        .iter()
        .filter(|token| searchable.contains(token.as_str()))
        .map(|token| token.chars().count())
        .sum()
}

pub(super) fn annotate_missing_hit_terms(result: &mut SearchResult, requested: &[String]) {
    let missing = missing_hit_terms(&result.hits, requested);
    if missing.is_empty() {
        return;
    }
    prepend_search_note(
        &mut result.note,
        format!("no nearby match for {}", missing.join(", ")),
    );
}

pub(super) fn prepend_search_note(note: &mut Option<String>, prefix: String) {
    *note = Some(match note.take() {
        Some(existing) => format!("{prefix}; {existing}"),
        None => prefix,
    });
}

pub(super) fn suppress_inferred_missing_note(note: &mut Option<String>) {
    let Some(current) = note.take() else {
        return;
    };
    let retained = current
        .split("; ")
        .filter(|part| !part.starts_with("no nearby match for "))
        .collect::<Vec<_>>()
        .join("; ");
    *note = (!retained.is_empty()).then_some(retained);
}

pub(super) fn meaningful_query_tokens(query: &str) -> Vec<String> {
    let mut tokens = query_tokens(query);
    if tokens.len() > 1 && tokens.iter().any(|token| !search_syntax_token(token)) {
        tokens.retain(|token| !search_syntax_token(token));
    }
    if tokens.len() > 1 {
        tokens.retain(|token| token.chars().count() >= 2);
        tokens.retain(|token| {
            !matches!(
                token.as_str(),
                "all" | "and" | "for" | "from" | "in" | "of" | "on" | "or" | "the" | "to" | "with"
            )
        });
    }
    if query_requests_proof_body(query) {
        tokens.retain(|token| {
            !matches!(
                token.as_str(),
                "body" | "implementation" | "proof" | "source"
            )
        });
    }
    let aliases = tokens
        .iter()
        .filter_map(|token| match token.as_str() {
            "addition" => Some("add"),
            "composition" => Some("comp"),
            "continuity" => Some("continuous"),
            "multiplication" => Some("mul"),
            "projection" => Some("proj"),
            "scaling" => Some("smul"),
            _ => None,
        })
        .map(str::to_owned)
        .collect::<Vec<_>>();
    tokens.extend(aliases);
    tokens.extend(
        tokens
            .clone()
            .into_iter()
            .filter_map(|token| numeric_subscript_alias(&token)),
    );
    let identifier_parts = query
        .split(|character: char| {
            !character.is_alphanumeric() && character != '_' && character != '.'
        })
        // A guessed qualified declaration often gets the namespace right but the
        // leaf wrong. Keep the qualified token for exact lookup, and search the
        // leaf's Lean-style components for nearby members of that namespace.
        .flat_map(|token| identifier_query_parts(token.rsplit('.').next().unwrap_or(token)))
        .filter(|part| {
            part.chars().count() >= 3
                && !search_syntax_token(part)
                && !matches!(
                    part.as_str(),
                    "all" | "and" | "for" | "from" | "the" | "with"
                )
        })
        .collect::<Vec<_>>();
    tokens.extend(identifier_parts);
    let mut seen = HashSet::new();
    tokens.retain(|token| seen.insert(token.clone()));
    tokens
}

fn numeric_subscript_alias(token: &str) -> Option<String> {
    const ASCII: &str = "0123456789";
    const SUBSCRIPT: &str = "₀₁₂₃₄₅₆₇₈₉";
    let has_ascii = token.chars().any(|character| ASCII.contains(character));
    let has_subscript = token
        .chars()
        .any(|character| SUBSCRIPT.contains(character));
    if has_ascii == has_subscript {
        return None;
    }
    let (from, to) = if has_ascii {
        (ASCII, SUBSCRIPT)
    } else {
        (SUBSCRIPT, ASCII)
    };
    Some(
        token
            .chars()
            .map(|character| {
                from.chars()
                    .position(|candidate| candidate == character)
                    .and_then(|index| to.chars().nth(index))
                    .unwrap_or(character)
            })
            .collect(),
    )
}

fn ascii_numeric_spelling(value: &str) -> String {
    const ASCII: &str = "0123456789";
    const SUBSCRIPT: &str = "₀₁₂₃₄₅₆₇₈₉";
    value
        .chars()
        .map(|character| {
            SUBSCRIPT
                .chars()
                .position(|candidate| candidate == character)
                .and_then(|index| ASCII.chars().nth(index))
                .unwrap_or(character)
        })
        .collect()
}

pub(super) fn search_syntax_token(token: &str) -> bool {
    matches!(
        token,
        "aesop"
            | "apply"
            | "assumption"
            | "class"
            | "constructor"
            | "constructors"
            | "def"
            | "exact"
            | "instance"
            | "lemma"
            | "name"
            | "only"
            | "rfl"
            | "rw"
            | "simp"
            | "simpa"
            | "structure"
            | "theorem"
            | "using"
    )
}

pub(super) fn identifier_query_parts(token: &str) -> Vec<String> {
    let mut parts = Vec::new();
    for segment in token.split(['.', '_']) {
        let mut start = 0;
        let characters = segment.char_indices().collect::<Vec<_>>();
        for index in 1..characters.len() {
            let (_, previous) = characters[index - 1];
            let (offset, current) = characters[index];
            let next_is_lower = characters
                .get(index + 1)
                .is_some_and(|(_, next)| next.is_lowercase());
            if current.is_uppercase()
                && (previous.is_lowercase() || previous.is_numeric() || next_is_lower)
            {
                parts.push(segment[start..offset].to_lowercase());
                start = offset;
            }
        }
        if start > 0 || segment != token {
            parts.push(segment[start..].to_lowercase());
        }
    }
    parts
}

pub(super) fn qualified_member_score(query: &str, name: &str) -> f64 {
    if !declaration_name_query(query) {
        return 0.0;
    }
    let Some((query_owner, query_leaf_raw)) = query.trim().rsplit_once('.') else {
        return 0.0;
    };
    let Some((name_owner, name_leaf_raw)) = name.rsplit_once('.') else {
        return 0.0;
    };
    let query_owner = query_owner.to_lowercase();
    let name_owner = name_owner.to_lowercase();
    if name_owner != query_owner && !name_owner.ends_with(&format!(".{query_owner}")) {
        return 0.0;
    }

    let query_parts = identifier_query_parts(query_leaf_raw)
        .into_iter()
        .filter(|part| part.len() >= 3)
        .collect::<HashSet<_>>();
    let name_parts = identifier_query_parts(name_leaf_raw)
        .into_iter()
        .filter(|part| part.len() >= 3)
        .collect::<HashSet<_>>();
    let shared_parts = query_parts.intersection(&name_parts).count();
    let query_leaf = query_leaf_raw.to_lowercase();
    let name_leaf = name_leaf_raw.to_lowercase();
    let common_prefix = query_leaf
        .chars()
        .zip(name_leaf.chars())
        .take_while(|(left, right)| left == right)
        .count();
    let common_suffix = query_leaf
        .chars()
        .rev()
        .zip(name_leaf.chars().rev())
        .take_while(|(left, right)| left == right)
        .count();
    300.0
        + shared_parts as f64 * 250.0
        + common_prefix.saturating_sub(3).min(10) as f64 * 4.0
        + common_suffix.saturating_sub(3).min(10) as f64 * 4.0
}

pub(super) fn promote_query_coverage(ranked: &mut Vec<Candidate>, tokens: &[String]) {
    if ranked.len() <= 1 || tokens.len() <= 1 {
        return;
    }
    let mut remaining = std::mem::take(ranked);
    let mut promoted: Vec<Candidate> = Vec::new();
    let qualified = tokens
        .iter()
        .filter(|token| token.contains('.') && !token.ends_with(".lean"))
        .count();
    if qualified >= 1 {
        for token in tokens
            .iter()
            .filter(|token| token.contains('.') && !token.ends_with(".lean"))
        {
            let owner = token.rsplit_once('.').map(|(owner, _)| owner);
            let direct = remaining.iter().position(|candidate| {
                candidate.hit.name.eq_ignore_ascii_case(token)
                    || qualified_leaf_path_match(
                        token,
                        &candidate.hit.name,
                        &candidate.hit.module,
                        &candidate.hit.path,
                    )
            });
            let owner_position = || {
                remaining.iter().position(|candidate| {
                    owner.is_some_and(|owner| {
                        candidate.hit.name.eq_ignore_ascii_case(owner)
                            || candidate
                                .hit
                                .name
                                .to_lowercase()
                                .ends_with(&format!(".{owner}"))
                    })
                })
            };
            let position = if qualified == 1 {
                direct.or_else(owner_position)
            } else {
                owner_position().or(direct)
            };
            if let Some(position) = position {
                promoted.push(remaining.remove(position));
            }
        }
    }
    remaining.sort_by_cached_key(|candidate| {
        std::cmp::Reverse(hit_query_coverage(&candidate.hit, tokens))
    });
    if promoted.len() < SUMMARY_LIMIT && !remaining.is_empty() {
        promoted.push(remaining.remove(0));
    }
    for token in tokens.iter().filter(|token| token.len() >= 3) {
        if promoted
            .iter()
            .any(|candidate| hit_name_matches(&candidate.hit.name, token))
        {
            continue;
        }
        let eligible = |candidate: &Candidate| {
            !matches!(candidate.hit.kind.as_str(), "file" | "imports")
                || matches!(token.as_str(), "import" | "imports")
        };
        let exact = remaining
            .iter()
            .enumerate()
            .filter(|(_, candidate)| {
                eligible(candidate) && qualified_name_matches(&candidate.hit.name, token)
            })
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        let exact = (exact.len() == 1).then(|| exact[0]);
        if let Some(position) = exact.or_else(|| {
            remaining
                .iter()
                .enumerate()
                .filter(|(_, candidate)| {
                    eligible(candidate) && hit_name_matches(&candidate.hit.name, token)
                })
                .max_by_key(|(_, candidate)| {
                    tokens
                        .iter()
                        .filter(|facet| hit_name_matches(&candidate.hit.name, facet))
                        .count()
                })
                .map(|(index, _)| index)
        }) {
            promoted.push(remaining.remove(position));
        } else if token.len() >= 6
            && !promoted
                .iter()
                .any(|candidate| hit_matches_token(&candidate.hit, token))
            && let Some(position) = remaining.iter().position(|candidate| {
                eligible(candidate) && hit_matches_token(&candidate.hit, token)
            })
        {
            promoted.push(remaining.remove(position));
        }
        if promoted.len() == SUMMARY_LIMIT {
            break;
        }
    }
    promoted.extend(remaining);
    *ranked = promoted;
}

pub(super) fn promote_result_context(ranked: &mut Vec<Candidate>, tokens: &[String]) {
    let mut seen = HashSet::new();
    let tokens = tokens
        .iter()
        .filter(|token| seen.insert(token.as_str()))
        .collect::<Vec<_>>();
    let name_coverage = |candidate: &Candidate| {
        let leaf = candidate
            .hit
            .name
            .rsplit('.')
            .next()
            .unwrap_or(&candidate.hit.name);
        tokens
            .iter()
            .filter(|token| hit_name_matches(leaf, token))
            .count()
    };
    let Some(anchor) = ranked
        .iter()
        .enumerate()
        .filter(|(_, candidate)| !matches!(candidate.hit.kind.as_str(), "file" | "imports"))
        .filter(|(_, candidate)| name_coverage(candidate) >= 2)
        .min_by_key(|(_, candidate)| candidate.hit.name.matches('.').count())
        .map(|(index, _)| index)
    else {
        return;
    };
    let anchor = ranked.remove(anchor);
    let module = anchor.hit.module.clone();
    let path = anchor.hit.path.clone();
    let mut context = vec![anchor];
    let mut index = 0;
    while context.len() < 4 && index < ranked.len() {
        let candidate = &ranked[index];
        let same_source = if module.is_empty() {
            candidate.hit.path == path
        } else {
            candidate.hit.module == module
        };
        if same_source
            && !matches!(candidate.hit.kind.as_str(), "file" | "imports")
            && name_coverage(candidate) > 0
        {
            context.push(ranked.remove(index));
        } else {
            index += 1;
        }
    }
    context.append(ranked);
    *ranked = context;
}

pub(super) fn hit_name_matches(name: &str, token: &str) -> bool {
    if name.eq_ignore_ascii_case(token) {
        return true;
    }
    let leaf = token.rsplit('.').next().unwrap_or(token);
    name.split(['.', '_']).any(|segment| {
        words_match(segment, leaf)
            || identifier_query_parts(segment)
                .iter()
                .any(|part| conceptual_words_match(part, leaf))
    })
}

pub(super) fn hit_matches_token(hit: &SearchHit, token: &str) -> bool {
    hit_name_matches(&hit.name, token)
        || [
            hit.signature.as_deref(),
            hit.doc.as_deref(),
            hit.source.as_deref(),
            Some(hit.module.as_str()),
            Some(hit.path.as_str()),
        ]
        .into_iter()
        .flatten()
        .any(|text| text_matches_token(&text.to_lowercase(), token))
}

pub(super) fn hit_query_coverage(
    hit: &SearchHit,
    tokens: &[String],
) -> (usize, usize, usize, usize) {
    let matched = tokens
        .iter()
        .filter(|token| hit_matches_token(hit, token))
        .fold((0, 0), |(count, weight), token| {
            (count + 1, weight + token.chars().count())
        });
    let name_matched = tokens
        .iter()
        .filter(|token| hit_name_matches(&hit.name, token))
        .fold((0, 0), |(count, weight), token| {
            (count + 1, weight + token.chars().count())
        });
    (matched.0, matched.1, name_matched.0, name_matched.1)
}

pub(super) fn text_matches_token(text: &str, token: &str) -> bool {
    text.contains(token)
        || token
            .strip_suffix('s')
            .filter(|singular| singular.len() >= 4)
            .is_some_and(|singular| text.contains(singular))
}

pub(super) fn words_match(left: &str, right: &str) -> bool {
    left.eq_ignore_ascii_case(right)
        || numeric_subscript_alias(left)
            .is_some_and(|alias| alias.eq_ignore_ascii_case(right))
        || numeric_subscript_alias(right)
            .is_some_and(|alias| alias.eq_ignore_ascii_case(left))
        || right
            .strip_suffix('s')
            .filter(|singular| singular.len() >= 4)
            .is_some_and(|singular| left.eq_ignore_ascii_case(singular))
        || left
            .strip_suffix('s')
            .filter(|singular| singular.len() >= 4)
            .is_some_and(|singular| singular.eq_ignore_ascii_case(right))
}

fn conceptual_words_match(left: &str, right: &str) -> bool {
    if words_match(left, right) {
        return true;
    }
    let left = left.to_lowercase();
    let right = right.to_lowercase();
    let shared = left
        .chars()
        .zip(right.chars())
        .take_while(|(left, right)| left == right)
        .count();
    let shorter = left.chars().count().min(right.chars().count());
    shared >= 5 && shared * 3 >= shorter * 2
}

pub(super) fn declaration_leaf_matches(name: &str, query: &str) -> bool {
    let leaf = name.rsplit('.').next().unwrap_or(name);
    query_tokens(query).iter().any(|token| {
        let token = token.rsplit('.').next().unwrap_or(token);
        words_match(leaf, token)
    })
}

pub(super) fn lexical_score(query: &str, tokens: &[String], row: &IndexedRow) -> f64 {
    let exact_case_name = row.name == query;
    let exact_case_leaf = row.name.rsplit('.').next() == Some(query);
    let query = query.to_lowercase();
    let name = row.name.to_lowercase();
    let base = name.rsplit('.').next().unwrap_or(&name);
    let body = format!(
        "{} {} {} {}",
        row.signature.to_lowercase(),
        row.docs.to_lowercase(),
        row.body.to_lowercase(),
        row.path.to_lowercase()
    );
    let mut score = if name == query {
        600.0
    } else if base == query {
        105.0
    } else if name.ends_with(&format!(".{query}")) {
        95.0
    } else if name.starts_with(&query) || base.starts_with(&query) {
        75.0
    } else if name.contains(&query) {
        55.0
    } else {
        0.0
    };
    if row.kind != "file"
        && tokens.iter().any(|token| {
            token == &name || (token.len() >= 12 && !token.contains('.') && token.as_str() == base)
        })
    {
        score += 100.0;
    }
    if exact_case_name {
        score += 200.0;
    } else if exact_case_leaf {
        score += 160.0;
    }
    for token in tokens {
        if name.contains(token) {
            score += 12.0;
        } else if body.contains(token) {
            score += 3.0;
        }
    }
    let name_parts = identifier_query_parts(&row.name)
        .into_iter()
        .collect::<HashSet<_>>();
    let query_parts = tokens
        .iter()
        .flat_map(|token| {
            let parts = identifier_query_parts(token);
            if parts.is_empty() {
                vec![token.rsplit('.').next().unwrap_or(token).to_owned()]
            } else {
                parts
            }
        })
        .collect::<HashSet<_>>();
    for part in query_parts {
        if name_parts.contains(&part) {
            score += 40.0;
        } else if name_parts
            .iter()
            .any(|name_part| conceptual_words_match(name_part, &part))
        {
            score += 35.0;
        }
    }
    if row.kind != "file" {
        score += 20.0;
    } else {
        score -= 40.0;
    }
    score += qualified_member_score(&query, &row.name);
    score += qualified_leaf_path_score(&query, &row.name, &row.module, &row.path);
    score
}

pub(super) fn qualified_leaf_path_score(query: &str, name: &str, module: &str, path: &str) -> f64 {
    if !qualified_leaf_path_match(query, name, module, path) {
        let Some((query_owner, query_leaf)) = query.rsplit_once('.') else {
            return 0.0;
        };
        let Some((name_owner, name_leaf)) = name.rsplit_once('.') else {
            return 0.0;
        };
        if !name_leaf.eq_ignore_ascii_case(query_leaf) {
            return 0.0;
        }
        let query_owner = identifier_query_parts(query_owner)
            .into_iter()
            .collect::<HashSet<_>>();
        let name_owner = identifier_query_parts(name_owner)
            .into_iter()
            .collect::<HashSet<_>>();
        return 60.0 + query_owner.intersection(&name_owner).count() as f64 * 100.0;
    }
    280.0
}

pub(super) fn qualified_leaf_path_match(query: &str, name: &str, module: &str, path: &str) -> bool {
    let Some((owner, query_leaf)) = query.rsplit_once('.') else {
        return false;
    };
    let name_leaf = name.rsplit('.').next().unwrap_or(name);
    if !words_match(name_leaf, query_leaf) {
        return false;
    }
    let owner = owner.rsplit('.').next().unwrap_or(owner).to_lowercase();
    let location = format!("{module} {path}").to_lowercase();
    owner.chars().count() >= 3 && location.contains(&owner)
}

pub(super) fn type_shaped(query: &str) -> bool {
    query_tokens(query).iter().any(|token| token == "_")
        || query.contains('→')
        || query.contains("->")
        || query.contains('⊢')
        || query.contains("∀")
        || query.contains("fun ")
}

pub(super) fn conclusion_query(query: &str) -> bool {
    let query = query.trim_start();
    query.starts_with('⊢') || query.starts_with("|-")
}

pub(super) fn apply_import_context(candidate: &mut Candidate, context: &ImportContext) {
    if candidate.hit.module.is_empty() {
        return;
    }
    if context.accessible.contains(&candidate.hit.module) {
        candidate.score += 30.0;
        candidate.hit.required_import = None;
    } else if context.complete {
        candidate.score -= 10.0;
        candidate.hit.required_import = Some(candidate.hit.module.clone());
    }
}

pub(super) fn merge_duplicate_hit(existing: &mut SearchHit, candidate: &mut SearchHit) {
    if existing.kind == "declaration" && !matches!(candidate.kind.as_str(), "declaration" | "file")
    {
        existing.kind = candidate.kind.clone();
    }
    if existing.signature.is_none() {
        existing.signature = candidate.signature.take();
    }
    if existing.doc.is_none() {
        existing.doc = candidate.doc.take();
    }
    if existing
        .source
        .as_deref()
        .is_none_or(|source| source.trim().is_empty())
    {
        existing.source = candidate.source.take();
    }
    if existing.usages.is_empty() {
        existing.usages = std::mem::take(&mut candidate.usages);
    }
    existing.applicable |= candidate.applicable;
    if existing.required_import.is_none() {
        existing.required_import = candidate.required_import.take();
    }
}

pub(super) fn exact_search_result(mut hits: Vec<SearchHit>, base_warming: bool) -> SearchResult {
    // Exact results are commonly pasted into a namespace where their leading
    // namespace may be shadowed. Make the resolved declaration absolute while
    // leaving nearby API results compact.
    if let Some(hit) = hits.first_mut()
        && hit.kind != "fields"
        && !hit.name.starts_with("_root_.")
    {
        hit.name.insert_str(0, "_root_.");
    }
    SearchResult {
        hits,
        inference: if type_search_enabled() {
            "hybrid".into()
        } else {
            "hybrid(type-off)".into()
        },
        note: base_warming.then(|| "source index warming".into()),
        ok: true,
    }
}

pub(super) fn structural_type_score(pattern: &str, signature: &str) -> f64 {
    if signature.is_empty() {
        return 0.0;
    }
    let pattern_tokens = query_tokens(pattern)
        .into_iter()
        .filter(|token| token != "_")
        .collect::<Vec<_>>();
    let signature_lower = signature.to_lowercase();
    if !pattern_tokens
        .iter()
        .all(|token| signature_lower.contains(token))
    {
        return 0.0;
    }
    let explicit_conclusion = conclusion_query(pattern);
    let pattern_without_turnstile = pattern
        .trim_start()
        .strip_prefix('⊢')
        .or_else(|| pattern.trim_start().strip_prefix("|-"))
        .unwrap_or(pattern)
        .trim_start();
    let conclusion_head = pattern_without_turnstile
        .split(|character: char| character.is_whitespace() || character == '(')
        .find(|part| !part.is_empty());
    let conclusion_score = if explicit_conclusion
        && conclusion_head.is_some_and(|head| signature.contains(&format!(": {head}")))
    {
        80.0
    } else {
        0.0
    };
    let shape_score = ["∘", "→L", "≃L", "↔", "∈", "⊆"]
        .into_iter()
        .filter(|shape| pattern.contains(shape) && signature.contains(shape))
        .count() as f64
        * 50.0;
    let arrows = pattern.matches('→').count() + pattern.matches("->").count();
    let signature_arrows = signature.matches('→').count() + signature.matches("->").count();
    let arrow_score = if arrows == 0 {
        0.0
    } else if arrows == signature_arrows {
        24.0
    } else if arrows < signature_arrows {
        10.0
    } else {
        0.0
    };
    20.0 + arrow_score + conclusion_score + shape_score + pattern_tokens.len() as f64 * 5.0
}

pub(super) fn type_search_enabled() -> bool {
    let opted_out = std::env::var("MATHMUX_LOOGLE")
        .ok()
        .is_some_and(|value| matches!(value.to_ascii_lowercase().as_str(), "0" | "false" | "off"));
    let memory_limited = std::env::var("MATHMUX_SEARCH_MEMORY_MB")
        .ok()
        .and_then(|value| value.parse::<u64>().ok())
        .is_some_and(|limit| limit < 16_384);
    !opted_out && !memory_limited
}

pub(super) fn nonempty(value: String) -> Option<String> {
    (!value.trim().is_empty()).then_some(value)
}
