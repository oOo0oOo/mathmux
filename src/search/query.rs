use super::*;

pub(super) fn field_inventory_query(query: &str) -> Option<&str> {
    let terms = query.split_whitespace().collect::<Vec<_>>();
    let (name, facet) = match terms.as_slice() {
        [name, facet] => (*name, *facet),
        [kind, name, facet]
            if matches!(kind.to_ascii_lowercase().as_str(), "class" | "structure") =>
        {
            (*name, *facet)
        }
        _ => return None,
    };
    (declaration_name_query(name)
        && matches!(
            facet.to_ascii_lowercase().as_str(),
            "field" | "fields" | "projection" | "projections"
        ))
    .then_some(name)
}

pub(super) fn require_submission_refinement(reference: &str, refinement: &str) -> Result<()> {
    ensure!(
        !refinement.trim().is_empty(),
        "{reference} requires search terms; use show {reference} first, then --all only if needed"
    );
    Ok(())
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

pub(super) fn diagnostic_goal_detail(diagnostic: &str) -> Option<String> {
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

pub(super) fn diagnostic_defeq_detail(diagnostic: &str) -> Option<String> {
    let (_, comparison) = diagnostic.split_once("left-hand side")?;
    let (left, right) =
        comparison.split_once("is not definitionally equal to the right-hand side")?;
    let left = diagnostic_expression(left);
    let right = diagnostic_expression(right);
    (!left.is_empty() && !right.is_empty()).then(|| format!("left\n{left}\nright\n{right}"))
}

pub(super) fn diagnostic_rewrite_detail(
    diagnostic: &str,
    source_context: Option<&str>,
) -> Option<String> {
    let rewrite_failure = diagnostic.contains("rewrite")
        || diagnostic.contains("Tactic `rw`")
        || diagnostic.contains("pattern not found");
    if !rewrite_failure {
        return None;
    }
    let source = source_context
        .and_then(|context| {
            context
                .lines()
                .find(|line| line.trim_start().starts_with('>'))
        })
        .and_then(|line| line.split_once('|'))
        .map(|(_, code)| code.trim())
        .filter(|code| !code.is_empty());
    let message = diagnostic
        .lines()
        .find(|line| line.contains("rewrite") || line.contains("pattern not found"))
        .map(str::trim)
        .unwrap_or("rewrite failed");
    Some(match source {
        Some(source) => format!("rewrite\n{source}\n{message}"),
        None => format!("rewrite\n{message}"),
    })
}

fn diagnostic_expression(section: &str) -> String {
    section
        .lines()
        .map(str::trim)
        .skip_while(|line| line.is_empty())
        .take_while(|line| {
            !line.is_empty()
                && !line.starts_with("case ")
                && !line.starts_with("⊢ ")
                && !line.contains("Try this:")
        })
        .collect::<Vec<_>>()
        .join(" ")
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

#[allow(dead_code)]
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

#[allow(dead_code)]
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
            | "declaration"
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
    if !(declaration_name_query(name) || declaration_glob_query(name))
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
    let alternatives = query.split('|').map(str::trim).collect::<Vec<_>>();
    alternatives
        .iter()
        .any(|alternative| alternative.contains('*'))
        && alternatives.iter().all(|alternative| {
            alternative
                .chars()
                .filter(|character| character.is_alphanumeric())
                .count()
                >= 2
                && alternative.chars().all(|character| {
                    character.is_alphanumeric() || matches!(character, '_' | '.' | '\'' | '*')
                })
        })
}

pub(super) fn declaration_glob_fts_query(query: &str) -> Option<String> {
    declaration_glob_query(query).then(|| {
        query
            .split('|')
            .filter_map(|alternative| {
                let terms = query_tokens(alternative)
                    .into_iter()
                    .map(|term| format!("name : \"{}\"*", term.replace('"', "\"\"")))
                    .collect::<Vec<_>>();
                (!terms.is_empty()).then(|| format!("({})", terms.join(" AND ")))
            })
            .collect::<Vec<_>>()
            .join(" OR ")
    })
}

pub(super) fn apply_declaration_glob(candidates: &mut Vec<Candidate>, query: &str) -> bool {
    if !declaration_glob_query(query) {
        return false;
    }
    let had_candidates = !candidates.is_empty();
    candidates.retain(|candidate| declaration_alternative_matches(&candidate.hit.name, query));
    had_candidates && candidates.is_empty()
}

fn declaration_alternative_matches(name: &str, query: &str) -> bool {
    query.split('|').map(str::trim).any(|alternative| {
        if alternative.contains('*') {
            declaration_glob_matches(name, alternative)
        } else {
            qualified_name_matches(name, alternative)
        }
    })
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

pub(super) fn declaration_glob_leaf_matches(name: &str, query: &str) -> bool {
    let leaf = canonical_declaration_name(name)
        .rsplit('.')
        .next()
        .unwrap_or(name);
    query.split('|').map(str::trim).any(|alternative| {
        declaration_glob_matches(name, alternative)
            && declaration_glob_matches(leaf, alternative.rsplit('.').next().unwrap_or(alternative))
    })
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
    if show_all {
        RESULT_LIMIT
    } else if exact_name_miss {
        RELATED_RESULT_LIMIT.min(3)
    } else {
        8
    }
}

#[allow(dead_code)]
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
    let query_name = canonical_declaration_name(query);
    let exact_names = candidates
        .iter()
        .filter(|candidate| {
            canonical_declaration_name(&candidate.hit.name).eq_ignore_ascii_case(query_name)
        })
        .map(|candidate| canonical_declaration_name(&candidate.hit.name).to_lowercase())
        .collect::<HashSet<_>>();
    let names = if !exact_names.is_empty() {
        exact_names
    } else {
        candidates
            .iter()
            .filter(|candidate| exact_declaration_name_matches(&candidate.hit.name, query))
            .map(|candidate| canonical_declaration_name(&candidate.hit.name).to_lowercase())
            .collect::<HashSet<_>>()
    };
    let names = names.into_iter().collect::<Vec<_>>();
    let [name] = names.as_slice() else {
        return None;
    };
    Some(
        candidates
            .into_iter()
            .filter(|candidate| {
                canonical_declaration_name(&candidate.hit.name).eq_ignore_ascii_case(name)
            })
            .collect(),
    )
}

pub(super) fn exact_declaration_name_matches(name: &str, query: &str) -> bool {
    let name = canonical_declaration_name(name);
    let query = canonical_declaration_name(query.trim());
    if query.contains('.') {
        name.eq_ignore_ascii_case(query)
    } else {
        name.eq_ignore_ascii_case(query)
            || name
                .strip_suffix(query)
                .is_some_and(|prefix| prefix.ends_with('.'))
    }
}

pub(super) fn merge_exact_candidates(candidates: Vec<Candidate>) -> Candidate {
    let mut candidates = sort_and_merge_candidates(candidates);
    debug_assert_eq!(candidates.len(), 1);
    candidates.remove(0)
}

fn sort_and_merge_candidates(mut candidates: Vec<Candidate>) -> Vec<Candidate> {
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
        let identity = if matches!(candidate.hit.kind.as_str(), "file" | "imports") {
            candidate.hit.name.clone()
        } else {
            canonical_declaration_name(&candidate.hit.name).to_owned()
        };
        if let Some(index) = positions.get(&identity).copied() {
            merge_duplicate_hit(&mut deduplicated[index].hit, &mut candidate.hit);
            deduplicated[index].origins |= candidate.origins;
        } else {
            positions.insert(identity, deduplicated.len());
            deduplicated.push(candidate);
        }
    }
    deduplicated
}

pub(super) fn rank_discovery_candidates(
    mut candidates: Vec<Candidate>,
    query: &str,
    query_tokens: &[String],
    explicit_declaration: bool,
    import_context: Option<&ImportContext>,
) -> (Vec<Candidate>, bool) {
    // Candidate producers perform retrieval and base scoring. The bottleneck below
    // deliberately keeps the remaining rules in one stable, inspectable order.
    let glob_name_miss = apply_declaration_glob(&mut candidates, query);
    apply_context_scores(&mut candidates, import_context);
    let mut ranked = sort_and_merge_candidates(candidates);
    promote_ranked_candidates(&mut ranked, query, query_tokens, explicit_declaration);
    if !explicit_declaration {
        diversify_ranked_candidates(&mut ranked, query, query_tokens);
    }
    (ranked, glob_name_miss)
}

fn apply_context_scores(candidates: &mut [Candidate], import_context: Option<&ImportContext>) {
    if let Some(context) = import_context {
        for candidate in candidates {
            apply_import_context(candidate, context);
        }
    }
}

fn promote_ranked_candidates(
    ranked: &mut Vec<Candidate>,
    query: &str,
    query_tokens: &[String],
    explicit_declaration: bool,
) {
    if explicit_declaration {
        if declaration_glob_query(query) {
            ranked.sort_by_key(|candidate| {
                !declaration_glob_leaf_matches(&candidate.hit.name, query)
            });
        } else {
            ranked.sort_by_key(|candidate| !qualified_name_matches(&candidate.hit.name, query));
        }
        return;
    }
    promote_query_coverage(ranked, query, query_tokens);
}

fn diversify_ranked_candidates(ranked: &mut Vec<Candidate>, query: &str, query_tokens: &[String]) {
    let qualified_anchor = ranked.first().and_then(|candidate| {
        query_tokens
            .iter()
            .filter(|token| token.contains('.') && !token.ends_with(".lean"))
            .any(|token| {
                qualified_name_matches(&candidate.hit.name, token)
                    || token.rsplit_once('.').is_some_and(|(owner, _)| {
                        qualified_name_matches(&candidate.hit.name, owner)
                    })
            })
            .then(|| candidate.hit.name.clone())
    });
    if !query.contains('|') {
        promote_result_context(ranked, query, query_tokens);
        if !declaration_name_query(query) {
            promote_strongest_query_coverage(ranked, query_tokens);
        }
    }
    if let Some(anchor) = qualified_anchor
        && let Some(position) = ranked
            .iter()
            .position(|candidate| candidate.hit.name == anchor)
    {
        let anchor = ranked.remove(position);
        ranked.insert(0, anchor);
    }
}

fn promote_strongest_query_coverage(ranked: &mut Vec<Candidate>, tokens: &[String]) {
    if ranked.len() <= 1 || tokens.len() <= 1 {
        return;
    }
    let top_coverage = hit_query_coverage(&ranked[0].hit, tokens).0;
    let Some((position, best_coverage)) = ranked
        .iter()
        .enumerate()
        .skip(1)
        .map(|(position, candidate)| (position, hit_query_coverage(&candidate.hit, tokens).0))
        .max_by_key(|(_, coverage)| *coverage)
    else {
        return;
    };
    if best_coverage >= 2 && best_coverage > top_coverage {
        let candidate = ranked.remove(position);
        ranked.insert(0, candidate);
    }
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
                    SEARCH_TUNING.lexical.workspace
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
            source_requested: query_requests_proof_body(query),
        });
    }
    let terms = query.split_whitespace().collect::<Vec<_>>();
    if terms.len() > 1
        && declaration_name_query(terms[0])
        && query_requests_proof_body(query)
        && terms[1..].iter().all(|term| {
            matches!(
                term.to_ascii_lowercase().as_str(),
                "body" | "implementation" | "proof" | "source"
            )
        })
    {
        return Some(ExactPlan {
            anchor: terms[0].to_owned(),
            refinement_tokens: Vec::new(),
            requested_terms: Vec::new(),
            recover_continuation: false,
            source_requested: true,
        });
    }
    declaration_name_query(query).then(|| ExactPlan {
        anchor: query.to_owned(),
        refinement_tokens: Vec::new(),
        requested_terms: Vec::new(),
        recover_continuation: true,
        source_requested: false,
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
        .take(SEARCH_TUNING.promotion.missing_term_limit)
        .cloned()
        .collect()
}

#[allow(dead_code)]
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
    let has_subscript = token.chars().any(|character| SUBSCRIPT.contains(character));
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
            | "concept"
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
    let tuning = SEARCH_TUNING.qualified;
    tuning.member
        + shared_parts as f64 * tuning.shared_part
        + common_prefix
            .saturating_sub(tuning.affix_ignored)
            .min(tuning.affix_cap) as f64
            * tuning.affix_character
        + common_suffix
            .saturating_sub(tuning.affix_ignored)
            .min(tuning.affix_cap) as f64
            * tuning.affix_character
}

pub(super) fn promote_query_coverage(ranked: &mut Vec<Candidate>, query: &str, tokens: &[String]) {
    if ranked.len() <= 1 || tokens.len() <= 1 {
        return;
    }
    let mut remaining = std::mem::take(ranked);
    let mut promoted: Vec<Candidate> = Vec::new();
    let alternative_queries = query
        .split('|')
        .map(str::trim)
        .filter(|query| !query.is_empty())
        .collect::<Vec<_>>();
    if alternative_queries.len() > 1 {
        for alternative in &alternative_queries {
            let positions = remaining
                .iter()
                .enumerate()
                .filter(|(_, candidate)| {
                    !matches!(candidate.hit.kind.as_str(), "file" | "imports")
                        && qualified_name_matches(&candidate.hit.name, alternative)
                })
                .map(|(position, _)| position)
                .collect::<Vec<_>>();
            if let [position] = positions.as_slice() {
                promoted.push(remaining.remove(*position));
                break;
            }
        }
    }
    let qualified = if alternative_queries.len() > 1 {
        0
    } else {
        tokens
            .iter()
            .filter(|token| token.contains('.') && !token.ends_with(".lean"))
            .count()
    };
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
    let alternatives = alternative_queries
        .iter()
        .map(|query| meaningful_query_tokens(query))
        .filter(|tokens| !tokens.is_empty())
        .collect::<Vec<_>>();
    let compound_name_parts = compound_name_query_parts(query);
    remaining.sort_by_cached_key(|candidate| {
        let coverage = if alternatives.len() > 1 {
            alternatives
                .iter()
                .map(|tokens| hit_query_coverage(&candidate.hit, tokens))
                .max()
                .unwrap_or_default()
        } else {
            hit_query_coverage(&candidate.hit, tokens)
        };
        let compound_name_coverage = compound_name_parts.as_ref().map_or((0, 0), |parts| {
            parts
                .iter()
                .filter(|part| hit_name_matches(&candidate.hit.name, part))
                .fold((0, 0), |(count, weight), part| {
                    (count + 1, weight + part.chars().count())
                })
        });
        std::cmp::Reverse((compound_name_coverage, coverage))
    });
    if promoted.len() < SUMMARY_LIMIT && !remaining.is_empty() {
        promoted.push(remaining.remove(0));
    }
    for token in tokens
        .iter()
        .filter(|token| token.len() >= SEARCH_TUNING.promotion.coverage_token_chars)
    {
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
        } else if token.len() >= SEARCH_TUNING.promotion.body_token_chars
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

fn compound_name_query_parts(query: &str) -> Option<Vec<String>> {
    (declaration_name_query(query) && !query.contains('.'))
        .then(|| {
            identifier_query_parts(query)
                .into_iter()
                .filter(|part| part.len() >= SEARCH_TUNING.promotion.coverage_token_chars)
                .collect::<Vec<_>>()
        })
        .filter(|parts| parts.len() >= 2)
}

pub(super) fn promote_result_context(ranked: &mut Vec<Candidate>, query: &str, tokens: &[String]) {
    let mut seen = HashSet::new();
    let compound_name_parts = compound_name_query_parts(query);
    let tokens = compound_name_parts.as_ref().map_or_else(
        || {
            tokens
                .iter()
                .filter(|token| seen.insert(token.as_str()))
                .collect::<Vec<_>>()
        },
        |parts| parts.iter().collect::<Vec<_>>(),
    );
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
            .fold((0, 0), |(count, weight), token| {
                (count + 1, weight + token.chars().count())
            })
    };
    let Some(anchor) = ranked
        .iter()
        .enumerate()
        .filter(|(_, candidate)| !matches!(candidate.hit.kind.as_str(), "file" | "imports"))
        .filter(|(_, candidate)| {
            name_coverage(candidate).0 >= SEARCH_TUNING.promotion.context_name_coverage
        })
        .min_by_key(|(_, candidate)| {
            let coverage = compound_name_parts
                .as_ref()
                .map(|_| std::cmp::Reverse(name_coverage(candidate)))
                .unwrap_or_default();
            (coverage, candidate.hit.name.matches('.').count())
        })
        .map(|(index, _)| index)
    else {
        return;
    };
    let anchor = ranked.remove(anchor);
    let module = anchor.hit.module.clone();
    let path = anchor.hit.path.clone();
    let mut context = vec![anchor];
    let mut index = 0;
    while context.len() < SEARCH_TUNING.promotion.context_group_size && index < ranked.len() {
        let candidate = &ranked[index];
        let same_source = if module.is_empty() {
            candidate.hit.path == path
        } else {
            candidate.hit.module == module
        };
        if same_source
            && !matches!(candidate.hit.kind.as_str(), "file" | "imports")
            && name_coverage(candidate).0 > 0
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

pub(super) fn promote_bridge_candidate(
    ranked: &mut Vec<Candidate>,
    tokens: &[String],
) -> Option<String> {
    let anchor = ranked.first()?;
    let anchor_coverage = hit_query_coverage(&anchor.hit, tokens).0;
    let anchor_name = anchor.hit.name.to_ascii_lowercase();
    let anchor_leaf = anchor_name.rsplit('.').next().unwrap_or(&anchor_name);
    let mut best = None;
    for (index, candidate) in ranked.iter().enumerate().skip(1) {
        let candidate_name = candidate.hit.name.to_ascii_lowercase();
        let candidate_leaf = candidate_name.rsplit('.').next().unwrap_or(&candidate_name);
        let shared_consumer = anchor.hit.usages.iter().any(|left| {
            candidate
                .hit
                .usages
                .iter()
                .any(|right| left.path == right.path && left.context == right.context)
        });
        let usage_edge = anchor.hit.usages.iter().any(|usage| {
            usage
                .context
                .as_deref()
                .is_some_and(|context| context.to_ascii_lowercase().contains(candidate_leaf))
        }) || candidate.hit.usages.iter().any(|usage| {
            usage
                .context
                .as_deref()
                .is_some_and(|context| context.to_ascii_lowercase().contains(anchor_leaf))
        });
        let union_coverage = tokens
            .iter()
            .filter(|token| {
                hit_matches_token(&anchor.hit, token) || hit_matches_token(&candidate.hit, token)
            })
            .count();
        if union_coverage <= anchor_coverage {
            continue;
        }
        let relation = usage_edge || shared_consumer;
        let score = union_coverage * 10 + usize::from(relation) * 5;
        if best
            .as_ref()
            .is_none_or(|(_, best_score, _, _)| score > *best_score)
        {
            best = Some((index, score, union_coverage, relation));
        }
    }
    let (index, _, coverage, related) = best?;
    let bridge = ranked.remove(index);
    let bridge_name = bridge.hit.name.clone();
    ranked.insert(1, bridge);
    Some(format!(
        "bridge pair (inferred{}): {} ↔ {} covers {coverage}/{} concepts",
        if related { ", shared consumer" } else { "" },
        ranked[0].hit.name,
        bridge_name,
        tokens.len()
    ))
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
        || numeric_subscript_alias(left).is_some_and(|alias| alias.eq_ignore_ascii_case(right))
        || numeric_subscript_alias(right).is_some_and(|alias| alias.eq_ignore_ascii_case(left))
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
    let tuning = SEARCH_TUNING.lexical;
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
        tuning.exact_name
    } else if base == query {
        tuning.exact_leaf
    } else if name.ends_with(&format!(".{query}")) {
        tuning.suffix
    } else if name.starts_with(&query) || base.starts_with(&query) {
        tuning.prefix
    } else if name.contains(&query) {
        tuning.substring
    } else {
        0.0
    };
    if row.kind != "file"
        && tokens.iter().any(|token| {
            token == &name || (token.len() >= 12 && !token.contains('.') && token.as_str() == base)
        })
    {
        score += tuning.exact_token;
    }
    if exact_case_name {
        score += tuning.exact_case_name;
    } else if exact_case_leaf {
        score += tuning.exact_case_leaf;
    }
    for token in tokens {
        if name.contains(token) {
            score += tuning.token_in_name;
        } else if body.contains(token) {
            score += tuning.token_in_body;
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
            score += tuning.identifier_part;
        } else if name_parts
            .iter()
            .any(|name_part| conceptual_words_match(name_part, &part))
        {
            score += tuning.conceptual_part;
        }
    }
    if row.kind != "file" {
        score += tuning.declaration;
    } else {
        score -= tuning.file_penalty;
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
        let tuning = SEARCH_TUNING.qualified;
        return tuning.approximate_leaf
            + query_owner.intersection(&name_owner).count() as f64 * tuning.shared_owner_part;
    }
    SEARCH_TUNING.qualified.direct_leaf_path
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
        candidate.score += SEARCH_TUNING.promotion.import_available;
        if context
            .preferred_module
            .as_deref()
            .is_some_and(|module| candidate.hit.module.eq_ignore_ascii_case(module))
        {
            candidate.score += SEARCH_TUNING.promotion.current_context;
        }
        if context
            .preferred_path
            .as_deref()
            .is_some_and(|path| candidate.hit.path == *path || candidate.hit.path.ends_with(path))
        {
            candidate.score += SEARCH_TUNING.promotion.current_source;
        }
        candidate.hit.required_import = None;
    } else if context.complete {
        candidate.score -= SEARCH_TUNING.promotion.import_missing;
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
        inference: "exact".into(),
        note: base_warming.then(|| "source index warming".into()),
        ok: true,
    }
}

pub(super) fn structural_type_score(pattern: &str, signature: &str) -> f64 {
    let tuning = SEARCH_TUNING.type_score;
    if signature.is_empty() {
        return 0.0;
    }
    let pattern_tokens = query_tokens(pattern)
        .into_iter()
        .filter(|token| token != "_")
        .map(|token| token.rsplit('.').next().unwrap_or(&token).to_owned())
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
        tuning.conclusion
    } else {
        0.0
    };
    let shape_score = ["∘", "→L", "≃L", "↔", "∈", "⊆"]
        .into_iter()
        .filter(|shape| pattern.contains(shape) && signature.contains(shape))
        .count() as f64
        * tuning.shape;
    let arrows = pattern.matches('→').count() + pattern.matches("->").count();
    let signature_arrows = signature.matches('→').count() + signature.matches("->").count();
    let arrow_score = if arrows == 0 {
        0.0
    } else if arrows == signature_arrows {
        tuning.exact_arrows
    } else if arrows < signature_arrows {
        tuning.compatible_arrows
    } else {
        0.0
    };
    tuning.base
        + arrow_score
        + conclusion_score
        + shape_score
        + pattern_tokens.len() as f64 * tuning.token
}

pub(super) fn structural_result_type_score(pattern: &str, signature: &str) -> f64 {
    let result = declaration_result_type(signature);
    let required_shapes = ["≃L", "↔", "≤", "≥", "≠", "∈", "⊆", "∘"];
    if required_shapes
        .into_iter()
        .any(|shape| pattern.contains(shape) && !result.contains(shape))
        || (pattern.contains(" = ") && !result.contains(" = "))
        || (pattern.contains(" < ") && !result.contains(" < "))
        || (pattern.contains(" > ") && !result.contains(" > "))
    {
        return 0.0;
    }
    structural_type_score(pattern, result)
}

fn declaration_result_type(signature: &str) -> &str {
    let signature = signature.trim();
    if signature.starts_with('∀') {
        return signature;
    }
    let begins_with_binder = matches!(signature.chars().next(), Some('{' | '['))
        || (signature.starts_with('(')
            && signature
                .split_once(')')
                .is_some_and(|(binder, _)| binder.contains(':')));
    let mut depth = 0_u32;
    for (index, character) in signature.char_indices() {
        match character {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth = depth.saturating_sub(1),
            ':' if depth == 0 => return signature[index + 1..].trim(),
            _ => {}
        }
    }
    if begins_with_binder { "" } else { signature }
}

pub(super) fn nonempty(value: String) -> Option<String> {
    (!value.trim().is_empty()).then_some(value)
}
