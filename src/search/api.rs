use crate::reference::{Reference, ReferenceKind};
use anyhow::{Result, bail, ensure};

const KINDS: &[&str] = &[
    "abbrev",
    "class",
    "def",
    "inductive",
    "instance",
    "lemma",
    "structure",
    "theorem",
];

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum SearchExpression {
    ExactNames(Vec<String>),
    Type(String),
    Regex(String),
    Query(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct SearchRequest {
    pub(super) expression: SearchExpression,
    pub(super) displayed_query: String,
    pub(super) limit: Option<usize>,
    pub(super) all: bool,
}

impl SearchRequest {
    pub(super) fn parse(query: &str, limit: Option<usize>, all: bool) -> Result<Self> {
        let query = query.trim();
        ensure!(!query.is_empty(), "search query is empty");
        if let Some(limit) = limit {
            ensure!(
                (1..=200).contains(&limit),
                "--limit must be between 1 and 200"
            );
        }
        ensure!(
            !query
                .split_whitespace()
                .any(|term| term.eq_ignore_ascii_case("more")),
            "search has no `more` modifier; use `show qREF --all`"
        );
        ensure!(
            !Reference::is_kind(
                query.split_whitespace().next().unwrap_or(""),
                ReferenceKind::Check,
            ),
            "inspect a stored check with `mathmux probe cREF`"
        );
        ensure!(
            !matches!(
                query.split_whitespace().next(),
                Some("#check" | "#synth" | "#reduce" | "#print")
            ),
            "Lean directives belong to `mathmux probe CONTEXT \"#check TERM\"`"
        );

        let terms = query.split_whitespace().collect::<Vec<_>>();
        if terms.len() > 1 && KINDS.contains(&terms[0]) && terms[1].starts_with("name:") {
            bail!("KIND and name: are separate search forms and cannot be combined");
        }

        let expression = if let Some(names) = query.strip_prefix("name:") {
            ensure!(
                !names.chars().any(char::is_whitespace),
                "name: accepts one name or a `|` batch"
            );
            let names = names.split('|').map(str::trim).collect::<Vec<_>>();
            if names
                .iter()
                .skip(1)
                .any(|name| name.strip_prefix("name:").is_some())
            {
                let pattern = names
                    .iter()
                    .map(|name| name.strip_prefix("name:").unwrap_or(name))
                    .collect::<Vec<_>>()
                    .join("|");
                bail!("name: accepts one prefix; use `name:{pattern}` for an exact batch");
            }
            if names.is_empty() || !names.iter().all(|name| declaration_name(name)) {
                if names.iter().any(|name| name.contains('*')) {
                    let pattern = names.join("|");
                    bail!(
                        "name: is exact-only; use `mathmux search 'declaration {pattern}'` for wildcard discovery or name:A|B|C for an exact batch"
                    );
                }
                bail!("invalid exact-name batch; use name:A|B|C (no spaces)");
            }
            SearchExpression::ExactNames(names.into_iter().map(str::to_owned).collect())
        } else if let Some(pattern) = query.strip_prefix("type:") {
            let pattern = pattern.trim();
            ensure!(!pattern.is_empty(), "type: requires a Lean type pattern");
            validate_type_pattern(pattern)?;
            SearchExpression::Type(pattern.to_owned())
        } else if let Some(regex) = query.strip_prefix("re:") {
            SearchExpression::Regex(canonical_regex(None, regex)?)
        } else if terms.len() >= 2 && terms[1].starts_with("re:") {
            let path = terms[0];
            let regex = query[path.len()..].trim().strip_prefix("re:").unwrap();
            SearchExpression::Regex(canonical_regex(Some(path), regex)?)
        } else {
            validate_balanced_fragment(query)?;
            SearchExpression::Query(query.to_owned())
        };
        Ok(Self {
            expression,
            displayed_query: query.to_owned(),
            limit,
            all,
        })
    }
}

fn validate_type_pattern(pattern: &str) -> Result<()> {
    validate_balanced_fragment_with_hint(pattern, "type")
}

pub(super) fn validate_balanced_fragment(query: &str) -> Result<()> {
    validate_balanced_fragment_with_hint(query, "search")
}

fn validate_balanced_fragment_with_hint(fragment: &str, form: &str) -> Result<()> {
    let mut stack = Vec::new();
    let mut quoted = false;
    let mut escaped = false;
    for ch in fragment.chars() {
        if quoted {
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                quoted = false;
            }
            continue;
        }
        match ch {
            '"' => quoted = true,
            '(' | '[' | '{' => stack.push(ch),
            ')' | ']' | '}' => {
                let expected = match ch {
                    ')' => '(',
                    ']' => '[',
                    '}' => '{',
                    _ => unreachable!(),
                };
                ensure!(
                    stack.pop() == Some(expected),
                    "malformed {form} fragment: unmatched `{ch}`; try `type:{fragment}` for a type fragment or `FILE:LINE`/`FILE:START-END` for source code context"
                );
            }
            _ => {}
        }
    }
    ensure!(
        !quoted,
        "malformed {form} fragment: unterminated string literal; try `type:{fragment}` for a type fragment or `FILE:LINE`/`FILE:START-END` for source code context"
    );
    ensure!(
        stack.is_empty(),
        "malformed {form} fragment: unmatched delimiter; try `type:{fragment}` for a type fragment or `FILE:LINE`/`FILE:START-END` for source code context"
    );
    Ok(())
}

fn canonical_regex(path: Option<&str>, regex: &str) -> Result<String> {
    let regex = regex.trim();
    ensure!(
        regex.starts_with('/') && regex.ends_with('/') && regex.len() > 2,
        "re: expects /REGEX/"
    );
    Ok(match path {
        Some(path) => format!("{path} {regex}"),
        None => regex.to_owned(),
    })
}

fn declaration_name(name: &str) -> bool {
    !name.is_empty()
        && !name.starts_with('.')
        && !name.ends_with('.')
        && name.split('.').all(|part| {
            !part.is_empty()
                && part
                    .chars()
                    .all(|ch| ch.is_alphanumeric() || matches!(ch, '_' | '\''))
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_forced_query_classes_without_fallback() {
        assert_eq!(
            SearchRequest::parse("name:A.B|C.D", None, false)
                .unwrap()
                .expression,
            SearchExpression::ExactNames(vec!["A.B".into(), "C.D".into()])
        );
        assert_eq!(
            SearchRequest::parse("type:_ ≃L[ℂ] F", None, false)
                .unwrap()
                .expression,
            SearchExpression::Type("_ ≃L[ℂ] F".into())
        );
        assert_eq!(
            SearchRequest::parse("Mathlib re:/foo|bar/", None, false)
                .unwrap()
                .expression,
            SearchExpression::Regex("Mathlib /foo|bar/".into())
        );
        assert!(SearchRequest::parse("type:(Nat → Nat", None, false).is_err());
    }

    #[test]
    fn rejects_removed_legacy_forms() {
        assert!(SearchRequest::parse("q12 more", None, false).is_err());
        assert!(SearchRequest::parse("c12 repair", None, false).is_err());
        assert!(SearchRequest::parse("#check Nat", None, false).is_err());
        assert!(SearchRequest::parse("theorem name:foo", None, false).is_err());
    }

    #[test]
    fn explains_exact_name_batch_syntax() {
        let error = SearchRequest::parse("name:A B", None, false).unwrap_err();
        assert_eq!(error.to_string(), "name: accepts one name or a `|` batch");
        let error = SearchRequest::parse("name:A|", None, false).unwrap_err();
        assert_eq!(
            error.to_string(),
            "invalid exact-name batch; use name:A|B|C (no spaces)"
        );
        let error = SearchRequest::parse("name:*FinalCriterion*", None, false).unwrap_err();
        assert_eq!(
            error.to_string(),
            "name: is exact-only; use `mathmux search 'declaration *FinalCriterion*'` for wildcard discovery or name:A|B|C for an exact batch"
        );
        let error = SearchRequest::parse("name:A|name:B", None, false).unwrap_err();
        assert_eq!(
            error.to_string(),
            "name: accepts one prefix; use `name:A|B` for an exact batch"
        );
    }

    #[test]
    fn rejects_malformed_pasted_fragments_before_search() {
        let error = SearchRequest::parse("Fin (n + m)))))", None, false).unwrap_err();
        assert!(error.to_string().contains("malformed search fragment"));
        assert!(error.to_string().contains("type:Fin (n + m)))))"));
        assert!(error.to_string().contains("FILE:LINE"));

        let error = SearchRequest::parse("foo \"bar", None, false).unwrap_err();
        assert!(error.to_string().contains("unterminated string literal"));
    }
}
