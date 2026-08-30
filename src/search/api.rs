use crate::reference::{Reference, ReferenceKind};
use anyhow::{Result, ensure};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum SearchExpression {
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

        ensure!(
            !query.starts_with("name:")
                && !query
                    .split_whitespace()
                    .any(|term| term.starts_with("name:")),
            "name: search was removed; use a bare exact declaration name or `declaration PATTERN`"
        );
        let terms = query.split_whitespace().collect::<Vec<_>>();
        let expression = if let Some(pattern) = query.strip_prefix("type:") {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_forced_query_classes_without_fallback() {
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
        assert!(SearchRequest::parse("name:A.B", None, false).is_err());
    }

    #[test]
    fn explains_removed_exact_name_syntax() {
        let error = SearchRequest::parse("name:A", None, false).unwrap_err();
        assert_eq!(
            error.to_string(),
            "name: search was removed; use a bare exact declaration name or `declaration PATTERN`"
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
