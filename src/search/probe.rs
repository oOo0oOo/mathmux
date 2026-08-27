use std::path::Path;

use anyhow::{Result, bail, ensure};

use super::*;

const FOCUSES: &[&str] = &[
    "signature", "apply", "fields", "constructors", "ext", "simp", "instances",
    "coercions", "usages", "source", "goal", "types", "defeq", "rewrite", "profile",
];

#[derive(Debug, Clone, PartialEq, Eq)]
enum ProbeContext {
    File(String),
    Scope(String),
    Position(String),
    Check(String),
    Query(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum LeanDirective {
    Check(String),
    Synth(String),
    Reduce(String),
    Tactic(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ProbeRequest {
    context: Option<ProbeContext>,
    subject: Option<String>,
    focus: Option<String>,
    directive: Option<LeanDirective>,
}

impl ProbeRequest {
    fn parse(query: &str) -> Result<Self> {
        let query = query.trim();
        ensure!(!query.is_empty(), "probe query is empty");
        let mut parts = query.split_whitespace();
        let first = parts.next().unwrap();
        let context = parse_context(first);
        let remainder = if context.is_some() {
            query[first.len()..].trim()
        } else {
            query
        };
        if let Some(directive) = parse_directive(remainder)? {
            ensure!(context.is_some(), "Lean directives require FILE, FILE:LINE, cREF, or qREF context");
            return Ok(Self { context, subject: None, focus: None, directive: Some(directive) });
        }
        let mut terms = remainder.split_whitespace().collect::<Vec<_>>();
        let focus = terms
            .last()
            .filter(|term| FOCUSES.contains(&term.to_ascii_lowercase().as_str()))
            .map(|term| term.to_ascii_lowercase());
        if focus.is_some() {
            terms.pop();
        }
        let subject = (!terms.is_empty()).then(|| terms.join(" "));
        ensure!(context.is_some() || subject.is_some(), "probe requires a subject or context");
        Ok(Self { context, subject, focus, directive: None })
    }
}

fn parse_context(value: &str) -> Option<ProbeContext> {
    if reference(value, 'c') {
        return Some(ProbeContext::Check(value.into()));
    }
    if reference(value, 'q') {
        return Some(ProbeContext::Query(value.into()));
    }
    if value.rsplit_once(':').is_some_and(|(_, line)| line.parse::<u64>().is_ok()) {
        return Some(ProbeContext::Position(value.into()));
    }
    if value.ends_with(".lean") {
        return Some(ProbeContext::File(value.into()));
    }
    value.contains('/').then(|| ProbeContext::Scope(value.into()))
}

fn parse_directive(value: &str) -> Result<Option<LeanDirective>> {
    for (prefix, make) in [
        ("#check", LeanDirective::Check as fn(String) -> LeanDirective),
        ("#synth", LeanDirective::Synth),
        ("#reduce", LeanDirective::Reduce),
        ("by", LeanDirective::Tactic),
    ] {
        if value == prefix {
            bail!("{prefix} requires an argument");
        }
        if let Some(body) = value.strip_prefix(prefix).and_then(|rest| rest.strip_prefix(char::is_whitespace)) {
            let body = body.trim();
            ensure!(!body.is_empty(), "{prefix} requires an argument");
            return Ok(Some(make(body.to_owned())));
        }
    }
    Ok(None)
}

fn reference(term: &str, kind: char) -> bool {
    term.strip_prefix(kind)
        .is_some_and(|digits| !digits.is_empty() && digits.chars().all(|ch| ch.is_ascii_digit()))
}

impl Searcher {
    pub fn probe(&self, workspace: &Workspace, cwd: &Path, query: &str) -> Result<String> {
        let request = ProbeRequest::parse(query)?;
        if let Some(directive) = request.directive {
            return self.run_lean_probe(workspace, cwd, request.context.unwrap(), directive);
        }
        match (&request.context, request.subject.as_deref(), request.focus.as_deref()) {
            (Some(ProbeContext::Check(reference)), None, focus) => {
                self.probe_check_reference(workspace, reference, focus)
            }
            (Some(ProbeContext::Check(_)), Some(_), _) => {
                bail!("cREF accepts only types, defeq, rewrite, or profile focus")
            }
            (Some(ProbeContext::Position(location)), None, None | Some("goal")) => {
                self.run_position_probe(workspace, cwd, location, None)
            }
            (Some(ProbeContext::Position(location)), Some(subject), None | Some("signature")) => {
                self.run_position_probe(workspace, cwd, location, Some(subject))
            }
            (Some(ProbeContext::Position(_)), _, Some(focus)) => {
                bail!("focus `{focus}` is not valid at FILE:LINE; use goal, TERM, or a Lean directive")
            }
            (Some(ProbeContext::Query(reference)), subject, focus) => {
                self.probe_query_reference(workspace, cwd, reference, subject, focus)
            }
            (Some(ProbeContext::File(file)), Some(subject), None | Some("signature")) => {
                self.run_lean_probe(
                    workspace,
                    cwd,
                    ProbeContext::File(file.clone()),
                    LeanDirective::Check(subject.to_owned()),
                )
            }
            (context, Some(subject), focus) => {
                let query = static_probe_query(context.as_ref(), subject, focus)?;
                self.search(workspace, cwd, &query, None, false)
            }
            (Some(ProbeContext::File(file)), None, Some("goal")) => {
                bail!("goal requires an exact FILE:LINE context, not {file}")
            }
            _ => bail!("probe form is incomplete"),
        }
    }

    fn probe_check_reference(
        &self,
        workspace: &Workspace,
        reference: &str,
        focus: Option<&str>,
    ) -> Result<String> {
        let run = self
            .state
            .check_run(reference)?
            .with_context(|| format!("unknown check reference {reference}"))?;
        let diagnostic = run.diagnostics.first().or_else(|| run.warnings.first());
        let text = diagnostic.map(|diagnostic| diagnostic.text.as_str()).unwrap_or("check has no diagnostic");
        let (path, line) = diagnostic_position(text, run.failed.as_deref());
        let detail = match focus {
            Some("types") => diagnostic_type_detail(text)
                .with_context(|| format!("{reference} has no type or instance failure"))?,
            Some("defeq") => diagnostic_defeq_detail(text)
                .with_context(|| format!("{reference} has no definitional-equality failure"))?,
            Some("rewrite") => diagnostic_rewrite_detail(
                text,
                diagnostic.and_then(|diagnostic| diagnostic.context.as_deref()),
            )
            .with_context(|| format!("{reference} has no rewrite failure"))?,
            Some("profile") => {
                ensure!(run.profile.is_some(), "{reference} has no stored profile");
                self.state.show(reference, true)?
            }
            None => {
                let diagnostic = diagnostic.with_context(|| format!("{reference} has no failure to probe"))?;
                diagnostic_context(text, diagnostic.context.as_deref())
            }
            Some(other) => bail!("focus `{other}` is not meaningful for a stored check"),
        };
        self.store_probe_result(
            workspace,
            reference,
            "diagnostic-probe",
            detail,
            path.as_deref(),
            line,
        )
    }

    fn probe_query_reference(
        &self,
        workspace: &Workspace,
        cwd: &Path,
        reference: &str,
        subject: Option<&str>,
        focus: Option<&str>,
    ) -> Result<String> {
        let run = self
            .state
            .search_run(reference)?
            .with_context(|| format!("unknown query reference {reference}"))?;
        let hit = run
            .hits
            .first()
            .with_context(|| format!("{reference} has no probe subject"))?;
        if run.inference == "probe" && subject.is_none() && focus.is_none() {
            let detail = self.state.show(reference, true)?;
            return self.store_probe_result(
                workspace,
                reference,
                "stored-probe",
                detail,
                (!hit.path.is_empty()).then_some(hit.path.as_str()),
                hit.line,
            );
        }
        let positioned = run.inference == "probe"
            || matches!(
                hit.kind.as_str(),
                "location" | "location-expanded"
            );
        if positioned
            && hit.line > 0
            && !hit.path.is_empty()
            && subject.is_none()
            && matches!(focus, None | Some("goal"))
        {
            return self.run_position_probe(
                workspace,
                cwd,
                &format!("{}:{}", hit.path, hit.line),
                None,
            );
        }
        let subject = subject.unwrap_or(&hit.name);
        let query = static_probe_query(None, subject, focus)?;
        self.search(workspace, cwd, &query, None, false)
    }

    fn store_probe_result(
        &self,
        workspace: &Workspace,
        query: &str,
        kind: &str,
        detail: String,
        path: Option<&str>,
        line: u64,
    ) -> Result<String> {
        let reference = self.state.next_ref('q')?;
        let run = SearchRun {
            reference: reference.clone(),
            workspace_ref: workspace.reference.clone(),
            query: query.to_owned(),
            inference: "probe".into(),
            hits: vec![SearchHit {
                name: kind.into(),
                kind: kind.into(),
                signature: None,
                module: String::new(),
                path: path.unwrap_or_default().to_owned(),
                line,
                doc: None,
                source: Some(detail),
                usages: Vec::new(),
                applicable: false,
                required_import: None,
            }],
            note: None,
            duration_ms: 0,
            created_at: now_unix_ms(),
        };
        self.state.add_search(&run)?;
        Ok(render_summary(&run))
    }

    fn run_position_probe(
        &self,
        workspace: &Workspace,
        cwd: &Path,
        location: &str,
        subject: Option<&str>,
    ) -> Result<String> {
        let location = parse_source_location(
            &workspace.path,
            cwd,
            Some(&self.repo.root),
            location,
        )?
        .with_context(|| format!("invalid probe location {location}"))?;
        let (operation, input) = match subject {
            None | Some("goal") => ("goal", ""),
            Some(subject) => ("term", subject),
        };
        let (ok, detail) = self.checker.probe_context(
            workspace,
            &location.path,
            location.line,
            0,
            operation,
            input,
        )?;
        let stored_path = location
            .display_path
            .clone()
            .unwrap_or_else(|| {
                location
                    .path
                    .strip_prefix(&workspace.path)
                    .unwrap_or(&location.path)
                    .to_string_lossy()
                    .into_owned()
            });
        let rendered = self.store_probe_result(
            workspace,
            &format!("{stored_path}:{} {operation}", location.line),
            operation,
            detail,
            Some(&stored_path),
            location.line,
        )?;
        if ok { Ok(rendered) } else { bail!(rendered) }
    }

    fn run_lean_probe(
        &self,
        workspace: &Workspace,
        cwd: &Path,
        context: ProbeContext,
        directive: LeanDirective,
    ) -> Result<String> {
        let (path, line) = self.resolve_probe_context(workspace, cwd, context)?;
        let (operation, input) = match directive {
            LeanDirective::Check(input) => ("term", input),
            LeanDirective::Synth(input) => ("synth", input),
            LeanDirective::Reduce(input) => ("reduce", input),
            LeanDirective::Tactic(input) => {
                ensure!(line > 0, "by TACTIC requires FILE:LINE, cREF, or positioned qREF context");
                ("tactic", input)
            }
        };
        let (ok, detail) = self.checker.probe_context(
            workspace,
            &path,
            line,
            0,
            operation,
            &input,
        )?;
        let query = format!("{} {} {}", path.display(), operation, input);
        let stored_path = path
            .strip_prefix(&workspace.path)
            .unwrap_or(&path)
            .to_string_lossy()
            .into_owned();
        let rendered = self.store_probe_result(
            workspace,
            &query,
            operation,
            detail,
            Some(&stored_path),
            line,
        )?;
        if ok { Ok(rendered) } else { bail!(rendered) }
    }

    fn resolve_probe_context(
        &self,
        workspace: &Workspace,
        cwd: &Path,
        context: ProbeContext,
    ) -> Result<(PathBuf, u64)> {
        match context {
            ProbeContext::Position(location) => {
                let location = parse_source_location(
                    &workspace.path,
                    cwd,
                    Some(&self.repo.root),
                    &location,
                )?
                .with_context(|| format!("invalid probe location {location}"))?;
                Ok((location.path, location.line))
            }
            ProbeContext::File(file) => {
                let location = parse_source_location(
                    &workspace.path,
                    cwd,
                    Some(&self.repo.root),
                    &format!("{file}:tail"),
                )?
                .with_context(|| format!("invalid probe file {file}"))?;
                Ok((location.path, 0))
            }
            ProbeContext::Scope(path) => bail!("{path} is a search scope, not a Lean elaboration context"),
            ProbeContext::Check(reference) => {
                let run = self
                    .state
                    .check_run(&reference)?
                    .with_context(|| format!("unknown check reference {reference}"))?;
                let diagnostic = run.diagnostics.first().or_else(|| run.warnings.first());
                let (path, line) = diagnostic_position(
                    diagnostic.map(|value| value.text.as_str()).unwrap_or_default(),
                    run.failed.as_deref(),
                );
                let path = path.with_context(|| format!("{reference} has no source context"))?;
                let requested = if Path::new(&path).is_absolute() {
                    path
                } else {
                    workspace.path.join(path).to_string_lossy().into_owned()
                };
                let location = parse_source_location(
                    &workspace.path,
                    cwd,
                    Some(&self.repo.root),
                    &format!("{requested}:{line}"),
                )?
                .with_context(|| format!("stored context for {reference} is unavailable"))?;
                Ok((location.path, location.line))
            }
            ProbeContext::Query(reference) => {
                let run = self
                    .state
                    .search_run(&reference)?
                    .with_context(|| format!("unknown query reference {reference}"))?;
                let hit = run.hits.first().with_context(|| format!("{reference} has no source context"))?;
                ensure!(!hit.path.is_empty(), "{reference} has no source path");
                let positioned = run.inference == "probe" && hit.line > 0 || matches!(
                    hit.kind.as_str(),
                    "location" | "location-expanded"
                );
                let source_context = if positioned {
                    format!("{}:{}", hit.path, hit.line)
                } else {
                    format!("{}:tail", hit.path)
                };
                let location = parse_source_location(
                    &workspace.path,
                    cwd,
                    Some(&self.repo.root),
                    &source_context,
                )?
                .with_context(|| format!("stored context for {reference} is unavailable"))?;
                Ok((location.path, if positioned { location.line } else { 0 }))
            }
        }
    }
}

fn static_probe_query(context: Option<&ProbeContext>, subject: &str, focus: Option<&str>) -> Result<String> {
    let scoped = match context {
        Some(ProbeContext::Scope(path)) if focus == Some("usages") => Some(path.as_str()),
        None => None,
        Some(ProbeContext::File(_)) => {
            bail!("FILE with a declaration supports signature only; use probe NAME for API dossiers")
        }
        Some(_) => bail!("this probe requires a declaration or type subject"),
    };
    let default_focus = if subject.starts_with("type:") { "types" } else { "signature" };
    let query = match focus.unwrap_or(default_focus) {
        "signature" => format!("name:{subject}"),
        "source" => format!("{subject} source"),
        "fields" => format!("{subject} fields"),
        "constructors" => format!("{subject}.mk"),
        "coercions" => format!("{subject} coe"),
        "instances" => format!("{subject} instance"),
        "ext" => format!("{subject} ext"),
        "simp" => format!("{subject} simp"),
        "apply" => format!("{subject} theorem"),
        "usages" => match scoped {
            Some(path) => format!("{path} {subject}"),
            None => format!("name:{subject}"),
        },
        "types" if subject.starts_with("type:") => subject.to_owned(),
        other => bail!("focus `{other}` requires source or failure context"),
    };
    Ok(query)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn probe_grammar_keeps_context_explicit() {
        assert_eq!(
            ProbeRequest::parse("Demo.lean:42 by simp").unwrap(),
            ProbeRequest {
                context: Some(ProbeContext::Position("Demo.lean:42".into())),
                subject: None,
                focus: None,
                directive: Some(LeanDirective::Tactic("simp".into())),
            }
        );
        assert_eq!(
            ProbeRequest::parse("Mathlib/ Demo.foo usages").unwrap().context,
            Some(ProbeContext::Scope("Mathlib/".into()))
        );
        assert_eq!(
            static_probe_query(None, "type:_ → _", None).unwrap(),
            "type:_ → _"
        );
        assert!(static_probe_query(
            Some(&ProbeContext::File("Demo.lean".into())),
            "Demo.foo",
            Some("fields")
        )
        .is_err());
        assert!(ProbeRequest::parse("#check Nat").is_err());
    }
}
