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
        let directive_query = unquote(remainder);
        if let Some(directive) = parse_directive(directive_query)? {
            ensure!(context.is_some(), "Lean directives require FILE, FILE:LINE, cREF, or qREF context");
            return Ok(Self { context, subject: None, focus: None, directive: Some(directive) });
        }
        if context.is_none() {
            if remainder
                .split_whitespace()
                .skip(1)
                .map(|term| term.trim_matches(['\'', '"']))
                .any(|term| term == "by")
            {
                bail!("by requires FILE:LINE, cREF, or positioned qREF context");
            }
            if let Some(directive) = remainder
                .split_whitespace()
                .skip(1)
                .map(|term| term.trim_matches(['\'', '"']))
                .find(|term| matches!(*term, "#check" | "#synth" | "#reduce"))
            {
                bail!(
                    "{directive} requires FILE, FILE:LINE, cREF, or qREF context; use NAME signature for a declaration"
                );
            }
        }
        let mut terms = remainder.split_whitespace().collect::<Vec<_>>();
        let focus = terms
            .last()
            .filter(|term| FOCUSES.contains(&term.to_ascii_lowercase().as_str()))
            .map(|term| term.to_ascii_lowercase());
        if focus.is_some() {
            terms.pop();
        }
        if context.is_none()
            && !terms.first().is_some_and(|term| term.starts_with("type:"))
            && terms.len() > 1
        {
            let requested = terms.last().copied().unwrap_or_default();
            let name = terms[..terms.len() - 1].join(" ");
            match requested {
                "type" => bail!("declaration types use `probe {name} signature`"),
                "body" | "proof" => {
                    bail!("declaration {requested} uses `search '{name} {requested}'`")
                }
                "context" => bail!(
                    "Lean context requires an exact position; use `probe FILE:LINE goal` or `probe FILE:LINE TERM`"
                ),
                _ => bail!(
                    "unknown declaration focus `{requested}`; use signature, source, apply, fields, constructors, ext, simp, instances, coercions, or usages"
                ),
            }
        }
        let subject = (!terms.is_empty()).then(|| terms.join(" "));
        ensure!(context.is_some() || subject.is_some(), "probe requires a subject or context");
        Ok(Self { context, subject, focus, directive: None })
    }
}

fn unquote(value: &str) -> &str {
    let value = value.trim();
    for quote in ['\'', '"'] {
        if let Some(value) = value.strip_prefix(quote).and_then(|value| value.strip_suffix(quote)) {
            return value.trim();
        }
    }
    value
}

fn usage_path_matches_scope(path: &str, scope: &str) -> bool {
    let path = path.trim_start_matches("./").trim_end_matches('/');
    let scope = scope.trim_start_matches("./").trim_end_matches('/');
    path == scope || path.strip_prefix(scope).is_some_and(|rest| rest.starts_with('/'))
}

fn indexed_check_hit<'a>(run: &'a SearchRun, subject: &str) -> Option<&'a SearchHit> {
    declaration_name_query(subject).then_some(())?;
    run.hits.iter().find(|hit| {
        qualified_name_matches(&hit.name, subject)
            && hit.signature.as_deref().is_some_and(|value| !value.trim().is_empty())
    })
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
            let context = request.context.unwrap();
            if let LeanDirective::Check(subject) = &directive
                && let Some(rendered) = self.probe_indexed_check(workspace, &context, subject)?
            {
                return Ok(rendered);
            }
            return self.run_lean_probe(workspace, cwd, context, directive);
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
            (
                Some(context @ (ProbeContext::File(_) | ProbeContext::Scope(_))),
                Some(subject),
                Some("usages"),
            ) => self.probe_scoped_usages(workspace, context, subject),
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
                let rendered = self.search(workspace, cwd, &query, None, false)?;
                let effective_focus = focus.unwrap_or(if subject.starts_with("type:") {
                    "types"
                } else {
                    "signature"
                });
                let Some(reference) = rendered.split_whitespace().next().filter(|term| reference(term, 'q')) else {
                    return Ok(rendered);
                };
                let Some(run) = self.state.search_run(reference)? else {
                    return Ok(rendered);
                };
                Ok(render_static_probe_summary(&run, effective_focus))
            }
            (Some(ProbeContext::File(file)), None, Some("goal")) => {
                bail!("goal requires an exact FILE:LINE context, not {file}")
            }
            _ => bail!("probe form is incomplete"),
        }
    }

    fn probe_scoped_usages(
        &self,
        workspace: &Workspace,
        context: &ProbeContext,
        subject: &str,
    ) -> Result<String> {
        let scope = match context {
            ProbeContext::File(path) | ProbeContext::Scope(path) => path,
            _ => unreachable!("scoped usages require a path context"),
        };
        let started = Instant::now();
        let mut result = self.planned_text_search(
            workspace,
            subject,
            TextSearchPlan::ExactFirst,
            None,
            None,
            false,
        )?;
        result
            .hits
            .retain(|hit| qualified_name_matches(&hit.name, subject));
        result.hits.truncate(1);
        for hit in &mut result.hits {
            hit.source = None;
            hit.usages
                .retain(|usage| usage_path_matches_scope(&usage.path, scope));
        }
        if result.hits.is_empty() {
            result.note = Some(format!("declaration not found: {subject}"));
            result.ok = false;
        } else if result.hits[0].usages.is_empty()
            && !result.note.as_deref().is_some_and(|note| note.contains("warming"))
        {
            result.note = Some(format!("no indexed usages under {scope}"));
        }
        let ok = result.ok;
        let run = SearchRun {
            reference: self.state.next_ref('q')?,
            workspace_ref: workspace.reference.clone(),
            query: format!("{scope} {subject} usages"),
            inference: "exact".into(),
            hits: result.hits,
            note: result.note,
            duration_ms: started.elapsed().as_millis() as u64,
            created_at: now_unix_ms(),
        };
        self.state.add_search(&run)?;
        self.state.touch_workspace(&workspace.reference)?;
        let rendered = render_summary(&run);
        if ok { Ok(rendered) } else { bail!(rendered) }
    }

    fn probe_indexed_check(
        &self,
        workspace: &Workspace,
        context: &ProbeContext,
        subject: &str,
    ) -> Result<Option<String>> {
        let ProbeContext::Query(reference) = context else {
            return Ok(None);
        };
        let Some(run) = self.state.search_run(reference)? else {
            return Ok(None);
        };
        let Some(hit) = indexed_check_hit(&run, subject) else {
            return Ok(None);
        };
        let signature = hit.signature.as_deref().expect("indexed check requires a signature");
        self.store_probe_result(
            workspace,
            &format!("{reference} #check {subject}"),
            "check",
            format!("{} : {signature}", hit.name),
            (!hit.path.is_empty()).then_some(hit.path.as_str()),
            hit.line,
        )
        .map(Some)
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
        let stored_path = location.display_path.clone().unwrap_or_else(|| {
            location
                .path
                .strip_prefix(&workspace.path)
                .unwrap_or(&location.path)
                .to_string_lossy()
                .into_owned()
        });
        let (operation, input) = match subject {
            None | Some("goal") => ("goal", ""),
            Some(subject) => ("term", subject),
        };
        if operation == "goal" {
            let source = fs::read_to_string(&location.path)?;
            let requested_line = source
                .lines()
                .nth(location.line.saturating_sub(1) as usize)
                .unwrap_or_default();
            if requested_line.trim().is_empty() || is_declaration_header(requested_line) {
                bail!(
                    "goal needs an exact proof line, not a declaration header or blank line; use search {}:{} to read source",
                    stored_path,
                    location.line
                );
            }
        }
        let (ok, detail) = self.checker.probe_context(
            workspace,
            &location.path,
            location.line,
            0,
            operation,
            input,
        )?;
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

fn render_static_probe_summary(run: &SearchRun, focus: &str) -> String {
    let mut run = run.clone();
    match focus {
        "signature" | "ext" => {
            run.inference = "exact".into();
            for hit in &mut run.hits {
                hit.source = None;
            }
        }
        "source" => run.hits.truncate(1),
        _ => {}
    }
    if matches!(focus, "signature" | "source" | "ext")
        && matches!(
            run.note.as_deref(),
            Some("search indexes warming" | "source index warming")
        )
    {
        run.note = None;
    }
    render_summary(&run)
}

fn is_declaration_header(line: &str) -> bool {
    let mut line = line.trim_start();
    loop {
        let previous = line;
        for modifier in ["noncomputable ", "private ", "protected ", "unsafe "] {
            if let Some(rest) = line.strip_prefix(modifier) {
                line = rest.trim_start();
                break;
            }
        }
        if line == previous {
            break;
        }
    }
    [
        "abbrev ", "class ", "def ", "example ", "inductive ", "instance ", "lemma ",
        "structure ", "theorem ",
    ]
    .iter()
    .any(|keyword| line.starts_with(keyword))
}

fn static_probe_query(context: Option<&ProbeContext>, subject: &str, focus: Option<&str>) -> Result<String> {
    match context {
        None => {}
        Some(ProbeContext::File(_)) => {
            bail!("FILE with a declaration supports signature only; use probe NAME for API dossiers")
        }
        Some(_) => bail!("this probe requires a declaration or type subject"),
    }
    let default_focus = if subject.starts_with("type:") { "types" } else { "signature" };
    let query = match focus.unwrap_or(default_focus) {
        "signature" => format!("name:{subject}"),
        "source" => format!("{subject} source"),
        "fields" => format!("{subject} fields"),
        "constructors" => format!("{subject}.mk"),
        "coercions" => format!(
            "declaration {subject}.instCoe*|{subject}.instFunLike*|{subject}.instCoeFun*|{subject}.hasCoe*|{subject}.toFun*"
        ),
        "instances" => format!("declaration {subject}.inst*|{subject}.instance*"),
        "ext" => format!("name:{subject}.ext"),
        "simp" => format!("declaration {subject}*"),
        "apply" => format!("{subject} theorem"),
        "usages" => format!("name:{subject}"),
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
            ProbeRequest::parse("Demo.lean \"#check Nat\"").unwrap(),
            ProbeRequest {
                context: Some(ProbeContext::File("Demo.lean".into())),
                subject: None,
                focus: None,
                directive: Some(LeanDirective::Check("Nat".into())),
            }
        );
        assert_eq!(
            ProbeRequest::parse("Mathlib/ Demo.foo usages").unwrap().context,
            Some(ProbeContext::Scope("Mathlib/".into()))
        );
        assert_eq!(
            ProbeRequest::parse("Mathlib/Data/List.lean Demo.foo usages").unwrap(),
            ProbeRequest {
                context: Some(ProbeContext::File("Mathlib/Data/List.lean".into())),
                subject: Some("Demo.foo".into()),
                focus: Some("usages".into()),
                directive: None,
            }
        );
        assert!(usage_path_matches_scope(
            "Mathlib/Data/List/Basic.lean",
            "Mathlib/Data/List"
        ));
        assert!(!usage_path_matches_scope(
            "Mathlib/Data/ListExtra.lean",
            "Mathlib/Data/List"
        ));
        assert_eq!(
            static_probe_query(None, "type:_ → _", None).unwrap(),
            "type:_ → _"
        );
        assert_eq!(
            static_probe_query(None, "ContinuousMap", Some("ext")).unwrap(),
            "name:ContinuousMap.ext"
        );
        assert_eq!(
            static_probe_query(None, "ContinuousMap", Some("instances")).unwrap(),
            "declaration ContinuousMap.inst*|ContinuousMap.instance*"
        );
        assert_eq!(
            static_probe_query(None, "ContinuousMap", Some("coercions")).unwrap(),
            "declaration ContinuousMap.instCoe*|ContinuousMap.instFunLike*|ContinuousMap.instCoeFun*|ContinuousMap.hasCoe*|ContinuousMap.toFun*"
        );
        assert_eq!(
            static_probe_query(None, "Demo.apply", Some("simp")).unwrap(),
            "declaration Demo.apply*"
        );
        assert!(static_probe_query(
            Some(&ProbeContext::File("Demo.lean".into())),
            "Demo.foo",
            Some("fields")
        )
        .is_err());
        assert!(ProbeRequest::parse("#check Nat").is_err());
        assert_eq!(
            ProbeRequest::parse("Demo.foo \"#check Demo.foo\"")
                .unwrap_err()
                .to_string(),
            "#check requires FILE, FILE:LINE, cREF, or qREF context; use NAME signature for a declaration"
        );
        assert_eq!(
            ProbeRequest::parse("Demo.foo by simp")
                .unwrap_err()
                .to_string(),
            "by requires FILE:LINE, cREF, or positioned qREF context"
        );
        assert_eq!(
            ProbeRequest::parse("Demo.foo type")
                .unwrap_err()
                .to_string(),
            "declaration types use `probe Demo.foo signature`"
        );
        assert_eq!(
            ProbeRequest::parse("Demo.foo proof")
                .unwrap_err()
                .to_string(),
            "declaration proof uses `search 'Demo.foo proof'`"
        );
        assert_eq!(
            ProbeRequest::parse("Demo.foo context")
                .unwrap_err()
                .to_string(),
            "Lean context requires an exact position; use `probe FILE:LINE goal` or `probe FILE:LINE TERM`"
        );
        assert!(is_declaration_header(
            "noncomputable def parameterizedBottThickClutchingCore"
        ));
        assert!(is_declaration_header("private theorem hidden"));
        assert!(!is_declaration_header("  intro i"));
    }

    #[test]
    fn probe_focus_keeps_initial_dossiers_bounded() {
        let hit = |name: &str, source: &str| SearchHit {
            name: name.into(),
            kind: "theorem".into(),
            signature: Some("(n : Nat) : n = n".into()),
            module: "Demo".into(),
            path: "Demo.lean".into(),
            line: 10,
            doc: None,
            source: Some(source.into()),
            usages: Vec::new(),
            applicable: false,
            required_import: None,
        };
        let run = SearchRun {
            reference: "q1".into(),
            workspace_ref: "w1".into(),
            query: "Demo.first".into(),
            inference: "exact".into(),
            hits: vec![
                hit("Demo.first", "theorem first (n : Nat) : n = n := by\n  rfl"),
                hit("Demo.second", "theorem second (n : Nat) : n = n := by\n  rfl"),
            ],
            note: Some("search indexes warming".into()),
            duration_ms: 1,
            created_at: 0,
        };

        assert_eq!(
            indexed_check_hit(&run, "Demo.first").map(|hit| hit.name.as_str()),
            Some("Demo.first")
        );
        assert!(indexed_check_hit(&run, "Demo.first 1").is_none());

        let signature = render_static_probe_summary(&run, "signature");
        assert!(signature.contains("Demo.first : (n : Nat) : n = n"));
        assert!(!signature.contains(":= by"));
        assert!(!signature.contains("warming"));

        let ext = render_static_probe_summary(&run, "ext");
        assert!(!ext.contains(":= by"));

        let source = render_static_probe_summary(&run, "source");
        assert!(source.contains("theorem first"));
        assert!(!source.contains("Demo.second"));
    }
}
