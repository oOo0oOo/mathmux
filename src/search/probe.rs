use std::path::Path;

use anyhow::{Result, bail, ensure};

use super::*;
use crate::reference::{Reference, ReferenceKind};

const FOCUSES: &[&str] = &[
    "signature",
    "apply",
    "fields",
    "constructors",
    "ext",
    "simp",
    "instances",
    "coercions",
    "usages",
    "source",
    "goal",
    "types",
    "defeq",
    "rewrite",
    "profile",
    "warnings",
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
        if query == "mathmux probe" || query.starts_with("mathmux probe ") {
            bail!("probe receives QUERY only; omit the leading `mathmux probe`")
        }
        let mut parts = query.split_whitespace();
        let first = parts.next().unwrap();
        let context = parse_context(first);
        let remainder = if context.is_some() {
            query[first.len()..].trim()
        } else {
            query
        };
        if matches!(&context, Some(ProbeContext::Query(_)))
            && matches!(remainder.split_whitespace().next(), Some("show" | "--all"))
        {
            bail!("expand stored detail with `show {first} --all`, outside probe")
        }
        let directive_query = unquote(remainder);
        if let Some(directive) = parse_directive(directive_query)? {
            ensure!(
                context.is_some(),
                "Lean directives require FILE, FILE:LINE, cREF, or qREF context"
            );
            return Ok(Self {
                context,
                subject: None,
                focus: None,
                directive: Some(directive),
            });
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
        ensure!(
            context.is_some() || subject.is_some(),
            "probe requires a subject or context"
        );
        Ok(Self {
            context,
            subject,
            focus,
            directive: None,
        })
    }
}

fn unquote(value: &str) -> &str {
    let value = value.trim();
    for quote in ['\'', '"'] {
        if let Some(value) = value
            .strip_prefix(quote)
            .and_then(|value| value.strip_suffix(quote))
        {
            return value.trim();
        }
    }
    value
}

fn usage_path_matches_scope(path: &str, scope: &str) -> bool {
    let path = path.trim_start_matches("./").trim_end_matches('/');
    let scope = scope.trim_start_matches("./").trim_end_matches('/');
    path == scope
        || path
            .strip_prefix(scope)
            .is_some_and(|rest| rest.starts_with('/'))
}

fn indexed_check_hit<'a>(run: &'a SearchRun, subject: &str) -> Option<&'a SearchHit> {
    declaration_name_query(subject).then_some(())?;
    run.hits.iter().find(|hit| {
        qualified_name_matches(&hit.name, subject)
            && hit
                .signature
                .as_deref()
                .is_some_and(|value| !value.trim().is_empty())
    })
}

fn parse_context(value: &str) -> Option<ProbeContext> {
    if Reference::is_kind(value, ReferenceKind::Check) {
        return Some(ProbeContext::Check(value.into()));
    }
    if Reference::is_kind(value, ReferenceKind::Query) {
        return Some(ProbeContext::Query(value.into()));
    }
    if value
        .rsplit_once(':')
        .is_some_and(|(_, line)| line.parse::<u64>().is_ok())
    {
        return Some(ProbeContext::Position(value.into()));
    }
    if value.ends_with(".lean") {
        return Some(ProbeContext::File(value.into()));
    }
    value
        .contains('/')
        .then(|| ProbeContext::Scope(value.into()))
}

fn parse_directive(value: &str) -> Result<Option<LeanDirective>> {
    for (prefix, make) in [
        (
            "#check",
            LeanDirective::Check as fn(String) -> LeanDirective,
        ),
        ("#synth", LeanDirective::Synth),
        ("#reduce", LeanDirective::Reduce),
        ("by", LeanDirective::Tactic),
    ] {
        if value == prefix {
            bail!("{prefix} requires an argument");
        }
        if let Some(body) = value
            .strip_prefix(prefix)
            .and_then(|rest| rest.strip_prefix(char::is_whitespace))
        {
            let body = body.trim();
            ensure!(!body.is_empty(), "{prefix} requires an argument");
            return Ok(Some(make(body.to_owned())));
        }
    }
    Ok(None)
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
        match (
            &request.context,
            request.subject.as_deref(),
            request.focus.as_deref(),
        ) {
            (Some(ProbeContext::Check(reference)), None, focus) => {
                self.probe_check_reference(workspace, reference, focus)
            }
            (Some(ProbeContext::Check(_)), Some(_), _) => {
                bail!("cREF accepts only types, defeq, rewrite, or profile focus")
            }
            (Some(ProbeContext::Position(location)), None, None | Some("goal")) => {
                self.run_position_probe(workspace, cwd, location, None)
            }
            (Some(ProbeContext::File(file)), None, Some("warnings")) => {
                self.probe_file_warnings(workspace, cwd, file)
            }
            (Some(ProbeContext::Position(location)), Some(subject), None | Some("signature")) => {
                self.run_position_probe(workspace, cwd, location, Some(subject))
            }
            (Some(ProbeContext::Position(_)), _, Some(focus)) => {
                bail!(
                    "focus `{focus}` is not valid at FILE:LINE; use goal, TERM, or a Lean directive"
                )
            }
            (Some(ProbeContext::Query(reference)), subject, focus) => {
                self.probe_query_reference(workspace, cwd, reference, subject, focus)
            }
            (
                Some(context @ (ProbeContext::File(_) | ProbeContext::Scope(_))),
                Some(subject),
                Some("usages"),
            ) => self.probe_scoped_usages(workspace, context, subject),
            (Some(ProbeContext::File(file)), Some(subject), None | Some("signature")) => self
                .run_lean_probe(
                    workspace,
                    cwd,
                    ProbeContext::File(file.clone()),
                    LeanDirective::Check(subject.to_owned()),
                ),
            (None, Some(subject), Some("constructors")) => {
                self.run_constructors_probe(workspace, cwd, subject)
            }
            (context, Some(subject), focus) => {
                let query = static_probe_query(context.as_ref(), subject, focus)?;
                let effective_focus = focus.unwrap_or(if subject.starts_with("type:") {
                    "types"
                } else {
                    "signature"
                });
                self.run_static_probe_query(workspace, cwd, &query, effective_focus)
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
            && !result
                .note
                .as_deref()
                .is_some_and(|note| note.contains("warming"))
        {
            result.note = Some(format!("no indexed usages under {scope}"));
        }
        let ok = result.ok;
        let run = SearchRun {
            reference: self.state.next_reference(ReferenceKind::Query)?,
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
        let signature = hit
            .signature
            .as_deref()
            .expect("indexed check requires a signature");
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

    fn probe_file_warnings(&self, workspace: &Workspace, cwd: &Path, file: &str) -> Result<String> {
        let started = Instant::now();
        let (path, _) =
            self.resolve_probe_context(workspace, cwd, ProbeContext::File(file.to_owned()))?;
        let target = path
            .strip_prefix(&workspace.path)
            .with_context(|| format!("{} is outside the active workspace", path.display()))?;
        let target_name = target.to_string_lossy().into_owned();
        let run = match self
            .checker
            .current_check_run_for_target(workspace, target)?
        {
            Some(run) => run,
            None => {
                if let Some(stale) = self
                    .checker
                    .latest_successful_check_run_for_target(workspace, target)?
                {
                    bail!(
                        "latest successful check {} is stale because {target_name} or its dependencies changed; run `mathmux check {target_name}` again",
                        stale.reference
                    );
                }
                bail!(
                    "{target_name} has no successful check; run `mathmux check {target_name}` first"
                );
            }
        };
        let source =
            fs::read_to_string(&path).with_context(|| format!("cannot read {}", path.display()))?;
        let source_hash = hash_bytes(source.as_bytes());
        let mut residual = Vec::new();
        let mut mechanical = 0usize;
        for diagnostic in run.linters.iter().chain(&run.warnings) {
            let (reported_path, line, column) = warning_location(&diagnostic.text);
            if reported_path
                .as_deref()
                .is_some_and(|reported| !diagnostic_path_matches(reported, &target_name))
            {
                continue;
            }
            let classification = classify_warning(&diagnostic.text);
            if classification.mechanical {
                mechanical += 1;
                continue;
            }
            residual.push((
                classification,
                diagnostic.clone(),
                line.max(1),
                column.max(1),
            ));
        }
        residual.sort_by_key(|(classification, _, line, column)| {
            (risk_rank(classification.risk), *line, *column)
        });

        let mut index_hits = Vec::with_capacity(residual.len());
        for (classification, diagnostic, line, column) in residual {
            let reference = self.state.next_reference(ReferenceKind::Query)?;
            let declaration = enclosing_declaration(&source, line);
            let subject = declaration
                .as_ref()
                .map(|value| value.name.clone())
                .filter(|name| !name.is_empty());
            let detail = warning_dossier(
                &run.reference,
                (&target_name, line, column),
                &classification,
                &diagnostic,
                declaration.as_ref(),
                &source,
            );
            let created_at = now_unix_ms();
            let warning_run = SearchRun {
                reference: reference.clone(),
                workspace_ref: workspace.reference.clone(),
                query: format!("{} warning {}:{}", run.reference, target_name, line),
                inference: "probe".into(),
                hits: vec![SearchHit {
                    name: format!("{} warning", classification.category),
                    kind: "warning-dossier".into(),
                    signature: None,
                    module: String::new(),
                    path: target_name.clone(),
                    line,
                    doc: None,
                    source: Some(detail),
                    usages: Vec::new(),
                    applicable: false,
                    required_import: None,
                }],
                note: None,
                duration_ms: 0,
                created_at,
            };
            self.state.add_search(&warning_run)?;
            self.state.add_warning_probe(&WarningProbe {
                reference: reference.clone(),
                workspace_ref: workspace.reference.clone(),
                check_ref: run.reference.clone(),
                path: target_name.clone(),
                line,
                column,
                source_hash: source_hash.clone(),
                category: classification.category.into(),
                risk: classification.risk.into(),
                subject,
                diagnostic: diagnostic.clone(),
                created_at,
            })?;
            index_hits.push(SearchHit {
                name: format!(
                    "{reference} [{}] {} — {}",
                    classification.risk,
                    classification.category,
                    warning_summary(&diagnostic.text)
                ),
                kind: "warning-reference".into(),
                signature: None,
                module: String::new(),
                path: target_name.clone(),
                line,
                doc: None,
                source: None,
                usages: Vec::new(),
                applicable: false,
                required_import: None,
            });
        }
        let reference = self.state.next_reference(ReferenceKind::Query)?;
        let residual_count = index_hits.len();
        let note = match (residual_count, mechanical) {
            (0, 0) => Some(format!("no warnings in current check {}", run.reference)),
            (0, count) => Some(format!(
                "no residual warnings; {count} mechanical warning(s) belong to Lean automation"
            )),
            (_, 0) => Some(format!(
                "{residual_count} residual warning(s) from {}; probe a listed qREF for its dossier",
                run.reference
            )),
            (_, count) => Some(format!(
                "{residual_count} residual warning(s) from {}; {count} mechanical warning(s) omitted for Lean automation; probe a listed qREF",
                run.reference
            )),
        };
        let index = SearchRun {
            reference,
            workspace_ref: workspace.reference.clone(),
            query: format!("{target_name} warnings"),
            inference: "warning-index".into(),
            hits: index_hits,
            note,
            duration_ms: started.elapsed().as_millis() as u64,
            created_at: now_unix_ms(),
        };
        self.state.add_search(&index)?;
        self.state.touch_workspace(&workspace.reference)?;
        Ok(render_summary(&index))
    }

    fn probe_warning_reference(
        &self,
        workspace: &Workspace,
        warning: &WarningProbe,
    ) -> Result<String> {
        ensure!(
            warning.workspace_ref == workspace.reference,
            "{} belongs to {}; probe it from that workspace",
            warning.reference,
            warning.workspace_ref
        );
        let path = workspace.path.join(&warning.path);
        let source =
            fs::read_to_string(&path).with_context(|| format!("cannot read {}", path.display()))?;
        ensure!(
            hash_bytes(source.as_bytes()) == warning.source_hash,
            "{} is stale because {} changed; run check, then `mathmux probe {} warnings` again",
            warning.reference,
            warning.path,
            warning.path
        );
        let run = self
            .state
            .search_run(&warning.reference)?
            .with_context(|| format!("unknown warning reference {}", warning.reference))?;
        let mut detail = run
            .hits
            .first()
            .and_then(|hit| hit.source.clone())
            .with_context(|| format!("{} has no stored warning dossier", warning.reference))?;
        if let Some(subject) = warning.subject.as_deref() {
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
            let usages = result
                .hits
                .first()
                .map(|hit| hit.usages.as_slice())
                .unwrap_or_default();
            detail.push_str(&format!("\nAPI/dependency evidence for {subject}:"));
            if usages.is_empty() {
                detail.push_str(" no indexed downstream usages found");
            } else {
                for usage in usages.iter().take(SEARCH_USAGE_LIMIT) {
                    detail.push_str(&format!("\n  {}:{}", usage.path, usage.line));
                    if let Some(context) = &usage.context {
                        detail.push_str(&format!(" in {context}"));
                    }
                }
                if usages.len() > SEARCH_USAGE_LIMIT {
                    detail.push_str(&format!(
                        "\n  +{} indexed usages omitted",
                        usages.len() - SEARCH_USAGE_LIMIT
                    ));
                }
            }
        }
        detail.push_str(&format!(
            "\nVerification: edit a coherent packet in {}, then run `mathmux check {}`.",
            warning.path, warning.path
        ));
        self.store_probe_result(
            workspace,
            &warning.reference,
            "warning-dossier",
            detail,
            Some(&warning.path),
            warning.line,
        )
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
        let text = diagnostic
            .map(|diagnostic| diagnostic.text.as_str())
            .unwrap_or("check has no diagnostic");
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
                let diagnostic =
                    diagnostic.with_context(|| format!("{reference} has no failure to probe"))?;
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
        if let Some(warning) = self.state.warning_probe(reference)? {
            ensure!(
                subject.is_none() && focus.is_none(),
                "warning qREFs are complete dossiers and accept no further focus"
            );
            return self.probe_warning_reference(workspace, &warning);
        }
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
            || matches!(hit.kind.as_str(), "location" | "location-expanded");
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
        if run.inference != "probe"
            && subject.is_none()
            && matches!(focus, Some("types" | "defeq" | "rewrite" | "profile"))
        {
            let focus = focus.unwrap();
            bail!(
                "focus `{focus}` is not valid for a declaration qREF; use a declaration focus such as signature, source, or usages, or probe a cREF failure"
            )
        }
        if run.inference != "probe"
            && subject.is_none()
            && matches!(focus, None | Some("signature" | "source" | "usages"))
        {
            return self.store_query_hit_refinement(
                workspace,
                reference,
                hit,
                focus.unwrap_or("signature"),
            );
        }
        let selected_name = hit.name.strip_prefix("_root_.").unwrap_or(&hit.name);
        let subject = subject.unwrap_or(selected_name);
        if focus == Some("constructors") {
            return self.run_constructors_probe(workspace, cwd, subject);
        }
        let query = static_probe_query(None, subject, focus)?;
        self.run_static_probe_query(workspace, cwd, &query, focus.unwrap_or("signature"))
    }

    fn run_static_probe_query(
        &self,
        workspace: &Workspace,
        cwd: &Path,
        query: &str,
        focus: &str,
    ) -> Result<String> {
        let rendered = self.search(workspace, cwd, query, None, false)?;
        let Some(reference) = rendered
            .split_whitespace()
            .next()
            .filter(|term| Reference::is_kind(term, ReferenceKind::Query))
        else {
            return Ok(rendered);
        };
        let Some(run) = self.state.search_run(reference)? else {
            return Ok(rendered);
        };
        Ok(render_static_probe_summary(&run, focus))
    }

    fn run_constructors_probe(
        &self,
        workspace: &Workspace,
        cwd: &Path,
        subject: &str,
    ) -> Result<String> {
        let source_search = || -> Result<(String, Option<SearchRun>)> {
            let rendered = self.search(workspace, cwd, &format!("name:{subject}"), None, false)?;
            let run = rendered
                .split_whitespace()
                .next()
                .filter(|term| Reference::is_kind(term, ReferenceKind::Query))
                .map(|reference| self.state.search_run(reference))
                .transpose()?
                .flatten();
            Ok((rendered, run))
        };
        let (mut rendered, mut run) = source_search()?;
        if indexes_warming(&rendered) {
            (rendered, run) = source_search()?;
        }
        ensure!(
            !indexes_warming(&rendered),
            "constructor index warming; retry the probe"
        );
        let Some(run) = run else {
            return Ok(rendered);
        };
        let Some(hit) = run
            .hits
            .iter()
            .find(|hit| qualified_name_matches(&hit.name, subject))
        else {
            return Ok(rendered);
        };
        let name = hit.name.strip_prefix("_root_.").unwrap_or(&hit.name);
        let query = if matches!(hit.kind.as_str(), "class" | "structure") {
            format!("name:{name}.mk")
        } else if hit.kind == "inductive" {
            let constructors = inductive_constructors(name, hit.source.as_deref().unwrap_or(""));
            ensure!(
                !constructors.is_empty(),
                "no indexed constructors found for {name}"
            );
            let run = SearchRun {
                reference: self.state.next_reference(ReferenceKind::Query)?,
                workspace_ref: workspace.reference.clone(),
                query: format!("{name} constructors"),
                inference: "exact-batch".into(),
                hits: constructors
                    .into_iter()
                    .map(|constructor| SearchHit {
                        name: constructor.name,
                        kind: "constructor".into(),
                        signature: nonempty(constructor.signature),
                        module: hit.module.clone(),
                        path: hit.path.clone(),
                        line: hit.line + constructor.line_offset,
                        doc: None,
                        source: None,
                        usages: Vec::new(),
                        applicable: false,
                        required_import: hit.required_import.clone(),
                    })
                    .collect(),
                note: None,
                duration_ms: 0,
                created_at: now_unix_ms(),
            };
            self.state.add_search(&run)?;
            self.state.touch_workspace(&workspace.reference)?;
            return Ok(render_static_probe_summary(&run, "constructors"));
        } else {
            bail!("constructors requires a structure, class, or inductive declaration")
        };
        self.run_static_probe_query(workspace, cwd, &query, "constructors")
    }

    fn store_query_hit_refinement(
        &self,
        workspace: &Workspace,
        reference: &str,
        hit: &SearchHit,
        focus: &str,
    ) -> Result<String> {
        let run = SearchRun {
            reference: self.state.next_reference(ReferenceKind::Query)?,
            workspace_ref: workspace.reference.clone(),
            query: format!("{reference} {focus}"),
            inference: "probe-refinement".into(),
            hits: vec![hit.clone()],
            note: None,
            duration_ms: 0,
            created_at: now_unix_ms(),
        };
        self.state.add_search(&run)?;
        self.state.touch_workspace(&workspace.reference)?;
        Ok(render_static_probe_summary(&run, focus))
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
        let reference = self.state.next_reference(ReferenceKind::Query)?;
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
        let location =
            parse_source_location(&workspace.path, cwd, Some(&self.repo.root), location)?
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
                ensure!(
                    line > 0,
                    "by TACTIC requires FILE:LINE, cREF, or positioned qREF context"
                );
                ("tactic", input)
            }
        };
        let (ok, detail) = self
            .checker
            .probe_context(workspace, &path, line, 0, operation, &input)?;
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
                let location =
                    parse_source_location(&workspace.path, cwd, Some(&self.repo.root), &location)?
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
            ProbeContext::Scope(path) => {
                bail!("{path} is a search scope, not a Lean elaboration context")
            }
            ProbeContext::Check(reference) => {
                let run = self
                    .state
                    .check_run(&reference)?
                    .with_context(|| format!("unknown check reference {reference}"))?;
                ensure!(
                    run.workspace_ref == workspace.reference,
                    "{reference} belongs to {}; run the Lean probe from that workspace",
                    run.workspace_ref
                );
                let diagnostic = run.diagnostics.first().or_else(|| run.warnings.first());
                let (path, line) = diagnostic_position(
                    diagnostic
                        .map(|value| value.text.as_str())
                        .unwrap_or_default(),
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
                ensure!(
                    run.workspace_ref == workspace.reference,
                    "{reference} belongs to {}; run the Lean probe from that workspace",
                    run.workspace_ref
                );
                let hit = run
                    .hits
                    .first()
                    .with_context(|| format!("{reference} has no source context"))?;
                ensure!(!hit.path.is_empty(), "{reference} has no source path");
                let positioned = run.inference == "probe" && hit.line > 0
                    || matches!(hit.kind.as_str(), "location" | "location-expanded");
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
        "source" => {
            run.hits.truncate(1);
            for hit in &mut run.hits {
                hit.usages.clear();
            }
        }
        "simp" => {
            run.hits.retain(|hit| {
                hit.source
                    .as_deref()
                    .is_some_and(|source| source.contains("@[simp"))
            });
            if run.hits.is_empty()
                && !run
                    .note
                    .as_deref()
                    .is_some_and(|note| note.contains("warming"))
            {
                run.note = Some("no indexed @[simp] declaration in this name family".into());
            }
        }
        "usages" => {
            for hit in &mut run.hits {
                hit.source = None;
            }
        }
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
        "abbrev ",
        "class ",
        "def ",
        "example ",
        "inductive ",
        "instance ",
        "lemma ",
        "structure ",
        "theorem ",
    ]
    .iter()
    .any(|keyword| line.starts_with(keyword))
}

fn static_probe_query(
    context: Option<&ProbeContext>,
    subject: &str,
    focus: Option<&str>,
) -> Result<String> {
    match context {
        None => {}
        Some(ProbeContext::File(_)) => {
            bail!(
                "FILE with a declaration supports signature only; use probe NAME for API dossiers"
            )
        }
        Some(_) => bail!("this probe requires a declaration or type subject"),
    }
    let subject = subject.strip_prefix("_root_.").unwrap_or(subject);
    let default_focus = if subject.starts_with("type:") {
        "types"
    } else {
        "signature"
    };
    let query = match focus.unwrap_or(default_focus) {
        "signature" => format!("name:{subject}"),
        "source" => format!("{subject} source"),
        "fields" => format!("{subject} fields"),
        "constructors" => format!("name:{subject}.mk"),
        "coercions" => format!(
            "declaration {subject}.instCoe*|{subject}.instFunLike*|{subject}.instCoeFun*|{subject}.hasCoe*|{subject}.toFun*"
        ),
        "instances" => format!("declaration {subject}.inst*|{subject}.instance*"),
        "ext" => format!("name:{subject}.ext"),
        "simp" => format!("declaration {subject}*"),
        "apply" => format!("{subject} theorem"),
        "usages" => format!("name:{subject}"),
        "types" if subject.starts_with("type:") => subject.to_owned(),
        "types" => bail!(
            "types requires type:LEAN_TYPE or a cREF with a type/instance failure; use NAME signature for a declaration type"
        ),
        other => bail!("focus `{other}` requires source or failure context"),
    };
    Ok(query)
}

#[derive(Clone, Copy)]
struct WarningClassification {
    category: &'static str,
    risk: &'static str,
    mechanical: bool,
    guidance: &'static str,
}

#[derive(Debug)]
struct EnclosingDeclaration {
    name: String,
    header: String,
    public: bool,
}

fn classify_warning(text: &str) -> WarningClassification {
    let lower = text.to_ascii_lowercase();
    if lower.contains("unused") && lower.contains("simp") && lower.contains("argument") {
        return WarningClassification {
            category: "unused simp argument",
            risk: "mechanical",
            mechanical: true,
            guidance: "Handled by Lean automation's greedy remove-and-re-elaborate pass.",
        };
    }
    if lower.contains("unnecessary") && lower.contains("simpa") {
        return WarningClassification {
            category: "unnecessary simpa",
            risk: "mechanical",
            mechanical: true,
            guidance: "Handled by Lean automation using the linter-indicated rewrite.",
        };
    }
    if (lower.contains("havei") || lower.contains("leti"))
        && (lower.contains("have") || lower.contains("let"))
    {
        return WarningClassification {
            category: "Prop-only local instance",
            risk: "mechanical",
            mechanical: true,
            guidance: "Handled by Lean automation from the typed tactic-mode hint.",
        };
    }
    if lower.contains("automatically included section variable") {
        return WarningClassification {
            category: "implicit section variable",
            risk: "high",
            mechanical: false,
            guidance: "Decide whether to omit the variable, make it explicit, or restructure the section; preserve named-argument and downstream API behavior.",
        };
    }
    if lower.contains("unused variable") || lower.contains("unused argument") {
        return WarningClassification {
            category: "unused binder",
            risk: "high",
            mechanical: false,
            guidance: "Inspect whether the binder is public or used by downstream named arguments before removing or renaming it.",
        };
    }
    if lower.contains("duplicate") && lower.contains("instance") {
        return WarningClassification {
            category: "duplicate instance",
            risk: "high",
            mechanical: false,
            guidance: "Compare priorities, scopes, and downstream inference before choosing which instance survives.",
        };
    }
    if lower.contains("reducib") || lower.contains("class") && lower.contains("should be") {
        return WarningClassification {
            category: "declaration design",
            risk: "high",
            mechanical: false,
            guidance: "Treat this as an API design decision; inspect downstream uses and typeclass inference before changing annotations or declaration kind.",
        };
    }
    if lower.contains("deprecated") {
        return WarningClassification {
            category: "deprecation",
            risk: "medium",
            mechanical: false,
            guidance: "Confirm the replacement has the same elaboration behavior in this context and update related uses as one packet.",
        };
    }
    if lower.contains("seqfocus")
        || lower.contains("seq_focus")
        || lower.contains("no-op")
        || lower.contains("unused tactic")
        || lower.contains("unnecessary 'change'")
        || lower.contains("unnecessary `change`")
    {
        return WarningClassification {
            category: "local tactic cleanup",
            risk: "low",
            mechanical: false,
            guidance: "Simplify the local proof step, retaining the surrounding proof structure when the suggested replacement is unclear.",
        };
    }
    WarningClassification {
        category: "warning requiring judgment",
        risk: "medium",
        mechanical: false,
        guidance: "Inspect the declaration and related uses, make the narrowest coherent edit, and verify the file.",
    }
}

fn risk_rank(risk: &str) -> u8 {
    match risk {
        "low" => 0,
        "medium" => 1,
        "high" => 2,
        _ => 3,
    }
}

fn warning_location(text: &str) -> (Option<String>, u64, u64) {
    static LOCATION: OnceLock<Regex> = OnceLock::new();
    let location = LOCATION.get_or_init(|| {
        Regex::new(r"^(?P<path>.+?):(?P<line>[0-9]+)(?::(?P<column>[0-9]+))?(?::|$)")
            .expect("valid warning location regex")
    });
    let Some(captures) = text.lines().next().and_then(|line| location.captures(line)) else {
        return (None, 1, 1);
    };
    (
        captures.name("path").map(|value| value.as_str().to_owned()),
        captures
            .name("line")
            .and_then(|value| value.as_str().parse().ok())
            .unwrap_or(1),
        captures
            .name("column")
            .and_then(|value| value.as_str().parse().ok())
            .unwrap_or(1),
    )
}

fn diagnostic_path_matches(reported: &str, target: &str) -> bool {
    let reported = reported.trim_start_matches("./");
    let target = target.trim_start_matches("./");
    let target_module = target
        .strip_suffix(".lean")
        .unwrap_or(target)
        .replace('/', ".");
    reported == target
        || reported.ends_with(&format!("/{target}"))
        || reported == target_module
        || Path::new(reported).file_name() == Path::new(target).file_name()
}

fn warning_summary(text: &str) -> String {
    let first = text.lines().next().unwrap_or(text);
    let message = warning_location(first)
        .0
        .and_then(|_| first.splitn(4, ':').nth(3))
        .unwrap_or(first)
        .trim()
        .trim_start_matches("warning:")
        .trim();
    truncate_line(message, 100)
}

fn enclosing_declaration(source: &str, line: u64) -> Option<EnclosingDeclaration> {
    let lines = source.lines().collect::<Vec<_>>();
    let before = line.min(lines.len() as u64) as usize;
    for index in (0..before).rev() {
        let original = lines[index];
        let mut candidate = original.trim_start();
        let public = !candidate.starts_with("private ");
        for modifier in ["private ", "protected ", "noncomputable ", "unsafe "] {
            if let Some(rest) = candidate.strip_prefix(modifier) {
                candidate = rest.trim_start();
            }
        }
        let Some((keyword, rest)) = [
            "abbrev ",
            "class ",
            "def ",
            "example ",
            "inductive ",
            "instance ",
            "lemma ",
            "structure ",
            "theorem ",
        ]
        .into_iter()
        .find_map(|keyword| candidate.strip_prefix(keyword).map(|rest| (keyword, rest))) else {
            continue;
        };
        let name = rest
            .split(|character: char| {
                character.is_whitespace() || matches!(character, '(' | '{' | '[' | ':' | '=')
            })
            .next()
            .unwrap_or_default()
            .trim();
        if name.is_empty() || keyword == "example " || keyword == "instance " && name == ":" {
            return Some(EnclosingDeclaration {
                name: String::new(),
                header: original.trim().to_owned(),
                public: false,
            });
        }
        let end = (index + 6).min(before.max(index + 1)).min(lines.len());
        return Some(EnclosingDeclaration {
            name: name.to_owned(),
            header: lines[index..end]
                .iter()
                .map(|line| line.trim_end())
                .collect::<Vec<_>>()
                .join("\n"),
            public,
        });
    }
    None
}

fn warning_dossier(
    check_ref: &str,
    location: (&str, u64, u64),
    classification: &WarningClassification,
    diagnostic: &Diagnostic,
    declaration: Option<&EnclosingDeclaration>,
    source: &str,
) -> String {
    let (path, line, column) = location;
    let diagnostic_text = warning_diagnostic_for_dossier(&diagnostic.text);
    let mut detail = format!(
        "category: {}\nrisk: {}\ncheck: {check_ref}\nlocation: {path}:{line}:{column}\ndiagnostic:\n{}",
        classification.category, classification.risk, diagnostic_text
    );
    if let Some(declaration) = declaration {
        let exposure = if declaration.public {
            "public"
        } else {
            "local/private"
        };
        detail.push_str(&format!(
            "\nenclosing declaration ({exposure}):\n{}",
            declaration.header
        ));
    }
    let lines = source.lines().collect::<Vec<_>>();
    if !lines.is_empty() {
        let current = line
            .saturating_sub(1)
            .min(lines.len().saturating_sub(1) as u64) as usize;
        let start = current.saturating_sub(2);
        let end = (current + 3).min(lines.len());
        detail.push_str("\nsource context:");
        for (index, source_line) in lines.iter().enumerate().take(end).skip(start) {
            detail.push_str(&format!(
                "\n{} {:>4} | {}",
                if index == current { ">" } else { " " },
                index + 1,
                source_line
            ));
        }
    }
    detail.push_str(&format!("\nassessment: {}", classification.guidance));
    detail
}

fn warning_diagnostic_for_dossier(text: &str) -> String {
    let mut lines = Vec::new();
    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("Note: This linter can be disabled with `set_option ")
            || trimmed.starts_with("This linter can be disabled with `set_option ")
        {
            continue;
        }
        if trimmed.is_empty()
            && lines
                .last()
                .is_some_and(|previous: &&str| previous.trim().is_empty())
        {
            continue;
        }
        lines.push(line);
    }
    while lines.last().is_some_and(|line| line.trim().is_empty()) {
        lines.pop();
    }
    lines.join("\n")
}

struct InductiveConstructor {
    name: String,
    signature: String,
    line_offset: u64,
}

fn indexes_warming(rendered: &str) -> bool {
    rendered.contains("warming") && rendered.contains("index")
}

fn inductive_constructors(name: &str, source: &str) -> Vec<InductiveConstructor> {
    let lines = source.lines().collect::<Vec<_>>();
    let declaration = lines
        .iter()
        .position(|line| line.trim_start().starts_with("inductive "))
        .unwrap_or(0);
    let Some(constructor_indent) = lines
        .iter()
        .enumerate()
        .skip(declaration + 1)
        .filter(|(_, line)| line.trim_start().starts_with('|'))
        .map(|(_, line)| line.len() - line.trim_start().len())
        .min()
    else {
        return Vec::new();
    };
    let starts = lines
        .iter()
        .enumerate()
        .skip(declaration + 1)
        .filter(|(_, line)| {
            line.len() - line.trim_start().len() == constructor_indent
                && line.trim_start().starts_with('|')
        })
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    starts
        .iter()
        .enumerate()
        .filter_map(|(position, &start)| {
            let end = starts.get(position + 1).copied().unwrap_or(lines.len());
            let mut content = Vec::new();
            let mut in_comment = false;
            let mut name_line = start;
            for (index, line) in lines[start..end].iter().enumerate() {
                let trimmed = line.trim_start();
                let indent = line.len() - trimmed.len();
                if index > 0
                    && !in_comment
                    && indent <= constructor_indent
                    && !trimmed.is_empty()
                    && !trimmed.starts_with("/-")
                    && !trimmed.starts_with("--")
                {
                    break;
                }
                let mut rest = if index == 0 {
                    trimmed.strip_prefix('|')?.trim_start()
                } else {
                    line.trim()
                };
                loop {
                    if in_comment {
                        let Some((_, after)) = rest.split_once("-/") else {
                            rest = "";
                            break;
                        };
                        in_comment = false;
                        rest = after.trim_start();
                    } else if rest.starts_with("/-") {
                        let Some((_, after)) = rest.split_once("-/") else {
                            in_comment = true;
                            rest = "";
                            break;
                        };
                        rest = after.trim_start();
                    } else {
                        break;
                    }
                }
                if !rest.is_empty() && !rest.starts_with("--") {
                    if content.is_empty() {
                        name_line = start + index;
                    }
                    content.push(rest);
                }
            }
            let constructor = content.join(" ");
            let leaf = constructor.split_whitespace().next()?.trim_end_matches(':');
            if leaf.is_empty() {
                return None;
            }
            let signature = constructor
                .strip_prefix(leaf)
                .unwrap_or_default()
                .trim()
                .trim_start_matches(':')
                .trim()
                .to_owned();
            Some(InductiveConstructor {
                name: if leaf.contains('.') {
                    leaf.to_owned()
                } else {
                    format!("{name}.{leaf}")
                },
                signature,
                line_offset: (name_line - declaration) as u64,
            })
        })
        .collect()
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
            ProbeRequest::parse("Mathlib/ Demo.foo usages")
                .unwrap()
                .context,
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
        assert_eq!(
            ProbeRequest::parse("Mathlib/Data/List.lean warnings").unwrap(),
            ProbeRequest {
                context: Some(ProbeContext::File("Mathlib/Data/List.lean".into())),
                subject: None,
                focus: Some("warnings".into()),
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
            static_probe_query(None, "ContinuousMap", Some("constructors")).unwrap(),
            "name:ContinuousMap.mk"
        );
        assert_eq!(
            inductive_constructors(
                "Option",
                "inductive Option (α : Type) where\n  | none : Option α\n  | some (value : α) : Option α"
            )
            .into_iter()
            .map(|constructor| (constructor.name, constructor.signature, constructor.line_offset))
            .collect::<Vec<_>>(),
            [
                ("Option.none".into(), "Option α".into(), 1),
                ("Option.some".into(), "(value : α) : Option α".into(), 2),
            ]
        );
        assert_eq!(
            inductive_constructors(
                "IntInterval",
                "inductive IntInterval : Type where\n  | /-- A finite interval. -/\n    co (lo hi : Int)\n  |\n    /-- An infinite interval. -/\n    infinite\n  deriving Inhabited\n\nnamespace IntInterval"
            )
            .into_iter()
            .map(|constructor| (constructor.name, constructor.signature, constructor.line_offset))
            .collect::<Vec<_>>(),
            [
                ("IntInterval.co".into(), "(lo hi : Int)".into(), 2),
                ("IntInterval.infinite".into(), "".into(), 5),
            ]
        );
        assert_eq!(
            static_probe_query(None, "_root_.ContinuousMap", Some("source")).unwrap(),
            "ContinuousMap source"
        );
        assert_eq!(
            static_probe_query(None, "ContinuousMap", Some("coercions")).unwrap(),
            "declaration ContinuousMap.instCoe*|ContinuousMap.instFunLike*|ContinuousMap.instCoeFun*|ContinuousMap.hasCoe*|ContinuousMap.toFun*"
        );
        assert_eq!(
            static_probe_query(None, "Demo.apply", Some("simp")).unwrap(),
            "declaration Demo.apply*"
        );
        assert!(
            static_probe_query(
                Some(&ProbeContext::File("Demo.lean".into())),
                "Demo.foo",
                Some("fields")
            )
            .is_err()
        );
        assert!(ProbeRequest::parse("#check Nat").is_err());
        assert_eq!(
            ProbeRequest::parse("mathmux probe Demo.foo source")
                .unwrap_err()
                .to_string(),
            "probe receives QUERY only; omit the leading `mathmux probe`"
        );
        assert_eq!(
            ProbeRequest::parse("q123 show --all")
                .unwrap_err()
                .to_string(),
            "expand stored detail with `show q123 --all`, outside probe"
        );
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
            static_probe_query(None, "Demo.foo", Some("types"))
                .unwrap_err()
                .to_string(),
            "types requires type:LEAN_TYPE or a cREF with a type/instance failure; use NAME signature for a declaration type"
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
                hit(
                    "Demo.second",
                    "@[simp] theorem second (n : Nat) : n = n := by\n  rfl",
                ),
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

        let simp = render_static_probe_summary(&run, "simp");
        assert!(simp.contains("Demo.second"));
        assert!(!simp.contains("Demo.first"));

        let usages = render_static_probe_summary(&run, "usages");
        assert!(usages.contains("Demo.first"));
        assert!(!usages.contains("theorem first"));
    }

    #[test]
    fn warning_triage_separates_automation_from_judgment() {
        for warning in [
            "Demo.lean:1:1: warning: unused argument `h` in simp invocation",
            "Demo.lean:2:1: warning: unnecessary simpa",
            "Demo.lean:3:1: warning: use `have` instead of `haveI` when the goal is a proposition",
        ] {
            assert!(classify_warning(warning).mechanical, "{warning}");
        }
        let binder =
            classify_warning("Demo.lean:4:1: warning: automatically included section variable `G`");
        assert_eq!(binder.category, "implicit section variable");
        assert_eq!(binder.risk, "high");
        assert!(!binder.mechanical);
        assert_eq!(
            warning_location("Mathlib/Demo.lean:42:7: warning: unused variable"),
            (Some("Mathlib/Demo.lean".into()), 42, 7)
        );
        assert_eq!(
            warning_location("Mathlib.Demo:43:0: warning: unused variable"),
            (Some("Mathlib.Demo".into()), 43, 0)
        );
        assert!(diagnostic_path_matches("Mathlib.Demo", "Mathlib/Demo.lean"));
    }

    #[test]
    fn warning_dossiers_capture_declaration_exposure_and_source() {
        let source =
            "namespace Demo\n\ntheorem publicResult (unused : Nat) : True := by\n  trivial\n";
        let declaration = enclosing_declaration(source, 3).unwrap();
        assert_eq!(declaration.name, "publicResult");
        assert!(declaration.public);
        let classification = classify_warning("Demo.lean:3:23: warning: unused variable `unused`");
        let dossier = warning_dossier(
            "c7",
            ("Demo.lean", 3, 23),
            &classification,
            &Diagnostic {
                kind: "linter.unusedVariables".into(),
                text: "Demo.lean:3:23: warning: unused variable `unused`\n\nNote: This linter can be disabled with `set_option linter.unusedVariables false`".into(),
                context: None,
            },
            Some(&declaration),
            source,
        );
        assert!(dossier.contains("risk: high"));
        assert!(dossier.contains("enclosing declaration (public)"));
        assert!(dossier.contains(">    3 | theorem publicResult"));
        assert!(!dossier.contains("This linter can be disabled"));
    }
}
