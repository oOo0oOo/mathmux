use std::path::Path;

use anyhow::{Result, bail, ensure};

use super::*;
use crate::reference::{Reference, ReferenceKind};

const FOCUSES: &[&str] = &[
    "assumptions",
    "evidence",
    "examples",
    "context",
    "signature",
    "apply",
    "fields",
    "constructors",
    "ext",
    "simp",
    "usages",
    "source",
    "outline",
    "goal",
    "types",
    "defeq",
    "rewrite",
    "profile",
    "warnings",
];
const REMOVED_FOCUSES: &[&str] = &["neighborhood", "dependencies", "instances", "coercions"];

#[derive(Debug, Clone, PartialEq, Eq)]
enum ProbeContext {
    File(String),
    Scope(String),
    Position(String),
    Check(String),
    Query(String, usize),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum LeanDirective {
    Check(String),
    Synth(String),
    Reduce(String),
    Tactic(String),
    Inspect(String),
    Apply(String),
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
        let query = normalize_colon_attached_source_facet(query.trim());
        let query = query.trim();
        ensure!(!query.is_empty(), "probe query is empty");
        if query == "mathmux probe" || query.starts_with("mathmux probe ") {
            bail!("probe receives QUERY only; omit the leading `mathmux probe`")
        }
        let mut parts = query.split_whitespace();
        let first = parts.next().unwrap();
        let context = parse_context(first);
        ensure!(
            context.is_some() || first.starts_with("type:") || !first.contains('\\'),
            "declaration names require literal characters, not backslash escapes; use the literal apostrophe or Unicode character"
        );
        if let Some((path, start)) = source_range_context(first) {
            bail!(
                "source ranges are a search form, not a probe context; use `mathmux search {first}` for source or `mathmux probe {path}:{start} goal` for Lean context"
            );
        }
        let remainder = if context.is_some() {
            query[first.len()..].trim()
        } else {
            query
        };
        if matches!(&context, Some(ProbeContext::Query(_, _)))
            && matches!(remainder.split_whitespace().next(), Some("show" | "--all"))
        {
            bail!(
                "probe --all is not valid here; use `mathmux show {first} --all` for stored detail"
            )
        }
        if let Some(ProbeContext::Check(reference)) = &context
            && remainder
                .split_whitespace()
                .next()
                .is_some_and(|term| term.trim_matches(['\'', '"']) == "--wait")
        {
            bail!("--wait belongs to show; use `mathmux show {reference} --wait`")
        }
        if remainder
            .split_whitespace()
            .any(|term| term.trim_matches(['\'', '"']) == "--all")
        {
            let hint = match &context {
                Some(ProbeContext::Check(reference)) => {
                    format!("use `mathmux probe {reference} goal|types|defeq|rewrite|profile`")
                }
                Some(ProbeContext::Query(reference, _)) => {
                    format!("use `mathmux show {reference} --all` for stored results")
                }
                _ => "use `mathmux probe NAME source` or `mathmux probe NAME usages`".into(),
            };
            bail!("probe --all is not valid here; {hint}")
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
        if let Some(ProbeContext::File(file) | ProbeContext::Scope(file)) = &context {
            let mut facet_terms = remainder.split_whitespace();
            if let (Some(facet), None) = (facet_terms.next(), facet_terms.next()) {
                let facet = facet.trim_matches(['\'', '"']);
                if matches!(
                    facet.to_ascii_lowercase().as_str(),
                    "outline" | "declarations" | "imports" | "dependents"
                ) {
                    bail!(
                        "`{facet}` is a source-search facet, not a probe subject; use `mathmux search {file} {facet}`"
                    )
                }
            }
        }
        if let Some(ProbeContext::Position(location)) = &context {
            let mut focus_terms = remainder.split_whitespace();
            if let (Some(focus), None) = (focus_terms.next(), focus_terms.next())
                && focus.trim_matches(['\'', '"']) == "source"
            {
                bail!(
                    "source is a search form at FILE:LINE; use `mathmux search {location}` for source or `mathmux probe {location} goal` for Lean context"
                )
            }
        }
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
        validate_balanced_fragment(remainder)?;
        let mut terms = remainder.split_whitespace().collect::<Vec<_>>();
        if let Some(removed) = terms
            .last()
            .map(|term| term.to_ascii_lowercase())
            .filter(|term| REMOVED_FOCUSES.contains(&term.as_str()))
        {
            bail!(
                "probe focus `{removed}` was removed; use signature, source, usages, or a kind-specific focus"
            );
        }
        let focus = terms
            .last()
            .map(|term| unquote(term))
            .filter(|term| FOCUSES.contains(&term.to_ascii_lowercase().as_str()))
            .map(|term| term.to_ascii_lowercase());
        if focus.is_some() {
            terms.pop();
        }
        if focus.as_deref() == Some("context") && !matches!(context, Some(ProbeContext::Check(_))) {
            bail!(
                "Lean context requires an exact position; use `probe FILE:LINE goal` or `probe FILE:LINE TERM`"
            );
        }

        if let Some(first) = terms.first_mut()
            && let Some(stripped) = first.strip_prefix('@')
        {
            *first = stripped;
        }
        if context.is_none() && terms.len() >= 3 && terms[1].eq_ignore_ascii_case("find") {
            return Ok(Self {
                context,
                subject: Some(terms[0].to_owned()),
                focus: Some(format!("find:{}", terms[2..].join(" "))),
                directive: None,
            });
        }
        if matches!(context, Some(ProbeContext::Query(_, _)))
            && terms.len() >= 2
            && terms[0].eq_ignore_ascii_case("find")
        {
            return Ok(Self {
                context,
                subject: None,
                focus: Some(format!("find:{}", terms[1..].join(" "))),
                directive: None,
            });
        }
        if context.is_none()
            && !terms.first().is_some_and(|term| term.starts_with("type:"))
            && terms.len() > 1
        {
            let requested = unquote(terms.last().copied().unwrap_or_default());
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
                    "unknown declaration focus `{requested}`; try `probe {name} signature`, `probe {name} source`, or `probe {name} usages`"
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

fn indexed_check_hit_from_result(result: SearchResult, subject: &str) -> Option<SearchHit> {
    result.hits.into_iter().find(|hit| {
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
    if let Some((reference, index)) = parse_query_hit_reference(value) {
        return Some(ProbeContext::Query(reference, index));
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

fn parse_query_hit_reference(value: &str) -> Option<(String, usize)> {
    let (reference, index) = if let Some((reference, index)) = value.split_once('#') {
        (reference, index.parse::<usize>().ok()?)
    } else {
        (value, 1)
    };
    (index > 0 && Reference::is_kind(reference, ReferenceKind::Query))
        .then(|| (reference.to_owned(), index - 1))
}

fn source_range_context(value: &str) -> Option<(&str, u64)> {
    let (path, range) = value.rsplit_once(':')?;
    let (start, _) = parse_source_line_range(range)?;
    (Path::new(path)
        .extension()
        .and_then(|extension| extension.to_str())
        .is_some_and(|extension| extension.eq_ignore_ascii_case("lean")))
    .then_some((path, start))
}

fn parse_directive(value: &str) -> Result<Option<LeanDirective>> {
    for (prefix, make) in [
        (
            "#check",
            LeanDirective::Check as fn(String) -> LeanDirective,
        ),
        ("#synth", LeanDirective::Synth),
        ("#reduce", LeanDirective::Reduce),
        ("#inspect", LeanDirective::Inspect),
        ("#apply", LeanDirective::Apply),
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
        let request = ProbeRequest::parse(query)
            .context(crate::protocol::DiscoveryFailure::InvalidRequest)?;
        if let Some(directive) = request.directive {
            let context = request.context.unwrap();
            if let LeanDirective::Check(subject) = &directive
                && let Some(rendered) =
                    self.probe_indexed_check(workspace, cwd, &context, subject)?
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
                bail!("cREF accepts only goal, types, defeq, rewrite, or profile focus")
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
            (Some(ProbeContext::Position(location)), Some(subject), Some("examples")) => {
                self.resolve_probe_context(
                    workspace,
                    cwd,
                    ProbeContext::Position(location.clone()),
                )?;
                self.probe_examples(workspace, subject, Some(location))
            }
            (Some(ProbeContext::Position(location)), Some(subject), Some("evidence")) => {
                let (path, line) = self.resolve_probe_context(
                    workspace,
                    cwd,
                    ProbeContext::Position(location.clone()),
                )?;
                self.probe_verified_evidence(workspace, subject, &path, line)
            }
            (Some(ProbeContext::Position(_)), _, Some(focus)) => {
                bail!(
                    "focus `{focus}` is not valid at FILE:LINE; use goal, TERM, or a Lean directive"
                )
            }
            (Some(ProbeContext::Query(reference, hit_index)), subject, focus) => {
                self.probe_query_reference(workspace, cwd, reference, *hit_index, subject, focus)
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
            (None, Some(subject), Some("examples")) => {
                self.probe_examples(workspace, subject, None)
            }
            (None, Some(subject), Some(focus @ ("assumptions" | "evidence"))) => {
                self.probe_contract(workspace, cwd, subject, focus)
            }
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
            result.note = Some(format!(
                "declaration not found: {subject}; try search {subject}"
            ));
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
        cwd: &Path,
        context: &ProbeContext,
        subject: &str,
    ) -> Result<Option<String>> {
        let query = match context {
            ProbeContext::Query(reference, _) => format!("{reference} #check {subject}"),
            ProbeContext::File(file) => format!("{file} #check {subject}"),
            _ => return Ok(None),
        };
        let file_target = match context {
            ProbeContext::File(file) => {
                let (path, _) =
                    self.resolve_probe_context(workspace, cwd, ProbeContext::File(file.clone()))?;
                Some(
                    path.strip_prefix(&workspace.path)
                        .unwrap_or(&path)
                        .to_owned(),
                )
            }
            _ => None,
        };
        let hit = match context {
            ProbeContext::Query(reference, hit_index) => {
                let Some(run) = self.state.search_run(reference)? else {
                    return Ok(None);
                };
                run.hits
                    .get(*hit_index)
                    .filter(|hit| qualified_name_matches(&hit.name, subject))
                    .or_else(|| indexed_check_hit(&run, subject))
                    .cloned()
            }
            ProbeContext::File(_) if declaration_name_query(subject) => self
                .planned_text_search(
                    workspace,
                    subject,
                    TextSearchPlan::ExactFirst,
                    file_target.as_deref(),
                    None,
                    false,
                )
                .ok()
                .and_then(|result| indexed_check_hit_from_result(result, subject)),
            _ => None,
        };
        let Some(hit) = hit else {
            return Ok(None);
        };
        let signature = hit
            .signature
            .as_deref()
            .expect("indexed check requires a signature");
        self.store_probe_result(
            workspace,
            &query,
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
        if run.status == crate::state::CheckStatus::Running && diagnostic.is_none() {
            bail!("{}", running_check_probe_hint(reference));
        }
        let text = diagnostic
            .map(|diagnostic| diagnostic.text.as_str())
            .unwrap_or("check has no diagnostic");
        let (path, line) = diagnostic_position(text, run.failed.as_deref());
        let detail = match focus {
            Some("context") => {
                let mut detail =
                    diagnostic_context(text, diagnostic.and_then(|d| d.context.as_deref()));
                detail.push_str(&self.failure_context(
                    workspace,
                    text,
                    if run.workspace_ref == workspace.reference {
                        path.as_deref()
                    } else {
                        None
                    },
                )?);
                detail
            }
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
            Some("goal") => {
                let diagnostic = diagnostic
                    .with_context(|| format!("{reference} has no stored failure goal"))?;
                stored_goal_detail(text, diagnostic.context.as_deref())
            }
            None => {
                let diagnostic =
                    diagnostic.with_context(|| format!("{reference} has no failure to probe"))?;
                diagnostic_context(text, diagnostic.context.as_deref())
            }
            Some(other) => bail!(
                "focus `{other}` is not valid for a stored check; valid analyses: goal, types, defeq, rewrite, profile"
            ),
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
        hit_index: usize,
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
        let hit = run.hits.get(hit_index).with_context(|| {
            format!(
                "{reference} has {} result(s), not result #{}",
                run.hits.len(),
                hit_index + 1
            )
        })?;
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
                "focus `{focus}` is not valid for a declaration qREF; use signature, source, outline, neighborhood, dependencies, find TERM, or usages, or probe a cREF failure"
            )
        }
        if run.inference != "probe"
            && subject.is_none()
            && matches!(
                focus,
                None | Some("signature" | "source" | "outline" | "usages")
            )
            || focus.is_some_and(|focus| focus.starts_with("find:"))
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
        if focus == Some("examples") {
            return self.probe_examples(workspace, subject, None);
        }
        if let Some(focus @ ("assumptions" | "evidence")) = focus {
            return self.probe_contract(workspace, cwd, subject, focus);
        }
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
        let Some(reference) = rendered_search_reference(&rendered) else {
            return Ok(rendered);
        };
        let Some(mut run) = self.state.search_run(&reference)? else {
            return Ok(rendered);
        };
        if focus == "fields"
            && run
                .note
                .as_deref()
                .is_some_and(|note| note.contains("not a class or structure"))
        {
            let subject = query.split_whitespace().next().unwrap_or("the subject");
            if let Some(hit) = run.hits.first()
                && hit.kind == "abbrev"
                && let Some(target) = abbreviation_target(hit)
                && target != subject
            {
                return self.run_static_probe_query(
                    workspace,
                    cwd,
                    &format!("{target} fields"),
                    "fields",
                );
            }
            let kind = run
                .note
                .as_deref()
                .and_then(|note| note.split(" is ").nth(1))
                .and_then(|detail| detail.split(',').next())
                .unwrap_or("a declaration");
            bail!(invalid_declaration_focus_message(
                subject,
                kind,
                "a class or structure"
            ));
        }
        if focus == "usages" {
            self.enrich_usage_dossier(workspace, &mut run)?;
        }
        if (matches!(focus, "source" | "outline") || focus.starts_with("find:"))
            && !run.hits.is_empty()
        {
            return self.store_query_hit_refinement(workspace, &reference, &run.hits[0], focus);
        }
        Ok(render_static_probe_summary(&run, focus))
    }

    fn enrich_usage_dossier(&self, workspace: &Workspace, run: &mut SearchRun) -> Result<()> {
        let Some(hit) = run.hits.first() else {
            return Ok(());
        };
        let subject = hit.name.strip_prefix("_root_.").unwrap_or(&hit.name);
        let law_query = format!(
            "declaration {subject}.apply*|{subject}_apply*|{subject}.comp*|{subject}_comp*|{subject}.trans*|{subject}_trans*"
        );
        let law = self
            .planned_text_search(
                workspace,
                &law_query,
                TextSearchPlan::Discovery,
                None,
                None,
                false,
            )?
            .hits
            .into_iter()
            .find(|candidate| matches!(candidate.kind.as_str(), "lemma" | "theorem"));
        let mut seen_consumers = HashSet::new();
        let consumers = hit
            .usages
            .iter()
            .filter_map(|usage| usage.context.as_deref())
            .filter(|context| context.trim_start_matches("_root_.") != subject)
            .filter(|context| seen_consumers.insert(context.trim_start_matches("_root_.")))
            .take(2)
            .collect::<Vec<_>>();
        let excerpt = hit.usages.first().and_then(|usage| {
            let path = if std::path::Path::new(&usage.path).is_absolute() {
                std::path::PathBuf::from(&usage.path)
            } else {
                workspace.path.join(&usage.path)
            };
            std::fs::read_to_string(path).ok().and_then(|source| {
                source
                    .lines()
                    .nth(usage.line.saturating_sub(1) as usize)
                    .map(|line| truncate_line(line.trim(), 180))
            })
        });
        let mut dossier = Vec::new();
        if let Some(law) = law {
            dossier.push(format!(
                "law: {}{}",
                law.name,
                law.signature
                    .as_deref()
                    .map(|signature| format!(" : {}", truncate_line(signature, 180)))
                    .unwrap_or_default()
            ));
        }
        if !consumers.is_empty() {
            dossier.push(format!("indexed consumers: {}", consumers.join(", ")));
        }
        if let Some(excerpt) = excerpt {
            dossier.push(format!("usage excerpt: {excerpt}"));
        }
        if hit.usages.is_empty() {
            dossier.push("no indexed usages".into());
        }
        if !dossier.is_empty() {
            run.note = Some(match run.note.take() {
                Some(note) => format!("{}\n{note}", dossier.join("\n")),
                None => dossier.join("\n"),
            });
        }
        Ok(())
    }

    fn run_constructors_probe(
        &self,
        workspace: &Workspace,
        cwd: &Path,
        subject: &str,
    ) -> Result<String> {
        let source_search = || -> Result<(String, Option<SearchRun>)> {
            let rendered =
                self.search(workspace, cwd, &format!("{subject} source"), None, false)?;
            let run = rendered_search_reference(&rendered)
                .map(|reference| self.state.search_run(&reference))
                .transpose()?
                .flatten();
            Ok((rendered, run))
        };
        let (mut rendered, mut run) = source_search()?;
        if indexes_warming(&rendered) {
            (rendered, run) = source_search()?;
        }
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
            format!("{name}.mk")
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
            bail!(invalid_declaration_focus_message(
                name,
                hit.kind.as_str(),
                "a structure, class, or inductive declaration"
            ))
        };
        self.run_static_probe_query(workspace, cwd, &query, "constructors")
    }

    // Explicit source requests read the current file, not the bounded search preview.
    // Keep that snapshot under a new reference so --all can recover omitted lines.
    pub(super) fn refresh_probe_source(
        &self,
        workspace: &Workspace,
        hit: &mut SearchHit,
    ) -> Result<bool> {
        let Some((path, _, _)) =
            source_query::resolve_source_path(&workspace.path, &workspace.path, &hit.path)?
        else {
            return Ok(false);
        };
        let source = fs::read_to_string(&path)?;
        let entry = source::parse_source_with_limit(&source, &hit.module, usize::MAX)
            .into_iter()
            .find(|entry| {
                entry.name.trim_start_matches("_root_.") == hit.name.trim_start_matches("_root_.")
                    && (entry.kind == hit.kind
                        || matches!(hit.kind.as_str(), "declaration" | "generated" | "source-group"))
            })
            .or_else(|| source::alias_source_entry(&source, &hit.name))
            .or_else(|| source::explicit_generator_source_entry(&source, &hit.module, &hit.name));
        let Some(entry) = entry else {
            return Ok(false);
        };
        hit.line = entry.line;
        if !matches!(entry.kind.as_str(), "alias" | "generator") || hit.signature.is_none() {
            hit.signature = nonempty(entry.signature);
        }
        hit.kind = entry.kind;
        hit.doc = nonempty(entry.docs);
        hit.source = Some(entry.body);
        Ok(true)
    }

    fn store_query_hit_refinement(
        &self,
        workspace: &Workspace,
        reference: &str,
        hit: &SearchHit,
        focus: &str,
    ) -> Result<String> {
        let mut hit = hit.clone();
        let source_focus = matches!(focus, "source" | "outline") || focus.starts_with("find:");
        let fresh_source = source_focus && self.refresh_probe_source(workspace, &mut hit)?;
        if !fresh_source && (matches!(focus, "source" | "outline") || focus.starts_with("find:")) {
            let (scopes, _) = self.search_scopes(workspace)?;
            self.enrich_exact_source(&mut hit, &scopes)?;
        }
        let note = (source_focus && !fresh_source).then(|| {
            if hit.source.is_none() {
                format!(
                    "Source unavailable in the current file or index; no completeness claim.\nInspect the declaration contract in an importing project file: mathmux probe FILE:LINE {}",
                    shell_argument(&format!("#inspect {}", hit.name.trim_start_matches("_root_.")))
                )
            } else {
                "Indexed source excerpt; completeness unavailable.".into()
            }
        });
        let run = SearchRun {
            reference: self.state.next_reference(ReferenceKind::Query)?,
            workspace_ref: workspace.reference.clone(),
            query: format!("{reference} {focus}"),
            inference: if fresh_source {
                "probe-source"
            } else {
                "probe-refinement"
            }
            .into(),
            hits: vec![hit],
            note,
            duration_ms: 0,
            created_at: now_unix_ms(),
        };
        self.state.add_search(&run)?;
        self.state.touch_workspace(&workspace.reference)?;
        Ok(render_static_probe_summary(&run, focus))
    }

    pub(super) fn store_probe_result(
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
        ensure_lean_project_context(&workspace.path, &location.path)?;
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
        let (path, line) = self
            .resolve_probe_context(workspace, cwd, context)
            .map_err(|error| {
                if error
                    .downcast_ref::<crate::protocol::DiscoveryFailure>()
                    .is_some()
                {
                    error
                } else {
                    error.context(crate::protocol::DiscoveryFailure::UnavailableContext)
                }
            })?;
        let (operation, input) = match directive {
            LeanDirective::Check(input) => ("term", input),
            LeanDirective::Synth(input) => ("synth", input),
            LeanDirective::Reduce(input) => ("reduce", input),
            LeanDirective::Inspect(input) => {
                ensure!(
                    line > 0,
                    "#inspect requires FILE:LINE, cREF, or positioned qREF context"
                );
                ("inspect", input)
            }
            LeanDirective::Apply(input) => {
                ensure!(
                    line > 0,
                    "#apply requires FILE:LINE, cREF, or positioned qREF context"
                );
                ("tactic", format!("apply ({input})"))
            }
            LeanDirective::Tactic(input) => {
                ensure!(
                    line > 0,
                    "by TACTIC requires FILE:LINE, cREF, or positioned qREF context"
                );
                ("tactic", input)
            }
        };
        let (worker_ok, detail) = self
            .checker
            .probe_context(workspace, &path, line, 0, operation, &input)
            .context(crate::protocol::DiscoveryFailure::Infrastructure)?;
        let (ok, mut detail) = decisive_directive_result(operation, &input, worker_ok, detail);
        if operation == "tactic" && input.starts_with("apply (") {
            detail = if !ok && let Some(focused) = diagnostic_apply_detail(&detail) {
                format!(
                    "application experiment failed (not a check certificate)\n{focused}\nFull Lean diagnostic:\n{detail}"
                )
            } else {
                format!(
                    "application experiment (not a check certificate)\n{detail}\nRemaining goals are obligations, not established facts."
                )
            };
        }
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
        let resolved: Result<(PathBuf, u64)> = match context {
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
            ProbeContext::Query(reference, hit_index) => {
                let run = self
                    .state
                    .search_run(&reference)?
                    .with_context(|| format!("unknown query reference {reference}"))?;
                ensure!(
                    run.workspace_ref == workspace.reference,
                    "{reference} belongs to {}; run the Lean probe from that workspace",
                    run.workspace_ref
                );
                let hit = run.hits.get(hit_index).with_context(|| {
                    format!(
                        "{reference} has {} result(s), not result #{}",
                        run.hits.len(),
                        hit_index + 1
                    )
                })?;
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
        };
        let (path, line) = resolved?;
        ensure_lean_project_context(&workspace.path, &path)?;
        Ok((path, line))
    }
}

fn ensure_lean_project_context(root: &Path, path: &Path) -> Result<()> {
    let root = fs::canonicalize(root)?;
    let path = fs::canonicalize(path)?;
    if !path.starts_with(&root) {
        return Err(anyhow::anyhow!("Lean experiments need a project file in this workspace. Use a project FILE:LINE that imports the declaration, then retry the directive. Dependency source remains readable with search or probe NAME source."))
            .context(crate::protocol::DiscoveryFailure::UnavailableContext);
    }
    Ok(())
}

fn decisive_directive_result(
    operation: &str,
    input: &str,
    worker_ok: bool,
    detail: String,
) -> (bool, String) {
    if operation == "tactic" || operation == "goal" {
        return (worker_ok, detail);
    }
    let lower = detail.to_ascii_lowercase();
    let failed = lower.contains("unknown identifier")
        || lower.contains("failed to synthesize")
        || lower.contains("type mismatch")
        || lower.contains("declaration has metavariables")
        || lower.contains("error:");
    if operation == "term"
        && let Some(start) = detail
            .lines()
            .position(|line| line.trim_start().starts_with(input) && line.contains(" : "))
    {
        let decisive = detail
            .lines()
            .skip(start)
            .take_while(|line| !line.trim_start().starts_with("warning:"))
            .collect::<Vec<_>>()
            .join("\n");
        return (true, decisive);
    }
    (!failed && (worker_ok || !detail.trim().is_empty()), detail)
}

fn abbreviation_target(hit: &SearchHit) -> Option<&str> {
    let source = hit.source.as_deref()?;
    let target = source.split_once(":=")?.1.trim();
    target
        .split(|character: char| {
            !(character.is_alphanumeric() || matches!(character, '_' | '\'' | '.'))
        })
        .find(|token| !token.is_empty())
}

fn render_static_probe_summary(run: &SearchRun, focus: &str) -> String {
    let mut run = run.clone();
    match focus {
        "constructors" => {
            if let Some(hit) = run.hits.first().filter(|hit| hit.signature.is_none()) {
                let name = hit.name.trim_start_matches("_root_.");
                let fields = name
                    .strip_suffix(".mk")
                    .map(|parent| format!("mathmux probe {} fields; ", shell_argument(parent)))
                    .unwrap_or_default();
                prepend_search_note(
                    &mut run.note,
                    format!(
                        "Constructor signature is not indexed. Inspect obligations: {fields}mathmux probe FILE:LINE {} in a project file importing it.",
                        shell_argument(&format!("#inspect {name}"))
                    ),
                );
            }
        }
        "signature" | "apply" => {
            run.inference = if focus == "signature" {
                "signature".into()
            } else {
                "exact".into()
            };
            for hit in &mut run.hits {
                hit.source = None;
            }
        }
        "source" => {
            if run.inference != "probe-source" {
                run.inference = "probe-source-excerpt".into();
            }
            run.hits.truncate(1);
            for hit in &mut run.hits {
                hit.usages.clear();
            }
        }
        "outline" => {
            run.inference = "probe".into();
            run.hits.truncate(1);
            for hit in &mut run.hits {
                hit.usages.clear();
                let declaration_kind = hit.kind.clone();
                hit.kind = "declaration-outline".into();
                hit.signature = Some(format!("{declaration_kind} outline from line {}", hit.line));
                hit.source = hit.source.as_deref().map(|source| {
                    declaration_outline_from_hit(source, hit.line, &declaration_kind)
                });
            }
        }
        focus if focus.starts_with("find:") => {
            let term = focus.trim_start_matches("find:").trim();
            run.inference = "probe".into();
            run.hits.truncate(1);
            for hit in &mut run.hits {
                hit.usages.clear();
                hit.kind = "declaration-find".into();
                hit.signature = Some(format!("local matches for {term}"));
                hit.source = hit.source.as_deref().map(|source| {
                    declaration_find_from_hit(source, hit.line, term, &run.reference)
                });
            }
        }
        "ext" => {
            if run.hits.is_empty()
                && !run
                    .note
                    .as_deref()
                    .is_some_and(|note| note.contains("warming"))
            {
                run.note = Some("no indexed @[ext] declaration in this name family".into());
            }
            for hit in &mut run.hits {
                hit.source = None;
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
            for hit in &mut run.hits {
                hit.source = None;
            }
        }
        "usages" => {
            run.inference = "usages".into();
            for hit in &mut run.hits {
                hit.source = None;
            }
        }
        _ => {}
    }
    if matches!(focus, "signature" | "source" | "outline" | "ext")
        && matches!(
            run.note.as_deref(),
            Some("search indexes warming" | "source index warming")
        )
    {
        run.note = None;
    }
    if focus == "signature" && run.hits.len() == 1
        && let Some(hit) = run.hits.first().filter(|hit| hit.signature.is_none())
    {
        let name = hit.name.trim_start_matches("_root_.");
        let guidance = if hit.kind == "file" {
            format!(
                "File result has no declaration signature; choose a declaration: mathmux search {} outline",
                shell_argument(&hit.path)
            )
        } else {
            format!(
                "Signature is not indexed; inspect textual context: mathmux probe {} source",
                shell_argument(name)
            )
        };
        prepend_search_note(&mut run.note, guidance);
    }
    render_summary_without_hints(&run)
}

fn declaration_find_from_hit(
    source: &str,
    declaration_line: u64,
    term: &str,
    reference: &str,
) -> String {
    let lines = source.lines().collect::<Vec<_>>();
    let header = source::declaration_source_header_offset(source);
    let matches = lines
        .iter()
        .enumerate()
        .filter(|(_, line)| line.contains(term))
        .map(|(index, line)| {
            if index < header {
                format!("ambient: {}", truncate_line(line, 180))
            } else {
                format!(
                    "{:>5}  {}",
                    declaration_line + (index - header) as u64,
                    truncate_line(line, 180)
                )
            }
        })
        .collect::<Vec<_>>();
    if matches.is_empty() {
        return "No literal matches in the available source snapshot.".into();
    }
    let mut result = matches
        .iter()
        .take(12)
        .cloned()
        .collect::<Vec<_>>()
        .join("\n");
    if matches.len() > 12 {
        result.push_str(&format!(
            "\n… {} matching lines not shown; full source: mathmux show {reference} --all",
            matches.len() - 12
        ));
    }
    result
}

fn declaration_outline_from_hit(source: &str, declaration_line: u64, kind: &str) -> String {
    let lines = source.lines().collect::<Vec<_>>();
    let header = source::declaration_source_header_offset(source);
    let proof_steps = [
        "let ",
        "letI ",
        "have ",
        "suffices ",
        "show ",
        "refine ",
        "exact ",
        "apply ",
        "simpa ",
        "rw ",
        "constructor",
        "cases ",
        "rcases ",
        "intro ",
        "case ",
        "calc",
    ];
    lines
        .iter()
        .enumerate()
        .skip(header)
        .filter_map(|(index, line)| {
            let trimmed = line.trim_start();
            let indent = line.len().saturating_sub(trimmed.len());
            let structural = index == header
                || is_declaration_header(line)
                || match kind {
                    "class" | "structure" => {
                        indent <= 4 && (trimmed.contains(" : ") || trimmed.starts_with("extends "))
                    }
                    "inductive" => trimmed.starts_with('|') || trimmed.starts_with("deriving "),
                    "def" | "abbrev" | "instance" => {
                        indent <= 6
                            && (trimmed.contains(" :=")
                                || trimmed.starts_with('|')
                                || trimmed.starts_with("{ ")
                                || trimmed.contains(" := "))
                    }
                    _ => indent <= 8 && proof_steps.iter().any(|step| trimmed.starts_with(step)),
                };
            structural.then(|| {
                format!(
                    "{:>5}  {}",
                    declaration_line + index.saturating_sub(header) as u64,
                    truncate_line(line.trim_end(), 180)
                )
            })
        })
        .take(80)
        .collect::<Vec<_>>()
        .join("\n")
}

fn is_declaration_header(line: &str) -> bool {
    source::declaration_regex().is_match(line) || line.trim_start().starts_with("example ")
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
        "signature" => subject.to_owned(),
        "source" => format!("{subject} source"),
        "outline" => format!("{subject} source"),
        focus if focus.starts_with("find:") => format!("{subject} source"),
        "fields" => format!("{subject} fields"),
        "constructors" => format!("{subject}.mk"),
        "ext" => format!("declaration {subject}.ext*|{subject}_ext*"),
        "simp" => format!("declaration {subject}*"),
        "apply" => format!("declaration {subject}.apply*|{subject}_apply*"),
        "usages" => subject.to_owned(),
        "types" if subject.starts_with("type:") => subject.to_owned(),
        "types" => bail!(
            "types requires type:LEAN_TYPE or a cREF with a type/instance failure; use NAME signature for a declaration type"
        ),
        other => bail!("focus `{other}` requires source or failure context"),
    };
    Ok(query)
}

fn invalid_declaration_focus_message(subject: &str, kind: &str, required: &str) -> String {
    format!(
        "{subject} is {kind}, not {required}; valid focuses: signature, source, outline, usages, apply"
    )
}

fn rendered_search_reference(rendered: &str) -> Option<String> {
    rendered.lines().rev().find_map(|line| {
        line.strip_prefix("ref: ")
            .filter(|reference| Reference::is_kind(reference, ReferenceKind::Query))
            .map(str::to_owned)
    })
}

fn stored_goal_detail(diagnostic: &str, source_context: Option<&str>) -> String {
    let primary = diagnostic_goal_detail(diagnostic).unwrap_or_else(|| {
        format!(
            "primary diagnostic\n{}",
            diagnostic_context(diagnostic, None)
        )
    });
    [primary, source_context.unwrap_or_default().to_owned()]
        .into_iter()
        .filter(|part| !part.trim().is_empty())
        .collect::<Vec<_>>()
        .join("\n")
}

fn running_check_probe_hint(reference: &str) -> String {
    format!(
        "check {reference} is still running; use `mathmux show {reference} --wait`, then retry `mathmux probe {reference} goal|types|defeq|rewrite|profile`"
    )
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
    fn bodyless_multiline_headers_keep_parameters_and_parents() {
        let source = "class Parent (n : Nat) : Prop where\n  good : n = n\nclass Child\n  (n : Nat) : Prop\n  extends Parent n\nstructure Empty\n  (n : Nat)\n  deriving Inhabited\naxiom value\n  (n : Nat) :\n  n = n\ninductive Choice\n  (n : Nat)\n  | mk : Choice n\n";
        let entries = source::parse_source(source, "Fixture");
        let child = entries.iter().find(|e| e.name == "Child").unwrap();
        assert!(
            child.signature.contains("(n : Nat) : Prop"),
            "{}",
            child.signature
        );
        assert!(
            child.signature.contains("extends Parent n"),
            "{}",
            child.signature
        );
        let value = entries.iter().find(|e| e.name == "value").unwrap();
        assert!(value.signature.contains("n = n"), "{}", value.signature);
        for name in ["Empty", "Choice"] {
            let entry = entries.iter().find(|e| e.name == name).unwrap();
            assert!(entry.signature.contains("(n : Nat)"), "{}", entry.signature);
            assert!(
                !entry.signature.contains("deriving") && !entry.signature.contains("| mk"),
                "{}",
                entry.signature
            );
        }
        let commented = "theorem target /- where is not syntax here -/ (n : Nat) : n = n := rfl";
        assert_eq!(
            &commented[source::declaration_header_end(commented)..],
            ":= rfl"
        );
    }

    #[test]
    fn signature_name_position_ignores_matching_attribute_text() {
        for declaration in [
            "@[trans]\nprotected def trans : Nat := 0",
            "  @[simp]\n  theorem simp (n : Nat) : n = n := rfl",
            "@[attr αβ]\ndef αβ : Nat := 0",
        ] {
            let entry = source::parse_source(declaration, "Fixture")
                .into_iter()
                .find(|e| matches!(e.kind.as_str(), "def" | "theorem"))
                .unwrap();
            assert!(!entry.signature.contains(']'), "{}", entry.signature);
            assert!(
                entry.signature == "Nat" || entry.signature == "(n : Nat) : n = n",
                "{}",
                entry.signature
            );
        }
    }

    #[test]
    fn declaration_probe_rejects_escaped_names_without_rewriting_them() {
        let error = ProbeRequest::parse(r"Demo.mono\u0027 source").unwrap_err();
        assert!(error.to_string().contains("literal characters"));
        assert!(ProbeRequest::parse("Demo.mono' source").is_ok());
        assert!(ProbeRequest::parse(r"Demo.lean:3 #check s \ t").is_ok());
    }

    #[test]
    fn explicit_generated_source_retains_origin_without_fabricating_signature() {
        let source = "namespace Demo\n@[simp]\n@[to_additive additive]\ntheorem multiplicative (n : Nat) : n = n := rfl\nend Demo\n";
        let hit =
            source::explicit_generator_source_entry(source, "Fixture", "Demo.additive").unwrap();
        assert_eq!(hit.kind, "generator");
        assert!(hit.signature.is_empty());
        assert!(hit.docs.contains("not its generated proof"));
        assert!(hit.body.contains("theorem multiplicative"));
        assert!(
            source::explicit_generator_source_entry(source, "Fixture", "Other.additive").is_none()
        );
        assert!(
            source::explicit_generator_source_entry(
                "-- @[to_additive additive]\ntheorem multiplicative : True := trivial",
                "Fixture",
                "additive"
            )
            .is_none()
        );
        assert!(
            source::explicit_generator_source_entry(
                "@[to_additive]\ntheorem multiplicative : True := trivial",
                "Fixture",
                "additive"
            )
            .is_none()
        );
    }

    #[test]
    fn unsigned_constructor_result_gives_obligation_followup() {
        let run = SearchRun {
            reference: "q1".into(),
            workspace_ref: "w1".into(),
            query: "Demo.Data.mk".into(),
            inference: "exact".into(),
            hits: vec![SearchHit {
                name: "Demo.Data.mk".into(),
                kind: "declaration".into(),
                signature: None,
                module: "Demo".into(),
                path: "Demo.lean".into(),
                line: 1,
                doc: None,
                source: None,
                usages: vec![],
                applicable: false,
                required_import: None,
            }],
            note: None,
            duration_ms: 0,
            created_at: 0,
        };
        let detail = render_static_probe_summary(&run, "constructors");
        assert!(detail.contains("probe Demo.Data fields"), "{detail}");
        assert!(detail.contains("#inspect Demo.Data.mk"), "{detail}");
    }

    #[test]
    fn missing_signature_routes_to_source_without_implying_a_type() {
        let run = SearchRun {
            reference: "q1".into(),
            workspace_ref: "w1".into(),
            query: "Demo.target".into(),
            inference: "exact".into(),
            hits: vec![SearchHit {
                name: "_root_.Demo.target".into(),
                kind: "declaration".into(),
                signature: None,
                module: "Demo".into(),
                path: "Demo.lean".into(),
                line: 1,
                doc: None,
                source: None,
                usages: vec![],
                applicable: false,
                required_import: None,
            }],
            note: Some("source index warming".into()),
            duration_ms: 0,
            created_at: 0,
        };
        let output = render_static_probe_summary(&run, "signature");
        assert!(output.contains("Signature is not indexed"), "{output}");
        assert!(output.contains("mathmux probe Demo.target source"), "{output}");
        let mut file = run.clone();
        file.hits[0].kind = "file".into();
        file.hits[0].path = "Demo Facts.lean".into();
        let output = render_static_probe_summary(&file, "signature");
        assert!(output.contains("File result has no declaration signature"), "{output}");
        assert!(output.contains("mathmux search \"Demo Facts.lean\" outline"), "{output}");
        assert!(!output.contains("not indexed"), "{output}");
        assert!(!output.contains("mathmux probe"), "{output}");
        let mut signed = run;
        signed.hits[0].signature = Some("Nat".into());
        let output = render_static_probe_summary(&signed, "signature");
        assert!(!output.contains("not indexed"), "{output}");
        assert!(!output.contains("warming"), "{output}");
        assert!(!output.contains("Full signature/context"), "{output}");
        signed.hits[0].signature = Some(
            "{X : Type} [TopologicalSpace X] (f : X → X) (hf : Continuous f) : Continuous f".into(),
        );
        let output = render_static_probe_summary(&signed, "signature");
        assert!(output.contains("(hf : Continuous f) : Continuous f"), "{output}");
        assert!(output.contains("[TopologicalSpace X]"), "{output}");
        assert!(!output.contains("Full signature/context"), "{output}");
        signed.hits[0].signature = Some(format!(
            "{}(f : X → X) (hf : Continuous f) : Continuous f",
            "[TopologicalSpace X] ".repeat(20),
        ));
        let output = render_static_probe_summary(&signed, "signature");
        assert!(output.contains("(hf : Continuous f) : Continuous f"), "{output}");
        assert!(output.contains("[context: 20 implicit/typeclass]"), "{output}");
        assert!(output.contains("Full signature/context: mathmux show q1 --all"), "{output}");
        signed.hits[0].signature = Some(format!("(hyp : {}) : True", "Nat → ".repeat(60)));
        let output = render_static_probe_summary(&signed, "signature");
        assert!(output.contains("Full signature/context: mathmux show q1 --all"), "{output}");
    }

    #[test]
    fn dependency_probe_context_explains_project_import_requirement() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path().join("workspace");
        fs::create_dir(&root).unwrap();
        let external = dir.path().join("Dependency.lean");
        fs::write(&external, "").unwrap();
        let link = root.join("Dependency.lean");
        std::os::unix::fs::symlink(&external, &link).unwrap();
        let error = ensure_lean_project_context(&root, &link).unwrap_err();
        assert!(format!("{error:#}").contains("project FILE:LINE"));
        assert!(
            error
                .downcast_ref::<crate::protocol::DiscoveryFailure>()
                .is_some()
        );
        let own = root.join("Own.lean");
        fs::write(&own, "").unwrap();
        assert!(ensure_lean_project_context(&root, &own).is_ok());
    }

    #[test]
    fn attributed_source_navigation_uses_attribute_start_line() {
        let source = "-- ambient context\nvariable (n : Nat)\n\n@[simp]\ntheorem target : True := by\n  trivial";
        assert_eq!(
            declaration_find_from_hit(source, 10, "trivial", "q1"),
            "   12    trivial"
        );
        let outline = declaration_outline_from_hit(source, 10, "theorem");
        assert!(outline.contains("   10  @[simp]"));
        assert!(outline.contains("   11  theorem target"));
    }

    #[test]
    fn declaration_find_uses_file_coordinates_and_labels_ambient_matches() {
        let source = "-- ambient context\nvariable {α : Type}\n\n@[simp] public theorem target : True := by\n  have h : True := by trivial\n  exact h";
        assert_eq!(
            declaration_find_from_hit(source, 20, "exact", "q1"),
            "   22    exact h"
        );
        assert!(declaration_find_from_hit(source, 20, "Type", "q1").starts_with("ambient:"));
        assert!(
            declaration_find_from_hit(source, 20, "missing", "q1").contains("No literal matches")
        );
        let many = format!("theorem target : True := by\n{}", "  -- match\n".repeat(15));
        let found = declaration_find_from_hit(&many, 20, "match", "q1");
        assert!(found.contains("3 matching lines not shown"));
        assert!(found.contains("show q1 --all"));
    }

    #[test]
    fn file_directives_prefer_the_requested_result_over_prior_diagnostics() {
        let detail = "unsolved goals\nDemo.target : Nat\nwarning: prior warning".to_owned();
        let (ok, detail) = decisive_directive_result("term", "Demo.target", false, detail);
        assert!(ok);
        assert_eq!(detail, "Demo.target : Nat");

        let (ok, _) = decisive_directive_result(
            "synth",
            "MissingClass Nat",
            false,
            "failed to synthesize instance of type class\n  MissingClass Nat".into(),
        );
        assert!(!ok);
    }

    #[test]
    fn contract_probes_require_explicit_lean_context() {
        assert!(ProbeRequest::parse("#inspect Nat").is_err());
        assert!(ProbeRequest::parse("#apply Nat.add_zero").is_err());
        assert_eq!(
            ProbeRequest::parse("Demo.lean:8 #apply h")
                .unwrap()
                .directive,
            Some(LeanDirective::Apply("h".into()))
        );
        assert_eq!(
            ProbeRequest::parse("Demo.lean:8 #inspect Nat")
                .unwrap()
                .directive,
            Some(LeanDirective::Inspect("Nat".into()))
        );
        assert_eq!(
            ProbeRequest::parse("Demo.Data assumptions")
                .unwrap()
                .focus
                .as_deref(),
            Some("assumptions")
        );
        assert_eq!(
            ProbeRequest::parse("Demo.lean:8 Demo.Data evidence")
                .unwrap()
                .focus
                .as_deref(),
            Some("evidence")
        );
        assert_eq!(
            ProbeRequest::parse("c1 context").unwrap().focus.as_deref(),
            Some("context")
        );
    }

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
        for facet in ["outline", "declarations", "imports", "dependents"] {
            assert_eq!(
                ProbeRequest::parse(&format!("Demo.lean {facet}"))
                    .unwrap_err()
                    .to_string(),
                format!(
                    "`{facet}` is a source-search facet, not a probe subject; use `mathmux search Demo.lean {facet}`"
                )
            );
            assert_eq!(
                ProbeRequest::parse(&format!("Demo.lean:{facet}"))
                    .unwrap_err()
                    .to_string(),
                format!(
                    "`{facet}` is a source-search facet, not a probe subject; use `mathmux search Demo.lean {facet}`"
                )
            );
        }
        assert_eq!(
            ProbeRequest::parse("Demo/ outline")
                .unwrap_err()
                .to_string(),
            "`outline` is a source-search facet, not a probe subject; use `mathmux search Demo/ outline`"
        );
        assert_eq!(
            ProbeRequest::parse("Demo.lean:42-48 source")
                .unwrap_err()
                .to_string(),
            "source ranges are a search form, not a probe context; use `mathmux search Demo.lean:42-48` for source or `mathmux probe Demo.lean:42 goal` for Lean context"
        );
        assert_eq!(
            ProbeRequest::parse("Demo.lean:42 source")
                .unwrap_err()
                .to_string(),
            "source is a search form at FILE:LINE; use `mathmux search Demo.lean:42` for source or `mathmux probe Demo.lean:42 goal` for Lean context"
        );
        assert_eq!(
            ProbeRequest::parse("c42 --wait").unwrap_err().to_string(),
            "--wait belongs to show; use `mathmux show c42 --wait`"
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
            "declaration ContinuousMap.ext*|ContinuousMap_ext*"
        );
        assert_eq!(
            static_probe_query(None, "ContinuousMap", Some("constructors")).unwrap(),
            "ContinuousMap.mk"
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
            static_probe_query(None, "ContinuousMap", Some("outline")).unwrap(),
            "ContinuousMap source"
        );
        for removed in ["neighborhood", "dependencies", "instances", "coercions"] {
            assert!(
                ProbeRequest::parse(&format!("ContinuousMap {removed}"))
                    .unwrap_err()
                    .to_string()
                    .contains("was removed")
            );
        }
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
            "probe --all is not valid here; use `mathmux show q123 --all` for stored detail"
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
            ProbeRequest::parse("Demo.foo Fiber")
                .unwrap_err()
                .to_string(),
            "unknown declaration focus `Fiber`; try `probe Demo.foo signature`, `probe Demo.foo source`, or `probe Demo.foo usages`"
        );
        let quoted_focus = ProbeRequest::parse("Demo.foo 'source'").unwrap();
        assert_eq!(quoted_focus.subject.as_deref(), Some("Demo.foo"));
        assert_eq!(quoted_focus.focus.as_deref(), Some("source"));
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
        assert_eq!(
            invalid_declaration_focus_message(
                "Demo.value",
                "def",
                "a structure, class, or inductive declaration"
            ),
            "Demo.value is def, not a structure, class, or inductive declaration; valid focuses: signature, source, outline, usages, apply"
        );
        let explicit = ProbeRequest::parse("@Demo.foo outline").unwrap();
        assert_eq!(explicit.subject.as_deref(), Some("Demo.foo"));
        assert_eq!(explicit.focus.as_deref(), Some("outline"));
        assert!(
            ProbeRequest::parse("q123#2 dependencies")
                .unwrap_err()
                .to_string()
                .contains("was removed")
        );
        let local_find = ProbeRequest::parse("Demo.foo find simp only").unwrap();
        assert_eq!(local_find.subject.as_deref(), Some("Demo.foo"));
        assert_eq!(local_find.focus.as_deref(), Some("find:simp only"));
        let selected_find = ProbeRequest::parse("q123#2 find exact").unwrap();
        assert_eq!(
            selected_find.context,
            Some(ProbeContext::Query("q123".into(), 1))
        );
        assert_eq!(selected_find.focus.as_deref(), Some("find:exact"));
        let stored = stored_goal_detail(
            "Demo.lean:7:2: error: type mismatch\n  x\nhas type\n  Nat",
            Some(">    7 | exact x"),
        );
        assert!(stored.starts_with("primary diagnostic\n"));
        assert!(stored.contains(">    7 | exact x"));
        assert_eq!(
            ProbeRequest::parse("c123 goal").unwrap().focus.as_deref(),
            Some("goal")
        );
        assert_eq!(
            ProbeRequest::parse("q123 --all").unwrap_err().to_string(),
            "probe --all is not valid here; use `mathmux show q123 --all` for stored detail"
        );
        assert_eq!(
            ProbeRequest::parse("c123 --all").unwrap_err().to_string(),
            "probe --all is not valid here; use `mathmux probe c123 goal|types|defeq|rewrite|profile`"
        );
        assert_eq!(
            running_check_probe_hint("c123"),
            "check c123 is still running; use `mathmux show c123 --wait`, then retry `mathmux probe c123 goal|types|defeq|rewrite|profile`"
        );
        assert!(is_declaration_header(
            "noncomputable def parameterizedBottThickClutchingCore"
        ));
        assert!(is_declaration_header("private theorem hidden"));
        assert!(!is_declaration_header("  intro i"));
    }

    #[test]
    fn indexed_file_check_accepts_an_exact_declaration_hit() {
        let result = SearchResult {
            hits: vec![SearchHit {
                name: "Demo.target".into(),
                kind: "theorem".into(),
                signature: Some(": True".into()),
                module: "Demo".into(),
                path: "Demo.lean".into(),
                line: 7,
                doc: None,
                source: None,
                usages: Vec::new(),
                applicable: false,
                required_import: None,
            }],
            inference: "exact".into(),
            note: None,
            ok: true,
        };

        assert_eq!(
            indexed_check_hit_from_result(result, "Demo.target").map(|hit| hit.name),
            Some("Demo.target".into())
        );
    }

    #[test]
    fn running_check_probe_redirects_to_bounded_wait() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path().join("root");
        let state_dir = directory.path().join("state");
        std::fs::create_dir_all(&root).unwrap();
        std::fs::create_dir_all(&state_dir).unwrap();
        let repo = Repo {
            root: root.clone(),
            common_git_dir: directory.path().join("git"),
            state_dir: state_dir.clone(),
            socket_path: state_dir.join("daemon.sock"),
            db_path: state_dir.join("state.sqlite3"),
            search_db_path: state_dir.join("search.sqlite3"),
            log_path: state_dir.join("daemon.log"),
            cache_dir: state_dir.join("cache"),
            integration_lock: state_dir.join("integration.lock"),
            validation_lock: state_dir.join("validation.lock"),
            startup_lock: state_dir.join("startup.lock"),
        };
        let state = State::new(repo.db_path.clone()).unwrap();
        let workspace = Workspace {
            reference: "w1".into(),
            name: "demo".into(),
            path: root.clone(),
            branch: "demo".into(),
            model: None,
        };
        state.add_workspace(&workspace).unwrap();
        let checker = Arc::new(Checker::new(repo.clone(), state.clone(), None).unwrap());
        let searcher = Searcher::new(repo, state.clone(), checker, None).unwrap();
        state
            .add_check_run(
                &crate::state::CheckRun {
                    reference: "c123".into(),
                    workspace_ref: workspace.reference.clone(),
                    status: crate::state::CheckStatus::Running,
                    files: Vec::new(),
                    passed: Vec::new(),
                    failed: None,
                    not_checked: Vec::new(),
                    warnings: Vec::new(),
                    linters: Vec::new(),
                    suggestions: Vec::new(),
                    diagnostics: Vec::new(),
                    profile: None,
                    duration_ms: 0,
                    created_at: now_unix_ms(),
                },
                &[],
            )
            .unwrap();

        let error = searcher
            .probe(&workspace, &root, "c123 goal")
            .unwrap_err()
            .to_string();
        assert_eq!(error, running_check_probe_hint("c123"));
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

        let mut ext_run = run.clone();
        ext_run.note = None;
        ext_run.hits.clear();
        ext_run.hits.push(hit(
            "Demo.ext",
            "@[ext] theorem ext (h : True) : True := by\n  trivial",
        ));
        let ext = render_static_probe_summary(&ext_run, "ext");
        assert!(ext.contains("Demo.ext"));
        assert!(!ext.contains(":= by"));

        ext_run.hits.pop();
        let no_ext = render_static_probe_summary(&ext_run, "ext");
        assert!(no_ext.contains("no indexed @[ext] declaration"));

        let source = render_static_probe_summary(&run, "source");
        assert!(source.contains("theorem first"));
        assert!(!source.contains("Demo.second"));

        let outline = render_static_probe_summary(&run, "outline");
        assert!(outline.contains("theorem first"));
        assert!(outline.contains("ref: q1"));

        assert_eq!(
            declaration_outline_from_hit(
                "structure Config where\n  value : Nat\n  label : String",
                20,
                "structure"
            ),
            "   20  structure Config where\n   21    value : Nat\n   22    label : String"
        );
        let simp = render_static_probe_summary(&run, "simp");
        assert!(simp.contains("Demo.second"));
        assert!(!simp.contains("Demo.first"));
        assert!(!simp.contains(":= by"));

        let apply = render_static_probe_summary(&run, "apply");
        assert!(apply.contains("Demo.first"));
        assert!(!apply.contains(":= by"));

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
