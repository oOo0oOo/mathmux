//! Bounded, project-independent evidence retrieval. Indexed text is a lead,
//! never a claim that a theorem is applicable or a premise is inhabited.
use super::*;

const CANDIDATE_LIMIT: usize = 128;

fn identifiers(text: &str) -> Vec<String> {
    static IDENTIFIERS: OnceLock<Regex> = OnceLock::new();
    let re = IDENTIFIERS.get_or_init(|| Regex::new(r"[\p{L}_][\p{L}\p{N}_'.]*").unwrap());
    let mut seen = HashSet::new();
    re.find_iter(text)
        .map(|m| m.as_str().trim_end_matches('.').to_owned())
        .filter(|s| seen.insert(s.clone()))
        .collect()
}

fn bound_input_names(signature: &str, source: Option<&str>) -> HashSet<String> {
    static BINDERS: OnceLock<Regex> = OnceLock::new();
    let binders = BINDERS.get_or_init(|| {
        Regex::new(r"[({⦃]\s*([^:(){}⦃⦄\[\]\n]+)\s*:").expect("valid binder names")
    });
    let mut names = HashSet::new();
    for text in std::iter::once(signature).chain(source) {
        for capture in binders.captures_iter(text) {
            names.extend(identifiers(&capture[1]));
        }
    }
    names
}

fn mentions(text: &str, name: &str) -> bool {
    let name = name.trim_start_matches("_root_.");
    identifiers(text)
        .iter()
        .any(|s| s.trim_start_matches("_root_.") == name)
}

/// Top-level declaration result, retaining arrows so hypotheses cannot be
/// mistaken for a negative conclusion. This is deliberately conservative.
fn conclusion(signature: &str) -> &str {
    let signature = signature
        .strip_prefix("[private]")
        .unwrap_or(signature)
        .trim_start();
    let mut depth = 0i32;
    for (i, c) in signature.char_indices() {
        match c {
            '(' | '[' | '{' | '⦃' => depth += 1,
            ')' | ']' | '}' | '⦄' => depth -= 1,
            ':' if depth == 0 => return signature[i + 1..].trim(),
            _ => (),
        }
    }
    signature.trim()
}

fn top_level_relation(result: &str) -> bool {
    let mut depth = 0i32;
    for c in result.chars() {
        match c {
            '(' | '[' | '{' | '⦃' => depth += 1,
            ')' | ']' | '}' | '⦄' => depth -= 1,
            '→' | '↔' | '≃' | '≅' | '↪' | '×' | '=' | '<' | '>' if depth == 0 => {
                return true;
            }
            _ => (),
        }
    }
    false
}

fn unparen(mut text: &str) -> &str {
    loop {
        text = text.trim();
        if !text.starts_with('(') || !text.ends_with(')') {
            return text;
        }
        let mut depth = 0;
        let mut wraps_all = true;
        for (i, c) in text.char_indices() {
            if c == '(' {
                depth += 1;
            }
            if c == ')' {
                depth -= 1;
            }
            if depth == 0 && i + c.len_utf8() < text.len() {
                wraps_all = false;
                break;
            }
        }
        if !wraps_all {
            return text;
        }
        text = &text[1..text.len() - 1];
    }
}

fn direct_subject(text: &str, name: &str) -> bool {
    let text = unparen(text);
    !top_level_relation(text)
        && identifiers(text).first().is_some_and(|head| {
            head.trim_start_matches("_root_.") == name.trim_start_matches("_root_.")
                || head == name.rsplit('.').next().unwrap_or(name)
        })
}

fn relation(signature: &str, name: &str) -> Option<&'static str> {
    let result = unparen(conclusion(signature));
    let leaf = name.rsplit('.').next().unwrap_or(name);
    if !mentions(result, name) && !mentions(result, leaf) {
        return None;
    }
    let negative = result
        .strip_prefix('¬')
        .or_else(|| result.strip_prefix("Not "));
    if negative
        .and_then(|s| unparen(s).strip_prefix("Nonempty "))
        .is_some_and(|s| direct_subject(s, name))
    {
        Some("obstruction candidate")
    } else if result
        .strip_prefix("Subsingleton ")
        .is_some_and(|s| direct_subject(s, name))
    {
        Some("subsingleton candidate")
    } else if result
        .strip_prefix("IsEmpty ")
        .is_some_and(|s| direct_subject(s, name))
    {
        Some("emptiness candidate")
    } else if direct_subject(result, name)
        || result
            .strip_prefix("Nonempty ")
            .is_some_and(|s| direct_subject(s, name))
    {
        Some("construction candidate")
    } else {
        Some("related law candidate")
    }
}

/// Split only outer binders. Nested function types and default values stay intact.
fn signature_binders(signature: &str) -> Vec<&str> {
    let mut rest = signature.trim();
    let mut binders = Vec::new();
    while rest.starts_with(['(', '{', '[', '⦃']) {
        let mut depth = 0i32;
        let mut end = None;
        for (i, c) in rest.char_indices() {
            match c {
                '(' | '{' | '[' | '⦃' => depth += 1,
                ')' | '}' | ']' | '⦄' => {
                    depth -= 1;
                    if depth == 0 {
                        end = Some(i + c.len_utf8());
                        break;
                    }
                }
                _ => (),
            }
        }
        let Some(end) = end else {
            break;
        };
        binders.push(&rest[..end]);
        rest = rest[end..].trim_start();
    }
    binders
}

fn input_heads(signature: &str) -> Vec<String> {
    let binders = signature_binders(signature);
    binders
        .iter()
        .filter(|b| b.starts_with('('))
        .chain(binders.iter().filter(|b| !b.starts_with('(')))
        .filter_map(|binder| {
            let start = binder.chars().next().unwrap().len_utf8();
            let end = binder.chars().last().unwrap().len_utf8();
            let interior = &binder[start..binder.len() - end];
            let ty = interior
                .split_once(':')
                .map_or(interior, |(_, ty)| ty)
                .trim();
            identifiers(ty).into_iter().next()
        })
        .collect()
}

fn construction_needs_subject(signature: &str, subject: &str) -> bool {
    signature_binders(signature).iter().any(|binder| {
        let first = binder.chars().next().unwrap().len_utf8();
        let last = binder.chars().last().unwrap().len_utf8();
        binder[first..binder.len() - last]
            .split_once(':')
            .is_some_and(|(_, ty)| direct_subject(ty.trim(), subject))
    })
}

fn wrapped_contract_line(label: &str, text: &str) -> String {
    let mut result = String::new();
    let mut line = label.to_owned();
    for word in text.split_whitespace() {
        if line.chars().count() + word.chars().count() + 1 > 180 {
            result.push_str(&line);
            result.push('\n');
            line = "  ".into();
        }
        if !line.ends_with(' ') {
            line.push(' ');
        }
        line.push_str(word);
    }
    result.push_str(&line);
    result.push('\n');
    result
}

fn assumption_signature(signature: &str) -> String {
    let (visibility, signature) =
        signature
            .strip_prefix("[private]")
            .map_or(("", signature), |signature| {
                (
                    "visibility: private; not a public API in importing modules.\n",
                    signature.trim_start(),
                )
            });
    let binders = signature_binders(signature);
    if binders.is_empty() {
        return format!(
            "{visibility}{}",
            wrapped_contract_line("signature (premises retained):", signature)
        );
    }
    let result = conclusion(signature);
    let mut detail = if result == signature.trim() {
        String::new()
    } else {
        wrapped_contract_line("result (indexed):", result)
    };
    detail.push_str(visibility);
    detail.push_str("signature (premises retained); explicit inputs first:\n");
    for binder in binders.iter().filter(|b| b.starts_with('(')) {
        detail.push_str(&wrapped_contract_line("input:", binder));
    }
    for binder in binders.iter().filter(|b| !b.starts_with('(')) {
        detail.push_str(&wrapped_contract_line("implicit/context:", binder));
    }
    detail.push_str(
        "Section parameters may be implicit; #inspect resolves the full Lean contract.\n",
    );
    detail
}

fn contract_exact_hit(
    rows: Vec<IndexedRow>,
    subject: &str,
    workspace: &Workspace,
) -> Result<SearchHit> {
    let rows = rows
        .into_iter()
        .filter(|r| !matches!(r.kind.as_str(), "file" | "imports"))
        .collect();
    resolved_exact_candidates(ranked_exact_candidates(rows,subject,workspace),subject)
        .and_then(merge_exact_candidates)
        .map(|c| c.hit)
        .with_context(|| format!("exact declaration unavailable or ambiguous: {subject}; search the qualified name first"))
}

impl Searcher {
    fn contract_rows(&self, workspace: &Workspace, terms: &[String]) -> Result<Vec<IndexedRow>> {
        let (scopes, _) = self.search_scopes(workspace)?;
        let connection = self.open()?;
        install_active_scopes(&connection, &scopes)?;
        let query = terms
            .iter()
            .take(8)
            .map(|s| format!("signature : \"{}\"", s.replace('"', "\"\"")))
            .collect::<Vec<_>>()
            .join(" OR ");
        if query.is_empty() {
            return Ok(Vec::new());
        }
        let sql = ranked_rows_sql(&format!(
            "WHERE search_fts MATCH ?1 AND kind NOT IN ('file', 'imports', 'field') AND signature <> ''
             AND owner IN (SELECT owner FROM active_search_scopes)
             ORDER BY rank LIMIT {CANDIDATE_LIMIT}"
        ));
        let rows = connection
            .prepare(&sql)?
            .query_map([query], indexed_row_from_row)?
            .collect::<rusqlite::Result<Vec<_>>>()?;
        Ok(rows)
    }

    fn risk_rows(&self, workspace: &Workspace, subject: &str) -> Result<Vec<IndexedRow>> {
        let (scopes, _) = self.search_scopes(workspace)?;
        let connection = self.open()?;
        install_active_scopes(&connection, &scopes)?;
        let leaf = subject
            .rsplit('.')
            .next()
            .unwrap_or(subject)
            .replace('"', "\"\"");
        let query =
            format!("signature : \"{leaf}\" AND signature : (Nonempty OR Subsingleton OR IsEmpty)");
        let sql = ranked_rows_sql(
            "WHERE search_fts MATCH ?1 AND kind NOT IN ('file','imports','field')
            AND owner IN (SELECT owner FROM active_search_scopes) ORDER BY rank LIMIT 24",
        );
        let rows = connection
            .prepare(&sql)?
            .query_map([query], indexed_row_from_row)?
            .collect::<rusqlite::Result<Vec<_>>>()?;
        Ok(rows
            .into_iter()
            .filter(|r| {
                matches!(
                    relation(&r.signature, subject),
                    Some(
                        "obstruction candidate" | "subsingleton candidate" | "emptiness candidate"
                    )
                )
            })
            .collect())
    }

    pub(super) fn prioritize_requested_risk(
        &self,
        workspace: &Workspace,
        run: &mut SearchRun,
    ) -> Result<()> {
        let terms = run.query.split_whitespace().collect::<Vec<_>>();
        if terms.len() != 2 {
            return Ok(());
        }
        let Some(index) = terms
            .iter()
            .position(|t| matches!(t.to_ascii_lowercase().as_str(), "subsingleton" | "isempty"))
        else {
            return Ok(());
        };
        let subject = terms[1 - index];
        let mut names = run
            .hits
            .iter()
            .filter(|h| {
                matches!(
                    h.kind.as_str(),
                    "def" | "abbrev" | "structure" | "class" | "inductive"
                )
            })
            .map(|h| h.name.trim_start_matches("_root_."))
            .filter(|n| {
                n.eq_ignore_ascii_case(subject)
                    || n.rsplit('.')
                        .next()
                        .is_some_and(|leaf| leaf.eq_ignore_ascii_case(subject))
            })
            .collect::<Vec<_>>();
        names.sort();
        names.dedup();
        if names.len() != 1 {
            return Ok(());
        }
        let kind = if terms[index].eq_ignore_ascii_case("subsingleton") {
            "subsingleton candidate"
        } else {
            "emptiness candidate"
        };
        let candidates = self
            .risk_rows(workspace, names[0])?
            .into_iter()
            .filter(|r| relation(&r.signature, names[0]) == Some(kind))
            .take(3)
            .map(|r| SearchHit {
                name: r.name,
                kind: r.kind,
                signature: Some(r.signature),
                module: r.module,
                path: r.path,
                line: r.line,
                doc: Some(
                    "source candidate; specialization and premises require verification".into(),
                ),
                source: Some(r.body),
                usages: Vec::new(),
                applicable: false,
                required_import: None,
            })
            .collect::<Vec<_>>();
        if candidates.is_empty() {
            return Ok(());
        }
        let lead = &candidates[0];
        let guidance = format!(
            "Requested property found in source; not verified applicability.\nInspect: mathmux search {}:{}; use #synth in the relevant Lean context.",
            lead.path, lead.line
        );
        run.hits = candidates;
        run.inference = "contract-property".into();
        let prior = run.note.take().unwrap_or_default();
        run.note = Some(format!("{prior}\n{guidance}").trim().into());
        Ok(())
    }

    pub(super) fn probe_contract(
        &self,
        workspace: &Workspace,
        _cwd: &Path,
        subject: &str,
        focus: &str,
    ) -> Result<String> {
        let (scopes, warming) = self.search_scopes(workspace)?;
        let mut hit =
            contract_exact_hit(self.exact_candidates(subject, &scopes)?, subject, workspace)?;
        self.enrich_exact_source(&mut hit, &scopes)?;
        let name = hit.name.trim_start_matches("_root_.");
        let mut detail = format!(
            "{name}\nsource evidence: {}:{}; index warming: {warming}\n",
            hit.path, hit.line
        );
        if focus == "assumptions" {
            detail.push_str(&assumption_signature(
                hit.signature.as_deref().unwrap_or("unavailable"),
            ));
        } else {
            detail.push_str(&format!(
                "signature (premises retained):\n{}\n",
                hit.signature.as_deref().unwrap_or("unavailable")
            ));
        }
        if focus == "assumptions" {
            detail.push_str("A conditional signature does not construct its inputs. Inspect selected input types and fields, then test the intended application.\n");
            if matches!(hit.kind.as_str(), "structure" | "class" | "abbrev") {
                detail.push_str(&format!("fields: mathmux probe {name} fields\n"));
            }
            let terms = input_heads(hit.signature.as_deref().unwrap_or(""));
            let mut shown = 0;
            for term in terms
                .into_iter()
                .filter(|t| t.contains('.') || t.chars().next().is_some_and(char::is_uppercase))
                .take(8)
            {
                if let Ok(input) =
                    contract_exact_hit(self.exact_candidates(&term, &scopes)?, &term, workspace)
                    && input.name != hit.name
                    && matches!(input.kind.as_str(), "structure" | "class" | "abbrev")
                {
                    detail.push_str(&format!(
                        "input API: {} — mathmux probe {} fields\n",
                        input.name, input.name
                    ));
                    shown += 1;
                    if shown == 3 {
                        break;
                    }
                }
            }
            detail.push_str("next: mathmux probe FILE:LINE '#inspect NAME_OR_TERM' for full premises; #apply TERM tests the intended use.\n");
        } else {
            let leaf = name.rsplit('.').next().unwrap_or(name);
            let mut rows = self.risk_rows(workspace, name)?;
            rows.extend(self.contract_rows(workspace, &[leaf.to_owned()])?);
            let mut related = rows
                .into_iter()
                .filter(|r| r.name.trim_start_matches("_root_.") != name)
                .filter_map(|r| relation(&r.signature, name).map(|kind| (kind, r)))
                .collect::<Vec<_>>();
            related.sort_by_key(|(kind, r)| {
                (
                    match *kind {
                        "obstruction candidate"
                        | "emptiness candidate"
                        | "subsingleton candidate" => 0,
                        "construction candidate" => 1,
                        _ => 2,
                    },
                    r.name.clone(),
                )
            });
            let mut seen = HashSet::new();
            related.retain(|(_, r)| seen.insert(r.name.clone()));
            for (kind, row) in related.iter().take(3) {
                detail.push_str(&format!(
                    "\n{kind}: {}\n{}:{}\n{}\n",
                    row.name, row.path, row.line, row.signature
                ));
                if row.kind == "instance" && row.name.contains("instance@") {
                    detail.push_str(&format!(
                        "verify: mathmux probe {}:{} '#synth {}'\n",
                        row.path,
                        row.line,
                        conclusion(&row.signature)
                    ));
                }
            }
            if related.is_empty() {
                detail.push_str("No construction or obstruction found in this bounded index search; this is not an existence verdict.\n");
            }
            detail.push_str("Candidates are indexed source, not verified applicability. Hypotheses and namespace resolution matter. Verify a candidate in your exact Lean context with #inspect and #apply; check remains certification.\n");
        }
        if let Some(notice) = self.verified_contract_notice(workspace, name)? {
            detail.push_str(&format!("\n{notice}\n"));
        }
        detail.push_str(&self.authored_route_detail(workspace, name)?);
        self.store_probe_result(
            workspace,
            &format!("{subject} {focus}"),
            "contract",
            detail,
            Some(&hit.path),
            hit.line,
        )
    }

    pub(super) fn probe_examples(
        &self,
        workspace: &Workspace,
        subject: &str,
        location: Option<&str>,
    ) -> Result<String> {
        let (scopes, _) = self.search_scopes(workspace)?;
        let hit = contract_exact_hit(self.exact_candidates(subject, &scopes)?, subject, workspace)?;
        let name = hit.name.trim_start_matches("_root_.");
        let leaf = name.rsplit('.').next().unwrap_or(name);
        let mut candidates = Vec::new();
        for route in super::evidence::routes(workspace, name)? {
            for example in route.examples {
                candidates.extend(
                    self.exact_candidates(&example, &scopes)?
                        .into_iter()
                        .filter(|r| r.kind != "field")
                        .map(|r| (0usize, r)),
                );
            }
        }
        candidates.extend(
            self.contract_rows(workspace, &[leaf.to_owned()])?
                .into_iter()
                .filter(|r| {
                    relation(&r.signature, name) == Some("construction candidate")
                        && r.name.trim_start_matches("_root_.") != name
                })
                .map(|r| {
                    (
                        10 + if r.signature.starts_with("[private]") {
                            2000
                        } else {
                            0
                        } + if construction_needs_subject(&r.signature, name) {
                            1000
                        } else {
                            0
                        } + r
                            .signature
                            .chars()
                            .filter(|c| matches!(c, '(' | '[' | '{' | '⦃'))
                            .count(),
                        r,
                    )
                }),
        );
        candidates.sort_by(|a, b| {
            a.0.cmp(&b.0)
                .then(a.1.signature.len().cmp(&b.1.signature.len()))
                .then(a.1.name.cmp(&b.1.name))
        });
        let mut seen = HashSet::new();
        candidates.retain(|(_, r)| !r.signature.is_empty() && seen.insert(r.name.clone()));
        let context = location.unwrap_or("FILE:LINE");
        let hits = candidates
            .into_iter()
            .take(3)
            .map(|(_, row)| SearchHit {
                name: row.name,
                kind: row.kind,
                signature: Some(row.signature),
                module: row.module,
                path: row.path,
                line: row.line,
                doc: (!row.docs.is_empty()).then_some(row.docs),
                source: Some(row.body),
                usages: Vec::new(),
                applicable: false,
                required_import: None,
            })
            .collect::<Vec<_>>();
        let reference = self.state.next_reference(ReferenceKind::Query)?;
        let mut note = format!(
            "Existing construction candidates for {name}; project selections are advisory.\nRanked by indexed inputs; hidden prerequisites remain. No inhabitability conclusion follows from absence.\nInspect one: mathmux probe {reference}#1 assumptions; test {context} '#check (TERM : EXPECTED_TYPE)'."
        );
        for (index, hit) in hits.iter().enumerate() {
            if hit
                .signature
                .as_deref()
                .is_some_and(|s| s.starts_with("[private]"))
            {
                note.push_str(&format!("\n{reference}#{} is private: inspect its source for a public construction; its displayed name is not a public API in importing modules.", index + 1));
            }
            if hit
                .signature
                .as_deref()
                .is_some_and(|s| construction_needs_subject(s, name))
            {
                note.push_str(&format!(
                    "\n{reference}#{} requires an existing {name} input.",
                    index + 1
                ));
            }
        }
        if hits.is_empty() {
            note = format!(
                "No construction found in the bounded index for {name}; this is not an inhabitability verdict. Try {context} '#check (TERM : EXPECTED_TYPE)'."
            );
        }
        let run = SearchRun {
            reference: reference.clone(),
            workspace_ref: workspace.reference.clone(),
            query: format!("{subject} examples"),
            inference: "probe-examples".into(),
            hits,
            note: Some(note),
            duration_ms: 0,
            created_at: now_unix_ms(),
        };
        self.state.add_search(&run)?;
        Ok(render_summary(&run))
    }

    pub(super) fn input_obstruction_notice(
        &self,
        workspace: &Workspace,
        signature: &str,
        source: Option<&str>,
    ) -> Result<Option<String>> {
        let bound = bound_input_names(signature, source);
        let (scopes, _) = self.search_scopes(workspace)?;
        let mut seen = HashSet::new();
        for binder in signature_binders(signature)
            .into_iter()
            .filter(|b| b.starts_with('('))
            .take(3)
        {
            let Some((_, ty)) = binder.split_once(':') else {
                continue;
            };
            let Some(head) = identifiers(ty).into_iter().next() else {
                continue;
            };
            let context_incomplete =
                source.is_none_or(|source| source.contains("earlier ambient commands omitted"));
            if (context_incomplete && !head.contains('.'))
                || bound.contains(&head)
                || !seen.insert(head.clone())
            {
                continue;
            }
            let Ok(hit) =
                contract_exact_hit(self.exact_candidates(&head, &scopes)?, &head, workspace)
            else {
                continue;
            };
            if let Some((evidence, statement)) =
                self.direct_obstruction_candidate(workspace, &hit.name)?
            {
                return Ok(Some(format!(
                    "input type {} has source contract evidence (unverified): {evidence}\n{}\nCompare the specialization and premises with your inputs; probe {} evidence",
                    hit.name,
                    truncate_line(&statement, 240),
                    hit.name
                )));
            }
        }
        Ok(None)
    }

    pub(super) fn direct_obstruction_candidate(
        &self,
        workspace: &Workspace,
        subject: &str,
    ) -> Result<Option<(String, String)>> {
        Ok(self
            .risk_rows(workspace, subject)?
            .into_iter()
            .next()
            .map(|r| {
                let label = relation(&r.signature, subject).unwrap_or("source candidate");
                (
                    format!("{label}: {} ({}:{})", r.name, r.path, r.line),
                    r.signature,
                )
            }))
    }

    pub(super) fn probe_verified_evidence(
        &self,
        workspace: &Workspace,
        subject: &str,
        path: &Path,
        line: u64,
    ) -> Result<String> {
        ensure!(
            line > 0,
            "evidence verification requires an explicit position"
        );
        let (scopes, _) = self.search_scopes(workspace)?;
        let mut rows = self
            .risk_rows(workspace, subject)?
            .into_iter()
            .filter(|r| relation(&r.signature, subject) == Some("obstruction candidate"))
            .collect::<Vec<_>>();
        for route in super::evidence::routes(workspace, subject)? {
            if let Some(name) = route.obstruction {
                rows.extend(self.exact_candidates(&name, &scopes)?);
            }
        }
        rows.sort_by(|a, b| a.name.cmp(&b.name));
        rows.dedup_by(|a, b| a.name == b.name);
        let before = super::evidence::snapshot(workspace, path)?;
        let mut detail = format!("Obstruction inspection at {}:{line}\n", path.display());
        let mut inspection_ok = true;
        let mut verified = None;
        let started = Instant::now();
        for row in rows.iter().take(3) {
            if started.elapsed() > std::time::Duration::from_secs(30) {
                detail.push_str(
                    "Candidate inspection budget exhausted; remaining candidates were not tried.\n",
                );
                break;
            }
            let (ok, payload) = self
                .checker
                .probe_context(workspace, path, line, 0, "inspect_evidence", &row.name)
                .context(crate::protocol::DiscoveryFailure::Infrastructure)?;
            inspection_ok = ok;
            if ok {
                let evidence: super::evidence::LeanEvidence =
                    serde_json::from_str(&payload).context("invalid structured Lean evidence")?;
                detail.push_str(&format!(
                    "candidate: {}\nLean inspection succeeded:\n{}\n",
                    row.name, evidence.detail
                ));
                if evidence.trusted()
                    && evidence.subject.as_deref().is_some_and(|s| {
                        s == subject.trim_start_matches("_root_.")
                            || s.rsplit('.').next() == Some(subject)
                    })
                {
                    // Canonical subject comes from Lean, never from a leaf-name guess.
                    verified = Some(evidence);
                } else {
                    detail.push_str("Not cached as a verified obstruction: inspect the actual subject and axiom dependencies.\n");
                }
            } else {
                detail.push_str(&format!("Lean inspection failed:\n{payload}\n"));
            }
            if verified.is_some() {
                break;
            }
        }
        detail.push_str("Match every hypothesis and specialization; this inspection is not a check certificate.\n");
        if rows.is_empty() {
            detail.push_str("No direct negative-existence candidate found in the bounded index. This is not evidence of inhabitability.\n");
        }
        detail.push_str(&self.authored_route_detail(workspace, subject)?);
        let rendered = self.store_probe_result(
            workspace,
            &format!("{subject} evidence"),
            "obstruction-inspection",
            detail,
            path.to_str(),
            line,
        )?;
        if let Some(evidence) = verified
            && super::evidence::snapshot(workspace, path)? == before
            && let Some(reference) = rendered.lines().rev().find_map(|l| l.strip_prefix("ref: "))
        {
            let summary = format!(
                "premises: {}\nconclusion: {}",
                evidence.premises.join("; "),
                evidence.conclusion
            );
            let relative = path
                .strip_prefix(&workspace.path)
                .unwrap_or(path)
                .to_string_lossy();
            self.state.add_contract_evidence(
                reference,
                evidence.subject.as_deref().unwrap(),
                &evidence.declaration,
                &relative,
                &before,
                &summary,
            )?;
        }
        if inspection_ok {
            Ok(rendered)
        } else {
            bail!(rendered)
        }
    }

    pub(super) fn failure_context(
        &self,
        workspace: &Workspace,
        diagnostic: &str,
        path: Option<&str>,
    ) -> Result<String> {
        if ![
            "type mismatch",
            "definitionally equal",
            "failed to synthesize",
            "Type mismatch",
        ]
        .iter()
        .any(|s| diagnostic.contains(s))
        {
            return Ok("\nNo focused type-conversion retrieval for this diagnostic.".into());
        }
        let focused = diagnostic_type_detail(diagnostic)
            .or_else(|| diagnostic_defeq_detail(diagnostic))
            .unwrap_or_else(|| diagnostic.to_owned());
        let mut terms = identifiers(&focused)
            .into_iter()
            .filter(|s| {
                (s.contains('.') || s.chars().next().is_some_and(char::is_uppercase))
                    && s.chars().count() > 1
                    && !s.ends_with("lean")
                    && !matches!(
                        s.as_str(),
                        "Type" | "Sort" | "Prop" | "Hint" | "Application"
                    )
            })
            .take(6)
            .collect::<Vec<_>>();
        let (scopes, _) = self.search_scopes(workspace)?;
        // Recover hidden representation types from the actual callee, rather
        // than guessing a coercion namespace from mathematical vocabulary.
        if let Some((_, application)) = diagnostic.split_once("in the application") {
            for name in identifiers(application)
                .into_iter()
                .filter(|s| s.contains('.'))
                .take(2)
            {
                for row in self
                    .exact_candidates(&name, &scopes)?
                    .into_iter()
                    .filter(|r| !r.signature.is_empty())
                    .take(1)
                {
                    for term in identifiers(&row.signature).into_iter().filter(|s| {
                        s.chars().count() > 1
                            && s.chars().next().is_some_and(char::is_uppercase)
                            && !matches!(s.as_str(), "Type" | "Sort" | "Prop")
                    }) {
                        if !terms.contains(&term) {
                            terms.push(term);
                        }
                        if terms.len() >= 8 {
                            break;
                        }
                    }
                }
            }
        }
        terms.truncate(8);
        let mut candidates = self.contract_rows(workspace, &terms)?;
        // Reserve retrieval for small application laws; otherwise one long
        // signature matching many ambient types can crowd them all out.
        for term in terms.iter().filter(|t| t.contains('.')).take(3) {
            candidates.extend(self.exact_candidates(&format!("{term}_apply"), &scopes)?);
            candidates.extend(self.exact_candidates(&format!("{term}.apply"), &scopes)?);
        }
        if !terms.is_empty() && focused.contains('↑') && focused.contains("⁻¹") {
            let connection = self.open()?;
            install_active_scopes(&connection, &scopes)?;
            let type_terms = terms
                .iter()
                .map(|s| format!("signature : \"{}\"", s.replace('"', "\"\"")))
                .collect::<Vec<_>>()
                .join(" OR ");
            let query = format!("name : (coe AND inv) AND ({type_terms})");
            let sql = ranked_rows_sql(
                "WHERE search_fts MATCH ?1
                AND signature <> '' AND owner IN (SELECT owner FROM active_search_scopes) ORDER BY rank LIMIT 24",
            );
            candidates.extend(
                connection
                    .prepare(&sql)?
                    .query_map([query], indexed_row_from_row)?
                    .collect::<rusqlite::Result<Vec<_>>>()?,
            );
        }
        let import_context = path.and_then(|p| {
            self.import_context(
                workspace,
                &scopes,
                self.base_scopes(workspace).1,
                Some(Path::new(p)),
            )
        });
        let mut rows = candidates
            .into_iter()
            .filter(|r| matches!(r.kind.as_str(), "theorem" | "lemma"))
            .map(|r| {
                let overlap = terms
                    .iter()
                    .filter(|term| mentions(&r.signature, term))
                    .count();
                let conversion = ["↑", "⁻¹", "⇑"]
                    .iter()
                    .filter(|symbol| focused.contains(**symbol) && r.signature.contains(**symbol))
                    .count();
                let direct_law = terms.iter().any(|t| {
                    r.name.ends_with(&format!("{t}_apply"))
                        || r.name.ends_with(&format!("{t}.apply"))
                });
                let score = (overlap.min(2) * 2 + conversion * 4 + usize::from(direct_law) * 12)
                    .saturating_sub((r.signature.chars().count() / 200).min(6));
                let accessible = import_context
                    .as_ref()
                    .is_some_and(|c| c.accessible.contains(&r.module));
                (
                    score + usize::from(accessible) * 2,
                    overlap + usize::from(direct_law),
                    r,
                )
            })
            .filter(|(score, overlap, _)| *overlap > 0 && *score >= 4)
            .map(|(score, _, row)| (score, row))
            .collect::<Vec<_>>();
        rows.sort_by(|a, b| {
            b.0.cmp(&a.0)
                .then(a.1.signature.len().cmp(&b.1.signature.len()))
                .then(a.1.name.cmp(&b.1.name))
        });
        let mut seen = HashSet::new();
        rows.retain(|(_, r)| seen.insert(r.name.clone()));
        let mut detail = format!("\n{focused}\n");
        if !rows.is_empty() {
            detail.push_str(
                "\nConversion/law candidates (signature overlap; applicability unverified):\n",
            );
            for (_, row) in rows.iter().take(3) {
                let availability = match &import_context {
                    Some(c) if c.accessible.contains(&row.module) => {
                        "available through imports".to_owned()
                    }
                    Some(_) => format!("import may be required: {}", row.module),
                    None => "import availability unknown".into(),
                };
                detail.push_str(&format!(
                    "{} : {}\n  {}:{}; {availability}; probe {} source\n",
                    row.name,
                    truncate_line(&row.signature, 250),
                    row.path,
                    row.line,
                    row.name
                ));
            }
        }
        if let Some((_, row)) = rows.first() {
            let (scopes, _) = self.search_scopes(workspace)?;
            if let Some(usage) = self.usages(&row.name, &scopes, workspace)?.first() {
                detail.push_str(&format!(
                    "usage: {}:{}{}\n",
                    usage.path,
                    usage.line,
                    usage
                        .context
                        .as_deref()
                        .map(|c| format!(" in {c}"))
                        .unwrap_or_default()
                ));
                let source_path = workspace.path.join(&usage.path);
                if let Ok(source) = fs::read_to_string(source_path)
                    && let Some(line) = source.lines().nth(usage.line.saturating_sub(1) as usize)
                {
                    detail.push_str(&format!("  {}\n", truncate_line(line.trim(), 180)));
                }
            }
        }
        if let Some(path) = path {
            detail.push_str(&format!(
                "\nTest in explicit context: mathmux probe {path}:LINE '#apply TERM'\n"
            ));
        }
        Ok(detail)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn examples_distinguish_existing_subject_inputs_from_other_requirements() {
        assert!(construction_needs_subject(
            "(f : Demo.Data Nat) : Demo.Data Nat",
            "Demo.Data"
        ));
        assert!(!construction_needs_subject(
            "(n : Nat) : Demo.Data Nat",
            "Demo.Data"
        ));
        assert!(!construction_needs_subject(
            "(f : X → Demo.Data Nat) : Demo.Data Nat",
            "Demo.Data"
        ));
    }

    #[test]
    fn evidence_does_not_resolve_bound_types_as_global_names() {
        let bound = bound_input_names(
            "(m : E) (d : Demo.Data E) : True",
            Some("-- ambient context\nvariable {E F : Type*}\nvariable [NormedSpace ℝ E]"),
        );
        assert!(bound.contains("E") && bound.contains("F") && bound.contains("m"));
        assert!(!bound.contains("Demo.Data"));
        assert!(bound_input_names("{Vector : Type} (v : Vector) : True", None).contains("Vector"));
    }

    #[test]
    fn warming_exact_search_never_claims_absence_or_suggests_name_repair() {
        let run = SearchRun {
            reference: "q1".into(),
            workspace_ref: "w1".into(),
            query: "Demo.exists".into(),
            inference: "exact-miss".into(),
            hits: Vec::new(),
            note: Some("exact declaration not found: Demo.exists\nsource index warming".into()),
            duration_ms: 0,
            created_at: 0,
        };
        let output = render_summary(&run);
        assert!(output.contains("absence not established"), "{output}");
        assert!(!output.contains("exact declaration not found"), "{output}");
        assert!(!output.contains("next: mathmux search"), "{output}");
    }

    #[test]
    fn apply_difference_excludes_repeated_local_context() {
        let diagnostic = "Tactic `apply` failed: could not unify the type of `h`\n  D.index = supplied D\nwith the goal\n  D.index = target D\n\nn : Nat\nh : True";
        let focused = diagnostic_apply_detail(diagnostic).unwrap();
        assert!(focused.contains("actual: supplied"), "{focused}");
        assert!(focused.contains("expected: target"), "{focused}");
        assert!(!focused.contains("n : Nat"));
    }

    #[test]
    fn constructions_exclude_maps_and_equivalences_out_of_the_type() {
        for signature in [
            "¬ Nonempty (Wrapper Demo.Data)",
            "Subsingleton (Demo.Data → Nat)",
            "Demo.Data →+ ℤ",
            "Demo.Data ≃+ Other",
            "Demo.Data = Other",
            "Demo.Data × Other",
        ] {
            assert_eq!(
                relation(signature, "Demo.Data"),
                Some("related law candidate")
            );
        }
        assert_eq!(
            relation("(f : X → Y) : Demo.Data", "Demo.Data"),
            Some("construction candidate")
        );
        assert_eq!(
            relation("Subsingleton (Demo.Data PUnit)", "Demo.Data"),
            Some("subsingleton candidate")
        );
        assert_eq!(
            relation("(h : Subsingleton (Demo.Data PUnit)) : True", "Demo.Data"),
            None
        );
        assert_eq!(
            input_heads("⦃X : Type⦄ (d : Demo.Data X) : True")[0],
            "Demo.Data"
        );
    }

    #[test]
    fn explicit_contract_inputs_survive_long_signatures() {
        let signature = "{X : Type} [TopologicalSpace X] (d : BundleData X) (f : (x : X) → X) (hBridge : actualIndex d = suppliedIndex d) : actualIndex d = targetIndex d";
        let detail = assumption_signature(signature);
        assert!(detail.starts_with("result (indexed): actualIndex d = targetIndex d"));
        assert!(detail.contains("input: (hBridge : actualIndex d = suppliedIndex d)"));
        assert!(detail.find("input: (d").unwrap() < detail.find("implicit/context:").unwrap());
        assert_eq!(signature_binders(signature).len(), 5);
        assert_eq!(input_heads(signature)[0], "BundleData");
        assert!(!input_heads(signature).contains(&"TopologicalSpace X".to_owned()));
    }

    #[test]
    fn contract_evidence_uses_active_index_and_preserves_hypotheses() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path().join("root");
        let state_dir = dir.path().join("state");
        fs::create_dir_all(&root).unwrap();
        fs::create_dir_all(&state_dir).unwrap();
        fs::write(root.join("Demo.lean"), "namespace Demo\nstructure Data (n : Nat) where\n  value : Fin n\ntheorem impossible (h : n = 0) : ¬ Nonempty (Data n) := by sorry\ndef construct (h : 0 < n) : Data n := sorry\ndef transform (d : Data n) : Data n := d\nprivate def hidden : Data n := sorry\ntheorem conditional (h : ¬ Nonempty (Data n)) : True := trivial\ninstance : Subsingleton (Data 1) := sorry\nstructure Container where\n  item : Data 1\nstructure Derived extends Container where\n  good : True\nstructure InheritedOnly extends Container\nend Demo\n").unwrap();
        fs::write(root.join("API.lean"), "namespace ContinuousMap\ntheorem const_apply (b : β) (a : α) : const α b a = b := by sorry\nend ContinuousMap\nnamespace Matrix\ntheorem coe_units_inv (A : (Matrix n n R)ˣ) : ↑A⁻¹ = (A⁻¹ : Matrix n n R) := by sorry\nend Matrix\nnamespace Demo\ntheorem callee (A : Matrix n n R) : True := trivial\nend Demo\n").unwrap();
        let repo = Repo {
            root: root.clone(),
            common_git_dir: dir.path().join("git"),
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
        let state = State::new(&repo.db_path).unwrap();
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
        let output = searcher
            .probe_contract(&workspace, &root, "Demo.Data", "evidence")
            .unwrap();
        let reference = output
            .lines()
            .find_map(|l| l.strip_prefix("ref: "))
            .unwrap();
        let detail = state.show(reference, true).unwrap();
        assert!(
            detail.contains("obstruction candidate: Demo.impossible"),
            "{detail}"
        );
        assert!(detail.contains("h : n = 0"), "{detail}");
        assert!(detail.contains("subsingleton candidate:"), "{detail}");
        assert!(!detail.contains("Container.item"), "{detail}");
        assert!(
            detail.contains("construction candidate: Demo.construct"),
            "{detail}"
        );
        assert!(
            !detail.contains("obstruction candidate: Demo.conditional"),
            "{detail}"
        );
        assert!(detail.contains("not verified applicability"), "{detail}");
        for source in [
            None,
            Some("-- 2 earlier ambient commands omitted\ndef f (d : Data 0) : True := trivial"),
        ] {
            assert!(
                searcher
                    .input_obstruction_notice(&workspace, "(d : Data 0) : True", source)
                    .unwrap()
                    .is_none()
            );
        }
        let notice = searcher
            .input_obstruction_notice(&workspace, "(d : Demo.Data 0) : True", None)
            .unwrap()
            .unwrap();
        assert!(notice.contains("Compare the specialization"), "{notice}");
        assert!(notice.contains("Demo.Data"), "{notice}");
        assert!(
            searcher
                .input_obstruction_notice(&workspace, "(n : Nat) : True", None)
                .unwrap()
                .is_none()
        );
        let property = searcher
            .search(&workspace, &root, "Demo.Data subsingleton", None, false)
            .unwrap();
        assert!(property.contains("Subsingleton (Data 1)"), "{property}");
        assert!(
            property.contains("Requested property found in source"),
            "{property}"
        );
        let examples = searcher
            .probe_examples(&workspace, "Demo.Data", None)
            .unwrap();
        assert!(!examples.contains("Container.item"), "{examples}");
        assert!(examples.contains("Demo.construct"), "{examples}");
        assert!(
            examples.find("Demo.construct").unwrap() < examples.find("Demo.transform").unwrap(),
            "{examples}"
        );
        assert!(
            examples.contains("requires an existing Demo.Data input"),
            "{examples}"
        );
        assert!(
            examples.find("Demo.transform").unwrap() < examples.find("Demo.hidden").unwrap(),
            "{examples}"
        );
        assert!(
            examples.contains("is private: inspect its source"),
            "{examples}"
        );
        let private = assumption_signature("[private] (n : Nat) : Data n");
        assert!(private.contains("visibility: private"), "{private}");
        assert!(
            !private.contains("implicit/context: [private]"),
            "{private}"
        );
        assert!(private.contains("input: (n : Nat)"), "{private}");

        assert!(
            searcher
                .input_obstruction_notice(
                    &workspace,
                    "(d : Data) : True",
                    Some("variable {Data : Type}")
                )
                .unwrap()
                .is_none()
        );

        assert!(
            searcher
                .probe_contract(&workspace, &root, "Missing.Data", "evidence")
                .is_err()
        );
        for name in ["Demo.Derived", "Demo.InheritedOnly"] {
            let output = searcher
                .search(&workspace, &root, &format!("{name} fields"), None, false)
                .unwrap();
            assert!(
                output.contains("inherited obligations are omitted"),
                "{output}"
            );
            assert!(output.contains("Extends: Container"), "{output}");
            assert!(output.contains(&format!("#inspect {name}.mk")), "{output}");
        }
        let assumptions = searcher
            .probe_contract(&workspace, &root, "Demo.Data", "assumptions")
            .unwrap();
        assert!(
            assumptions.contains("signature (premises retained)"),
            "{assumptions}"
        );
        let diagnostic = "Application type mismatch: The argument\n h\nhas type\n ∀ x : OnePoint ℂ, P x = ↑g⁻¹\nbut is expected to have type\n ∀ x : OnePoint ℂ, P x = (↑((ContinuousMap.const _ g) x))⁻¹\nin the application\n Demo.callee A";
        let bundle = searcher
            .failure_context(&workspace, diagnostic, Some("Demo.lean"))
            .unwrap();
        assert!(bundle.contains("ContinuousMap.const_apply"), "{bundle}");
        assert!(bundle.contains("Matrix.coe_units_inv"), "{bundle}");
        assert!(bundle.contains("applicability unverified"), "{bundle}");
        searcher
            .open()
            .unwrap()
            .execute(
                "UPDATE search_fts SET kind = 'declaration' WHERE name = 'Demo.Data'",
                [],
            )
            .unwrap();
        let (scopes, _) = searcher.search_scopes(&workspace).unwrap();
        let fields = searcher
            .field_inventory_result("Demo.Data", &scopes, &workspace, None, true)
            .unwrap()
            .unwrap();
        let note = fields.note.unwrap();
        assert!(note.contains("structural status is unknown"), "{note}");
        assert!(!note.contains("not a class or structure"), "{note}");
    }

    #[test]
    fn i140_source_and_compiled_entries_are_one_declaration() {
        let ws = Workspace {
            reference: "w1".into(),
            name: "demo".into(),
            path: "/demo".into(),
            branch: "demo".into(),
            model: None,
        };
        let row = |owner: &str, name: &str, kind: &str, signature: &str| IndexedRow {
            owner: owner.into(),
            path: "Demo.lean".into(),
            module: "Demo".into(),
            line: 1,
            name: name.into(),
            kind: kind.into(),
            signature: signature.into(),
            docs: String::new(),
            body: String::new(),
            rank: 0.0,
        };
        let hit = contract_exact_hit(
            vec![
                row(
                    "artifacts:w1",
                    "_root_.Demo.publicTheorem",
                    "declaration",
                    "",
                ),
                row(
                    "workspace:w1",
                    "Demo.publicTheorem",
                    "theorem",
                    "(n : Nat) : n = n",
                ),
            ],
            "Demo.publicTheorem",
            &ws,
        )
        .unwrap();
        assert!(hit.signature.unwrap().contains("n = n"));
        assert!(
            contract_exact_hit(
                vec![
                    row("workspace:w1", "Left.Data", "structure", ": Type"),
                    row("workspace:w1", "Right.Data", "structure", ": Type")
                ],
                "Data",
                &ws
            )
            .is_err()
        );
    }

    #[test]
    fn obstruction_requires_negative_result_not_premise() {
        assert_eq!(
            relation("(X : Type) : ¬ Nonempty (Demo.Data X)", "Demo.Data"),
            Some("obstruction candidate")
        );
        assert_ne!(
            relation("(h : ¬ Nonempty (Demo.Data X)) : True", "Demo.Data"),
            Some("obstruction candidate")
        );
        assert_ne!(
            relation("¬ Nonempty (Demo.Data X) → False", "Demo.Data"),
            Some("obstruction candidate")
        );
        assert_eq!(
            relation("(x : X) : Demo.Data X", "Demo.Data"),
            Some("construction candidate")
        );
        assert_eq!(relation("(h : Demo.Data X) : Other", "Demo.Data"), None);
        assert_eq!(
            relation(": ¬ Nonempty (Demo.Database X)", "Demo.Data"),
            None
        );
    }
}
