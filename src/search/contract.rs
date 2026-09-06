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

fn mentions(text: &str, name: &str) -> bool {
    let name = name.trim_start_matches("_root_.");
    identifiers(text)
        .iter()
        .any(|s| s.trim_start_matches("_root_.") == name)
}

/// Top-level declaration result, retaining arrows so hypotheses cannot be
/// mistaken for a negative conclusion. This is deliberately conservative.
fn conclusion(signature: &str) -> &str {
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

fn relation(signature: &str, name: &str) -> Option<&'static str> {
    let result = conclusion(signature);
    let leaf = name.rsplit('.').next().unwrap_or(name);
    if !mentions(result, name) && !mentions(result, leaf) {
        return None;
    }
    // Never classify a negative premise on the left of an implication as an obstruction.
    let negative = result.starts_with("¬ Nonempty")
        || result.starts_with("Not (Nonempty")
        || result.starts_with("¬Nonempty");
    if negative && !result.contains('→') && !result.contains("->") {
        Some("obstruction candidate")
    } else if result.starts_with(name)
        || result.starts_with(leaf)
        || result.starts_with("Nonempty ")
    {
        Some("construction candidate")
    } else {
        Some("related law candidate")
    }
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
            "WHERE search_fts MATCH ?1 AND kind NOT IN ('file', 'imports') AND signature <> ''
             AND owner IN (SELECT owner FROM active_search_scopes)
             ORDER BY rank LIMIT {CANDIDATE_LIMIT}"
        ));
        let rows = connection
            .prepare(&sql)?
            .query_map([query], indexed_row_from_row)?
            .collect::<rusqlite::Result<Vec<_>>>()?;
        Ok(rows)
    }

    pub(super) fn probe_contract(
        &self,
        workspace: &Workspace,
        _cwd: &Path,
        subject: &str,
        focus: &str,
    ) -> Result<String> {
        let (scopes, warming) = self.search_scopes(workspace)?;
        let candidates = self.exact_candidates(subject, &scopes)?;
        let exact = resolved_exact_candidates(candidates.into_iter().map(compact_ranked_hit).collect(), subject)
            .with_context(|| format!("exact declaration unavailable or ambiguous: {subject}; search the qualified name first"))?;
        ensure!(exact.len() == 1, "choose one fully qualified declaration");
        let mut hit = exact[0].hit.clone();
        self.enrich_exact_source(&mut hit, &scopes)?;
        let name = hit.name.trim_start_matches("_root_.");
        let mut detail = format!(
            "{name}\nsource evidence: {}:{}; index warming: {warming}\n",
            hit.path, hit.line
        );
        detail.push_str(&format!(
            "signature (premises retained):\n{}\n",
            hit.signature.as_deref().unwrap_or("unavailable")
        ));
        if focus == "assumptions" {
            detail.push_str("A conditional signature does not construct its inputs. Inspect selected input types and fields, then test the intended application.\n");
            if matches!(hit.kind.as_str(), "structure" | "class" | "abbrev") {
                detail.push_str(&format!("fields: mathmux probe {name} fields\n"));
            }
            let terms = identifiers(hit.signature.as_deref().unwrap_or(""));
            let mut shown = 0;
            for term in terms
                .into_iter()
                .filter(|t| t.contains('.') || t.chars().next().is_some_and(char::is_uppercase))
                .take(16)
            {
                let rows = self.exact_candidates(&term, &scopes)?;
                if let Some(rows) = resolved_exact_candidates(
                    rows.into_iter().map(compact_ranked_hit).collect(),
                    &term,
                ) && rows.len() == 1
                    && rows[0].hit.name != hit.name
                    && matches!(rows[0].hit.kind.as_str(), "structure" | "class" | "abbrev")
                {
                    detail.push_str(&format!(
                        "input API: {} — mathmux probe {} fields\n",
                        rows[0].hit.name, rows[0].hit.name
                    ));
                    shown += 1;
                    if shown == 3 {
                        break;
                    }
                }
            }
            detail.push_str("exact Lean inspection: mathmux probe FILE:LINE '#inspect NAME_OR_TERM'\napplication: mathmux probe FILE:LINE '#apply TERM'\nsmall case: mathmux probe FILE:LINE '#check (TERM : EXPECTED_TYPE)' or '#reduce TERM'\n");
        } else {
            let leaf = name.rsplit('.').next().unwrap_or(name);
            let mut related = self
                .contract_rows(workspace, &[leaf.to_owned()])?
                .into_iter()
                .filter(|r| r.name.trim_start_matches("_root_.") != name)
                .filter_map(|r| relation(&r.signature, name).map(|kind| (kind, r)))
                .collect::<Vec<_>>();
            related.sort_by_key(|(kind, r)| {
                (
                    match *kind {
                        "obstruction candidate" => 0,
                        "construction candidate" => 1,
                        _ => 2,
                    },
                    r.name.clone(),
                )
            });
            let mut seen = HashSet::new();
            related.retain(|(_, r)| seen.insert(r.name.clone()));
            for (kind, row) in related.iter().take(6) {
                detail.push_str(&format!(
                    "\n{kind}: {}\n{}:{}\n{}\nnext: mathmux probe {} assumptions\n",
                    row.name,
                    row.path,
                    row.line,
                    truncate_line(&row.signature, 650),
                    row.name
                ));
            }
            if related.is_empty() {
                detail.push_str("No construction or obstruction found in this bounded index search; this is not an existence verdict.\n");
            }
            detail.push_str("Candidates are indexed source, not verified applicability. Hypotheses and namespace resolution matter. Verify a candidate in your exact Lean context with #inspect and #apply; check remains certification.\n");
        }
        self.store_probe_result(
            workspace,
            &format!("{subject} {focus}"),
            "contract",
            detail,
            Some(&hit.path),
            hit.line,
        )
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
        let leaf = subject.rsplit('.').next().unwrap_or(subject);
        let mut rows = self
            .contract_rows(workspace, &[leaf.to_owned()])?
            .into_iter()
            .filter(|r| relation(&r.signature, subject) == Some("obstruction candidate"))
            .collect::<Vec<_>>();
        rows.sort_by(|a, b| a.name.cmp(&b.name));
        rows.dedup_by(|a, b| a.name == b.name);
        let mut detail = format!("Obstruction inspection at {}:{line}\n", path.display());
        let mut inspection_ok = true;
        // At most one Lean operation: no surprise multi-minute verification fanout.
        if let Some(row) = rows.first() {
            let (ok, inspected) = self
                .checker
                .probe_context(workspace, path, line, 0, "inspect", &row.name)?;
            inspection_ok = ok;
            detail.push_str(&format!(
                "candidate: {} (source {}:{})\nLean inspection {}:\n{}\n",
                row.name,
                row.path,
                row.line,
                if ok { "succeeded" } else { "failed" },
                inspected
            ));
            detail.push_str("The elaborated result and axioms above are authoritative, not the indexed candidate label. Match every hypothesis and specialization; check remains certification.\n");
            if rows.len() > 1 {
                detail.push_str("More source candidates: probe NAME evidence; verify a selected one with FILE:LINE '#inspect QUALIFIED_NAME'.\n");
            }
        } else {
            detail.push_str("No direct negative-existence candidate found in the bounded index. This is not evidence of inhabitability.\n");
        }
        let rendered = self.store_probe_result(
            workspace,
            &format!("{subject} evidence"),
            "obstruction-inspection",
            detail,
            path.to_str(),
            line,
        )?;
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
                (score, overlap + usize::from(direct_law), r)
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
        let mut detail = String::new();
        if !rows.is_empty() {
            detail.push_str(
                "\nConversion/law candidates (signature overlap; applicability unverified):\n",
            );
            for (_, row) in rows.iter().take(3) {
                detail.push_str(&format!(
                    "{} : {}\n  {}:{}; probe {} source\n",
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
    fn contract_evidence_uses_active_index_and_preserves_hypotheses() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path().join("root");
        let state_dir = dir.path().join("state");
        fs::create_dir_all(&root).unwrap();
        fs::create_dir_all(&state_dir).unwrap();
        fs::write(root.join("Demo.lean"), "namespace Demo\nstructure Data (n : Nat) where\n  value : Fin n\ntheorem impossible (h : n = 0) : ¬ Nonempty (Data n) := by sorry\ndef construct (h : 0 < n) : Data n := sorry\ntheorem conditional (h : ¬ Nonempty (Data n)) : True := trivial\nend Demo\n").unwrap();
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
        assert!(
            detail.contains("construction candidate: Demo.construct"),
            "{detail}"
        );
        assert!(
            !detail.contains("obstruction candidate: Demo.conditional"),
            "{detail}"
        );
        assert!(detail.contains("not verified applicability"), "{detail}");
        assert!(
            searcher
                .probe_contract(&workspace, &root, "Missing.Data", "evidence")
                .is_err()
        );
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
