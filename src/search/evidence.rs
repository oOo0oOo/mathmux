//! Snapshot-bound Lean evidence and explicitly authored project routes.
use super::*;

#[derive(Debug, Deserialize)]
pub(super) struct LeanEvidence {
    pub declaration: String,
    pub subject: Option<String>,
    pub conclusion: String,
    pub premises: Vec<String>,
    pub axioms: Vec<String>,
    pub detail: String,
}
impl LeanEvidence {
    pub fn trusted(&self) -> bool {
        self.subject.is_some()
            && self
                .axioms
                .iter()
                .all(|a| matches!(a.as_str(), "propext" | "Classical.choice" | "Quot.sound"))
    }
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Registry {
    version: u32,
    links: Vec<Route>,
}
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Route {
    pub subject: String,
    #[serde(default)]
    pub obstruction: Option<String>,
    #[serde(default)]
    pub replacement: Option<String>,
    #[serde(default)]
    pub examples: Vec<String>,
    #[serde(default)]
    pub explanation: String,
}
fn declaration_name(name: &str) -> bool {
    !name.is_empty()
        && name.len() <= 512
        && name.split('.').all(|part| {
            part.chars()
                .next()
                .is_some_and(|c| c.is_alphabetic() || c == '_')
                && part
                    .chars()
                    .all(|c| c.is_alphanumeric() || c == '_' || c == '\'')
        })
}

pub(super) fn routes(workspace: &Workspace, subject: &str) -> Result<Vec<Route>> {
    let path = workspace.path.join(".mathmux-evidence.json");
    if !path.exists() {
        return Ok(Vec::new());
    }
    ensure!(
        fs::metadata(&path)?.len() <= 65_536,
        ".mathmux-evidence.json exceeds 64 KiB"
    );
    let registry: Registry =
        serde_json::from_slice(&fs::read(&path)?).context("invalid .mathmux-evidence.json")?;
    ensure!(
        registry.version == 1 && registry.links.len() <= 256,
        "evidence registry requires version 1 and at most 256 links"
    );
    for route in &registry.links {
        ensure!(
            declaration_name(&route.subject)
                && route.obstruction.as_deref().is_none_or(declaration_name)
                && route.replacement.as_deref().is_none_or(declaration_name)
                && route.examples.len() <= 4
                && route.examples.iter().all(|n| declaration_name(n))
                && route.explanation.len() <= 1000,
            "invalid or oversized evidence route"
        );
    }
    Ok(registry
        .links
        .into_iter()
        .filter(|r| {
            r.subject.trim_start_matches("_root_.") == subject.trim_start_matches("_root_.")
        })
        .take(3)
        .collect())
}

pub(super) fn snapshot(workspace: &Workspace, path: &Path) -> Result<String> {
    let path = if path.is_absolute() {
        path.strip_prefix(&workspace.path)?
    } else {
        path
    };
    ensure!(
        !path
            .components()
            .any(|c| matches!(c, std::path::Component::ParentDir)),
        "evidence path escapes workspace"
    );
    let dependencies = crate::check::transitive_dependencies(&workspace.path, path)?;
    crate::check::certificate_fingerprint(&workspace.path, path, &dependencies)
}

impl Searcher {
    pub(super) fn authored_route_detail(
        &self,
        workspace: &Workspace,
        subject: &str,
    ) -> Result<String> {
        let mut detail = String::new();
        for route in routes(workspace, subject)? {
            detail.push_str("\nproject-authored route (advisory, not an equivalence proof):\n");
            if let Some(obstruction) = route.obstruction {
                detail.push_str(&format!(
                    "  obstruction: {obstruction}; verify in your Lean context\n"
                ));
            }
            if let Some(replacement) = route.replacement {
                detail.push_str(&format!(
                    "  replacement: {replacement}; probe {replacement} assumptions\n"
                ));
            }
            for example in route.examples {
                detail.push_str(&format!(
                    "  selected example: {example}; probe {example} source\n"
                ));
            }
            if !route.explanation.is_empty() {
                detail.push_str(&format!(
                    "  {}\n",
                    truncate_line(&single_line(&route.explanation), 240)
                ));
            }
        }
        Ok(detail)
    }

    pub(super) fn verified_contract_notice(
        &self,
        workspace: &Workspace,
        subject: &str,
    ) -> Result<Option<String>> {
        for crate::state::ContractEvidenceRecord {
            reference,
            theorem,
            path,
            fingerprint,
            details,
        } in self.state.contract_evidence(subject)?
        {
            if snapshot(workspace, Path::new(&path)).ok().as_deref() == Some(&fingerprint) {
                return Ok(Some(format!(
                    "Lean-verified obstruction at matching project-source/configuration snapshot: {theorem}\n{}\nHypotheses/specialization still apply; probe {reference}",
                    truncate_line(&details, 400)
                )));
            }
        }
        Ok(None)
    }

    pub(super) fn append_discovery_contract(&self, workspace: &Workspace, run: &mut SearchRun) {
        if !matches!(run.inference.as_str(), "exact" | "exact-batch") || run.hits.len() != 1 {
            return;
        }
        let hit = &run.hits[0];
        let subject = hit.name.trim_start_matches("_root_.");
        let verified = self
            .verified_contract_notice(workspace, subject)
            .ok()
            .flatten();
        let authored = self.authored_route_detail(workspace, subject);
        let mut notes = Vec::new();
        if let Some(verified) = verified {
            notes.push(verified);
        } else if matches!(hit.kind.as_str(), "structure" | "class" | "inductive")
            && let Ok(Some((name, signature))) =
                self.direct_obstruction_candidate(workspace, subject)
        {
            notes.push(format!("source obstruction candidate (unverified): {name}\n{}\nInspect hypotheses: mathmux probe {subject} evidence", truncate_line(&signature, 240)));
        }
        match authored {
            Ok(authored) if !authored.is_empty() => notes.push(authored),
            Err(_) => notes.push(
                "project route registry invalid; probe NAME evidence for the diagnostic".into(),
            ),
            _ => (),
        }
        if !notes.is_empty() {
            let prior = run.note.take().unwrap_or_default();
            run.note = Some(format!("{prior}\n{}", notes.join("\n")).trim().to_owned());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn snapshot_changes_for_transitive_project_imports_and_configuration() {
        let dir = tempfile::tempdir().unwrap();
        let ws = Workspace {
            reference: "w1".into(),
            name: "test".into(),
            path: dir.path().into(),
            branch: "test".into(),
            model: None,
        };
        fs::write(dir.path().join("Main.lean"), "import Dependency\n").unwrap();
        fs::write(dir.path().join("Dependency.lean"), "def value := 1\n").unwrap();
        let first = snapshot(&ws, Path::new("Main.lean")).unwrap();
        fs::write(dir.path().join("Dependency.lean"), "def value := 2\n").unwrap();
        let second = snapshot(&ws, Path::new("Main.lean")).unwrap();
        assert_ne!(first, second);
        fs::write(dir.path().join("lean-toolchain"), "different-toolchain").unwrap();
        assert_ne!(second, snapshot(&ws, Path::new("Main.lean")).unwrap());
        assert!(snapshot(&ws, Path::new("../outside.lean")).is_err());
    }

    #[test]
    fn registry_is_explicit_bounded_and_advisory() {
        let dir = tempfile::tempdir().unwrap();
        let ws = Workspace {
            reference: "w1".into(),
            name: "demo".into(),
            path: dir.path().into(),
            branch: "demo".into(),
            model: None,
        };
        assert!(routes(&ws, "Demo.Data").unwrap().is_empty());
        fs::write(dir.path().join(".mathmux-evidence.json"), r#"{"version":1,"links":[{"subject":"Demo.Data","replacement":"Other.Data","examples":["Other.example"]}]}"#).unwrap();
        assert_eq!(
            routes(&ws, "Demo.Data").unwrap()[0].replacement.as_deref(),
            Some("Other.Data")
        );
        assert!(routes(&ws, "Unrelated.Data").unwrap().is_empty());
        fs::write(
            dir.path().join(".mathmux-evidence.json"),
            r#"{"version":1,"links":[{"subject":"Demo.Data","replacement":"$(run)"}]}"#,
        )
        .unwrap();
        assert!(routes(&ws, "Demo.Data").is_err());
    }
    #[test]
    fn admitted_or_custom_axiom_evidence_is_never_trusted() {
        let mut evidence = LeanEvidence {
            declaration: "empty".into(),
            subject: Some("Empty".into()),
            conclusion: "¬ Nonempty Empty".into(),
            premises: vec![],
            axioms: vec![],
            detail: String::new(),
        };
        assert!(evidence.trusted());
        evidence.axioms.push("sorryAx".into());
        assert!(!evidence.trusted());
        evidence.axioms = vec!["Demo.assumeEmpty".into()];
        assert!(!evidence.trusted());
    }
}
