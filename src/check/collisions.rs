use std::collections::HashSet;
use std::path::Path;
use std::time::{Duration, Instant};

use rusqlite::{Connection, OpenFlags, params};

use crate::state::{Diagnostic, Workspace};

/// Advisory only: the existing artifact index can be incomplete or stale.
/// Do not rebuild artifacts, block certification, or launch another Lean process.
pub(super) fn indexed_instance_collisions(
    database: &Path, workspace: &Workspace, target: &Path, names: &[String],
) -> Vec<Diagnostic> {
    if names.is_empty() { return Vec::new(); }
    read_collisions(database, workspace, target, names).unwrap_or_default()
}

fn read_collisions(
    database: &Path, workspace: &Workspace, target: &Path, names: &[String],
) -> rusqlite::Result<Vec<Diagnostic>> {
    let connection = Connection::open_with_flags(database, OpenFlags::SQLITE_OPEN_READ_ONLY)?;
    connection.busy_timeout(Duration::from_millis(25))?;
    let owner = format!("artifacts:{}", workspace.reference);
    let mut statement = connection.prepare(
        "SELECT name, file, line FROM search_fts WHERE search_fts MATCH ?1 AND owner = ?2 LIMIT 16")?;
    let started = Instant::now();
    let mut warnings = Vec::new();
    let mut seen = HashSet::new();
    for name in names.iter().take(256) {
        if started.elapsed() >= Duration::from_millis(100) || warnings.len() >= 3 { break; }
        let query = format!("name:\"{}\"", name.replace('"', "\"\""));
        let rows = statement.query_map(params![query, owner], |row| {
            Ok((row.get::<_, String>(0)?, row.get::<_, String>(1)?, row.get::<_, u64>(2)?))
        })?;
        for row in rows {
            let (indexed_name, file, line) = row?;
            if indexed_name != *name || Path::new(&file) == target
                || !workspace.path.join(&file).is_file()
                || !seen.insert((name.clone(), file.clone())) { continue; }
            warnings.push(Diagnostic {
                kind: "possible-declaration-collision".into(),
                text: format!("possible cross-module instance collision: {name} is also indexed in {file}:{line}. Give this instance a unique explicit name, or verify the two modules can be imported together. Compiled index evidence may be stale; this warning is not a joint-import certificate."),
                context: None,
            });
            if warnings.len() >= 3 { break; }
        }
    }
    Ok(warnings)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn collisions_are_exact_workspace_local_and_advisory() {
        let temp = tempdir().unwrap();
        let workspace = Workspace { reference: "w1".into(), name: "test".into(), path: temp.path().into(), branch: "test".into(), model: None };
        let database = temp.path().join("search.sqlite3");
        let db = Connection::open(&database).unwrap();
        db.execute_batch("CREATE VIRTUAL TABLE search_fts USING fts5(owner UNINDEXED, file UNINDEXED, line UNINDEXED, name);").unwrap();
        for (owner, file, name) in [
            ("artifacts:w1", "Target.lean", "Demo.instInhabitedNat"),
            ("artifacts:w1", "Other.lean", "Demo.instInhabitedNat"),
            ("artifacts:w2", "Elsewhere.lean", "Demo.instInhabitedNat"),
            ("artifacts:w1", "Deleted.lean", "Demo.instInhabitedNat"),
            ("artifacts:w1", "Other.lean", "Demo.instInhabitedNatExtra"),
        ] {
            if file != "Deleted.lean" { std::fs::write(temp.path().join(file), "-- fixture").unwrap(); }
            db.execute("INSERT INTO search_fts VALUES (?1,?2,7,?3)", params![owner,file,name]).unwrap();
        }
        let warnings = indexed_instance_collisions(&database, &workspace, Path::new("Target.lean"), &["Demo.instInhabitedNat".into()]);
        assert_eq!(warnings.len(), 1);
        assert!(warnings[0].text.contains("Other.lean:7"));
        assert!(warnings[0].text.contains("may be stale"));
        assert!(indexed_instance_collisions(&database, &workspace, Path::new("Target.lean"), &["Demo.instUnique".into()]).is_empty());
        assert!(indexed_instance_collisions(&temp.path().join("missing"), &workspace, Path::new("Target.lean"), &["Demo.instInhabitedNat".into()]).is_empty());
        assert!(!temp.path().join("missing").exists());
    }
}
