use std::fs;
use std::path::Path;

use anyhow::{Context, Result, ensure};

pub(crate) fn restore_available_olean(cache_dir: &Path, artifact: &Path) -> Result<bool> {
    if artifact.is_file()
        || artifact
            .extension()
            .is_none_or(|extension| extension != "olean")
    {
        return Ok(false);
    }
    if !artifact.with_extension("trace").is_file()
        && !artifact.with_extension("olean.hash").is_file()
    {
        return Ok(false);
    }
    let Ok(hash) = project_olean_hash(artifact) else {
        return Ok(false);
    };
    if hash.len() != 16 || !hash.chars().all(|character| character.is_ascii_hexdigit()) {
        return Ok(false);
    }
    let cached = cache_dir.join("artifacts").join(format!("{hash}.olean"));
    if !cached.is_file() {
        return Ok(false);
    }
    materialize_olean(&cached, artifact)?;
    Ok(true)
}

pub(crate) fn restore_olean(cache_dir: &Path, artifact: &Path) -> Result<()> {
    if artifact.is_file() {
        return Ok(());
    }
    let hash = project_olean_hash(artifact)?;
    ensure!(
        hash.len() == 16 && hash.chars().all(|character| character.is_ascii_hexdigit()),
        "invalid artifact hash"
    );
    let cached = cache_dir.join("artifacts").join(format!("{hash}.olean"));
    ensure!(cached.is_file(), "cached artifact missing");
    materialize_olean(&cached, artifact)
}

fn materialize_olean(cached: &Path, artifact: &Path) -> Result<()> {
    if let Some(parent) = artifact.parent() {
        fs::create_dir_all(parent)?;
    }
    if let Err(error) = fs::hard_link(cached, artifact) {
        fs::copy(cached, artifact).with_context(|| {
            format!("cannot restore cached olean after hard-link failed: {error}")
        })?;
    }
    Ok(())
}

fn project_olean_hash(artifact: &Path) -> Result<String> {
    let trace_path = artifact.with_extension("trace");
    if trace_path.is_file() {
        let trace: serde_json::Value = serde_json::from_slice(&fs::read(trace_path)?)?;
        if let Some(hash) = trace
            .pointer("/outputs/o")
            .and_then(serde_json::Value::as_array)
            .into_iter()
            .flatten()
            .filter_map(serde_json::Value::as_str)
            .find_map(|name| {
                Path::new(name)
                    .file_stem()
                    .and_then(|stem| stem.to_str())
                    .map(str::to_owned)
            })
        {
            return Ok(hash);
        }
    }
    fs::read_to_string(artifact.with_extension("olean.hash"))
        .map(|hash| hash.trim().to_owned())
        .context("artifact has neither a cached olean output nor an olean hash")
}
