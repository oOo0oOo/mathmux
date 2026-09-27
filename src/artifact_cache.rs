use std::fs;
use std::os::unix::fs::MetadataExt;
use std::path::Path;
use std::sync::atomic::{AtomicU64, Ordering};

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

/// Lake rewrites these metadata files in place. Break legacy donor hard links
/// before a new build, preserving mtime so isolation itself does not invalidate caches.
pub(crate) fn isolate_build_metadata(root: &Path, module: &str) -> Result<()> {
    let relative = module.replace('.', "/");
    for (directory, extensions) in [
        (
            ".lake/build/lib/lean",
            &["trace", "olean.hash", "ilean.hash"][..],
        ),
        (".lake/build/ir", &["setup.json", "c.hash", "ir.hash"][..]),
    ] {
        let base = root.join(directory).join(&relative);
        for extension in extensions {
            isolate_metadata_file(&base.with_extension(extension))?;
        }
    }
    Ok(())
}

fn isolate_metadata_file(path: &Path) -> Result<()> {
    let metadata = match fs::metadata(path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(error.into()),
    };
    if !metadata.is_file() || metadata.nlink() <= 1 {
        return Ok(());
    }
    // Lake writes module setup scratch before every compiler invocation. Drop
    // only this workspace's shared link instead of copying gigabytes of JSON.
    if path.to_string_lossy().ends_with(".setup.json") {
        fs::remove_file(path)?;
        return Ok(());
    }
    static NEXT_COPY: AtomicU64 = AtomicU64::new(0);
    let temporary = path.with_extension(format!(
        "mathmux-copy-{}-{}",
        std::process::id(),
        NEXT_COPY.fetch_add(1, Ordering::Relaxed)
    ));
    let file = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&temporary)?;
    let result = (|| -> Result<()> {
        fs::copy(path, &temporary)?;
        file.set_times(fs::FileTimes::new().set_modified(metadata.modified()?))?;
        fs::rename(&temporary, path)?;
        Ok(())
    })();
    if result.is_err() {
        let _ = fs::remove_file(&temporary);
    }
    result.with_context(|| format!("cannot isolate mutable build metadata {}", path.display()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn legacy_metadata_links_are_detached_without_changing_mtime() {
        let directory = tempfile::tempdir().unwrap();
        let donor = directory.path().join("donor.trace");
        let target = directory.path().join(".lake/build/lib/lean/Demo.trace");
        fs::create_dir_all(target.parent().unwrap()).unwrap();
        fs::write(&donor, "original provenance").unwrap();
        fs::hard_link(&donor, &target).unwrap();
        let original_time = fs::metadata(&target).unwrap().modified().unwrap();
        isolate_build_metadata(directory.path(), "Demo").unwrap();
        assert_eq!(
            fs::metadata(&target).unwrap().modified().unwrap(),
            original_time
        );
        assert_eq!(fs::metadata(&target).unwrap().nlink(), 1);
        fs::write(&donor, "different build").unwrap();
        assert_eq!(fs::read_to_string(&target).unwrap(), "original provenance");
        isolate_build_metadata(directory.path(), "Demo").unwrap();
        let setup = directory.path().join(".lake/build/ir/Demo.setup.json");
        fs::create_dir_all(setup.parent().unwrap()).unwrap();
        fs::hard_link(&donor, &setup).unwrap();
        isolate_build_metadata(directory.path(), "Demo").unwrap();
        assert!(!setup.exists());
        assert_eq!(fs::read_to_string(&donor).unwrap(), "different build");
    }
}
