use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::OnceLock;
use std::time::{SystemTime, UNIX_EPOCH};

use anyhow::{Context, Result, bail};

pub const SOURCE_PREVIEW_LINES: usize = 16;

pub fn now_unix_ms() -> i64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis() as i64
}

pub fn canonical(path: impl AsRef<Path>) -> Result<PathBuf> {
    fs::canonicalize(path.as_ref())
        .with_context(|| format!("cannot resolve {}", path.as_ref().display()))
}

pub fn run_output<I, S>(program: impl AsRef<OsStr>, args: I, cwd: &Path) -> Result<Output>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    Command::new(program)
        .args(args)
        .current_dir(cwd)
        .stdin(Stdio::null())
        .output()
        .with_context(|| format!("failed to start command in {}", cwd.display()))
}

pub fn run_checked<I, S>(program: impl AsRef<OsStr>, args: I, cwd: &Path) -> Result<String>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let output = run_output(program, args, cwd)?;
    if !output.status.success() {
        let stderr = output_text(&output.stderr);
        let stdout = output_text(&output.stdout);
        let detail = if stderr.is_empty() { stdout } else { stderr };
        bail!("command failed: {detail}");
    }
    Ok(output_text(&output.stdout))
}

pub fn command_detail(output: &Output) -> String {
    let stderr = output_text(&output.stderr);
    if stderr.is_empty() {
        output_text(&output.stdout)
    } else {
        stderr
    }
}

pub(crate) fn output_text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).trim().to_owned()
}

pub fn hash_bytes(bytes: &[u8]) -> String {
    blake3::hash(bytes).to_hex().to_string()
}

pub fn hash_file(path: &Path) -> Result<String> {
    let bytes = fs::read(path).with_context(|| format!("cannot read {}", path.display()))?;
    Ok(hash_bytes(&bytes))
}

pub fn build_id() -> &'static str {
    static BUILD_ID: OnceLock<String> = OnceLock::new();
    BUILD_ID.get_or_init(|| {
        let hash = std::env::current_exe()
            .ok()
            .and_then(|path| hash_file(&path).ok())
            .unwrap_or_else(|| "unknown".into());
        format!(
            "{}+{}",
            env!("CARGO_PKG_VERSION"),
            &hash[..hash.len().min(12)]
        )
    })
}

pub fn build_generation() -> u64 {
    static GENERATION: OnceLock<u64> = OnceLock::new();
    *GENERATION.get_or_init(|| {
        std::env::current_exe()
            .ok()
            .and_then(|path| fs::metadata(path).ok())
            .and_then(|metadata| metadata.modified().ok())
            .and_then(|modified| modified.duration_since(UNIX_EPOCH).ok())
            .map(|duration| duration.as_nanos() as u64)
            .unwrap_or_default()
    })
}

pub fn clean_line(value: &str) -> String {
    value.replace(['\r', '\n'], " ").trim().to_owned()
}

pub fn single_line(value: &str) -> String {
    value.split_whitespace().collect::<Vec<_>>().join(" ")
}

pub fn truncate_line(value: &str, limit: usize) -> String {
    if value.chars().count() <= limit {
        return value.to_owned();
    }
    let mut output = value
        .chars()
        .take(limit.saturating_sub(1))
        .collect::<String>();
    output.push('…');
    output
}

pub fn truncate_middle(value: &str, limit: usize) -> String {
    let length = value.chars().count();
    if length <= limit {
        return value.to_owned();
    }
    if limit == 0 {
        return String::new();
    }
    let kept = limit - 1;
    let head = kept.div_ceil(2);
    let tail = kept - head;
    let mut output = value.chars().take(head).collect::<String>();
    output.push('…');
    output.extend(
        value
            .chars()
            .rev()
            .take(tail)
            .collect::<Vec<_>>()
            .into_iter()
            .rev(),
    );
    output
}

pub fn query_requests_proof_body(query: &str) -> bool {
    let normalized = single_line(query).to_lowercase();
    normalized.starts_with("def ")
        || normalized.starts_with("theorem ")
        || normalized.starts_with("lemma ")
        || normalized.contains(":= by")
        || normalized.contains("proof body")
        || normalized.contains("implementation body")
}

pub fn format_duration(milliseconds: u64) -> String {
    if milliseconds < 1000 {
        format!("{milliseconds}ms")
    } else {
        format!("{:.1}s", milliseconds as f64 / 1000.0)
    }
}

pub fn short_hash(hash: &str) -> &str {
    hash.get(..8).unwrap_or(hash)
}

pub fn resident_memory_kib() -> Option<u64> {
    fs::read_to_string("/proc/self/status")
        .ok()?
        .lines()
        .find_map(|line| line.strip_prefix("VmRSS:"))?
        .split_whitespace()
        .next()?
        .parse()
        .ok()
}
