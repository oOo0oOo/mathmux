use std::ffi::OsStr;
use std::fs;
use std::io::{ErrorKind, Read};
use std::os::fd::AsRawFd;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Output, Stdio};
use std::sync::OnceLock;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use anyhow::{Context, Result, anyhow, bail};

#[derive(Debug)]
pub(crate) struct CommandTimeout {
    pub(crate) phase: &'static str,
    pub(crate) timeout: Duration,
    last_output: String,
}

impl std::fmt::Display for CommandTimeout {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let duration = if self.timeout == Duration::from_secs(5 * 60) {
            "five minutes".to_owned()
        } else if self.timeout < Duration::from_secs(1) {
            format!("{}ms", self.timeout.as_millis())
        } else {
            format!("{} seconds", self.timeout.as_secs())
        };
        if self.phase == "dependency setup" {
            write!(
                formatter,
                "dependency setup exceeded {duration} while running lake setup-file; child process terminated"
            )
        } else {
            write!(
                formatter,
                "{} exceeded {duration}; child process group terminated",
                self.phase
            )
        }?;
        if !self.last_output.is_empty() {
            write!(
                formatter,
                "\nLast {} output:\n{}",
                self.phase, self.last_output
            )?;
        }
        Ok(())
    }
}

impl std::error::Error for CommandTimeout {}

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

pub(crate) fn run_command_with_timeout(
    command: Command,
    timeout: Duration,
    phase: &'static str,
) -> Result<Output> {
    run_command_with_timeout_cancelable(command, timeout, phase, || false)
}

pub(crate) fn run_command_with_timeout_cancelable(
    mut command: Command,
    timeout: Duration,
    phase: &'static str,
    cancelled: impl Fn() -> bool,
) -> Result<Output> {
    command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .process_group(0);
    let mut child = command.spawn().context("cannot start timed command")?;
    let Some(mut stdout) = child.stdout.take() else {
        kill_process_group(&mut child);
        return Err(anyhow!("timed command has no stdout"));
    };
    let Some(mut stderr) = child.stderr.take() else {
        kill_process_group(&mut child);
        return Err(anyhow!("timed command has no stderr"));
    };
    if let Err(error) = set_nonblocking(&stdout) {
        kill_process_group(&mut child);
        return Err(error).context("cannot make timed command stdout nonblocking");
    }
    if let Err(error) = set_nonblocking(&stderr) {
        kill_process_group(&mut child);
        return Err(error).context("cannot make timed command stderr nonblocking");
    }
    let mut stdout_bytes = Vec::new();
    let mut stderr_bytes = Vec::new();
    let mut stdout_done = false;
    let mut stderr_done = false;
    let mut status = None;
    let deadline = Instant::now() + timeout;
    loop {
        if !stdout_done {
            stdout_done = drain_nonblocking(&mut stdout, &mut stdout_bytes)
                .context("cannot read timed command stdout")?;
        }
        if !stderr_done {
            stderr_done = drain_nonblocking(&mut stderr, &mut stderr_bytes)
                .context("cannot read timed command stderr")?;
        }
        if status.is_none() {
            match child.try_wait() {
                Ok(Some(exit)) => status = Some(exit),
                Ok(None) if cancelled() => {
                    terminate_and_drain(
                        &mut child,
                        &mut stdout,
                        &mut stderr,
                        &mut stdout_bytes,
                        &mut stderr_bytes,
                        &mut stdout_done,
                        &mut stderr_done,
                    );
                    return Err(anyhow!("{phase} cancelled by operator"));
                }
                Ok(None) => {}
                Err(error) => {
                    terminate_and_drain(
                        &mut child,
                        &mut stdout,
                        &mut stderr,
                        &mut stdout_bytes,
                        &mut stderr_bytes,
                        &mut stdout_done,
                        &mut stderr_done,
                    );
                    return Err(error).context("cannot wait for timed command");
                }
            }
        }
        if status.is_some() && stdout_done && stderr_done {
            break;
        }
        if Instant::now() >= deadline {
            terminate_and_drain(
                &mut child,
                &mut stdout,
                &mut stderr,
                &mut stdout_bytes,
                &mut stderr_bytes,
                &mut stdout_done,
                &mut stderr_done,
            );
            return Err(CommandTimeout {
                phase,
                timeout,
                last_output: recent_output(&stderr_bytes),
            }
            .into());
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    Ok(Output {
        status: status.expect("timed command status is present"),
        stdout: stdout_bytes,
        stderr: stderr_bytes,
    })
}

fn set_nonblocking(file: &impl AsRawFd) -> std::io::Result<()> {
    let descriptor = file.as_raw_fd();
    let flags = unsafe { libc::fcntl(descriptor, libc::F_GETFL) };
    if flags < 0 {
        return Err(std::io::Error::last_os_error());
    }
    if unsafe { libc::fcntl(descriptor, libc::F_SETFL, flags | libc::O_NONBLOCK) } < 0 {
        return Err(std::io::Error::last_os_error());
    }
    Ok(())
}

fn drain_nonblocking<R: Read>(reader: &mut R, bytes: &mut Vec<u8>) -> std::io::Result<bool> {
    let mut buffer = [0_u8; 64 * 1024];
    loop {
        match reader.read(&mut buffer) {
            Ok(0) => return Ok(true),
            Ok(read) => bytes.extend_from_slice(&buffer[..read]),
            Err(error) if error.kind() == ErrorKind::WouldBlock => return Ok(false),
            Err(error) if error.kind() == ErrorKind::Interrupted => continue,
            Err(error) => return Err(error),
        }
    }
}

fn terminate_and_drain(
    child: &mut Child,
    stdout: &mut impl Read,
    stderr: &mut impl Read,
    stdout_bytes: &mut Vec<u8>,
    stderr_bytes: &mut Vec<u8>,
    stdout_done: &mut bool,
    stderr_done: &mut bool,
) {
    // The direct child may have exited while a descendant still owns one of
    // these pipe ends. Kill the whole group, then give the pipes a short,
    // bounded chance to close; never join an unbounded reader here.
    kill_process_group(child);
    let deadline = Instant::now() + Duration::from_secs(1);
    while !*stdout_done || !*stderr_done {
        if !*stdout_done {
            *stdout_done = drain_nonblocking(stdout, stdout_bytes).unwrap_or(true);
        }
        if !*stderr_done {
            *stderr_done = drain_nonblocking(stderr, stderr_bytes).unwrap_or(true);
        }
        if (*stdout_done && *stderr_done) || Instant::now() >= deadline {
            break;
        }
        std::thread::sleep(Duration::from_millis(5));
    }
}

fn recent_output(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes)
        .lines()
        .filter(|line| !line.trim().is_empty())
        .rev()
        .take(8)
        .map(|line| truncate_line(line, 240))
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .collect::<Vec<_>>()
        .join("\n")
}

fn kill_process_group(child: &mut Child) {
    let pid = child.id() as i32;
    unsafe {
        libc::kill(-pid, libc::SIGKILL);
    }
    let _ = child.wait();
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

pub fn build_error_diagnostic(output: &str) -> Option<&str> {
    output.lines().find_map(|line| {
        let message = line.trim().strip_prefix("error:")?.trim();
        (!message.is_empty() && message != "build failed").then_some(message)
    })
}

pub fn enriched_validation_detail(
    detail: Option<&str>,
    build_output: Option<&str>,
) -> Option<String> {
    let detail = detail?;
    if detail == "build failed"
        && let Some(diagnostic) = build_output.and_then(build_error_diagnostic)
    {
        return Some(format!("build failed: {diagnostic}"));
    }
    Some(detail.to_owned())
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
        || normalized
            .split_whitespace()
            .last()
            .is_some_and(|term| matches!(term, "body" | "implementation" | "proof" | "source"))
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn timed_command_does_not_wait_for_an_inherited_pipe_after_child_exit() {
        let mut command = Command::new("sh");
        command.args(["-c", "sleep 30 & exit 0"]);
        let started = Instant::now();
        let error = run_command_with_timeout(command, Duration::from_millis(100), "fixture")
            .expect_err("an inherited pipe must not hide the child exit");

        assert!(started.elapsed() < Duration::from_secs(2));
        assert!(error.to_string().contains("fixture exceeded 100ms"));
    }

    #[test]
    fn legacy_build_failure_details_use_the_stored_diagnostic() {
        assert_eq!(
            enriched_validation_detail(
                Some("build failed"),
                Some("warning: noise\nerror: Demo.lean:7:2: unknown identifier\n"),
            )
            .as_deref(),
            Some("build failed: Demo.lean:7:2: unknown identifier")
        );
        assert_eq!(
            enriched_validation_detail(Some("build failed"), Some("error: build failed\n"))
                .as_deref(),
            Some("build failed")
        );
    }
}
