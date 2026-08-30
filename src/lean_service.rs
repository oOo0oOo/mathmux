use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::os::fd::AsRawFd;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Stdio};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use anyhow::{Context, Result, bail, ensure};
use serde::Serialize;
use serde::de::DeserializeOwned;

use crate::coordination::{lock_exclusive, open_lock};
use crate::git::{lake_command, lake_executable};
use crate::repo::Repo;
use crate::util::hash_bytes;

const SERVICE_SOURCE: &str = include_str!("MathmuxLeanService.lean");

const SERVICE_FILES: &[(&str, &str)] = &[("MathmuxLeanService.lean", SERVICE_SOURCE)];

const COMPILE_ORDER: &[&str] = &["MathmuxLeanService.lean"];

#[derive(Debug)]
pub(crate) enum ServiceRequestError {
    Timeout(Duration),
    Failed(anyhow::Error),
}

impl std::fmt::Display for ServiceRequestError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Timeout(timeout) => write!(
                formatter,
                "Lean service response exceeded {}ms",
                timeout.as_millis()
            ),
            Self::Failed(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for ServiceRequestError {}

pub(crate) struct LeanServiceProcess {
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
    stderr: Arc<Mutex<String>>,
}

impl LeanServiceProcess {
    pub(crate) fn start(repo: &Repo, workspace: &Path, arguments: &[String]) -> Result<Self> {
        let root = prepare(repo, workspace)?;
        let lean_path = lean_path(repo, workspace, &root)?;
        let mut command = lake_command(repo, workspace);
        command
            .args(["env", "lean"])
            .arg("-R")
            .arg(&root)
            .arg("--run")
            .arg(root.join("MathmuxLeanService.lean"))
            .args(arguments)
            .env("LEAN_PATH", lean_path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        command.process_group(0);
        let mut child = command.spawn().context("cannot start Lean service")?;
        let stdin = child.stdin.take().context("Lean service has no stdin")?;
        let stdout = BufReader::new(child.stdout.take().context("Lean service has no stdout")?);
        let mut stderr_pipe = child.stderr.take().context("Lean service has no stderr")?;
        let stderr = Arc::new(Mutex::new(String::new()));
        let stderr_copy = stderr.clone();
        std::thread::spawn(move || {
            let mut reader = BufReader::new(&mut stderr_pipe);
            let mut line = String::new();
            loop {
                line.clear();
                let Ok(read) = reader.read_line(&mut line) else {
                    break;
                };
                if read == 0 {
                    break;
                }
                stderr_copy
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner)
                    .push_str(&line);
            }
        });
        Ok(Self {
            child,
            stdin,
            stdout,
            stderr,
        })
    }

    pub(crate) fn request<Request, Response>(
        &mut self,
        request: &Request,
        timeout: Duration,
    ) -> std::result::Result<Response, ServiceRequestError>
    where
        Request: Serialize,
        Response: DeserializeOwned,
    {
        serde_json::to_writer(&mut self.stdin, request)
            .map_err(|error| ServiceRequestError::Failed(error.into()))?;
        self.stdin
            .write_all(b"\n")
            .and_then(|()| self.stdin.flush())
            .map_err(|error| ServiceRequestError::Failed(error.into()))?;
        let line = self.read_line(timeout)?;
        serde_json::from_str(&line).map_err(|error| {
            ServiceRequestError::Failed(
                anyhow::Error::new(error)
                    .context(format!("invalid Lean service response: {}", line.trim())),
            )
        })
    }

    pub(crate) fn read_ready(&mut self, timeout: Duration) -> Result<serde_json::Value> {
        let line = self
            .read_line(timeout)
            .map_err(|error| anyhow::anyhow!(error))?;
        serde_json::from_str(&line)
            .with_context(|| format!("invalid Lean service startup response: {}", line.trim()))
    }

    fn read_line(&mut self, timeout: Duration) -> std::result::Result<String, ServiceRequestError> {
        let mut descriptor = libc::pollfd {
            fd: self.stdout.get_ref().as_raw_fd(),
            events: libc::POLLIN,
            revents: 0,
        };
        let ready = unsafe {
            libc::poll(
                &mut descriptor,
                1,
                timeout.as_millis().min(i32::MAX as u128) as i32,
            )
        };
        if ready == 0 {
            self.kill(libc::SIGKILL);
            return Err(ServiceRequestError::Timeout(timeout));
        }
        if ready < 0 {
            return Err(ServiceRequestError::Failed(
                std::io::Error::last_os_error().into(),
            ));
        }
        let mut line = String::new();
        let read = self
            .stdout
            .read_line(&mut line)
            .map_err(|error| ServiceRequestError::Failed(anyhow::Error::from(error)))?;
        if read == 0 {
            let stderr = self.stderr();
            return Err(ServiceRequestError::Failed(anyhow::anyhow!(
                "Lean service exited: {stderr}"
            )));
        }
        Ok(line)
    }

    pub(crate) fn alive(&mut self) -> bool {
        matches!(self.child.try_wait(), Ok(None))
    }

    pub(crate) fn rss_kib(&self) -> Option<u64> {
        let group = self.child.id() as i32;
        let mut total = 0_u64;
        let mut found = false;
        for process in fs::read_dir("/proc").ok()?.flatten() {
            let Some(pid) = process
                .file_name()
                .to_str()
                .and_then(|name| name.parse::<i32>().ok())
            else {
                continue;
            };
            if unsafe { libc::getpgid(pid) } != group {
                continue;
            }
            let Some(rss) = fs::read_to_string(process.path().join("status"))
                .ok()
                .and_then(|status| {
                    status.lines().find_map(|line| {
                        line.strip_prefix("VmRSS:")?
                            .split_whitespace()
                            .next()?
                            .parse::<u64>()
                            .ok()
                    })
                })
            else {
                continue;
            };
            total = total.saturating_add(rss);
            found = true;
        }
        found.then_some(total)
    }

    pub(crate) fn stderr_len(&self) -> usize {
        self.stderr
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .len()
    }

    pub(crate) fn stderr_since(&self, offset: usize) -> String {
        let stderr = self
            .stderr
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        stderr.get(offset..).unwrap_or_default().to_owned()
    }

    pub(crate) fn stderr(&self) -> String {
        self.stderr
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clone()
    }

    fn kill(&mut self, signal: i32) {
        if matches!(self.child.try_wait(), Ok(Some(_))) {
            return;
        }
        let pid = self.child.id() as i32;
        unsafe {
            libc::kill(-pid, signal);
        }
        let _ = self.child.wait();
    }
}

impl Drop for LeanServiceProcess {
    fn drop(&mut self) {
        self.kill(libc::SIGTERM);
    }
}

pub(crate) fn prepare(repo: &Repo, workspace: &Path) -> Result<PathBuf> {
    fs::create_dir_all(&repo.state_dir)?;
    let lock_path = repo.state_dir.join("lean-service.lock");
    let lock =
        open_lock(&lock_path).with_context(|| format!("cannot open {}", lock_path.display()))?;
    lock_exclusive(&lock)?;

    let fingerprint = generation_fingerprint(workspace);
    let root = repo.state_dir.join("lean-service").join(&fingerprint[..16]);
    let marker = root.join("built");
    if fs::read_to_string(&marker).ok().as_deref() == Some(fingerprint.as_str()) {
        return Ok(root);
    }

    for (relative, source) in SERVICE_FILES {
        let path = root.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(path, source)?;
    }
    let lean_path = lean_path(repo, workspace, &root)?;
    for relative in COMPILE_ORDER {
        let source = root.join(relative);
        let output = source.with_extension("olean");
        let result = std::process::Command::new("timeout")
            .args(["--signal=KILL", "180s"])
            .arg(lake_executable())
            .args(["env", "lean"])
            .arg("-R")
            .arg(&root)
            .arg("-o")
            .arg(&output)
            .arg(&source)
            .current_dir(workspace)
            .env("LAKE_ARTIFACT_CACHE", "true")
            .env("LAKE_CACHE_DIR", &repo.cache_dir)
            .env("LEAN_PATH", &lean_path)
            .stdin(Stdio::null())
            .output()
            .with_context(|| format!("cannot compile Lean service module {relative}"))?;
        if !result.status.success() {
            let detail = if result.stderr.is_empty() {
                String::from_utf8_lossy(&result.stdout)
            } else {
                String::from_utf8_lossy(&result.stderr)
            };
            bail!(
                "cannot compile Lean service module {relative}: {}",
                detail.trim()
            );
        }
    }
    fs::write(marker, &fingerprint)?;
    Ok(root)
}

pub(crate) fn generation_name(workspace: &Path) -> String {
    generation_fingerprint(workspace)[..16].to_owned()
}

fn generation_fingerprint(workspace: &Path) -> String {
    let toolchain = fs::read_to_string(workspace.join("lean-toolchain")).unwrap_or_default();
    let mut material = toolchain.into_bytes();
    for (_, source) in SERVICE_FILES {
        material.extend_from_slice(source.as_bytes());
    }
    hash_bytes(&material)
}

fn lean_path(repo: &Repo, workspace: &Path, root: &Path) -> Result<String> {
    let output = lake_command(repo, workspace)
        .args(["env", "printenv", "LEAN_PATH"])
        .output()
        .context("cannot read the Lake search path")?;
    ensure!(
        output.status.success(),
        "Lake did not provide a Lean search path"
    );
    Ok(format!(
        "{}:{}",
        root.display(),
        String::from_utf8_lossy(&output.stdout).trim()
    ))
}

pub(crate) fn reap_stale_processes(repo: &Repo) -> usize {
    let Ok(processes) = fs::read_dir("/proc") else {
        return 0;
    };
    let service_root = repo.state_dir.join("lean-service");
    let service_root = service_root.as_os_str().as_bytes();
    let own_group = unsafe { libc::getpgrp() };
    let mut groups = std::collections::HashSet::new();
    for process in processes.flatten() {
        let Some(pid) = process
            .file_name()
            .to_str()
            .and_then(|name| name.parse::<i32>().ok())
        else {
            continue;
        };
        let Ok(command) = fs::read(process.path().join("cmdline")) else {
            continue;
        };
        if !command
            .split(|byte| *byte == 0)
            .any(|argument| argument.starts_with(service_root))
        {
            continue;
        }
        let group = unsafe { libc::getpgid(pid) };
        if group == pid && group != own_group && !has_daemon_parent(&process.path()) {
            groups.insert(group);
        }
    }
    for group in &groups {
        unsafe {
            libc::kill(-group, libc::SIGTERM);
        }
    }
    groups.len()
}

fn has_daemon_parent(process: &Path) -> bool {
    let parent = fs::read_to_string(process.join("status"))
        .ok()
        .and_then(|status| {
            status
                .lines()
                .find_map(|line| line.strip_prefix("PPid:")?.trim().parse::<u32>().ok())
        });
    let Some(parent) = parent else {
        return false;
    };
    fs::read(
        process
            .parent()
            .unwrap_or(Path::new("/proc"))
            .join(parent.to_string())
            .join("cmdline"),
    )
    .is_ok_and(|command| {
        command
            .split(|byte| *byte == 0)
            .any(|argument| argument == b"__daemon")
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn live_daemon_service_is_not_stale() {
        let proc = tempdir().unwrap();
        let worker = proc.path().join("101");
        let daemon = proc.path().join("42");
        fs::create_dir(&worker).unwrap();
        fs::create_dir(&daemon).unwrap();
        fs::write(worker.join("status"), "Name:\tlean\nPPid:\t42\n").unwrap();
        fs::write(daemon.join("cmdline"), b"mathmux\0__daemon\0--repo\0Demo").unwrap();
        assert!(has_daemon_parent(&worker));
        fs::write(daemon.join("cmdline"), b"init\0").unwrap();
        assert!(!has_daemon_parent(&worker));
    }

    #[test]
    fn source_context_failures_keep_a_copy_ready_search_hint() {
        assert!(
            SERVICE_SOURCE
                .contains("s!\"\\nnext: `mathmux search {request.file_name}:{request.line}`\"")
        );
        assert_eq!(
            SERVICE_SOURCE.matches("sourceContextHint request").count(),
            3
        );
    }
}
