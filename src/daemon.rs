use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use anyhow::{Context, Result, bail, ensure};
use notify::{RecommendedWatcher, RecursiveMode, Watcher};

use crate::check::{CheckOutcome, Checker};
use crate::git::{self, dirty_lean_files, dirty_paths};
use crate::protocol::{Command, Request, Response};
use crate::repo::Repo;
use crate::search::Searcher;
use crate::state::{State, Submission};
use crate::status;
use crate::util::{build_id, clean_line, now_unix_ms, resident_memory_kib, truncate_middle};
use crate::validation::ValidationQueue;

pub fn run(repo: Repo) -> Result<()> {
    let _ = build_id();
    if repo.socket_path.exists() {
        match UnixStream::connect(&repo.socket_path) {
            Ok(_) => bail!("mathmux daemon is already running"),
            Err(_) => fs::remove_file(&repo.socket_path)?,
        }
    }
    git::reconcile_integration(&repo)?;
    let listener = UnixListener::bind(&repo.socket_path)
        .with_context(|| format!("cannot bind {}", repo.socket_path.display()))?;
    fs::set_permissions(&repo.socket_path, fs::Permissions::from_mode(0o600))?;
    listener.set_nonblocking(true)?;

    let state = State::new(&repo.db_path)?;
    let checker = Arc::new(Checker::new(repo.clone(), state.clone())?);
    let searcher = Searcher::new(repo.clone(), state.clone())?;
    let retiring = Arc::new(AtomicBool::new(false));
    let validation = ValidationQueue::start(repo.clone(), state.clone(), retiring.clone())?;
    let watcher = WorkspaceWatcher::new(state.clone(), checker.clone())?;
    for workspace in state.list_workspaces()? {
        git::prepare_workspace(&repo, &workspace.path)?;
        watcher.watch(&workspace.path)?;
    }
    let service = Arc::new(Service {
        repo: repo.clone(),
        state,
        checker,
        searcher,
        validation,
        watcher,
        mutations: Mutex::new(()),
        retiring: retiring.clone(),
    });
    let clients = Arc::new(AtomicUsize::new(0));
    let mut last_activity = Instant::now();
    let grace = Duration::from_secs(
        std::env::var("MATHMUX_IDLE_SECONDS")
            .ok()
            .and_then(|value| value.parse().ok())
            .unwrap_or(30),
    );

    loop {
        match listener.accept() {
            Ok((stream, _)) => {
                last_activity = Instant::now();
                clients.fetch_add(1, Ordering::SeqCst);
                let service = service.clone();
                let clients = clients.clone();
                thread::spawn(move || {
                    let _ = serve_client(stream, &service);
                    clients.fetch_sub(1, Ordering::SeqCst);
                });
            }
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                thread::sleep(Duration::from_millis(50));
            }
            Err(error) => return Err(error.into()),
        }
        let has_check_workers = service
            .checker
            .evict_idle_workers(Duration::from_secs(5 * 60));
        let has_search_worker = service
            .searcher
            .evict_idle_worker(Duration::from_secs(5 * 60));
        let has_workers = has_check_workers || has_search_worker;
        let has_jobs = service.state.has_validation_work().unwrap_or(true);
        if retiring.load(Ordering::SeqCst)
            && clients.load(Ordering::SeqCst) == 0
            && !service.state.has_running_validation().unwrap_or(true)
        {
            break;
        }
        if clients.load(Ordering::SeqCst) == 0
            && !has_workers
            && !has_jobs
            && last_activity.elapsed() >= grace
        {
            break;
        }
    }
    let _ = fs::remove_file(&repo.socket_path);
    Ok(())
}

fn serve_client(mut stream: UnixStream, service: &Service) -> Result<()> {
    let started = Instant::now();
    let mut line = String::new();
    BufReader::new(stream.try_clone()?).read_line(&mut line)?;
    let mut response = match serde_json::from_str::<Request>(&line) {
        Ok(request)
            if service.retiring.load(Ordering::SeqCst)
                || (!request.build.is_empty() && request.build != build_id()) =>
        {
            service.retiring.store(true, Ordering::SeqCst);
            if request.command.transport_retry_safe()
                && service.state.has_running_validation().unwrap_or(false)
            {
                match service.handle(request) {
                    Ok(summary) => Response::ok(summary),
                    Err(error) => Response::error(format!("{error:#}")),
                }
            } else {
                Response::retry()
            }
        }
        Ok(request) => match service.handle(request) {
            Ok(summary) => Response::ok(summary),
            Err(error) => Response::error(format!("{error:#}")),
        },
        Err(error) => Response::error(format!("invalid request: {error}")),
    };
    response.daemon_ms = started.elapsed().as_millis() as u64;
    response.rss_kib = resident_memory_kib();
    serde_json::to_writer(&mut stream, &response)?;
    stream.write_all(b"\n")?;
    stream.flush()?;
    Ok(())
}

struct Service {
    repo: Repo,
    state: State,
    checker: Arc<Checker>,
    searcher: Searcher,
    validation: ValidationQueue,
    watcher: WorkspaceWatcher,
    mutations: Mutex<()>,
    retiring: Arc<AtomicBool>,
}

impl Service {
    fn handle(&self, request: Request) -> Result<String> {
        let cwd = PathBuf::from(request.cwd);
        match request.command {
            Command::WsCreate { name } => {
                let _guard = self.mutations.lock().expect("mutation lock poisoned");
                let workspace = git::create_workspace(&self.repo, &self.state, &name)?;
                self.watcher.watch(&workspace.path)?;
                Ok(format!(
                    "{} {}",
                    workspace.reference,
                    workspace.path.display()
                ))
            }
            Command::WsList => {
                let workspaces = self.state.list_workspaces()?;
                if workspaces.is_empty() {
                    return Ok("no workspaces".into());
                }
                Ok(workspaces
                    .iter()
                    .map(|workspace| {
                        let dirty = dirty_paths(&workspace.path)
                            .map(|paths| paths.len())
                            .unwrap_or(0);
                        if dirty == 0 {
                            format!("{} {} clean", workspace.reference, workspace.name)
                        } else {
                            format!("{} {} dirty:{dirty}", workspace.reference, workspace.name)
                        }
                    })
                    .collect::<Vec<_>>()
                    .join("\n"))
            }
            Command::Status => status::render(&self.repo, &self.state),
            Command::WsDelete { name } => {
                let _guard = self.mutations.lock().expect("mutation lock poisoned");
                let workspace = self
                    .state
                    .workspace_named(&name)?
                    .with_context(|| format!("unknown workspace {name}"))?;
                self.watcher.unwatch(&workspace.path);
                self.checker.evict_worker(&workspace.reference);
                git::delete_workspace(&self.repo, &self.state, &name)?;
                Ok(format!("{} deleted", workspace.reference))
            }
            Command::Check { file, profile } => {
                let workspace = self.state.workspace_for_path(&cwd)?;
                git::prepare_workspace(&self.repo, &workspace.path)?;
                let outcome =
                    self.checker
                        .check(&workspace, file.as_deref().map(Path::new), profile)?;
                let summary = check_summary(&outcome);
                if outcome.ok {
                    Ok(format!("ok {summary}"))
                } else {
                    bail!(summary)
                }
            }
            Command::Search { query } => {
                let workspace = self.state.workspace_for_path(&cwd)?;
                git::prepare_workspace(&self.repo, &workspace.path)?;
                self.searcher.search(&workspace, &cwd, &query)
            }
            Command::Sync => {
                let _guard = self.mutations.lock().expect("mutation lock poisoned");
                let workspace = self.state.workspace_for_path(&cwd)?;
                let result = git::sync(&self.repo, &workspace)?;
                self.checker.invalidate_workspace(&workspace.reference);
                let status = if result.clean { "clean" } else { "conflict" };
                let reference =
                    self.state
                        .add_sync(&workspace.reference, status, &result.detail)?;
                if result.clean {
                    Ok(format!("ok {reference}"))
                } else {
                    bail!("{reference} conflict: {}", clean_line(&result.detail))
                }
            }
            Command::Submit { message } => {
                let _guard = self.mutations.lock().expect("mutation lock poisoned");
                let workspace = self.state.workspace_for_path(&cwd)?;
                let dirty = dirty_paths(&workspace.path)?;
                ensure!(!dirty.is_empty(), "workspace has no changes to submit");
                let targets = dirty_lean_files(&workspace.path)?;
                ensure!(
                    !targets.is_empty(),
                    "submission has no checked Lean changes"
                );
                let checks = self.checker.valid_certificates(&workspace, &targets)?;
                let message = message
                    .filter(|value| !value.trim().is_empty())
                    .unwrap_or_else(|| default_submit_message(&dirty));
                let result = git::submit(&self.repo, &workspace, &message)?;
                let reference = self.state.next_ref('s')?;
                self.state.add_submission(&Submission {
                    reference: reference.clone(),
                    workspace_ref: workspace.reference.clone(),
                    workspace_commit: result.workspace_commit,
                    main_commit: result.main_commit,
                    base_commit: result.base_commit,
                    checks,
                    validation_status: "queued".into(),
                    validation_detail: None,
                    build_output: None,
                    axioms: Vec::new(),
                    sorries: Vec::new(),
                    validation_duration_ms: None,
                    validated_by: None,
                    created_at: now_unix_ms(),
                })?;
                self.checker.invalidate_workspace(&workspace.reference);
                self.validation.wake();
                Ok(reference)
            }
            Command::Show { reference, all } => self.state.show(&reference, all),
        }
    }
}

fn check_summary(outcome: &CheckOutcome) -> String {
    const DIAGNOSTIC_PREVIEW_CHARS: usize = 1200;

    let mut output = format!("{} {}ms", outcome.reference, outcome.elapsed_ms);
    for warning in outcome.warnings.iter().take(3) {
        output.push_str(&format!("\nwarning {}", clean_line(&warning.text)));
    }
    if outcome.warnings.len() > 3 {
        output.push_str(&format!(
            "\n+{} warnings; show {}",
            outcome.warnings.len() - 3,
            outcome.reference
        ));
    }
    if !outcome.ok {
        if let Some(diagnostic) = outcome.diagnostics.first() {
            let detail = clean_line(&diagnostic.text);
            output.push_str(&format!(
                "\n{}",
                truncate_middle(&detail, DIAGNOSTIC_PREVIEW_CHARS)
            ));
            if let Some(context) = &diagnostic.context {
                output.push('\n');
                output.push_str(context);
            }
            if detail.chars().count() > DIAGNOSTIC_PREVIEW_CHARS {
                output.push_str(&format!("\nfull diagnostic: show {}", outcome.reference));
            }
        }
        if outcome.diagnostics.len() > 1 {
            output.push_str(&format!(
                "\n+{} diagnostics; show {}",
                outcome.diagnostics.len() - 1,
                outcome.reference
            ));
        }
    }
    if let Some(profile) = &outcome.profile {
        output.push('\n');
        output.push_str(&profile.render());
    }
    output
}

fn default_submit_message(paths: &[PathBuf]) -> String {
    if let [path] = paths {
        format!("Update {}", path.display())
    } else {
        format!("Update {} files", paths.len())
    }
}

struct WorkspaceWatcher {
    watcher: Mutex<RecommendedWatcher>,
}

impl WorkspaceWatcher {
    fn new(state: State, checker: Arc<Checker>) -> Result<Self> {
        let watcher = notify::recommended_watcher(move |event: notify::Result<notify::Event>| {
            let Ok(event) = event else { return };
            if matches!(event.kind, notify::EventKind::Access(_)) {
                return;
            }
            for path in event.paths {
                if path.components().any(|part| part.as_os_str() == ".lake") {
                    continue;
                }
                if !path
                    .extension()
                    .is_some_and(|extension| extension == "lean")
                {
                    continue;
                }
                if let Ok(workspaces) = state.list_workspaces()
                    && let Some(workspace) = workspaces
                        .iter()
                        .find(|workspace| path.starts_with(&workspace.path))
                {
                    checker.handle_filesystem_change(workspace, &path);
                }
            }
        })?;
        Ok(Self {
            watcher: Mutex::new(watcher),
        })
    }

    fn watch(&self, path: &Path) -> Result<()> {
        self.watcher
            .lock()
            .expect("watcher poisoned")
            .watch(path, RecursiveMode::Recursive)?;
        Ok(())
    }

    fn unwatch(&self, path: &Path) {
        let _ = self.watcher.lock().expect("watcher poisoned").unwatch(path);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::Diagnostic;

    #[test]
    fn check_summary_keeps_source_and_both_ends_of_long_diagnostics() {
        let diagnostic = format!(
            "Demo.Proof:3:1: error: {} final target",
            "detail ".repeat(300)
        );
        let summary = check_summary(&CheckOutcome {
            reference: "c1".into(),
            ok: false,
            elapsed_ms: 10,
            warnings: Vec::new(),
            diagnostics: vec![Diagnostic {
                kind: "error".into(),
                text: diagnostic,
                context: Some(">    3 | failing tactic".into()),
            }],
            profile: None,
        });
        assert!(summary.contains("Demo.Proof:3:1"));
        assert!(summary.contains("final target"));
        assert!(summary.contains(">    3 | failing tactic"));
        assert!(summary.contains("full diagnostic: show c1"));
    }
}
