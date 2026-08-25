use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use anyhow::{Context, Result, bail, ensure};
use notify::{RecommendedWatcher, RecursiveMode, Watcher};

use crate::check::Checker;
use crate::git::{self, dirty_lean_files, dirty_paths};
use crate::protocol::{Command, Request, Response};
use crate::repo::Repo;
use crate::state::{State, Submission};
use crate::util::{clean_line, now_unix_ms};
use crate::validation::ValidationQueue;

pub fn run(repo: Repo) -> Result<()> {
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
    let validation = ValidationQueue::start(repo.clone(), state.clone())?;
    let watcher = WorkspaceWatcher::new(state.clone(), checker.clone())?;
    for workspace in state.list_workspaces()? {
        watcher.watch(&workspace.path)?;
    }
    let service = Arc::new(Service {
        repo: repo.clone(),
        state,
        checker,
        validation,
        watcher,
        mutations: Mutex::new(()),
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
        let has_workers = service
            .checker
            .evict_idle_workers(Duration::from_secs(5 * 60));
        let has_jobs = service.state.has_validation_work().unwrap_or(true);
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
    let mut line = String::new();
    BufReader::new(stream.try_clone()?).read_line(&mut line)?;
    let response = match serde_json::from_str::<Request>(&line) {
        Ok(request) => match service.handle(request) {
            Ok(summary) => Response::ok(summary),
            Err(error) => Response::error(format!("{error:#}")),
        },
        Err(error) => Response::error(format!("invalid request: {error}")),
    };
    serde_json::to_writer(&mut stream, &response)?;
    stream.write_all(b"\n")?;
    stream.flush()?;
    Ok(())
}

struct Service {
    repo: Repo,
    state: State,
    checker: Arc<Checker>,
    validation: ValidationQueue,
    watcher: WorkspaceWatcher,
    mutations: Mutex<()>,
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
                    "{} {} {}",
                    workspace.reference,
                    workspace.name,
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
                        format!("{} {} {} dirty", workspace.reference, workspace.name, dirty)
                    })
                    .collect::<Vec<_>>()
                    .join("\n"))
            }
            Command::WsDelete { name } => {
                let _guard = self.mutations.lock().expect("mutation lock poisoned");
                let workspace = self
                    .state
                    .workspace_named(&name)?
                    .with_context(|| format!("unknown workspace {name}"))?;
                self.watcher.unwatch(&workspace.path);
                self.checker.evict_worker(&workspace.reference);
                git::delete_workspace(&self.repo, &self.state, &name)?;
                Ok(format!(
                    "deleted {} {}",
                    workspace.reference, workspace.name
                ))
            }
            Command::Check { file } => {
                let workspace = self.state.workspace_for_path(&cwd)?;
                let outcomes = self
                    .checker
                    .check(&workspace, file.as_deref().map(Path::new))?;
                Ok(outcomes
                    .iter()
                    .map(|outcome| {
                        format!(
                            "{} {} {}ms",
                            outcome.reference, outcome.target, outcome.elapsed_ms
                        )
                    })
                    .collect::<Vec<_>>()
                    .join("\n"))
            }
            Command::Sync => {
                let _guard = self.mutations.lock().expect("mutation lock poisoned");
                let workspace = self.state.workspace_for_path(&cwd)?;
                let result = git::sync(&self.repo, &workspace)?;
                self.checker.invalidate_workspace(&workspace.reference)?;
                let status = if result.clean { "clean" } else { "conflict" };
                let reference =
                    self.state
                        .add_sync(&workspace.reference, status, &result.detail)?;
                if result.clean {
                    Ok(format!("{reference} synced"))
                } else {
                    bail!("{reference} {}", clean_line(&result.detail))
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
                    validated_by: None,
                    created_at: now_unix_ms(),
                })?;
                self.checker.invalidate_workspace(&workspace.reference)?;
                self.validation.wake();
                Ok(format!("{reference} accepted; validation queued"))
            }
            Command::Show { reference } => self.state.show(&reference),
        }
    }
}

struct WorkspaceWatcher {
    watcher: Mutex<RecommendedWatcher>,
}

impl WorkspaceWatcher {
    fn new(state: State, checker: Arc<Checker>) -> Result<Self> {
        let watcher = notify::recommended_watcher(move |event: notify::Result<notify::Event>| {
            let Ok(event) = event else { return };
            for path in event.paths {
                if path.components().any(|part| part.as_os_str() == ".lake") {
                    continue;
                }
                let relevant = path.extension().is_some_and(|extension| {
                    matches!(extension.to_str(), Some("lean" | "toml" | "json"))
                }) || path
                    .file_name()
                    .is_some_and(|name| name == "lean-toolchain");
                if !relevant {
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
