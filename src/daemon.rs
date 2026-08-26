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
use notify::{Config, RecommendedWatcher, RecursiveMode, Watcher};

use crate::check::{CheckOutcome, Checker};
use crate::git::{self, dirty_lean_files, dirty_paths};
use crate::issue::{TelemetryOperation, TelemetryStore, development_enabled};
use crate::protocol::{Command, Progress, Request, Response};
use crate::repo::Repo;
use crate::search::Searcher;
use crate::state::{State, Submission};
use crate::status;
use crate::util::{
    build_generation, build_id, clean_line, now_unix_ms, resident_memory_kib, truncate_middle,
};
use crate::validation::ValidationQueue;

pub fn run(repo: Repo) -> Result<()> {
    let startup_started = Instant::now();
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

    let phase = Instant::now();
    let state = State::new(&repo.db_path)?;
    let state_ms = phase.elapsed().as_millis() as u64;
    let checker = Arc::new(Checker::new(repo.clone(), state.clone())?);
    let phase = Instant::now();
    let searcher = Searcher::new(repo.clone(), state.clone(), checker.clone())?;
    let search_ms = phase.elapsed().as_millis() as u64;
    let retiring = Arc::new(AtomicBool::new(false));
    let phase = Instant::now();
    let validation = ValidationQueue::start(repo.clone(), state.clone(), retiring.clone())?;
    let validation_ms = phase.elapsed().as_millis() as u64;
    let phase = Instant::now();
    let watcher = WorkspaceWatcher::new(state.clone(), checker.clone())?;
    let workspaces = state.list_workspaces()?;
    for workspace in &workspaces {
        git::prepare_workspace(&repo, &workspace.path)?;
        watcher.watch(&workspace.path)?;
    }
    let workspaces_ms = phase.elapsed().as_millis() as u64;
    if development_enabled()
        && let Ok(store) = TelemetryStore::global()
    {
        let detail = format!(
            "state={state_ms}ms search={search_ms}ms validation={validation_ms}ms workspaces={workspaces_ms}ms count={}",
            workspaces.len()
        );
        let _ = store.record_operation(
            &repo,
            &TelemetryOperation {
                workspace: None,
                verb: "daemon_startup",
                reference: None,
                ok: true,
                duration_ms: startup_started.elapsed().as_millis() as u64,
                detail: &detail,
                rss_kib: resident_memory_kib(),
            },
        );
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
    let mut listener = Some(listener);

    loop {
        if let Some(listener) = &listener {
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
        } else {
            thread::sleep(Duration::from_millis(50));
        }
        let active_clients = clients.load(Ordering::SeqCst);
        if retiring.load(Ordering::SeqCst) && listener.take().is_some() {
            // Existing streams remain valid after unlinking a Unix socket. Let a
            // replacement daemon serve new clients while this image drains its
            // active checks and validation work.
            let _ = fs::remove_file(&repo.socket_path);
        }
        let has_workers = if active_clients == 0 {
            let has_check_workers = service
                .checker
                .evict_idle_workers(Duration::from_secs(5 * 60));
            let has_search_worker = service
                .searcher
                .evict_idle_worker(Duration::from_secs(5 * 60));
            has_check_workers || has_search_worker
        } else {
            true
        };
        let has_jobs = service.state.has_validation_work().unwrap_or(true);
        if retiring.load(Ordering::SeqCst)
            && active_clients == 0
            && !service.state.has_running_validation().unwrap_or(true)
        {
            break;
        }
        if active_clients == 0
            && !has_workers
            && !has_jobs
            && last_activity.elapsed() >= grace
        {
            break;
        }
    }
    if listener.is_some() {
        let _ = fs::remove_file(&repo.socket_path);
    }
    Ok(())
}

fn serve_client(mut stream: UnixStream, service: &Service) -> Result<()> {
    let started = Instant::now();
    let mut line = String::new();
    BufReader::new(stream.try_clone()?).read_line(&mut line)?;
    let mut response = match serde_json::from_str::<Request>(&line) {
        Ok(request) => {
            if client_build_is_newer(&request) {
                service.retiring.store(true, Ordering::SeqCst);
                Response::retry()
            } else {
                let mut report = |progress: &str| {
                    let _ = serde_json::to_writer(
                        &mut stream,
                        &Progress {
                            progress: progress.to_owned(),
                        },
                    );
                    let _ = stream.write_all(b"\n");
                    let _ = stream.flush();
                };
                handled_response(service, request, &mut report)
            }
        }
        Err(error) => Response::error(format!("invalid request: {error}")),
    };
    response.daemon_ms = started.elapsed().as_millis() as u64;
    response.rss_kib = resident_memory_kib();
    serde_json::to_writer(&mut stream, &response)?;
    stream.write_all(b"\n")?;
    stream.flush()?;
    Ok(())
}

fn client_build_is_newer(request: &Request) -> bool {
    build_precedes(
        build_id(),
        build_generation(),
        &request.build,
        request.generation,
    )
}

fn build_precedes(
    current: &str,
    current_generation: u64,
    other: &str,
    other_generation: u64,
) -> bool {
    !other.is_empty() && other != current && other_generation > current_generation
}

fn handled_response(
    service: &Service,
    request: Request,
    report: &mut dyn FnMut(&str),
) -> Response {
    match service.handle(request, report) {
        Ok(summary) => Response::ok(summary),
        Err(error) => Response::error(format!("{error:#}")),
    }
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
    fn handle(&self, request: Request, report: &mut dyn FnMut(&str)) -> Result<String> {
        let cwd = PathBuf::from(request.cwd);
        match request.command {
            Command::WsCreate { name, model } => {
                let _guard = self.mutations.lock().expect("mutation lock poisoned");
                let workspace =
                    git::create_workspace(&self.repo, &self.state, &name, model.as_deref())?;
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
                        let model = workspace
                            .model
                            .as_deref()
                            .map(|model| format!(" model:{model}"))
                            .unwrap_or_default();
                        if dirty == 0 {
                            format!("{} {} clean{model}", workspace.reference, workspace.name)
                        } else {
                            format!(
                                "{} {} dirty:{dirty}{model}",
                                workspace.reference, workspace.name
                            )
                        }
                    })
                    .collect::<Vec<_>>()
                    .join("\n"))
            }
            Command::Status {
                formalization_yaml,
            } => {
                if formalization_yaml {
                    status::render_formalization_yaml(&self.repo, &self.state)
                } else {
                    status::render(&self.repo, &self.state)
                }
            }
            Command::WsDelete { name } => {
                let _guard = self.mutations.lock().expect("mutation lock poisoned");
                let workspace = self
                    .state
                    .workspace_named(&name)?
                    .with_context(|| format!("unknown workspace {name}"))?;
                self.watcher.unwatch(&workspace.path);
                self.checker.evict_workspace_workers(&workspace.reference);
                git::delete_workspace(&self.repo, &self.state, &name)?;
                Ok(format!("{} deleted", workspace.reference))
            }
            Command::Check { file, profile } => {
                let workspace = self.state.workspace_for_path(&cwd)?;
                git::prepare_workspace(&self.repo, &workspace.path)?;
                let outcome =
                    self.checker
                        .check(&workspace, file.as_deref().map(Path::new), profile, report)?;
                let summary = check_summary(&outcome);
                if outcome.ok {
                    Ok(format!("ok {summary}"))
                } else {
                    bail!(summary)
                }
            }
            Command::Search { query, all } => {
                let workspace = self.state.workspace_for_path(&cwd)?;
                git::prepare_workspace(&self.repo, &workspace.path)?;
                self.searcher.search(&workspace, &cwd, &query, all)
            }
            Command::Sync { push: true } => {
                let _guard = self.mutations.lock().expect("mutation lock poisoned");
                let detail = git::push_main(&self.repo)?;
                Ok(format!("ok pushed main\n{detail}"))
            }
            Command::Sync { push: false } => {
                let _guard = self.mutations.lock().expect("mutation lock poisoned");
                let workspace = self.state.workspace_for_path(&cwd)?;
                let result = git::sync(&self.repo, &workspace)?;
                self.checker.evict_workspace_workers(&workspace.reference);
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
                for path in &targets {
                    if is_root_scratch(path)
                        && workspace.path.join(path).is_file()
                        && !git::tracked_at_head(&workspace.path, path)?
                    {
                        bail!(
                            "{} is a check-only scratch file; move the result into a project module or remove it before submit",
                            path.display()
                        );
                    }
                }
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
                self.validation.wake();
                Ok(reference)
            }
            Command::Show { reference, all } => self.state.show(&reference, all),
        }
    }
}

fn check_summary(outcome: &CheckOutcome) -> String {
    const DIAGNOSTIC_PREVIEW_CHARS: usize = 1200;
    const ADDITIONAL_DIAGNOSTIC_PREVIEW_CHARS: usize = 320;
    const ADDITIONAL_DIAGNOSTIC_LIMIT: usize = 3;

    let mut output = format!("{} {}ms", outcome.reference, outcome.elapsed_ms);
    if outcome.ok {
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
    }
    if outcome.ok && !outcome.linters.is_empty() {
        output.push_str(&format!(
            "\nlinters: {}; show {} --all",
            outcome.linters.len(),
            outcome.reference
        ));
    }
    if outcome.ok && !outcome.suggestions.is_empty() {
        output.push_str(&format!(
            "\nsuggestions: {}; search {}",
            outcome.suggestions.len(),
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
        let additional = outcome
            .diagnostics
            .iter()
            .skip(1)
            .take(ADDITIONAL_DIAGNOSTIC_LIMIT)
            .collect::<Vec<_>>();
        for diagnostic in &additional {
            output.push_str(&format!(
                "\nalso {}",
                truncate_middle(
                    &clean_line(&diagnostic.text),
                    ADDITIONAL_DIAGNOSTIC_PREVIEW_CHARS
                )
            ));
        }
        let shown = usize::from(!outcome.diagnostics.is_empty()) + additional.len();
        if outcome.diagnostics.len() > shown {
            output.push_str(&format!(
                "\n+{} diagnostics; show {}",
                outcome.diagnostics.len() - shown,
                outcome.reference
            ));
        }
        if let Some(repetition) = &outcome.repetition {
            let next = if repetition.deterministic_timeout {
                "check --profile".to_owned()
            } else {
                format!("search {}", outcome.reference)
            };
            output.push_str(&format!(
                "\nrepeated blocker: {} checks ({}..{}, previous {}); {}",
                repetition.count,
                repetition.first_reference,
                outcome.reference,
                repetition.previous_reference,
                next
            ));
        }
    }
    if let Some(profile) = &outcome.profile {
        output.push('\n');
        output.push_str(&profile.render(false));
        if profile.files.iter().map(|file| file.entries.len()).sum::<usize>() > 8 {
            output.push_str(&format!("\nfull profile: show {} --all", outcome.reference));
        }
    }
    output
}

fn is_root_scratch(path: &Path) -> bool {
    path.parent().is_none_or(|parent| parent.as_os_str().is_empty())
        && path.extension().is_some_and(|extension| extension == "lean")
        && path
            .file_stem()
            .and_then(|stem| stem.to_str())
            .is_some_and(|stem| stem.to_ascii_lowercase().starts_with("scratch"))
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
        let watcher = RecommendedWatcher::new(
            move |event: notify::Result<notify::Event>| {
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
            },
            Config::default().with_follow_symlinks(false),
        )?;
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
    fn root_scratch_files_are_ephemeral() {
        assert!(is_root_scratch(Path::new("Scratch.lean")));
        assert!(is_root_scratch(Path::new("ScratchHard.lean")));
        assert!(!is_root_scratch(Path::new("Demo/Scratch.lean")));
        assert!(!is_root_scratch(Path::new("Scratch.md")));
    }

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
            linters: Vec::new(),
            suggestions: Vec::new(),
            diagnostics: vec![Diagnostic {
                kind: "error".into(),
                text: diagnostic,
                context: Some(">    3 | failing tactic".into()),
            }],
            profile: None,
            repetition: Some(crate::check::CheckRepetition {
                count: 3,
                first_reference: "c8".into(),
                previous_reference: "c9".into(),
                deterministic_timeout: false,
            }),
        });
        assert!(summary.contains("Demo.Proof:3:1"));
        assert!(summary.contains("final target"));
        assert!(summary.contains(">    3 | failing tactic"));
        assert!(summary.contains("full diagnostic: show c1"));
        assert!(summary.contains("repeated blocker: 3 checks (c8..c1, previous c9); search c1"));
    }

    #[test]
    fn repeated_timeout_recommends_profile() {
        let summary = check_summary(&CheckOutcome {
            reference: "c3".into(),
            ok: false,
            elapsed_ms: 10,
            warnings: Vec::new(),
            linters: Vec::new(),
            suggestions: Vec::new(),
            diagnostics: Vec::new(),
            profile: None,
            repetition: Some(crate::check::CheckRepetition {
                count: 4,
                first_reference: "c1".into(),
                previous_reference: "c2".into(),
                deterministic_timeout: true,
            }),
        });
        assert!(summary.contains("repeated blocker: 4 checks (c1..c3, previous c2); check --profile"));
    }

    #[test]
    fn passed_check_summary_exposes_stored_linters() {
        let summary = check_summary(&CheckOutcome {
            reference: "c1".into(),
            ok: true,
            elapsed_ms: 10,
            warnings: Vec::new(),
            linters: vec![Diagnostic {
                kind: "warning".into(),
                text: "unused variable".into(),
                context: None,
            }],
            suggestions: Vec::new(),
            diagnostics: Vec::new(),
            profile: None,
            repetition: None,
        });
        assert!(summary.contains("linters: 1; show c1 --all"));
    }

    #[test]
    fn failed_check_summary_previews_additional_errors() {
        let diagnostics = (1..=5)
            .map(|line| Diagnostic {
                kind: "error".into(),
                text: format!("Demo.Proof:{line}:1: error: failure {line}"),
                context: Some(format!("> {line} | source {line}")),
            })
            .collect();
        let summary = check_summary(&CheckOutcome {
            reference: "c2".into(),
            ok: false,
            elapsed_ms: 10,
            warnings: Vec::new(),
            linters: Vec::new(),
            suggestions: Vec::new(),
            diagnostics,
            profile: None,
            repetition: None,
        });
        assert!(summary.contains("Demo.Proof:1:1: error: failure 1"));
        assert!(summary.contains("also Demo.Proof:2:1: error: failure 2"));
        assert!(summary.contains("also Demo.Proof:4:1: error: failure 4"));
        assert!(!summary.contains("source 2"));
        assert!(summary.contains("+1 diagnostics; show c2"));
    }

    #[test]
    fn failed_check_summary_omits_non_blocking_warnings() {
        let summary = check_summary(&CheckOutcome {
            reference: "c4".into(),
            ok: false,
            elapsed_ms: 10,
            warnings: vec![Diagnostic {
                kind: "warning".into(),
                text: "non-blocking warning".into(),
                context: None,
            }],
            linters: Vec::new(),
            suggestions: Vec::new(),
            diagnostics: vec![Diagnostic {
                kind: "error".into(),
                text: "blocking error".into(),
                context: None,
            }],
            profile: None,
            repetition: None,
        });
        assert_eq!(summary, "c4 10ms\nblocking error");
    }

    #[test]
    fn only_newer_clients_retire_a_mismatched_daemon() {
        assert!(build_precedes("old", 10, "new", 11));
        assert!(!build_precedes("new", 11, "old", 10));
        assert!(!build_precedes("same", 10, "same", 11));
        assert!(!build_precedes("new", 11, "old", 0));
    }
}
