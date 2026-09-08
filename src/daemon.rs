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
use crate::presentation::{
    CHECK_ADDITIONAL_DIAGNOSTIC_CHARS, CHECK_ADDITIONAL_DIAGNOSTICS, CHECK_DIAGNOSTIC_CHARS,
};
use crate::protocol::{Command, Progress, Request, Response};
use crate::reference::{Reference, ReferenceKind};
use crate::repo::Repo;
use crate::search::Searcher;
use crate::state::{State, Submission, ValidationStatus};
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
    let telemetry = development_enabled()
        .then(|| TelemetryStore::global_for_repo(&repo))
        .and_then(Result::ok)
        .map(Arc::new);
    let checker = Arc::new(Checker::new(
        repo.clone(),
        state.clone(),
        telemetry.clone(),
    )?);
    let phase = Instant::now();
    let searcher = Searcher::new(
        repo.clone(),
        state.clone(),
        checker.clone(),
        telemetry.clone(),
    )?;
    let search_ms = phase.elapsed().as_millis() as u64;
    let retiring = Arc::new(AtomicBool::new(false));
    let phase = Instant::now();
    let validation = ValidationQueue::start(
        repo.clone(),
        state.clone(),
        retiring.clone(),
        telemetry.clone(),
    )?;
    let validation_ms = phase.elapsed().as_millis() as u64;
    let phase = Instant::now();
    let watcher = WorkspaceWatcher::new(state.clone(), checker.clone())?;
    let workspaces = state.list_workspaces()?;
    for workspace in &workspaces {
        git::prepare_workspace(&repo, &workspace.path)?;
        watcher.watch(&workspace.path)?;
    }
    let workspaces_ms = phase.elapsed().as_millis() as u64;
    if let Some(store) = &telemetry {
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
        telemetry,
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
        // Type search owns a large, opt-in Lean process. Evict it based on its
        // own idle time even while unrelated clients keep the daemon alive;
        // checker workers retain the existing no-client safety gate.
        let has_search_worker = service
            .searcher
            .evict_idle_worker(Duration::from_secs(5 * 60));
        let has_workers = if active_clients == 0 {
            let has_check_workers = service
                .checker
                .evict_idle_workers(Duration::from_secs(5 * 60));
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
        if active_clients == 0 && !has_workers && !has_jobs && last_activity.elapsed() >= grace {
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
    let mut server_request = None;
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
                server_request = service.telemetry.as_ref().map(|_| request.clone());
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
    if let (Some(request), Some(store)) = (server_request, &service.telemetry) {
        let _ = store.record(
            &service.repo,
            &request,
            &response,
            started.elapsed().as_millis() as u64,
        );
    }
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

fn handled_response(service: &Service, request: Request, report: &mut dyn FnMut(&str)) -> Response {
    let discovery = matches!(
        request.command,
        Command::Search { .. } | Command::Probe { .. }
    );
    let mut response = match service.handle(request, report) {
        Ok(summary) => Response::ok(summary),
        Err(error) => {
            let failure = error
                .downcast_ref::<crate::protocol::DiscoveryFailure>()
                .map(|kind| match kind {
                    crate::protocol::DiscoveryFailure::InvalidRequest => "invalid_request",
                    crate::protocol::DiscoveryFailure::UnavailableContext => "unavailable_context",
                    crate::protocol::DiscoveryFailure::Infrastructure => "infrastructure",
                });
            let mut response = Response::error(format!("{error:#}"));
            if discovery {
                response.search_outcome = Some(crate::protocol::SearchOutcome {
                    resolution: "none".into(),
                    result_count: 0,
                    failure_class: Some(failure.unwrap_or("unclassified_error").into()),
                });
            }
            response
        }
    };
    if discovery {
        // The trailing reference selects the persisted result, not a classification
        // inferred from display wording. Earlier nested probes may also have refs.
        if let Some(reference) = response
            .summary
            .lines()
            .rev()
            .find_map(|line| line.strip_prefix("ref: "))
            && let Ok(Some(run)) = service.state.search_run(reference.trim())
        {
            let mut outcome = crate::protocol::SearchOutcome::from_run(&run);
            if !response.ok && run.inference.starts_with("probe") {
                outcome.failure_class = Some("lean_elaboration".into());
            }
            response.search_outcome = Some(outcome);
        }
    }
    response
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
    telemetry: Option<Arc<TelemetryStore>>,
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
            Command::Status { formalization_yaml } => {
                if formalization_yaml {
                    status::render_formalization_yaml(
                        &self.repo,
                        &self.state,
                        self.telemetry.as_deref(),
                    )
                } else {
                    status::render(&self.repo, &self.state, self.telemetry.as_deref(), &cwd)
                }
            }
            Command::WsDelete { name, force } => {
                let _guard = self.mutations.lock().expect("mutation lock poisoned");
                let workspace = self
                    .state
                    .workspace_named(&name)?
                    .with_context(|| format!("unknown workspace {name}"))?;
                self.watcher.unwatch(&workspace.path);
                self.checker.evict_workspace_workers(&workspace.reference);
                git::delete_workspace(&self.repo, &self.state, &name, force)?;
                Ok(format!("{} deleted", workspace.reference))
            }
            Command::Check { file, profile } => {
                let workspace = self.state.workspace_for_path(&cwd)?;
                git::prepare_workspace(&self.repo, &workspace.path)?;
                let outcome = self.checker.check(
                    &workspace,
                    file.as_deref().map(Path::new),
                    profile,
                    report,
                )?;
                let summary = check_summary(&outcome);
                if outcome.ok {
                    Ok(format!("ok {summary}"))
                } else {
                    bail!(summary)
                }
            }
            Command::Cancel { reference } => {
                let workspace = self.state.workspace_for_path(&cwd)?;
                self.checker.cancel(&workspace.reference, &reference)
            }
            Command::Search {
                query,
                max_results,
                all,
            } => {
                let workspace = self.state.workspace_for_path(&cwd)?;
                git::prepare_workspace(&self.repo, &workspace.path)?;
                self.searcher
                    .search(&workspace, &cwd, &query, max_results, all)
            }
            Command::Probe { query } => {
                let workspace = self.state.workspace_for_path(&cwd)?;
                git::prepare_workspace(&self.repo, &workspace.path)?;
                self.searcher.probe(&workspace, &cwd, &query)
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
                    ensure!(
                        !is_root_scratch(path)
                            || !workspace.path.join(path).is_file()
                            || git::tracked_at_head(&workspace.path, path)?,
                        "{} is a check-only scratch file; move the result into a project module or remove it before submit",
                        path.display()
                    );
                }
                let checks = self.checker.valid_certificates(&workspace, &targets)?;
                let message = message
                    .filter(|value| !value.trim().is_empty())
                    .unwrap_or_else(|| match dirty.as_slice() {
                        [path] => format!("Update {}", path.display()),
                        paths => format!("Update {} files", paths.len()),
                    });
                let result = git::submit(&self.repo, &workspace, &message)?;
                let reference = self.state.next_reference(ReferenceKind::Submission)?;
                self.state.add_submission(&Submission {
                    reference: reference.clone(),
                    workspace_ref: workspace.reference.clone(),
                    workspace_commit: result.workspace_commit,
                    main_commit: result.main_commit,
                    base_commit: result.base_commit,
                    checks,
                    validation_status: ValidationStatus::Queued,
                    validation_detail: None,
                    build_output: None,
                    build_summary: None,
                    axioms: Vec::new(),
                    sorries: Vec::new(),
                    validation_duration_ms: None,
                    validated_by: None,
                    created_at: now_unix_ms(),
                })?;
                self.validation.wake();
                Ok(reference)
            }
            Command::Show {
                reference,
                all,
                wait,
            } => self.show_reference(&reference, all, wait, report),
            Command::Restart => {
                self.retiring.store(true, Ordering::SeqCst);
                Ok("restarting mathmux daemon".into())
            }
        }
    }

    fn show_reference(
        &self,
        reference: &str,
        all: bool,
        wait: bool,
        report: &mut dyn FnMut(&str),
    ) -> Result<String> {
        show_reference(&self.state, reference, all, wait, report)
    }
}

fn show_reference(
    state: &State,
    reference: &str,
    all: bool,
    wait: bool,
    report: &mut dyn FnMut(&str),
) -> Result<String> {
    if !wait {
        return state.show(reference, all);
    }
    ensure!(
        Reference::is_kind(reference, ReferenceKind::Check)
            || Reference::is_kind(reference, ReferenceKind::Submission),
        "`--wait` applies only to a cREF or a queued/running sREF"
    );
    let is_submission = Reference::is_kind(reference, ReferenceKind::Submission);
    let deadline = Instant::now() + Duration::from_secs(10 * 60);
    loop {
        if is_submission {
            let submission = state
                .submission(reference)?
                .with_context(|| format!("unknown reference {reference}"))?;
            if !matches!(
                submission.validation_status,
                ValidationStatus::Queued | ValidationStatus::Running
            ) {
                return state.show(reference, all);
            }
            if Instant::now() >= deadline {
                bail!(
                    "submission {reference} is still {} after 10 minutes; rerun `mathmux show {reference} --wait`",
                    submission.validation_status
                );
            }
            report(&format!(
                "waiting for {reference} ({})",
                submission.validation_status
            ));
        } else {
            let run = state
                .check_run(reference)?
                .with_context(|| format!("unknown reference {reference}"))?;
            if run.status != crate::state::CheckStatus::Running {
                return state.show(reference, all);
            }
            if Instant::now() >= deadline {
                bail!(
                    "check {reference} is still running after 10 minutes; rerun `mathmux show {reference} --wait`"
                );
            }
            report(&format!("waiting for {reference} (running)"));
        }
        thread::sleep(Duration::from_secs(1));
    }
}

// Put goal targets first when their boundaries are unambiguous. Keep hypotheses
// available rather than guessing which ones matter to the proof.
fn compact_type_mismatch(text: &str) -> Option<String> {
    let original_len = text.chars().count();
    if original_len <= CHECK_DIAGNOSTIC_CHARS / 2
        || !text.to_ascii_lowercase().contains("type mismatch")
    {
        return None;
    }
    let difference = crate::search::diagnostic_type_detail(text)?;
    if !difference.starts_with("first type difference") || difference.contains('…') {
        return None;
    }
    let header = text.lines().take_while(|line| line.trim() != "has type")
        .collect::<Vec<_>>().join("\n");
    let preview = format!("{header}\n{difference}\n(shared type context omitted)");
    (preview.chars().count() * 2 < original_len).then_some(preview)
}

fn goal_first_diagnostic(text: &str) -> Option<String> {
    let lines = text.lines().collect::<Vec<_>>();
    if !lines.first()?.contains("unsolved goals") {
        return None;
    }
    let goals = lines
        .iter()
        .enumerate()
        .filter(|(_, line)| line.trim_start().starts_with('⊢'))
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    let [start] = goals.as_slice() else {
        if goals.len() < 2 { return None; }
        let mut overview = Vec::new();
        let mut contexts = Vec::new();
        let mut previous = 0;
        for (number, start) in goals.iter().enumerate() {
            let case_index = previous + lines[previous..*start].iter()
                .rposition(|line| line.starts_with("case "))?;
            if lines[previous..*start].iter().filter(|line| line.starts_with("case ")).count() != 1
                || (number == 0 && lines[1..case_index].iter().any(|line| !line.trim().is_empty())) {
                return None;
            }
            let case = lines[case_index];
            let end = lines[*start + 1..].iter()
                .position(|line| line.starts_with("case "))
                .map_or(lines.len(), |offset| start + 1 + offset);
            if goals.get(number + 1).is_some_and(|next| *next < end) {
                return None;
            }
            overview.push(format!("goal {} ({case})\n{}", number + 1,
                lines[*start..end].join("\n").trim_end()));
            contexts.push(format!("local context (goal {}, {case}): {}", number + 1,
                clean_line(&lines[case_index + 1..*start].join("\n"))));
            previous = *start + 1;
        }
        return Some(format!("{}\n{}\n{}",
            lines[0], overview.join("\n"), contexts.join("\n")));
    };
    let context = lines[1..*start].join("\n");
    let goal = lines[*start..].join("\n");
    Some(format!(
        "{}\n{}\nlocal context: {}",
        lines[0],
        goal,
        clean_line(&context)
    ))
}

fn check_summary(outcome: &CheckOutcome) -> String {
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
            let compact_type = compact_type_mismatch(&diagnostic.text);
            let detail = goal_first_diagnostic(&diagnostic.text)
                .or_else(|| compact_type.clone())
                .unwrap_or_else(|| clean_line(&diagnostic.text));
            output.push_str(&format!(
                "\n{}",
                truncate_middle(&detail, CHECK_DIAGNOSTIC_CHARS)
            ));
            if let Some(context) = &diagnostic.context {
                output.push('\n');
                output.push_str(context);
            }
            if detail.to_ascii_lowercase().contains("type mismatch")
                || detail.contains("definitionally equal")
                || detail.contains("Did not find an occurrence of the pattern")
            {
                output.push_str(&format!(
                    "\ncontext: mathmux probe {} context",
                    outcome.reference
                ));
            }
            if compact_type.is_some() || detail.chars().count() > CHECK_DIAGNOSTIC_CHARS {
                output.push_str(&format!("\nfull diagnostic: show {}", outcome.reference));
            }
        }
        let additional = outcome
            .diagnostics
            .iter()
            .skip(1)
            .take(CHECK_ADDITIONAL_DIAGNOSTICS)
            .collect::<Vec<_>>();
        for diagnostic in &additional {
            output.push_str(&format!(
                "\nalso {}",
                truncate_middle(
                    &clean_line(&diagnostic.text),
                    CHECK_ADDITIONAL_DIAGNOSTIC_CHARS
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
        if profile
            .files
            .iter()
            .map(|file| file.entries.len())
            .sum::<usize>()
            > 8
        {
            output.push_str(&format!("\nfull profile: show {} --all", outcome.reference));
        }
    }
    output
}

fn is_root_scratch(path: &Path) -> bool {
    path.parent()
        .is_none_or(|parent| parent.as_os_str().is_empty())
        && path
            .extension()
            .is_some_and(|extension| extension == "lean")
        && path
            .file_stem()
            .and_then(|stem| stem.to_str())
            .is_some_and(|stem| stem.to_ascii_lowercase().starts_with("scratch"))
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
    use crate::state::{Diagnostic, ValidationReport, Workspace};
    use tempfile::tempdir;

    #[test]
    fn root_scratch_files_are_ephemeral() {
        assert!(is_root_scratch(Path::new("Scratch.lean")));
        assert!(is_root_scratch(Path::new("ScratchHard.lean")));
        assert!(!is_root_scratch(Path::new("Demo/Scratch.lean")));
        assert!(!is_root_scratch(Path::new("Scratch.md")));
    }

    #[test]
    fn show_wait_polls_queued_submission_until_validation_finishes() {
        let directory = tempdir().unwrap();
        let state = State::new(directory.path().join("state.sqlite3")).unwrap();
        state
            .add_workspace(&Workspace {
                reference: "w1".into(),
                name: "workspace".into(),
                path: directory.path().join("workspace"),
                branch: "workspace".into(),
                model: None,
            })
            .unwrap();
        state
            .add_submission(&Submission {
                reference: "s1".into(),
                workspace_ref: "w1".into(),
                workspace_commit: "workspace".into(),
                main_commit: "main".into(),
                base_commit: "base".into(),
                checks: Vec::new(),
                validation_status: ValidationStatus::Queued,
                validation_detail: None,
                build_output: None,
                build_summary: None,
                axioms: Vec::new(),
                sorries: Vec::new(),
                validation_duration_ms: None,
                validated_by: None,
                created_at: 0,
            })
            .unwrap();
        let updater = state.clone();
        let thread = thread::spawn(move || {
            thread::sleep(Duration::from_millis(25));
            updater
                .finish_validation(
                    "s1",
                    &ValidationReport {
                        passed: true,
                        sorry_audit: true,
                        detail: String::new(),
                        build_output: String::new(),
                        axioms: Vec::new(),
                        sorries: Vec::new(),
                        duration_ms: 25,
                    },
                )
                .unwrap();
        });
        let mut progress = Vec::new();
        let shown = show_reference(&state, "s1", false, true, &mut |message| {
            progress.push(message.to_owned());
        })
        .unwrap();
        thread.join().unwrap();
        assert!(shown.starts_with("s1 passed"));
        assert_eq!(progress, vec!["waiting for s1 (queued)"]);
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
    fn long_type_mismatch_focuses_distinct_instances() {
        let common = "SharedTypeArgument ".repeat(40);
        let text = format!("Demo:3:1: error: Type mismatch: term\n  proof\n has type\n  F {common}actualInstance x\nbut is expected to have type\n  F {common}expectedInstance x");
        let preview = compact_type_mismatch(&text).unwrap();
        assert!(preview.starts_with("Demo:3:1: error: Type mismatch: term\n  proof"));
        assert!(preview.contains("actual: actualInstance"));
        assert!(preview.contains("expected: expectedInstance"));
        assert!(!preview.contains("SharedTypeArgument"));
        assert!(compact_type_mismatch("Type mismatch\n has type\n Nat\nbut is expected to have type\n Bool").is_none());
        let unrelated = format!("Type mismatch\n has type\n {}\nbut is expected to have type\n {}", "Left ".repeat(65), "Right ".repeat(65));
        assert!(compact_type_mismatch(&unrelated).is_none());
        assert!(compact_type_mismatch(&text.replace("Type mismatch", "unknown identifier")).is_none());
    }

    #[test]
    fn single_goal_precedes_its_preserved_context() {
        let text = "Demo:3:1: error: unsolved goals\nα : Type\nx : α\nh : P x\n⊢ P x ∧\n    True";
        let rendered = goal_first_diagnostic(text).unwrap();
        assert!(rendered.starts_with("Demo:3:1: error: unsolved goals\n⊢ P x ∧\n    True"));
        assert!(rendered.ends_with("local context: α : Type x : α h : P x"));
        let multiple = goal_first_diagnostic(
            "error: unsolved goals\ncase left\nh : P\n⊢ P\ncase right\nh : Q\n⊢ Q"
        ).unwrap();
        assert!(multiple.starts_with("error: unsolved goals\ngoal 1 (case left)\n⊢ P\ngoal 2 (case right)\n⊢ Q"));
        assert!(multiple.contains("local context (goal 1, case left): h : P"));
        assert!(multiple.contains("local context (goal 2, case right): h : Q"));
        assert!(goal_first_diagnostic("error: unsolved goals\nh : P\n⊢ P\nh : Q\n⊢ Q").is_none());
        assert!(goal_first_diagnostic("error: unsolved goals\nshared : P\ncase left\n⊢ P\ncase right\n⊢ Q").is_none());
        let repeated = goal_first_diagnostic("error: unsolved goals\ncase e_a\n⊢ P\ncase e_a\n⊢ Q").unwrap();
        assert!(repeated.contains("goal 1 (case e_a)\n⊢ P\ngoal 2 (case e_a)\n⊢ Q"));
        assert!(goal_first_diagnostic("error: type mismatch\n⊢ P").is_none());
        assert!(goal_first_diagnostic("error: unsolved goals").is_none());
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
        assert!(
            summary.contains("repeated blocker: 4 checks (c1..c3, previous c2); check --profile")
        );
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
