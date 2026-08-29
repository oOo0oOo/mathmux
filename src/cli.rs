use std::fs::File;
use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::UnixStream;
use std::os::unix::process::CommandExt;
#[cfg(feature = "development")]
use std::path::Path;
use std::path::PathBuf;
use std::process::{Command as ProcessCommand, Stdio};
use std::time::{Duration, Instant};

use crate::coordination::{lock_exclusive, open_lock};
use crate::daemon;
use crate::issue::development_enabled;
#[cfg(feature = "development")]
use crate::issue::{IssueStore, TelemetryStore};
use crate::protocol::{Command, Progress, Request, Response};
use crate::repo::Repo;
use anyhow::{Context, Result, bail, ensure};
#[cfg(feature = "development")]
use clap::ValueEnum;
use clap::{CommandFactory, FromArgMatches, Parser, Subcommand};

const WORKFLOW_HELP: &str = r#"AGENT CONTRACT
  scope     Use the preassigned workspace; never run ws or enter main/another workspace.
  discover  Search unknown things; probe known API, exact context, or failures.
            Exact declarations go straight to probe NAME; qREFs store result sets.
            Source ranges <=48 lines are complete compact; read search/probe --help once.
  change    Edit intended files -> check -> submit. Use check FILE only to isolate dirty files.
            Run one check at a time; do not launch bulk parallel check processes.
  update    Use sync. Use mathmux only—never substitute git, lean, lake, or other tooling.
  Lean      Use explicit narrow imports and aligned module/namespace/path; keep public imports API-only.
  safety    sorry is tracked; new axioms fail validation. Never edit .lake/generated artifacts."#;

const SEARCH_HELP: &str = r#"SEARCH — find or read unknown things; returns qREF
FORMS — type one directly; declaration/type/source/compose are labels, not keywords
  declaration  NAME | NAME* | KIND NAME [source|body|proof]
               name:NAME | name:A|B|C
  type/concept TYPE_OR_CONCEPT_TERMS | type:LEAN_TYPE
  source       FILE:LINE | FILE:START-END | FILE:tail
               FILE[:RANGE] TERMS
               FILE outline|declarations|imports|dependents
               /REGEX/ | PATH /REGEX/ | re:/REGEX/ | PATH re:/REGEX/
  compose      A|B|C | qREF TERMS | sREF TERMS

KIND = abbrev|class|def|inductive|instance|lemma|structure|theorem

RESULT
  Exact declarations show signature, path, imports, and up to three usages.
  Use probe NAME source|usages for focused detail. qREFs retain stored result sets;
  show qREF --all expands genuine multi-result or source-range searches.
  --limit N (1–200) caps hits and cannot combine with --all.
  Source-only ranges of 48 lines or fewer are complete in compact mode; --all
  is needed for longer ranges or broader result detail.
  Exact names include full signatures.

NEXT
  One declaration -> probe NAME signature|source|usages. Exact misses fail closed
  with at most three near-name suggestions; concept search is a separate follow-up.
  Many hits -> refine first. Compact output gives one focused next action.

RULES
  name: forces exact lookup; its | batch returns all. Bare identifier queries are
  exact-first. type: matches declaration result types; `_` holes are legal.
  sREF requires TERMS; use show sREF first, then --all only if needed.
  Source facets follow a space, not a colon.
  FILE:LINE reads source only; use probe FILE:LINE for Lean context.
  Quote queries containing shell characters such as |, *, or #.
  Sigil what you know; leave inference for what you do not."#;

const PROBE_HELP: &str = r##"PROBE — inspect something known; returns qREF
FORMS — type one directly; there are no API, LEAN, or other category keywords
  NAME [signature|source|apply|fields|constructors|ext|simp|
        instances|coercions|usages]
  type:LEAN_TYPE [types]
  FILE warnings
  FILE:LINE [goal] | FILE:LINE TERM [signature]
  PATH NAME usages
  cREF [goal|types|defeq|rewrite|profile]
  declaration-qREF [signature|source|usages|constructors]
  positioned-qREF [goal] | stored-probe-qREF
  FILE|FILE:LINE|cREF|qREF "#check TERM"|"#synth TYPE"|"#reduce TERM"
  FILE:LINE|cREF|positioned-qREF "by TACTIC"

RESULT
  FILE warnings returns ranked residual-warning qREFs from its latest current check;
  probing one returns a source-bound dossier with API/dependency evidence.
  API focuses return one bounded dossier. goal returns the exact local goal;
  TERM/directives return Lean's elaborated answer; by returns solved or subgoals.
  NAME source resolves the exact declaration and returns that body; a miss never
  falls through to another declaration. search FILE:LINE/RANGE reads file text.

NEXT
  Start with signature; request source/usages only for the selected declaration.

RULES
  fields/constructors target structures/inductives; ext/simp may be empty.
  instances/coercions find declarations in the subject's name family; inspect
  signature for required typeclasses or a theorem result such as Bijective.
  cREF goal/analyses need a matching stored failure; profile needs check --profile.
  warnings omits mechanical fixes owned by Lean automation and never reruns Lean.
  Context is mandatory for directives and never guessed. FILE uses its imports;
  FILE:LINE uses that exact line—there is no nearby-line fallback. Probe never
  edits or certifies source; use check after editing. Use NAME signature, not
  NAME "#check NAME". Quote directives."##;

#[derive(Parser)]
#[command(
    name = "mathmux",
    version,
    disable_help_subcommand = true,
    about = "Managed Lean workspaces, search, checking, and integration",
    after_help = WORKFLOW_HELP
)]
struct Args {
    #[command(subcommand)]
    command: TopCommand,
}

#[derive(Subcommand)]
enum TopCommand {
    /// Manage workspaces (operator only).
    ///
    /// Creates, lists, or deletes managed worktrees. Proving agents already have an
    /// assigned workspace and should not use this command.
    Ws {
        #[command(subcommand)]
        command: WsCommand,
    },
    /// Show the live formalization dashboard.
    ///
    /// Reports agents, Lean size and growth, throughput, tool use, and validation.
    Status {
        /// Emit publication metadata as formalization.yaml v0.4.
        #[arg(long)]
        formalization_yaml: bool,
    },
    /// Check all dirty Lean files, or restrict to one file.
    ///
    /// No FILE is the normal form and checks every dirty Lean file. Use FILE only to
    /// isolate one of several dirty files. Stops at the first failing file and returns
    /// cREF. Keep a running check open; reruns only queue a duplicate.
    Check {
        /// Restrict checking to this Lean file and its source dependencies.
        file: Option<PathBuf>,
        /// Fresh elaboration with source hotspots and Lean timings; use only for slow checks.
        #[arg(long)]
        profile: bool,
    },
    /// Find Lean declarations, types, concepts, and source.
    #[command(before_help = SEARCH_HELP)]
    Search {
        /// Query terms; the query form is inferred as documented above.
        #[arg(required = true, num_args = 1..)]
        query: Vec<String>,
        /// Return at most N ranked results (1–200).
        #[arg(long, conflicts_with = "all")]
        limit: Option<usize>,
        /// Print the complete result instead of its compact preview.
        #[arg(long)]
        all: bool,
    },
    /// Inspect a known Lean API, exact context, or stored failure.
    #[command(before_help = PROBE_HELP)]
    Probe {
        /// Probe expression in the grammar documented above.
        #[arg(required = true, num_args = 1.., allow_hyphen_values = true)]
        query: Vec<String>,
    },
    /// Update the workspace from managed main, or push managed main.
    ///
    /// Default: merge managed main into this workspace. --push publishes managed main
    /// through its configured remote and does not change this workspace.
    Sync {
        /// Push managed main through its configured remote.
        #[arg(long)]
        push: bool,
    },
    /// Integrate a certified change and queue validation.
    ///
    /// Requires current check coverage for all dirty Lean files. Integrates into
    /// managed main, queues build and axiom validation, and returns sREF immediately.
    /// Takes no file arguments; current dirty coverage defines the submission.
    /// New root Scratch*.lean files are check-only and cannot be submitted.
    Submit {
        /// Integration commit message.
        #[arg(short = 'm')]
        message: Option<String>,
        #[arg(value_name = "FILE", hide = true)]
        files: Vec<PathBuf>,
    },
    /// Show stored detail for a short reference.
    ///
    /// Accepts cREF, qREF, sREF, uREF, or wREF. --all expands stored detail while
    /// keeping raw build logs bounded. --wait waits for a running cREF.
    Show {
        /// Stored cREF, qREF, sREF, uREF, or wREF.
        reference: String,
        /// Include expanded stored detail.
        #[arg(long, conflicts_with = "wait")]
        all: bool,
        /// Wait for a running cREF to finish, with bounded progress updates.
        #[arg(long, conflicts_with = "all")]
        wait: bool,
    },
    /// Report mathmux tooling problems (proving agents).
    ///
    /// Available only in development builds. Report missing or inefficient tooling;
    /// do not report formalization or project-API gaps.
    #[cfg(feature = "development")]
    Issue {
        #[command(subcommand)]
        command: IssueCommand,
    },
    /// Maintain mathmux itself (tooling developers only).
    ///
    /// Proving agents should use `issue report`, never this command.
    #[cfg(feature = "development")]
    Dev {
        #[command(subcommand)]
        command: DevCommand,
    },
    #[command(name = "__daemon", hide = true)]
    Daemon {
        #[arg(long)]
        repo: PathBuf,
    },
}

#[derive(Subcommand)]
enum WsCommand {
    /// Create a managed workspace.
    ///
    /// Branches from managed main, prepares the worktree, and prints wREF and path.
    Create {
        /// Unique workspace name.
        name: String,
        /// Model identifier for persistent attribution.
        #[arg(long)]
        model: Option<String>,
    },
    /// List workspace references, names, dirty counts, and model labels.
    List,
    /// Delete a clean managed workspace.
    ///
    /// Refuses dirty workspaces, then removes the worktree and its branch.
    Delete {
        /// Workspace name.
        name: String,
    },
}

#[derive(Subcommand)]
enum IssueCommand {
    /// Record a mathmux issue with local command context.
    Report {
        /// Concise tooling defect or inefficiency.
        summary: String,
        /// Related cREF, qREF, sREF, uREF, or eREF.
        #[arg(long = "ref")]
        reference: Option<String>,
    },
}

#[cfg(feature = "development")]
#[derive(Subcommand)]
enum DevCommand {
    /// Triage reported tooling issues.
    Issue {
        #[command(subcommand)]
        command: DevIssueCommand,
    },
    /// Summarize development telemetry.
    Telemetry {
        /// Time window such as 30m, 24h, 7d, or all.
        #[arg(long, default_value = "24h")]
        since: String,
        /// Restrict to one recorded verb.
        #[arg(long)]
        verb: Option<String>,
        /// Show N slowest events instead of aggregates.
        #[arg(long)]
        slow: Option<usize>,
    },
    /// Show a stored issue or telemetry event.
    Show {
        /// Stored iREF or eREF.
        reference: String,
        /// Include complete captured context.
        #[arg(long)]
        all: bool,
    },
}

#[cfg(feature = "development")]
#[derive(Subcommand)]
enum DevIssueCommand {
    /// List recorded mathmux issues.
    List {
        /// Issue status to include.
        #[arg(long, default_value = "open")]
        status: IssueFilter,
    },
    /// Mark an issue fixed.
    Resolve {
        /// Issue reference.
        issue: String,
        /// Fix commit or release identifier.
        #[arg(long)]
        fixed_by: Option<String>,
        /// Resolution note.
        #[arg(short = 'm')]
        note: Option<String>,
    },
    /// Dismiss an issue that is not an actionable tooling defect.
    Dismiss {
        /// Issue reference.
        issue: String,
        /// Why the issue is not actionable.
        #[arg(short = 'm', long = "reason")]
        reason: String,
    },
}

#[cfg(feature = "development")]
#[derive(Clone, Copy, ValueEnum)]
enum IssueFilter {
    Open,
    Resolved,
    Dismissed,
    All,
}

#[cfg(feature = "development")]
impl IssueFilter {
    fn as_str(self) -> &'static str {
        match self {
            Self::Open => "open",
            Self::Resolved => "resolved",
            Self::Dismissed => "dismissed",
            Self::All => "all",
        }
    }
}

pub fn run() -> Result<u8> {
    let command = command_line();
    let matches = command.get_matches();
    let args = Args::from_arg_matches(&matches)?;
    if let TopCommand::Daemon { repo } = &args.command {
        daemon::run(Repo::from_root(repo)?)?;
        return Ok(0);
    }
    let cwd = std::env::current_dir()?;
    #[cfg(feature = "development")]
    if let TopCommand::Issue { command } = &args.command {
        return run_issue_report(command, &cwd);
    }
    #[cfg(feature = "development")]
    if let TopCommand::Dev { command } = &args.command {
        return run_dev(command, &cwd);
    }
    let repo = Repo::discover(&cwd)?;
    let development = development_enabled();
    let command = match args.command {
        TopCommand::Ws { command } => match command {
            WsCommand::Create { name, model } => Command::WsCreate { name, model },
            WsCommand::List => Command::WsList,
            WsCommand::Delete { name } => Command::WsDelete { name },
        },
        TopCommand::Status { formalization_yaml } => Command::Status { formalization_yaml },
        TopCommand::Check { file, profile } => Command::Check {
            file: file.map(|path| {
                let path = if path.is_absolute() {
                    path
                } else {
                    cwd.join(path)
                };
                path.to_string_lossy().into_owned()
            }),
            profile,
        },
        TopCommand::Search { query, limit, all } => Command::Search {
            query: query.join(" "),
            limit,
            all,
        },
        TopCommand::Probe { query } => Command::Probe {
            query: query.join(" "),
        },
        TopCommand::Sync { push } => Command::Sync { push },
        TopCommand::Submit { message, files } => {
            ensure!(
                files.is_empty(),
                "submit takes no files; it uses all currently checked dirty Lean files"
            );
            Command::Submit { message }
        }
        TopCommand::Show {
            reference,
            all,
            wait,
        } => Command::Show {
            reference,
            all,
            wait,
        },
        #[cfg(feature = "development")]
        TopCommand::Issue { .. } | TopCommand::Dev { .. } => unreachable!(),
        TopCommand::Daemon { .. } => unreachable!(),
    };
    let request = Request {
        build: crate::util::build_id().to_owned(),
        generation: crate::util::build_generation(),
        cwd: cwd.to_string_lossy().into_owned(),
        command,
    };
    let client_started = Instant::now();
    if matches!(&request.command, Command::Sync { push: true }) {
        let response = match crate::git::push_main(&repo) {
            Ok(detail) => Response::ok(format!("ok pushed main\n{detail}")),
            Err(error) => Response::error(format!("{error:#}")),
        };
        if development {
            let _ = crate::issue::record_exchange(
                &repo,
                &request,
                &response,
                client_started.elapsed().as_millis() as u64,
            );
        }
        if response.ok {
            output_summary(&response.summary)?;
            return Ok(0);
        }
        eprintln!("error {}", response.summary);
        return Ok(1);
    }
    let mut handoffs = 0;
    let mut retirement_waits = 0;
    let mut transport_retries = 0;
    let mut handoff_stream = None;
    let response = loop {
        let stream = match handoff_stream.take() {
            Some(stream) => Ok(stream),
            None => connect_or_start(&repo),
        };
        let response = match stream.and_then(|stream| exchange(stream, &request)) {
            Ok(response) => response,
            Err(error)
                if transport_retries == 0
                    && request.command.transport_retry_safe()
                    && transient_transport_error(&error) =>
            {
                transport_retries += 1;
                std::thread::sleep(Duration::from_millis(50));
                continue;
            }
            Err(error) => return Err(error),
        };
        if !response.retry {
            break response;
        }
        if request.generation > response.generation {
            ensure!(
                handoffs == 0,
                "daemon build changed repeatedly; retry command"
            );
            handoffs += 1;
            handoff_stream = Some(replace_daemon(&repo, &request)?);
        } else {
            ensure!(
                retirement_waits < 2,
                "daemon replacement did not settle; retry command"
            );
            retirement_waits += 1;
            handoff_stream = Some(wait_for_replacement(&repo)?);
        }
    };
    if development {
        let _ = crate::issue::record_exchange(
            &repo,
            &request,
            &response,
            client_started.elapsed().as_millis() as u64,
        );
    }
    if response.ok {
        output_summary(&response.summary)?;
        Ok(0)
    } else {
        eprintln!("error {}", response.summary);
        Ok(1)
    }
}

fn exchange(mut stream: UnixStream, request: &Request) -> Result<Response> {
    serde_json::to_writer(&mut stream, &request)?;
    stream.write_all(b"\n")?;
    stream.flush()?;
    let progress_label = match request.command {
        Command::Check { .. } => Some("check"),
        Command::Probe { .. } => Some("probe"),
        _ => None,
    };
    if progress_label.is_some() {
        stream.set_read_timeout(Some(Duration::from_secs(30)))?;
    }
    let started = Instant::now();
    let mut reader = BufReader::new(stream);
    let mut progress = String::from("running");
    let mut next_report = Duration::from_secs(10);
    loop {
        let elapsed = started.elapsed();
        if progress_label.is_some() {
            let timeout = next_report
                .saturating_sub(elapsed)
                .max(Duration::from_millis(1));
            reader.get_ref().set_read_timeout(Some(timeout))?;
        }
        let mut line = String::new();
        match reader.read_line(&mut line) {
            Ok(0) => {
                return Err(std::io::Error::from(std::io::ErrorKind::UnexpectedEof).into());
            }
            Ok(_) => {
                if let Ok(frame) = serde_json::from_str::<Progress>(&line) {
                    progress = frame.progress;
                    continue;
                }
                return serde_json::from_str(&line).context("invalid daemon response");
            }
            Err(error)
                if progress_label.is_some()
                    && matches!(
                        error.kind(),
                        std::io::ErrorKind::TimedOut | std::io::ErrorKind::WouldBlock
                    ) =>
            {
                eprintln!(
                    "{} {progress} {}s",
                    progress_label.expect("progress label is present"),
                    started.elapsed().as_secs()
                );
                next_report += Duration::from_secs(30);
            }
            Err(error) => return Err(error.into()),
        }
    }
}

fn transient_transport_error(error: &anyhow::Error) -> bool {
    error.chain().any(|cause| {
        cause.downcast_ref::<std::io::Error>().is_some_and(|error| {
            matches!(
                error.kind(),
                std::io::ErrorKind::BrokenPipe
                    | std::io::ErrorKind::ConnectionAborted
                    | std::io::ErrorKind::ConnectionRefused
                    | std::io::ErrorKind::ConnectionReset
                    | std::io::ErrorKind::NotConnected
                    | std::io::ErrorKind::UnexpectedEof
            )
        })
    })
}

fn wait_for_daemon_exit(repo: &Repo) -> Result<()> {
    let started = Instant::now();
    while started.elapsed() < Duration::from_secs(10 * 60) {
        if !repo.socket_path.exists() || UnixStream::connect(&repo.socket_path).is_err() {
            return Ok(());
        }
        std::thread::sleep(Duration::from_millis(25));
    }
    bail!("daemon did not finish its active validation")
}

fn wait_for_replacement(repo: &Repo) -> Result<UnixStream> {
    let started = Instant::now();
    while started.elapsed() < Duration::from_secs(10 * 60) {
        if let Ok(stream) = UnixStream::connect(&repo.socket_path) {
            return Ok(stream);
        }
        std::thread::sleep(Duration::from_millis(25));
    }
    bail!("replacement daemon did not start")
}

#[cfg(feature = "development")]
fn run_issue_report(command: &IssueCommand, cwd: &Path) -> Result<u8> {
    let store = IssueStore::global()?;
    let summary = match command {
        IssueCommand::Report { summary, reference } => {
            store.create(cwd, summary, reference.as_deref())?
        }
    };
    output_summary(&summary)?;
    Ok(0)
}

#[cfg(feature = "development")]
fn run_dev(command: &DevCommand, _cwd: &Path) -> Result<u8> {
    let summary = match command {
        DevCommand::Issue { command } => {
            let store = IssueStore::global()?;
            match command {
                DevIssueCommand::List { status } => store.list(status.as_str())?,
                DevIssueCommand::Resolve {
                    issue,
                    fixed_by,
                    note,
                } => store.resolve(issue, fixed_by.as_deref(), note.as_deref())?,
                DevIssueCommand::Dismiss { issue, reason } => store.dismiss(issue, reason)?,
            }
        }
        DevCommand::Telemetry { since, verb, slow } => {
            TelemetryStore::global()?.summary(since, verb.as_deref(), *slow)?
        }
        DevCommand::Show { reference, all } => {
            if reference.starts_with('i') {
                IssueStore::global()?.show(reference, *all)?
            } else if reference.starts_with('e') {
                TelemetryStore::global()?.show(reference, *all)?
            } else {
                bail!("dev show expects iREF or eREF")
            }
        }
    };
    output_summary(&summary)?;
    Ok(0)
}

fn output_summary(summary: &str) -> Result<()> {
    output_summary_to(std::io::stdout().lock(), summary)
}

fn output_summary_to(mut output: impl Write, summary: &str) -> Result<()> {
    match writeln!(output, "{summary}") {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::BrokenPipe => Ok(()),
        Err(error) => Err(error.into()),
    }
}

fn command_line() -> clap::Command {
    Args::command()
}

fn connect_or_start(repo: &Repo) -> Result<UnixStream> {
    if let Ok(stream) = UnixStream::connect(&repo.socket_path) {
        return Ok(stream);
    }
    let startup_lock = startup_lock(repo)?;
    lock_exclusive(&startup_lock)?;
    connect_or_start_locked(repo)
}

fn replace_daemon(repo: &Repo, request: &Request) -> Result<UnixStream> {
    let startup_lock = startup_lock(repo)?;
    lock_exclusive(&startup_lock)?;
    if let Ok(stream) = UnixStream::connect(&repo.socket_path) {
        let probe = Request {
            build: request.build.clone(),
            generation: request.generation,
            cwd: request.cwd.clone(),
            command: Command::Show {
                reference: "q0".into(),
                all: false,
                wait: false,
            },
        };
        match exchange(stream, &probe) {
            Ok(response) if !response.retry && response.build == request.build => {
                return UnixStream::connect(&repo.socket_path).map_err(Into::into);
            }
            Ok(_) => {}
            Err(error) if transient_transport_error(&error) => {}
            Err(error) => return Err(error),
        }
    }
    wait_for_daemon_exit(repo)?;
    connect_or_start_locked(repo)
}

fn startup_lock(repo: &Repo) -> Result<File> {
    open_lock(&repo.startup_lock)
}

fn connect_or_start_locked(repo: &Repo) -> Result<UnixStream> {
    if let Ok(stream) = UnixStream::connect(&repo.socket_path) {
        return Ok(stream);
    }
    start_daemon(repo)?;
    let started = Instant::now();
    while started.elapsed() < Duration::from_secs(10) {
        match UnixStream::connect(&repo.socket_path) {
            Ok(stream) => return Ok(stream),
            Err(_) => std::thread::sleep(Duration::from_millis(25)),
        }
    }
    bail!("daemon did not start; see {}", repo.log_path.display())
}

fn start_daemon(repo: &Repo) -> Result<()> {
    let executable = daemon_executable()?;
    let log = File::options()
        .create(true)
        .append(true)
        .open(&repo.log_path)?;
    let error_log = log.try_clone()?;
    let mut command = ProcessCommand::new(executable);
    command
        .arg("__daemon")
        .arg("--repo")
        .arg(&repo.root)
        .stdin(Stdio::null())
        .stdout(Stdio::from(log))
        .stderr(Stdio::from(error_log));
    unsafe {
        command.pre_exec(|| {
            if libc::setsid() == -1 {
                return Err(std::io::Error::last_os_error());
            }
            Ok(())
        });
    }
    command.spawn().context("cannot start mathmux daemon")?;
    Ok(())
}

fn daemon_executable() -> Result<PathBuf> {
    let running_image = PathBuf::from("/proc/self/exe");
    if running_image.is_file() {
        Ok(running_image)
    } else {
        std::env::current_exe().map_err(Into::into)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct BrokenPipe;

    impl Write for BrokenPipe {
        fn write(&mut self, _buffer: &[u8]) -> std::io::Result<usize> {
            Err(std::io::Error::from(std::io::ErrorKind::BrokenPipe))
        }

        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    #[test]
    fn closed_stdout_pipe_is_a_successful_early_exit() {
        output_summary_to(BrokenPipe, "long search result").unwrap();
    }

    #[test]
    fn exchange_consumes_progress_before_the_final_response() {
        let (client, mut server) = UnixStream::pair().unwrap();
        let server_thread = std::thread::spawn(move || {
            let mut request = String::new();
            BufReader::new(server.try_clone().unwrap())
                .read_line(&mut request)
                .unwrap();
            serde_json::to_writer(
                &mut server,
                &Progress {
                    progress: "preparing imports for Demo.lean".into(),
                },
            )
            .unwrap();
            server.write_all(b"\n").unwrap();
            serde_json::to_writer(&mut server, &Response::ok("ok c1 1ms")).unwrap();
            server.write_all(b"\n").unwrap();
        });
        let response = exchange(
            client,
            &Request {
                build: String::new(),
                generation: 0,
                cwd: "/tmp".into(),
                command: Command::Check {
                    file: None,
                    profile: false,
                },
            },
        )
        .unwrap();
        server_thread.join().unwrap();
        assert!(response.ok);
        assert_eq!(response.summary, "ok c1 1ms");
    }

    #[cfg(not(feature = "development"))]
    #[test]
    fn production_help_omits_development_api() {
        let mut command = command_line();
        assert!(command.find_subcommand_mut("issue").is_none());
        assert!(command.find_subcommand_mut("dev").is_none());
        let help = command.render_help().to_string();
        assert!(help.contains("never substitute git, lean, lake"));
        assert!(help.contains("explicit narrow imports"));
    }

    #[cfg(feature = "development")]
    #[test]
    fn development_help_separates_reporting_from_maintenance() {
        let mut command = command_line();
        let help = command.render_help().to_string();
        assert!(help.contains("issue"));
        assert!(help.contains("dev"));
        assert!(help.contains("proving agents"));
        assert!(help.contains("tooling developers only"));
        let issue_help = command
            .find_subcommand_mut("issue")
            .unwrap()
            .render_help()
            .to_string();
        assert!(issue_help.contains("report"));
        assert!(!issue_help.contains("resolve"));
        assert!(!issue_help.contains("dismiss"));
        let matches = command_line()
            .try_get_matches_from(["mathmux", "issue", "report", "search missed an exact name"])
            .unwrap();
        let args = Args::from_arg_matches(&matches).unwrap();
        assert!(matches!(
            args.command,
            TopCommand::Issue {
                command: IssueCommand::Report { .. }
            }
        ));
        let matches = command_line()
            .try_get_matches_from(["mathmux", "dev", "issue", "list"])
            .unwrap();
        let args = Args::from_arg_matches(&matches).unwrap();
        assert!(matches!(
            args.command,
            TopCommand::Dev {
                command: DevCommand::Issue {
                    command: DevIssueCommand::List { .. }
                }
            }
        ));
    }

    #[test]
    fn search_all_is_an_option_not_a_query_term() {
        let matches = command_line()
            .try_get_matches_from(["mathmux", "search", "LinearEquiv.ofFinrankEq", "--all"])
            .unwrap();
        let args = Args::from_arg_matches(&matches).unwrap();
        let TopCommand::Search { query, all, limit } = args.command else {
            panic!("expected search command");
        };
        assert_eq!(query, ["LinearEquiv.ofFinrankEq"]);
        assert!(all);
        assert!(limit.is_none());
    }

    #[test]
    fn search_and_probe_help_expose_only_the_new_api() {
        let mut command = command_line();
        let help = command
            .find_subcommand_mut("search")
            .unwrap()
            .render_long_help()
            .to_string();
        assert!(help.contains("--limit N (1–200) caps hits and cannot combine with --all"));
        for form in [
            "name:NAME",
            "type:LEAN_TYPE",
            "FILE:LINE",
            "outline|declarations|imports|dependents",
            "PATH /REGEX/",
            "name:A|B|C",
            "source/compose are labels, not keywords",
            "sREF requires TERMS",
            "Source facets follow a space, not a colon.",
            "--limit",
        ] {
            assert!(help.contains(form), "missing search form {form}");
        }
        assert!(!help.contains("cREF repair"));
        let probe_help = command
            .find_subcommand_mut("probe")
            .unwrap()
            .render_long_help()
            .to_string();
        for contract in [
            "there are no API, LEAN, or other category keywords",
            "NAME [signature|source|apply",
            "FILE warnings",
            "FILE:LINE [goal]",
            "cREF [goal|types|defeq|rewrite|profile]",
            "declaration-qREF [signature|source|usages|constructors]",
            "Context is mandatory",
            "Use NAME signature, not",
            "no nearby-line fallback",
        ] {
            assert!(
                probe_help.contains(contract),
                "missing probe contract {contract}"
            );
        }
        assert!(!probe_help.contains("API       NAME"));
        assert!(!probe_help.contains("LEAN      FILE"));
        assert!(!help.contains("diagnostics, and goals"));

        let mut short_command = command_line();
        let short_search = short_command
            .find_subcommand_mut("search")
            .unwrap()
            .render_help()
            .to_string();
        assert!(short_search.contains("name:A|B|C"));
        let short_probe = short_command
            .find_subcommand_mut("probe")
            .unwrap()
            .render_help()
            .to_string();
        assert!(short_probe.contains("FILE:LINE [goal]"));
        assert!(short_probe.contains("NAME source resolves the exact declaration"));
        assert!(short_probe.contains("cREF goal/analyses need a matching stored failure"));
    }

    #[test]
    fn workflow_help_prefers_direct_workspace_experimentation() {
        let help = command_line().render_help().to_string();
        assert!(help.contains("Edit intended files -> check -> submit"));
        assert!(help.contains("Exact declarations go straight to probe NAME"));
        assert!(help.contains("Search unknown things; probe known API, exact context"));
    }
}
