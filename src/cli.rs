use std::fs::{File, OpenOptions};
use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::UnixStream;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command as ProcessCommand, Stdio};
use std::time::{Duration, Instant};

use anyhow::{Context, Result, bail, ensure};
use clap::{CommandFactory, FromArgMatches, Parser, Subcommand, ValueEnum};
use fs2::FileExt;

use crate::daemon;
use crate::issue::{IssueStore, TelemetryStore, development_enabled, enable_development};
use crate::protocol::{Command, Request, Response};
use crate::repo::Repo;

const WORKFLOW_HELP: &str = r#"WORKFLOW
  Work only in the current mathmux workspace. Use mathmux for repository search,
  coordination, and certification. Do not run git, lean, lake build, or equivalent
  commands directly. Do not enter managed main or another workspace.

  Check the smallest relevant file while editing. A bare check certifies all dirty
  Lean files. Use show <REF> for detail instead of rerunning commands. Use sync to
  bring managed main into the workspace and submit to integrate certified work.

LEAN
  Use Lean's module system. Keep each file coherent, imports explicit and narrow,
  and public imports limited to module API. Align module names, namespaces, and
  paths. Split files when unrelated edits cause costly suffix re-elaboration.

  sorry is tracked and allowed during development; extra axioms fail submission
  validation. Do not edit .lake or generated artifacts."#;

const SEARCH_HELP: &str = r#"Search local Lean declarations, types, source, and goals.

Query forms are inferred in this order:
  cREF [TERMS]                  search a check diagnostic
  qREF TERMS                    refine a stored search
  qREF MORE                     show complete stored results
  sREF [TERMS]                  search a submission

  FILE:LINE[:COLUMN]            elaborate the goal at a position
  FILE:LINE MORE                show larger bounded source context
  FILE:tail                     show bounded end-of-file context
  FILE:START-END                show a bounded source range
  FILE[:START-END] A|B          find literal source occurrences
  FILE outline|declarations     list declarations, lines, and signatures

  NAME                          exact declaration plus nearby API
  KIND NAME [body|proof|source] declaration-directed lookup
  NAME*                         declaration-name glob
  STRUCTURE fields              complete field inventory
  TYPE or WORDS                 type, name, concept, and source search
  A|B                           alternatives with short-circuiting

Lean forms such as #check, #print, #synth, and @NAME are accepted. Search is
import-aware and stores complete results under the returned qREF."#;

#[derive(Parser)]
#[command(
    name = "mathmux",
    version,
    disable_help_subcommand = true,
    about = "Fast local Lean development in isolated worktrees",
    after_help = WORKFLOW_HELP
)]
struct Args {
    #[arg(long, global = true, hide = true)]
    development: bool,
    #[command(subcommand)]
    command: TopCommand,
}

#[derive(Subcommand)]
enum TopCommand {
    /// Manage isolated workspaces.
    ///
    /// Create, list, or delete mathmux-owned branches and worktrees. Work from the
    /// assigned workspace and let mathmux manage main.
    Ws {
        #[command(subcommand)]
        command: WsCommand,
    },
    /// Show formalization activity, throughput, and tooling performance.
    ///
    /// Summarizes live project agents, Lean code size and growth, agent-normalized
    /// throughput, and recent check, build, and submission statistics.
    Status {
        /// Print a partially generated formalization.yaml draft.
        #[arg(long)]
        formalization_yaml: bool,
    },
    /// Certify one Lean file, or every dirty Lean file.
    ///
    /// With FILE, synchronously certifies that file and its source dependencies.
    /// Without FILE, certifies every dirty Lean file. Stops at the first error and
    /// stores full diagnostics under the returned reference.
    Check {
        /// Lean file to certify; omit to certify all dirty Lean files.
        file: Option<PathBuf>,
        /// Report dependency, cache, setup, and elaboration timings.
        #[arg(long)]
        profile: bool,
    },
    /// Search local Lean declarations, types, source, and goals.
    #[command(long_about = SEARCH_HELP)]
    Search {
        /// One inferred query; see the forms above.
        #[arg(required = true, num_args = 1..)]
        query: Vec<String>,
        /// Return complete results for this query instead of the compact preview.
        #[arg(long)]
        all: bool,
    },
    /// Bring managed main into the current workspace, or publish managed main.
    ///
    /// Merges mathmux-managed main into the current workspace and reports conflicts
    /// without moving work into main. With --push, publishes managed main through
    /// its configured Git remote instead of changing the workspace.
    Sync {
        /// Push managed main through its configured Git remote.
        #[arg(long)]
        push: bool,
    },
    /// Integrate a certified change and queue validation.
    ///
    /// Requires current check coverage for the dirty Lean files. Integrates the
    /// change into managed main, queues build and axiom validation, then returns a
    /// submission reference without waiting for validation.
    Submit {
        /// Optional integration commit message.
        #[arg(short = 'm')]
        message: Option<String>,
    },
    /// Show full details for a short reference.
    ///
    /// Shows stored check, sync, or submission detail. Use --all for complete
    /// diagnostics, linter output, build output, axioms, and sorry locations.
    Show {
        /// Short check, sync, or submission reference.
        reference: String,
        /// Include complete stored detail.
        #[arg(long)]
        all: bool,
    },
    /// Use the local development issue inbox.
    #[command(hide = true)]
    Issue {
        #[command(subcommand)]
        command: IssueCommand,
    },
    /// Inspect local development telemetry.
    #[command(hide = true)]
    Telemetry {
        /// Time window such as 30m, 24h, 7d, or all.
        #[arg(long, default_value = "24h")]
        since: String,
        /// Restrict results to one command verb.
        #[arg(long)]
        verb: Option<String>,
        /// Show the N slowest events instead of aggregates.
        #[arg(long)]
        slow: Option<usize>,
    },
    #[command(name = "__daemon", hide = true)]
    Daemon {
        #[arg(long)]
        repo: PathBuf,
    },
}

#[derive(Subcommand)]
enum WsCommand {
    /// Create a managed branch and worktree.
    Create {
        /// Unique workspace name.
        name: String,
        /// Model assigned to this workspace, for persistent attribution.
        #[arg(long)]
        model: Option<String>,
    },
    /// List managed workspaces.
    List,
    /// Delete a clean workspace.
    Delete {
        /// Workspace name.
        name: String,
    },
}

#[derive(Subcommand)]
enum IssueCommand {
    /// Record a tool-related issue with local context.
    Report {
        summary: String,
        #[arg(long = "ref")]
        reference: Option<String>,
    },
    /// List issues from the local development inbox.
    List {
        #[arg(long, default_value = "open")]
        status: IssueFilter,
    },
    /// Mark an issue resolved.
    Resolve {
        issue: String,
        #[arg(long)]
        fixed_by: Option<String>,
        #[arg(short = 'm')]
        note: Option<String>,
    },
    /// Dismiss an issue that is not an actionable tooling defect.
    Dismiss {
        issue: String,
        /// Why the issue is not actionable.
        #[arg(short = 'm', long = "reason")]
        reason: String,
    },
}

#[derive(Clone, Copy, ValueEnum)]
enum IssueFilter {
    Open,
    Resolved,
    Dismissed,
    All,
}

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
    let development = development_requested();
    if !development && matches!(requested_top_command().as_deref(), Some("telemetry")) {
        bail!("development commands are disabled");
    }
    let command = command_line(development);
    let matches = command.get_matches();
    let args = Args::from_arg_matches(&matches)?;
    let development = development || args.development;
    if let TopCommand::Daemon { repo } = args.command {
        daemon::run(Repo::from_root(&repo)?)?;
        return Ok(0);
    }
    let cwd = std::env::current_dir()?;
    if development && let Ok(repo) = Repo::discover(&cwd) {
        let _ = enable_development(&repo);
    }
    if let TopCommand::Issue { command } = args.command {
        ensure!(
            development || matches!(command, IssueCommand::Report { .. }),
            "development commands are disabled"
        );
        return run_issue(command, &cwd);
    }
    if let TopCommand::Telemetry { since, verb, slow } = args.command {
        ensure!(development, "development commands are disabled");
        println!(
            "{}",
            TelemetryStore::global()?.summary(&since, verb.as_deref(), slow)?
        );
        return Ok(0);
    }
    if let TopCommand::Show { reference, all } = &args.command
        && matches!(reference.as_bytes().first(), Some(b'i' | b'e'))
    {
        ensure!(development, "development commands are disabled");
        let summary = if reference.starts_with('i') {
            IssueStore::global()?.show(reference, *all)?
        } else {
            TelemetryStore::global()?.show(reference, *all)?
        };
        println!("{summary}");
        return Ok(0);
    }
    let repo = Repo::discover(&cwd)?;
    let project_development = development || development_enabled(&repo);
    let command = match args.command {
        TopCommand::Ws { command } => match command {
            WsCommand::Create { name, model } => Command::WsCreate { name, model },
            WsCommand::List => Command::WsList,
            WsCommand::Delete { name } => Command::WsDelete { name },
        },
        TopCommand::Status {
            formalization_yaml,
        } => Command::Status {
            formalization_yaml,
        },
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
        TopCommand::Search { query, all } => Command::Search {
            query: query.join(" "),
            all,
        },
        TopCommand::Sync { push } => Command::Sync { push },
        TopCommand::Submit { message } => Command::Submit { message },
        TopCommand::Show { reference, all } => Command::Show { reference, all },
        TopCommand::Issue { .. } | TopCommand::Telemetry { .. } | TopCommand::Daemon { .. } => {
            unreachable!()
        }
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
        if project_development {
            let _ = crate::issue::record_exchange(
                &repo,
                &request,
                &response,
                client_started.elapsed().as_millis() as u64,
            );
        }
        if response.ok {
            println!("{}", response.summary);
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
            None => connect_or_start(&repo, project_development),
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
            handoff_stream = Some(replace_daemon(&repo, project_development)?);
        } else {
            ensure!(
                retirement_waits < 2,
                "daemon replacement did not settle; retry command"
            );
            retirement_waits += 1;
            handoff_stream = Some(wait_for_replacement(&repo)?);
        }
    };
    if project_development {
        let _ = crate::issue::record_exchange(
            &repo,
            &request,
            &response,
            client_started.elapsed().as_millis() as u64,
        );
    }
    if response.ok {
        println!("{}", response.summary);
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
    let report_progress = matches!(request.command, Command::Check { .. });
    if report_progress {
        stream.set_read_timeout(Some(Duration::from_secs(30)))?;
    }
    let started = Instant::now();
    let mut reader = BufReader::new(stream);
    let mut line = String::new();
    let bytes = loop {
        match reader.read_line(&mut line) {
            Ok(bytes) => break bytes,
            Err(error)
                if report_progress
                    && matches!(
                        error.kind(),
                        std::io::ErrorKind::TimedOut | std::io::ErrorKind::WouldBlock
                    ) =>
            {
                eprintln!("check running {}s", started.elapsed().as_secs());
                reader
                    .get_ref()
                    .set_read_timeout(Some(Duration::from_secs(60)))?;
            }
            Err(error) => return Err(error.into()),
        }
    };
    if bytes == 0 {
        return Err(std::io::Error::from(std::io::ErrorKind::UnexpectedEof).into());
    }
    serde_json::from_str(&line).context("invalid daemon response")
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
        if !repo.socket_path.exists() {
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

fn run_issue(command: IssueCommand, cwd: &Path) -> Result<u8> {
    let store = IssueStore::global()?;
    let summary = match command {
        IssueCommand::Report { summary, reference } => {
            store.create(cwd, &summary, reference.as_deref())?
        }
        IssueCommand::List { status } => store.list(status.as_str())?,
        IssueCommand::Resolve {
            issue,
            fixed_by,
            note,
        } => store.resolve(&issue, fixed_by.as_deref(), note.as_deref())?,
        IssueCommand::Dismiss { issue, reason } => store.dismiss(&issue, &reason)?,
    };
    println!("{summary}");
    Ok(0)
}

fn development_requested() -> bool {
    let environment = std::env::var("MATHMUX_DEVELOPMENT")
        .ok()
        .is_some_and(|value| matches!(value.as_str(), "1" | "true" | "yes"));
    environment || std::env::args_os().any(|argument| argument == "--development")
}

fn requested_top_command() -> Option<String> {
    std::env::args_os()
        .skip(1)
        .filter(|argument| argument != "--development")
        .find(|argument| !argument.to_string_lossy().starts_with('-'))
        .map(|argument| argument.to_string_lossy().into_owned())
}

fn command_line(development: bool) -> clap::Command {
    let mut command = Args::command();
    if development {
        command = command
            .mut_subcommand("issue", |command| {
                command
                    .hide(false)
                    .mut_subcommand("list", |command| command.hide(false))
                    .mut_subcommand("resolve", |command| command.hide(false))
                    .mut_subcommand("dismiss", |command| command.hide(false))
            })
            .mut_subcommand("telemetry", |command| command.hide(false));
    } else {
        command = command.mut_subcommand("issue", |command| {
            command
                .mut_subcommand("list", |command| command.hide(true))
                .mut_subcommand("resolve", |command| command.hide(true))
                .mut_subcommand("dismiss", |command| command.hide(true))
        });
    }
    command
}

fn connect_or_start(repo: &Repo, development: bool) -> Result<UnixStream> {
    if let Ok(stream) = UnixStream::connect(&repo.socket_path) {
        return Ok(stream);
    }
    let startup_lock = startup_lock(repo)?;
    startup_lock.lock_exclusive()?;
    connect_or_start_locked(repo, development)
}

fn replace_daemon(repo: &Repo, development: bool) -> Result<UnixStream> {
    let startup_lock = startup_lock(repo)?;
    startup_lock.lock_exclusive()?;
    wait_for_daemon_exit(repo)?;
    connect_or_start_locked(repo, development)
}

fn startup_lock(repo: &Repo) -> Result<File> {
    OpenOptions::new()
        .create(true)
        .truncate(false)
        .read(true)
        .write(true)
        .open(&repo.startup_lock)
        .map_err(Into::into)
}

fn connect_or_start_locked(repo: &Repo, development: bool) -> Result<UnixStream> {
    if let Ok(stream) = UnixStream::connect(&repo.socket_path) {
        return Ok(stream);
    }
    start_daemon(repo, development)?;
    let started = Instant::now();
    while started.elapsed() < Duration::from_secs(10) {
        match UnixStream::connect(&repo.socket_path) {
            Ok(stream) => return Ok(stream),
            Err(_) => std::thread::sleep(Duration::from_millis(25)),
        }
    }
    bail!("daemon did not start; see {}", repo.log_path.display())
}

fn start_daemon(repo: &Repo, development: bool) -> Result<()> {
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
    if development {
        command.env("MATHMUX_DEVELOPMENT", "1");
    }
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

    #[test]
    fn development_commands_stay_out_of_normal_help() {
        let normal = command_line(false).render_help().to_string();
        let development = command_line(true).render_help().to_string();
        assert!(!normal.contains("issue"));
        assert!(!normal.contains("telemetry"));
        assert!(development.contains("issue"));
        assert!(development.contains("telemetry"));
        assert!(normal.contains("Do not run git, lean, lake build"));
        assert!(normal.contains("Use Lean's module system"));
    }

    #[test]
    fn managed_workspaces_can_report_but_not_triage_issues() {
        let mut normal = command_line(false);
        let issue_help = normal
            .find_subcommand_mut("issue")
            .unwrap()
            .render_help()
            .to_string();
        assert!(issue_help.contains("report"));
        assert!(!issue_help.contains("resolve"));
        assert!(!issue_help.contains("dismiss"));
        let matches = command_line(false)
            .try_get_matches_from(["mathmux", "issue", "report", "search missed an exact name"])
            .unwrap();
        let args = Args::from_arg_matches(&matches).unwrap();
        assert!(matches!(
            args.command,
            TopCommand::Issue {
                command: IssueCommand::Report { .. }
            }
        ));
    }

    #[test]
    fn search_all_is_an_option_not_a_query_term() {
        let matches = command_line(false)
            .try_get_matches_from(["mathmux", "search", "LinearEquiv.ofFinrankEq", "--all"])
            .unwrap();
        let args = Args::from_arg_matches(&matches).unwrap();
        let TopCommand::Search { query, all } = args.command else {
            panic!("expected search command");
        };
        assert_eq!(query, ["LinearEquiv.ofFinrankEq"]);
        assert!(all);
    }

    #[test]
    fn search_help_lists_inferred_query_forms() {
        let mut command = command_line(false);
        let help = command
            .find_subcommand_mut("search")
            .unwrap()
            .render_long_help()
            .to_string();
        for form in [
            "cREF [TERMS]",
            "FILE:LINE[:COLUMN]",
            "FILE outline|declarations",
            "STRUCTURE fields",
            "A|B",
        ] {
            assert!(help.contains(form), "missing search form {form}");
        }
    }
}
