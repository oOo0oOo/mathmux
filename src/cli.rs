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
use crate::issue::IssueStore;
use crate::protocol::{Command, Request, Response};
use crate::repo::Repo;

const WORKFLOW_HELP: &str = r#"WORKFLOW
  Work only in the current mathmux workspace. Use mathmux for all repository
  coordination and certification. Do not run git, lean, lake build, or equivalent
  commands directly. Do not enter managed main or another workspace.

  Check the smallest relevant file while editing. A bare check certifies all dirty
  Lean files. Use show <REF> for detail instead of rerunning commands. Use sync to
  bring managed main into the workspace and submit to integrate certified work.

LEAN
  Keep each file focused on one coherent module. Split files when unrelated edits
  cause costly suffix re-elaboration. Use the module system consistently, keep
  imports explicit and narrow, and use public import only for module API.

  Align module names, namespaces, and paths. Keep foundational modules stable and
  avoid broad umbrella imports. sorry is tracked and allowed during development;
  extra axioms fail submission validation. Do not edit .lake or generated artifacts."#;

#[derive(Parser)]
#[command(
    name = "mathmux",
    version,
    disable_help_subcommand = true,
    about = "Fast local Lean checks in isolated worktrees",
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
    /// Certify one Lean file, or every dirty Lean file.
    ///
    /// With FILE, synchronously certifies that file and its source dependencies.
    /// Without FILE, certifies every dirty Lean file. Stops at the first error and
    /// stores full diagnostics under the returned reference.
    Check {
        /// Lean file to certify; omit to certify all dirty Lean files.
        file: Option<PathBuf>,
    },
    /// Bring managed main into the current workspace.
    ///
    /// Merges mathmux-managed main into the current workspace and reports conflicts
    /// without moving work into main.
    Sync,
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
}

#[derive(Clone, Copy, ValueEnum)]
enum IssueFilter {
    Open,
    Resolved,
    All,
}

impl IssueFilter {
    fn as_str(self) -> &'static str {
        match self {
            Self::Open => "open",
            Self::Resolved => "resolved",
            Self::All => "all",
        }
    }
}

pub fn run() -> Result<u8> {
    let development = development_requested();
    if !development && requested_top_command().as_deref() == Some("issue") {
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
    if let TopCommand::Issue { command } = args.command {
        ensure!(development, "development commands are disabled");
        return run_issue(command, &cwd);
    }
    if let TopCommand::Show { reference, all } = &args.command
        && reference.starts_with('i')
    {
        ensure!(development, "development commands are disabled");
        println!("{}", IssueStore::global()?.show(reference, *all)?);
        return Ok(0);
    }
    let repo = Repo::discover(&cwd)?;
    let command = match args.command {
        TopCommand::Ws { command } => match command {
            WsCommand::Create { name } => Command::WsCreate { name },
            WsCommand::List => Command::WsList,
            WsCommand::Delete { name } => Command::WsDelete { name },
        },
        TopCommand::Check { file } => Command::Check {
            file: file.map(|path| {
                let path = if path.is_absolute() {
                    path
                } else {
                    cwd.join(path)
                };
                path.to_string_lossy().into_owned()
            }),
        },
        TopCommand::Sync => Command::Sync,
        TopCommand::Submit { message } => Command::Submit { message },
        TopCommand::Show { reference, all } => Command::Show { reference, all },
        TopCommand::Issue { .. } => unreachable!(),
        TopCommand::Daemon { .. } => unreachable!(),
    };
    let request = Request {
        build: crate::util::build_id().to_owned(),
        cwd: cwd.to_string_lossy().into_owned(),
        command,
    };
    let mut handoffs = 0;
    let response = loop {
        let response = exchange(connect_or_start(&repo)?, &request)?;
        if !response.retry {
            break response;
        }
        ensure!(
            handoffs == 0,
            "daemon build changed repeatedly; retry command"
        );
        handoffs += 1;
        wait_for_daemon_exit(&repo)?;
    };
    if development {
        let _ = crate::issue::record_exchange(&repo, &request, &response);
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
    let mut line = String::new();
    BufReader::new(stream).read_line(&mut line)?;
    serde_json::from_str(&line).context("invalid daemon response")
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
        command = command.mut_subcommand("issue", |command| command.hide(false));
    }
    command
}

fn connect_or_start(repo: &Repo) -> Result<UnixStream> {
    if let Ok(stream) = UnixStream::connect(&repo.socket_path) {
        return Ok(stream);
    }
    let startup_lock = OpenOptions::new()
        .create(true)
        .truncate(false)
        .read(true)
        .write(true)
        .open(&repo.startup_lock)?;
    startup_lock.lock_exclusive()?;
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
    let executable = std::env::current_exe()?;
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn issue_help_requires_the_development_opt_in() {
        let normal = command_line(false).render_help().to_string();
        let development = command_line(true).render_help().to_string();
        assert!(!normal.contains("issue"));
        assert!(development.contains("issue"));
        assert!(normal.contains("Do not run git, lean, lake build"));
        assert!(normal.contains("Keep each file focused on one coherent module"));
    }
}
