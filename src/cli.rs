use std::fs::{File, OpenOptions};
use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::UnixStream;
use std::os::unix::process::CommandExt;
use std::path::PathBuf;
use std::process::{Command as ProcessCommand, Stdio};
use std::time::{Duration, Instant};

use anyhow::{Context, Result, bail};
use clap::{Parser, Subcommand};
use fs2::FileExt;

use crate::daemon;
use crate::protocol::{Command, Request, Response};
use crate::repo::Repo;

#[derive(Parser)]
#[command(
    name = "mathmux",
    version,
    disable_help_subcommand = true,
    about = "Fast local Lean checks in isolated worktrees"
)]
struct Args {
    #[command(subcommand)]
    command: TopCommand,
}

#[derive(Subcommand)]
enum TopCommand {
    /// Manage isolated workspaces.
    Ws {
        #[command(subcommand)]
        command: WsCommand,
    },
    /// Certify one Lean file, or every dirty Lean file.
    Check { file: Option<PathBuf> },
    /// Bring managed main into the current workspace.
    Sync,
    /// Integrate a certified change and queue validation.
    Submit {
        #[arg(short = 'm')]
        message: Option<String>,
    },
    /// Show full details for a short reference.
    Show {
        reference: String,
        #[arg(long)]
        all: bool,
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
    Create { name: String },
    /// List managed workspaces.
    List,
    /// Delete a clean workspace.
    Delete { name: String },
}

pub fn run() -> Result<u8> {
    let args = Args::parse();
    if let TopCommand::Daemon { repo } = args.command {
        daemon::run(Repo::from_root(&repo)?)?;
        return Ok(0);
    }
    let cwd = std::env::current_dir()?;
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
        TopCommand::Daemon { .. } => unreachable!(),
    };
    let mut stream = connect_or_start(&repo)?;
    serde_json::to_writer(
        &mut stream,
        &Request {
            cwd: cwd.to_string_lossy().into_owned(),
            command,
        },
    )?;
    stream.write_all(b"\n")?;
    stream.flush()?;
    let mut line = String::new();
    BufReader::new(stream).read_line(&mut line)?;
    let response: Response = serde_json::from_str(&line).context("invalid daemon response")?;
    if response.ok {
        println!("{}", response.summary);
        Ok(0)
    } else {
        eprintln!("error {}", response.summary);
        Ok(1)
    }
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
