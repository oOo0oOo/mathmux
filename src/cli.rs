use std::fs::File;
use std::io::{BufRead, BufReader, Write};
use std::os::unix::fs::MetadataExt;
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
#[cfg(feature = "development")]
use crate::state::State;
use anyhow::{Context, Result, bail, ensure};
#[cfg(feature = "development")]
use clap::ValueEnum;
use clap::{CommandFactory, FromArgMatches, Parser, Subcommand};

const WORKFLOW_HELP: &str = r#"AGENT CONTRACT
  api       search-v12/probe-v17; reread search/probe help only when this digest changes.
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
API search-v12 — compact discovery; reread only when this digest changes
FORMS — type one directly; declaration/type/source/compose are labels, not keywords
  declaration  NAME | NAME* | KIND NAME [source|body|proof]
  type/concept TYPE_OR_CONCEPT_TERMS | type:LEAN_TYPE
  source       FILE:LINE | FILE:START-END | FILE:tail
               FILE[:RANGE] [find] TERMS
               FILE outline|declarations|imports|dependents
               MODULE outline|declarations
               /REGEX/ | PATH /REGEX/ | re:/REGEX/ | PATH re:/REGEX/
  compose      A|B|C | sREF TERMS

KIND = abbrev|class|def|inductive|instance|lemma|structure|theorem

RESULT
  Exact declarations show signature, path, imports, and a usage count.
  Recognizable API names accept trailing signature for exact lookup; usages routes to probe.
  Regex and source-term matches group by enclosing declaration. qREF metadata is last.
  Use probe NAME source|outline|usages for focused detail. qREFs retain stored result sets;
  show qREF --all expands genuine multi-result or source-range searches.
  --max-results/--limit N (1–200) caps hits and cannot combine with --all.
  Source-only ranges of 48 lines or fewer are complete in compact mode; longer
  ranges name the next non-overlapping range. search --all is accepted only for
  explicit FILE:START-END or FILE:tail reads. Refine grouped searches before expansion.
  Exact names include full signatures, including multiline declarations without bodies.
  NAME source/body/proof uses fresh snapshots
  with explicit continuation and lossless show qREF --all.

NEXT
  One declaration -> probe NAME signature|source|outline|usages. Exact misses fail
  closed with at most three near-name suggestions. With none, try the leaf name;
  an unqualified miss broadens to a quoted NAME* pattern instead of repeating itself.
  Many hits -> refine first. Compact output gives one focused next action.

RULES
  Bare identifier queries are exact-first. type: matches declaration result types;
  `_` holes are legal. Probe qREFs; do not compose them into new searches.
  sREF requires TERMS; use show sREF first, then --all only if needed.
  Source facets accept a space or FILE.lean:outline shorthand.
  FILE:LINE reads source only; use probe FILE:LINE for Lean context.
  Quote queries containing shell characters such as |, *, or #.
  Sigil what you know; leave inference for what you do not."#;

const PROBE_HELP: &str = r##"PROBE — inspect something known; returns qREF
API probe-v17 — bounded exact inspection; reread only when this digest changes
FORMS — type one directly; there are no API, LEAN, or other category keywords
  NAME [signature|source|outline|apply|fields|constructors|ext|simp|usages|assumptions|evidence|examples]
  NAME find TERM
  type:LEAN_TYPE [types]
  FILE warnings
  FILE:LINE [goal] | FILE:LINE TERM [signature]
  FILE:LINE NAME evidence  (inspect up to three candidates; stop at verified evidence)
  FILE:LINE NAME examples  (retrieve existing small-case candidates)
  PATH NAME usages
  cREF [goal|types|defeq|rewrite|profile|context]
  qREF[#N] [signature|source|outline|find TERM|usages|constructors]
  positioned-qREF [goal] | stored-probe-qREF
  FILE|FILE:LINE|cREF|qREF "#check TERM"|"#synth TYPE"|"#reduce TERM"
  FILE:LINE|cREF|positioned-qREF "by TACTIC"|"#apply TERM"|"#inspect TERM"

RESULT
  NAME source/outline/find reads a fresh textual snapshot. Source includes ambient
  binders, scoped options, bounded local-instance previews, and its own docs.
  Find reports actual file lines, labeling ambient matches.
  Long source previews show continuation ranges; show qREF --all recovers the stored
  snapshot. Aliases and explicitly named to_additive declarations show their generator
  and an origin follow-up; generator text is not the generated proof or signature.
  Source retains preceding attributes and multiline variables, including bare variable
  commands. Indexed fallbacks are labeled incomplete. Text is not Lean elaboration.
  Examples label direct existing-subject inputs; automatic ranking prefers public APIs,
  then fewer direct subject inputs. Private visibility is separate from Lean premises.
  Lean experiments need a project file importing the declaration; dependency files
  remain available for textual source inspection.
  NAME assumptions exposes premises and selected input APIs; evidence retrieves
  construction/obstruction/subsingleton candidates with hypotheses. Indexed text is not verified
  applicability; no results is not an existence verdict. Use qualified names.
  NAME examples selects existing constructions with fewer indexed inputs and
  project-authored examples as selectable qREF#N results; hidden premises remain.
  A current snapshot-verified obstruction may appear directly in search; changing
  project sources/configuration invalidates that evidence. Authored routes are advisory.
  Exact discovery can flag specialized evidence about an explicit input type.
  Unqualified inputs need lexical source context before global obstruction lookup.
  cREF context adds type differences, import-aware laws and one usage to the failure.
  Field inventories label omitted inherited obligations and show parent types.
  #inspect lists explicit inputs first; show qREF --all retains every input.
  Bare-name inspection preserves implicit/default binders instead of applying them.
  #inspect uses readable input names and labels instance inputs/assumptions.
  Constructor probes without indexed signatures point to fields or Lean inspection.
  #inspect inspects elaborated inputs/result, constructors or a definition body;
  #apply tests an application and reports remaining obligations, without editing.
  Test small cases with #check (TERM : EXPECTED_TYPE), #reduce TERM or by TACTIC.
  All experiments require explicit context; check remains certification.
  FILE warnings returns ranked residual-warning qREFs from its latest current check;
  probing one returns a source-bound dossier with API/dependency evidence.
  API focuses return one bounded dossier. goal returns the exact local goal;
  TERM/directives return Lean's elaborated answer; by returns solved or subgoals.
  NAME source resolves the exact declaration and returns that body; outline is
  kind-aware, and find searches only that declaration. A miss never
  falls through to another declaration. search FILE:LINE/RANGE reads file text.

NEXT
  Start with signature; request source/usages only for the selected declaration.

RULES
  fields/constructors target structures/inductives; ext/simp may be empty.
  cREF goal/analyses need a matching stored failure; for a running check, use
  mathmux show cREF --wait first; profile needs check --profile. For queued or
  running validation, use mathmux show sREF --wait.
  warnings omits mechanical fixes owned by Lean automation and never reruns Lean.
  Context is mandatory for directives and never guessed. FILE uses its imports;
  FILE:LINE uses that exact line—there is no nearby-line fallback. Probe never
  edits or certifies source; use check after editing. Use NAME signature, not
  NAME "#check NAME". Quote directives. Cancel an owned running check with
  `mathmux cancel cREF`, then use `mathmux show cREF` to confirm termination."##;

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
    /// Cancel an owned running check and terminate its Lean process group.
    Cancel {
        /// Running check reference, for example c123.
        reference: String,
    },
    /// Find Lean declarations, types, concepts, and source.
    #[command(before_help = SEARCH_HELP)]
    Search {
        /// Query terms; the query form is inferred as documented above.
        #[arg(required = true, num_args = 1..)]
        query: Vec<String>,
        /// Return at most N ranked results (1–200).
        #[arg(
            long = "max-results",
            visible_alias = "limit",
            value_parser = parse_max_results,
            conflicts_with = "all"
        )]
        max_results: Option<usize>,
        /// Expand an explicit FILE:START-END or FILE:tail source read.
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
    /// keeping raw build logs bounded. --wait waits for a running cREF or sREF validation.
    Show {
        /// Stored cREF, qREF, sREF, uREF, or wREF.
        reference: String,
        /// Include expanded stored detail.
        #[arg(long, conflicts_with = "wait")]
        all: bool,
        /// Wait for a running cREF or queued/running sREF to finish, with bounded progress updates.
        #[arg(long, conflicts_with = "all")]
        wait: bool,
    },
    /// Restart only the MathMux daemon for this repository.
    ///
    /// This drains active validation safely and starts a fresh per-repository
    /// daemon. It does not restart Oli or any agent-control service.
    Restart,
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
    /// Delete a managed workspace.
    ///
    /// Refuses dirty workspaces unless --force is supplied. --force discards
    /// uncommitted changes and unsubmitted branch commits.
    Delete {
        /// Workspace name.
        name: String,
        /// Explicitly discard all workspace and unsubmitted branch changes.
        #[arg(long)]
        force: bool,
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
    /// Report project-owned storage and safe reclaimable space.
    Storage,
    /// Reclaim deleted-workspace setups and obsolete generated services.
    Gc {
        /// Report what would be removed without changing anything.
        #[arg(long)]
        dry_run: bool,
        /// Include unreachable Lake artifacts, generated validation output,
        /// and safe unregistered worktrees.
        #[arg(long)]
        hard: bool,
        /// Confirm destructive hard-GC cleanup.
        #[arg(long, requires = "hard")]
        confirm: bool,
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
            WsCommand::Delete { name, force } => Command::WsDelete { name, force },
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
        TopCommand::Cancel { reference } => Command::Cancel { reference },
        TopCommand::Search {
            query,
            max_results,
            all,
        } => Command::Search {
            query: query.join(" "),
            max_results,
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
        TopCommand::Restart => Command::Restart,
        #[cfg(feature = "development")]
        TopCommand::Issue { .. } | TopCommand::Dev { .. } => unreachable!(),
        TopCommand::Daemon { .. } => unreachable!(),
    };
    let request = Request {
        build: crate::util::build_id().to_owned(),
        generation: crate::util::build_generation(),
        actor_id: telemetry_identity("MATHMUX_ACTOR_ID"),
        session_id: telemetry_identity("MATHMUX_SESSION_ID"),
        cwd: cwd.to_string_lossy().into_owned(),
        command,
    };
    if matches!(request.command, Command::Restart) {
        return restart_daemon(&repo, &request);
    }
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
    if response.ok {
        output_summary(&response.summary)?;
        Ok(0)
    } else {
        eprintln!("error {}", response.summary);
        Ok(1)
    }
}

fn parse_max_results(value: &str) -> std::result::Result<usize, String> {
    let max_results = value
        .parse::<usize>()
        .map_err(|_| "--max-results must be between 1 and 200".to_owned())?;
    if (1..=200).contains(&max_results) {
        Ok(max_results)
    } else {
        Err("--max-results must be between 1 and 200".to_owned())
    }
}

fn exchange_progress_label(command: &Command) -> Option<&'static str> {
    match command {
        Command::Check { .. } => Some("check"),
        Command::Probe { .. } => Some("probe"),
        Command::Show { wait: true, .. } => Some("show"),
        _ => None,
    }
}

fn progress_update_due(
    progress_label: Option<&str>,
    elapsed: Duration,
    next_report: Duration,
) -> bool {
    progress_label == Some("show") && elapsed >= next_report
}

fn exchange(mut stream: UnixStream, request: &Request) -> Result<Response> {
    serde_json::to_writer(&mut stream, &request)?;
    stream.write_all(b"\n")?;
    stream.flush()?;
    let progress_label = exchange_progress_label(&request.command);
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
                    if progress_update_due(progress_label, started.elapsed(), next_report) {
                        eprintln!(
                            "{} {progress} {}s",
                            progress_label.expect("progress label is present"),
                            started.elapsed().as_secs()
                        );
                        next_report += Duration::from_secs(30);
                    }
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
    let store = issue_store(cwd)?;
    let summary = match command {
        IssueCommand::Report { summary, reference } => {
            store.create(cwd, summary, reference.as_deref())?
        }
    };
    output_summary(&summary)?;
    Ok(0)
}

#[cfg(feature = "development")]
fn run_dev(command: &DevCommand, cwd: &Path) -> Result<u8> {
    let summary = match command {
        DevCommand::Issue { command } => {
            let store = issue_store(cwd)?;
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
            telemetry_store(cwd)?.summary(since, verb.as_deref(), *slow)?
        }
        DevCommand::Show { reference, all } => {
            if reference.starts_with('i') {
                issue_store(cwd)?.show(reference, *all)?
            } else if reference.starts_with('e') {
                telemetry_store(cwd)?.show(reference, *all)?
            } else {
                bail!("dev show expects iREF or eREF")
            }
        }
        DevCommand::Storage => {
            let repo = Repo::discover(cwd)?;
            let state = State::new(&repo.db_path)?;
            crate::storage::render_storage(&repo, &state)?
        }
        DevCommand::Gc {
            dry_run,
            hard,
            confirm,
        } => {
            let repo = Repo::discover(cwd)?;
            let state = State::new(&repo.db_path)?;
            crate::storage::run_gc(&repo, &state, *dry_run, *hard, *confirm)?
        }
    };
    output_summary(&summary)?;
    Ok(0)
}

#[cfg(feature = "development")]
fn issue_store(cwd: &Path) -> Result<IssueStore> {
    match Repo::discover(cwd) {
        Ok(repo) => IssueStore::global_for_repo(&repo),
        Err(_) => IssueStore::global(),
    }
}

#[cfg(feature = "development")]
fn telemetry_store(cwd: &Path) -> Result<TelemetryStore> {
    match Repo::discover(cwd) {
        Ok(repo) => TelemetryStore::global_for_repo(&repo),
        Err(_) => TelemetryStore::global(),
    }
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

fn restart_daemon(repo: &Repo, request: &Request) -> Result<u8> {
    let stream = connect_or_start(repo)?;
    let mut instance = socket_inode(repo)?;
    let mut response = exchange(stream, request)?;
    if response.retry {
        let stream = if request.generation > response.generation {
            replace_daemon(repo, request)?
        } else {
            wait_for_replacement(repo)?
        };
        instance = socket_inode(repo)?;
        response = exchange(stream, request)?;
    }
    ensure!(
        response.ok,
        "daemon restart request failed: {}",
        response.summary
    );
    wait_for_daemon_replacement(repo, instance)?;
    let stream = connect_or_start(repo)?;
    drop(stream);
    output_summary("restarted mathmux daemon")?;
    Ok(0)
}

fn socket_inode(repo: &Repo) -> Result<u64> {
    Ok(std::fs::metadata(&repo.socket_path)?.ino())
}

fn wait_for_daemon_replacement(repo: &Repo, previous_inode: u64) -> Result<()> {
    let started = Instant::now();
    while started.elapsed() < Duration::from_secs(10 * 60) {
        match std::fs::metadata(&repo.socket_path) {
            Ok(metadata) if metadata.ino() != previous_inode => return Ok(()),
            Ok(_) => std::thread::sleep(Duration::from_millis(25)),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
            Err(error) => return Err(error.into()),
        }
    }
    bail!("mathmux daemon did not restart within 10 minutes")
}

fn replace_daemon(repo: &Repo, request: &Request) -> Result<UnixStream> {
    let startup_lock = startup_lock(repo)?;
    lock_exclusive(&startup_lock)?;
    if let Ok(stream) = UnixStream::connect(&repo.socket_path) {
        let probe = Request {
            build: request.build.clone(),
            generation: request.generation,
            actor_id: None,
            session_id: None,
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

fn telemetry_identity(key: &str) -> Option<String> {
    std::env::var(key)
        .ok()
        .filter(|v| !v.is_empty() && v.len() <= 128 && !v.chars().any(char::is_control))
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
                actor_id: None,
                session_id: None,
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

    #[test]
    fn show_wait_progress_is_bounded_without_changing_plain_show() {
        let show_wait = Command::Show {
            reference: "s1".into(),
            all: false,
            wait: true,
        };
        let plain_show = Command::Show {
            reference: "s1".into(),
            all: false,
            wait: false,
        };

        assert_eq!(exchange_progress_label(&show_wait), Some("show"));
        assert_eq!(exchange_progress_label(&plain_show), None);
        assert!(!progress_update_due(
            Some("show"),
            Duration::from_secs(9),
            Duration::from_secs(10)
        ));
        assert!(progress_update_due(
            Some("show"),
            Duration::from_secs(10),
            Duration::from_secs(10)
        ));
        assert!(!progress_update_due(
            Some("check"),
            Duration::from_secs(20),
            Duration::from_secs(10)
        ));
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
        let matches = command_line()
            .try_get_matches_from(["mathmux", "dev", "gc", "--dry-run"])
            .unwrap();
        let args = Args::from_arg_matches(&matches).unwrap();
        assert!(matches!(
            args.command,
            TopCommand::Dev {
                command: DevCommand::Gc {
                    dry_run: true,
                    hard: false,
                    confirm: false
                }
            }
        ));
        let matches = command_line()
            .try_get_matches_from(["mathmux", "dev", "gc", "--hard", "--dry-run"])
            .unwrap();
        let args = Args::from_arg_matches(&matches).unwrap();
        assert!(matches!(
            args.command,
            TopCommand::Dev {
                command: DevCommand::Gc {
                    dry_run: true,
                    hard: true,
                    confirm: false
                }
            }
        ));
    }

    #[test]
    fn cancel_accepts_a_check_reference() {
        let matches = command_line()
            .try_get_matches_from(["mathmux", "cancel", "c123"])
            .unwrap();
        let args = Args::from_arg_matches(&matches).unwrap();
        assert!(matches!(
            args.command,
            TopCommand::Cancel { reference } if reference == "c123"
        ));
    }

    #[test]
    fn search_all_is_an_option_not_a_query_term() {
        let matches = command_line()
            .try_get_matches_from(["mathmux", "search", "LinearEquiv.ofFinrankEq", "--all"])
            .unwrap();
        let args = Args::from_arg_matches(&matches).unwrap();
        let TopCommand::Search {
            query,
            max_results,
            all,
        } = args.command
        else {
            panic!("expected search command");
        };
        assert_eq!(query, ["LinearEquiv.ofFinrankEq"]);
        assert_eq!(max_results, None);
        assert!(all);
        let matches = command_line()
            .try_get_matches_from(["mathmux", "search", "target", "--limit", "80"])
            .unwrap();
        let args = Args::from_arg_matches(&matches).unwrap();
        let TopCommand::Search { max_results, .. } = args.command else {
            panic!("expected search command");
        };
        assert_eq!(max_results, Some(80));
        let matches = command_line()
            .try_get_matches_from(["mathmux", "search", "target", "--max-results", "3"])
            .unwrap();
        let args = Args::from_arg_matches(&matches).unwrap();
        let TopCommand::Search {
            max_results, all, ..
        } = args.command
        else {
            panic!("expected search command");
        };
        assert_eq!(max_results, Some(3));
        assert!(!all);
        assert!(
            command_line()
                .try_get_matches_from(["mathmux", "search", "target", "--max-results", "0"])
                .is_err()
        );
    }

    #[test]
    fn search_and_probe_help_expose_only_the_new_api() {
        let mut command = command_line();
        let help = command
            .find_subcommand_mut("search")
            .unwrap()
            .render_long_help()
            .to_string();
        assert!(help.contains("API search-v12"));
        for form in [
            "type:LEAN_TYPE",
            "FILE:LINE",
            "outline|declarations|imports|dependents",
            "PATH /REGEX/",
            "source/compose are labels, not keywords",
            "sREF requires TERMS",
            "Source facets accept a space or FILE.lean:outline shorthand.",
            "--max-results/--limit N (1–200) caps hits and cannot combine with --all",
            "search --all is accepted only",
        ] {
            assert!(help.contains(form), "missing search form {form}");
        }
        assert!(help.contains("--limit"));
        assert!(!help.contains("cREF repair"));
        assert!(!help.contains("name:NAME"));
        assert!(!help.contains("name:A|B|C"));
        let probe_help = command
            .find_subcommand_mut("probe")
            .unwrap()
            .render_long_help()
            .to_string();
        assert!(probe_help.contains("API probe-v17"));
        for contract in [
            "there are no API, LEAN, or other category keywords",
            "NAME [signature|source|outline|apply|fields|constructors|ext|simp|usages|assumptions|evidence|examples]",
            "NAME find TERM",
            "FILE warnings",
            "FILE:LINE [goal]",
            "cREF [goal|types|defeq|rewrite|profile|context]",
            "qREF[#N] [signature|source|outline|find TERM|usages|constructors]",
            "Context is mandatory",
            "Use NAME signature, not",
            "no nearby-line fallback",
        ] {
            assert!(
                probe_help.contains(contract),
                "missing probe contract {contract}"
            );
        }
        assert!(!probe_help.contains("declaration-qREF"));
        assert!(!probe_help.contains("API       NAME"));
        assert!(!probe_help.contains("LEAN      FILE"));
        for removed in ["neighborhood", "|dependencies", "|instances", "|coercions"] {
            assert!(!probe_help.contains(removed));
        }
        assert!(!help.contains("diagnostics, and goals"));

        let mut short_command = command_line();
        let short_search = short_command
            .find_subcommand_mut("search")
            .unwrap()
            .render_help()
            .to_string();
        assert!(!short_search.contains("name:A|B|C"));
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
        assert!(help.contains("search-v12/probe-v17"));
        assert!(help.contains("Edit intended files -> check -> submit"));
        assert!(help.contains("Exact declarations go straight to probe NAME"));
        assert!(help.contains("Search unknown things; probe known API, exact context"));
    }
}
