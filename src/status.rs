use std::collections::HashMap;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::UNIX_EPOCH;

use anyhow::{Result, ensure};

use crate::git::{dirty_paths, head};
use crate::issue::{ContextEvent, TelemetryStore, development_enabled};
use crate::repo::Repo;
use crate::state::{ActivityMetrics, State, SubmissionInterval, Workspace};
use crate::util::{now_unix_ms, run_checked, run_output, short_hash};

const HOUR_SECS: i64 = 60 * 60;
const DAY_SECS: i64 = 24 * HOUR_SECS;
const ACTIVE_SECS: i64 = 5 * 60;
const EMPTY_TREE: &str = "4b825dc642cb6eb9a060e54bf8d69288fbee4904";

struct AgentStatus {
    id: u64,
    workspace_ref: String,
    workspace: String,
    model: String,
    state: String,
    started_at: i64,
    last_active: i64,
    dirty: usize,
}

struct CodeMetrics {
    files: usize,
    lines: u64,
}

#[derive(Default)]
struct SubmissionContext {
    created_at: i64,
    lines: u64,
    calls: u64,
    output_bytes: u64,
}

pub fn render(repo: &Repo, state: &State) -> Result<String> {
    let now = now_unix_ms() / 1000;
    let project = repo
        .root
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("project");
    let revision = head(&repo.root)?;
    let workspaces = state.list_workspaces()?;
    let activity = state
        .workspace_activity()?
        .into_iter()
        .collect::<HashMap<_, _>>();
    let agents = project_agents(&workspaces, &activity, now);
    let code = current_code(&repo.root)?;
    let context = submission_context(repo, state, (now - DAY_SECS) * 1000);
    let activity_events = development_enabled(repo)
        .then(|| {
            TelemetryStore::global().and_then(|store| {
                store.context_events(repo, (now - DAY_SECS - ACTIVE_SECS) * 1000)
            })
        })
        .transpose()
        .ok()
        .flatten();

    let mut output = format!("{project} {}", short_hash(&revision));
    render_agents(&mut output, &agents, now)?;
    write!(
        output,
        "\ncode {:>7} Lean lines in {} files",
        code.lines, code.files
    )?;

    output.push_str("\nmerged progress");
    for (label, seconds) in [("1h", HOUR_SECS), ("24h", DAY_SECS)] {
        let lines = net_lean_lines(&repo.root, now - seconds)?;
        let wall_hours = seconds as f64 / HOUR_SECS as f64;
        let agent_hours = agent_hours(
            &agents,
            activity_events.as_deref(),
            now - seconds,
            now,
        );
        write!(
            output,
            "\n{label:>3} {lines:+} lines  {:+.1}/h",
            lines as f64 / wall_hours
        )?;
        if agent_hours > 0.0 {
            write!(
                output,
                "  {:+.1}/agent-h ({agent_hours:.1} agent-h)",
                lines as f64 / agent_hours
            )?;
        }
        if let Some(metrics) = context_per_loc(&context, (now - seconds) * 1000) {
            write!(
                output,
                "  context/loc {:.2} mux calls + {} output",
                metrics.calls as f64 / metrics.lines as f64,
                format_bytes(metrics.output_bytes as f64 / metrics.lines as f64)
            )?;
        }
    }

    output.push_str("\ntooling");
    for (label, seconds) in [("1h", HOUR_SECS), ("24h", DAY_SECS)] {
        let metrics = state.activity_metrics((now - seconds) * 1000)?;
        output.push_str(&format!("\n{label:>3} "));
        render_tooling(&mut output, &metrics)?;
    }

    let pending = state.pending_submissions()?;
    if pending.is_empty() {
        output.push_str("\nvalidation idle");
    } else {
        output.push_str("\nvalidation");
        for submission in pending {
            write!(
                output,
                " {}:{}",
                submission.reference, submission.validation_status
            )?;
        }
    }
    Ok(output)
}

fn render_agents(output: &mut String, agents: &[AgentStatus], now: i64) -> std::fmt::Result {
    let active = agents
        .iter()
        .filter(|agent| agent.state == "active")
        .count();
    let idle = agents.iter().filter(|agent| agent.state == "idle").count();
    write!(
        output,
        "\nagents {} ({active} active, {idle} idle)",
        agents.len()
    )?;
    for agent in agents {
        write!(
            output,
            "\n{:>3} {:<10} {:<16} {:<7} last {}",
            agent.id,
            agent.workspace,
            agent.model,
            agent.state,
            format_age(now.saturating_sub(agent.last_active))
        )?;
        if agent.dirty > 0 {
            write!(output, " dirty:{}", agent.dirty)?;
        }
    }
    Ok(())
}

fn render_tooling(output: &mut String, metrics: &ActivityMetrics) -> std::fmt::Result {
    let passed = metrics.checks.saturating_sub(metrics.failed_checks);
    write!(
        output,
        "checks {} ({passed} ok/{} err) avg {}  builds {} avg {}  submits {}",
        metrics.checks,
        metrics.failed_checks,
        format_average(metrics.average_check_ms),
        metrics.builds,
        format_average(metrics.average_build_ms),
        metrics.submissions
    )
}

fn project_agents(
    workspaces: &[Workspace],
    activity: &HashMap<String, i64>,
    now: i64,
) -> Vec<AgentStatus> {
    let Some(state_dir) = agent_state_dir() else {
        return Vec::new();
    };
    let Ok(entries) = fs::read_dir(state_dir) else {
        return Vec::new();
    };
    let mut agents = entries
        .filter_map(Result::ok)
        .filter_map(|entry| agent_status(&entry.path(), workspaces, activity, now))
        .collect::<Vec<_>>();
    agents.sort_by_key(|agent| agent.id);
    agents
}

fn agent_status(
    path: &Path,
    workspaces: &[Workspace],
    activity: &HashMap<String, i64>,
    now: i64,
) -> Option<AgentStatus> {
    let id = path.file_stem()?.to_str()?.parse::<u64>().ok()?;
    let values = read_agent_state(path)?;
    if !agent_is_live(values.get("scope").map(String::as_str)) {
        return None;
    }
    let cwd = Path::new(values.get("cwd")?);
    let workspace = workspaces
        .iter()
        .find(|workspace| cwd.starts_with(&workspace.path))?;
    let started_at = parse_epoch(values.get("started_at"));
    let paths = dirty_paths(&workspace.path).unwrap_or_default();
    let last_active = agent_last_active(&values, workspace, activity, &paths, started_at);
    let recorded = values.get("state").map(String::as_str).unwrap_or("working");
    let state = match recorded {
        "working" if now.saturating_sub(last_active) <= ACTIVE_SECS => "active".into(),
        "working" => "idle".into(),
        state => state.to_owned(),
    };
    Some(AgentStatus {
        id,
        workspace_ref: workspace.reference.clone(),
        workspace: workspace.name.clone(),
        model: values
            .get("model")
            .cloned()
            .unwrap_or_else(|| "agent".into()),
        state,
        started_at,
        last_active,
        dirty: paths.len(),
    })
}

fn agent_last_active(
    values: &HashMap<String, String>,
    workspace: &Workspace,
    activity: &HashMap<String, i64>,
    dirty: &[PathBuf],
    started_at: i64,
) -> i64 {
    let session_activity = values
        .get("session_jsonl")
        .filter(|path| !path.is_empty())
        .map_or(0, |path| modified_at(Path::new(path)));
    let workspace_activity = activity
        .get(&workspace.reference)
        .copied()
        .unwrap_or_default()
        / 1000;
    let file_activity = dirty
        .iter()
        .map(|path| modified_at(&workspace.path.join(path)))
        .max()
        .unwrap_or_default();
    [
        started_at,
        parse_epoch(values.get("last_user_send_at")),
        session_activity,
        workspace_activity,
        file_activity,
    ]
    .into_iter()
    .max()
    .unwrap_or_default()
}

fn agent_is_live(scope: Option<&str>) -> bool {
    let Some(scope) = scope.filter(|scope| !scope.is_empty()) else {
        return false;
    };
    run_output(
        "systemctl",
        ["--user", "is-active", "--quiet", scope],
        Path::new("."),
    )
    .is_ok_and(|output| output.status.success())
}

fn agent_state_dir() -> Option<PathBuf> {
    if let Some(path) = std::env::var_os("AGENT_STATE_DIR") {
        return Some(path.into());
    }
    if let Some(path) = std::env::var_os("XDG_DATA_HOME") {
        return Some(PathBuf::from(path).join("agent-state"));
    }
    std::env::var_os("HOME").map(|path| PathBuf::from(path).join(".local/share/agent-state"))
}

fn read_agent_state(path: &Path) -> Option<HashMap<String, String>> {
    let source = fs::read_to_string(path).ok()?;
    Some(
        source
            .lines()
            .filter_map(|line| line.split_once('='))
            .map(|(key, value)| (key.to_owned(), value.to_owned()))
            .collect(),
    )
}

fn current_code(root: &Path) -> Result<CodeMetrics> {
    let output = run_output("git", ["ls-files", "-z", "--", "*.lean"], root)?;
    ensure!(output.status.success(), "cannot list tracked Lean files");
    let mut files = 0;
    let mut lines = 0;
    for path in output
        .stdout
        .split(|byte| *byte == 0)
        .filter(|path| !path.is_empty())
    {
        files += 1;
        lines += physical_lines(&fs::read(
            root.join(String::from_utf8_lossy(path).as_ref()),
        )?) as u64;
    }
    Ok(CodeMetrics { files, lines })
}

fn net_lean_lines(root: &Path, since: i64) -> Result<i64> {
    let cutoff = format!("@{since}");
    let base = run_checked(
        "git",
        ["rev-list", "-1", &format!("--before={cutoff}"), "HEAD"],
        root,
    )?;
    let base = if base.is_empty() { EMPTY_TREE } else { &base };
    let numstat = run_checked(
        "git",
        ["diff", "--numstat", base, "HEAD", "--", "*.lean"],
        root,
    )?;
    Ok(numstat.lines().fold(0, |total, line| {
        let mut fields = line.split('\t');
        let added = fields.next().and_then(|value| value.parse::<i64>().ok());
        let deleted = fields.next().and_then(|value| value.parse::<i64>().ok());
        match (added, deleted) {
            (Some(added), Some(deleted)) => total + added - deleted,
            _ => total,
        }
    }))
}

fn submission_context(repo: &Repo, state: &State, since: i64) -> Vec<SubmissionContext> {
    if !development_enabled(repo) {
        return Vec::new();
    }
    let Ok(submissions) = state.submission_intervals(since) else {
        return Vec::new();
    };
    let Some(earliest) = submissions
        .iter()
        .map(|submission| submission.previous_created_at)
        .min()
    else {
        return Vec::new();
    };
    let Ok(events) =
        TelemetryStore::global().and_then(|store| store.context_events(repo, earliest))
    else {
        return Vec::new();
    };
    let Ok(lines) = submitted_lean_lines(&repo.root, &submissions) else {
        return Vec::new();
    };
    submissions
        .iter()
        .map(|submission| {
            let start = event_time(&events, submission.previous_reference.as_deref())
                .unwrap_or(submission.previous_created_at);
            let end =
                event_time(&events, Some(&submission.reference)).unwrap_or(submission.created_at);
            let relevant = events.iter().filter(|event| {
                event.workspace == submission.workspace_ref
                    && event.created_at > start
                    && event.created_at <= end
            });
            let (calls, output_bytes) = relevant.fold((0_u64, 0_u64), |total, event| {
                (total.0 + 1, total.1 + event.response_bytes)
            });
            SubmissionContext {
                created_at: submission.created_at,
                lines: lines
                    .get(&submission.workspace_commit)
                    .copied()
                    .unwrap_or_default(),
                calls,
                output_bytes,
            }
        })
        .collect()
}

fn event_time(events: &[ContextEvent], reference: Option<&str>) -> Option<i64> {
    let reference = reference?;
    events
        .iter()
        .find(|event| event.reference.as_deref() == Some(reference))
        .map(|event| event.created_at)
}

fn submitted_lean_lines(
    root: &Path,
    submissions: &[SubmissionInterval],
) -> Result<HashMap<String, u64>> {
    let mut arguments = vec![
        "show".to_owned(),
        "--format=@@%H".to_owned(),
        "--numstat".to_owned(),
        "--no-renames".to_owned(),
    ];
    arguments.extend(
        submissions
            .iter()
            .map(|submission| submission.workspace_commit.clone()),
    );
    arguments.extend(["--".to_owned(), "*.lean".to_owned()]);
    let output = run_checked("git", arguments, root)?;
    let mut result = HashMap::new();
    let mut commit = None;
    for line in output.lines() {
        if let Some(hash) = line.strip_prefix("@@") {
            commit = Some(hash.to_owned());
            result.entry(hash.to_owned()).or_insert(0);
            continue;
        }
        let Some(hash) = &commit else {
            continue;
        };
        let Some(added) = line
            .split('\t')
            .next()
            .and_then(|value| value.parse::<u64>().ok())
        else {
            continue;
        };
        *result.entry(hash.clone()).or_default() += added;
    }
    Ok(result)
}

fn context_per_loc(context: &[SubmissionContext], since: i64) -> Option<SubmissionContext> {
    let metrics = context
        .iter()
        .filter(|metrics| metrics.created_at >= since)
        .fold(SubmissionContext::default(), |total, metrics| {
            SubmissionContext {
                created_at: 0,
                lines: total.lines + metrics.lines,
                calls: total.calls + metrics.calls,
                output_bytes: total.output_bytes + metrics.output_bytes,
            }
        });
    (metrics.lines > 0).then_some(metrics)
}

fn format_bytes(bytes: f64) -> String {
    if bytes < 1024.0 {
        format!("{bytes:.0}B")
    } else {
        format!("{:.1}KiB", bytes / 1024.0)
    }
}

fn physical_lines(source: &[u8]) -> usize {
    source.iter().filter(|byte| **byte == b'\n').count()
        + usize::from(!source.is_empty() && !source.ends_with(b"\n"))
}

fn agent_hours(
    agents: &[AgentStatus],
    events: Option<&[ContextEvent]>,
    since: i64,
    now: i64,
) -> f64 {
    let Some(events) = events else {
        return agents
            .iter()
            .map(|agent| now.saturating_sub(agent.started_at.max(since)) as f64)
            .sum::<f64>()
            / HOUR_SECS as f64;
    };
    let active_seconds = agents.iter().fold(0_i64, |total, agent| {
        let mut intervals = events
            .iter()
            .filter(|event| event.workspace == agent.workspace_ref)
            .map(|event| {
                let completed = event.created_at / 1000;
                let duration = event.client_ms.div_ceil(1000) as i64;
                (completed.saturating_sub(duration), completed + ACTIVE_SECS)
            })
            .filter(|(_, end)| *end >= agent.started_at)
            .collect::<Vec<_>>();
        intervals.extend([
            (agent.started_at, agent.started_at + ACTIVE_SECS),
            (agent.last_active, agent.last_active + ACTIVE_SECS),
        ]);
        intervals.sort_unstable();
        let intervals = intervals.into_iter().filter_map(|(start, end)| {
            let start = start.max(agent.started_at).max(since);
            let end = end.min(now);
            (start < end).then_some((start, end))
        });
        let (seconds, _) =
            intervals.fold((0_i64, None), |(seconds, end), (start, next_end)| {
                match end {
                    Some(end) if start <= end => (
                        seconds + next_end.saturating_sub(end),
                        Some(next_end.max(end)),
                    ),
                    _ => (seconds + next_end.saturating_sub(start), Some(next_end)),
                }
            });
        total + seconds
    });
    active_seconds as f64 / HOUR_SECS as f64
}

fn parse_epoch(value: Option<&String>) -> i64 {
    value
        .and_then(|value| value.parse().ok())
        .unwrap_or_default()
}

fn modified_at(path: &Path) -> i64 {
    fs::metadata(path)
        .and_then(|metadata| metadata.modified())
        .ok()
        .and_then(|time| time.duration_since(UNIX_EPOCH).ok())
        .map(|duration| duration.as_secs() as i64)
        .unwrap_or_default()
}

fn format_age(seconds: i64) -> String {
    match seconds.max(0) {
        0..=59 => format!("{}s", seconds.max(0)),
        60..=3599 => format!("{}m", seconds / 60),
        3600..=86_399 => format!("{}h", seconds / 3600),
        _ => format!("{}d", seconds / 86_400),
    }
}

fn format_average(milliseconds: Option<f64>) -> String {
    match milliseconds {
        None => "-".into(),
        Some(milliseconds) if milliseconds < 1000.0 => format!("{milliseconds:.0}ms"),
        Some(milliseconds) => format!("{:.1}s", milliseconds / 1000.0),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counts_physical_lines_with_or_without_a_final_newline() {
        assert_eq!(physical_lines(b""), 0);
        assert_eq!(physical_lines(b"one\ntwo\n"), 2);
        assert_eq!(physical_lines(b"one\ntwo"), 2);
    }

    #[test]
    fn agent_hours_only_count_the_window_overlap() {
        let agent = |started_at| AgentStatus {
            id: 1,
            workspace_ref: "w1".into(),
            workspace: "demo".into(),
            model: "agent".into(),
            state: "active".into(),
            started_at,
            last_active: 0,
            dirty: 0,
        };
        assert_eq!(
            agent_hours(&[agent(0), agent(5_400)], None, 3_600, 7_200),
            1.5
        );
    }

    #[test]
    fn agent_hours_merge_recent_activity_intervals() {
        let agent = AgentStatus {
            id: 1,
            workspace_ref: "w1".into(),
            workspace: "demo".into(),
            model: "agent".into(),
            state: "idle".into(),
            started_at: 3_600,
            last_active: 4_800,
            dirty: 0,
        };
        let event = |created_at| ContextEvent {
            created_at,
            client_ms: 0,
            workspace: "w1".into(),
            reference: None,
            response_bytes: 0,
        };
        let events = [event(3_600_000), event(3_780_000), event(4_200_000)];
        assert_eq!(agent_hours(&[agent], Some(&events), 3_600, 7_200), 0.3);
    }
}
