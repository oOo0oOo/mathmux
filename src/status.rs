use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use anyhow::{Result, ensure};

use crate::git::{dirty_paths, head};
use crate::repo::Repo;
use crate::state::{ActivityMetrics, State, Workspace};
use crate::util::{run_checked, run_output};

const HOUR_SECS: i64 = 60 * 60;
const DAY_SECS: i64 = 24 * HOUR_SECS;
const ACTIVE_SECS: i64 = 5 * 60;
const EMPTY_TREE: &str = "4b825dc642cb6eb9a060e54bf8d69288fbee4904";

struct AgentStatus {
    id: u64,
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

pub fn render(repo: &Repo, state: &State) -> Result<String> {
    let now = now_unix_seconds();
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

    let mut output = format!("{project} {}", short_hash(&revision));
    render_agents(&mut output, &agents, now);
    output.push_str(&format!(
        "\ncode {:>7} Lean lines in {} files",
        code.lines, code.files
    ));

    output.push_str("\nmerged progress");
    for (label, seconds) in [("1h", HOUR_SECS), ("24h", DAY_SECS)] {
        let lines = net_lean_lines(&repo.root, now - seconds)?;
        let wall_hours = seconds as f64 / HOUR_SECS as f64;
        let agent_hours = agent_hours(&agents, now - seconds, now);
        output.push_str(&format!(
            "\n{label:>3} {lines:+} lines  {:+.1}/h",
            lines as f64 / wall_hours
        ));
        if agent_hours > 0.0 {
            output.push_str(&format!(
                "  {:+.1}/agent-h ({agent_hours:.1} agent-h)",
                lines as f64 / agent_hours
            ));
        }
    }

    output.push_str("\ntooling");
    for (label, seconds) in [("1h", HOUR_SECS), ("24h", DAY_SECS)] {
        let metrics = state.activity_metrics((now - seconds) * 1000)?;
        output.push_str(&format!("\n{label:>3} "));
        render_tooling(&mut output, &metrics);
    }

    let pending = state.pending_submissions()?;
    if pending.is_empty() {
        output.push_str("\nvalidation idle");
    } else {
        output.push_str("\nvalidation");
        for submission in pending {
            output.push_str(&format!(
                " {}:{}",
                submission.reference, submission.validation_status
            ));
        }
    }
    Ok(output)
}

fn render_agents(output: &mut String, agents: &[AgentStatus], now: i64) {
    let active = agents
        .iter()
        .filter(|agent| agent.state == "active")
        .count();
    let idle = agents.iter().filter(|agent| agent.state == "idle").count();
    output.push_str(&format!(
        "\nagents {} ({active} active, {idle} idle)",
        agents.len()
    ));
    for agent in agents {
        output.push_str(&format!(
            "\n{:>3} {:<10} {:<16} {:<7} last {}",
            agent.id,
            agent.workspace,
            agent.model,
            agent.state,
            format_age(now.saturating_sub(agent.last_active))
        ));
        if agent.dirty > 0 {
            output.push_str(&format!(" dirty:{}", agent.dirty));
        }
    }
}

fn render_tooling(output: &mut String, metrics: &ActivityMetrics) {
    let passed = metrics.checks.saturating_sub(metrics.failed_checks);
    output.push_str(&format!(
        "checks {} ({passed} ok/{} err) avg {}  builds {} avg {}  submits {}",
        metrics.checks,
        metrics.failed_checks,
        format_average(metrics.average_check_ms),
        metrics.builds,
        format_average(metrics.average_build_ms),
        metrics.submissions
    ));
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
        .filter_map(|entry| {
            let id = entry.path().file_stem()?.to_str()?.parse::<u64>().ok()?;
            let values = read_agent_state(&entry.path())?;
            if !agent_is_live(values.get("scope").map(String::as_str)) {
                return None;
            }
            let cwd = Path::new(values.get("cwd")?);
            let workspace = workspaces
                .iter()
                .find(|workspace| cwd.starts_with(&workspace.path))?;
            let started_at = parse_epoch(values.get("started_at"));
            let mut last_active = started_at;
            last_active = last_active.max(parse_epoch(values.get("last_user_send_at")));
            last_active = last_active.max(
                activity
                    .get(&workspace.reference)
                    .copied()
                    .unwrap_or_default()
                    / 1000,
            );
            if let Some(path) = values.get("session_jsonl")
                && !path.is_empty()
            {
                last_active = last_active.max(modified_at(Path::new(path)));
            }
            let dirty_paths = dirty_paths(&workspace.path).unwrap_or_default();
            for path in &dirty_paths {
                last_active = last_active.max(modified_at(&workspace.path.join(path)));
            }
            let recorded = values.get("state").map(String::as_str).unwrap_or("working");
            let agent_state = if recorded != "working" {
                recorded.to_owned()
            } else if now.saturating_sub(last_active) <= ACTIVE_SECS {
                "active".into()
            } else {
                "idle".into()
            };
            Some(AgentStatus {
                id,
                workspace: workspace.name.clone(),
                model: values
                    .get("model")
                    .cloned()
                    .unwrap_or_else(|| "agent".into()),
                state: agent_state,
                started_at,
                last_active,
                dirty: dirty_paths.len(),
            })
        })
        .collect::<Vec<_>>();
    agents.sort_by_key(|agent| agent.id);
    agents
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
    let files = output
        .stdout
        .split(|byte| *byte == 0)
        .filter(|path| !path.is_empty())
        .collect::<Vec<_>>();
    let mut lines = 0;
    for path in &files {
        lines += physical_lines(&fs::read(
            root.join(String::from_utf8_lossy(path).as_ref()),
        )?) as u64;
    }
    Ok(CodeMetrics {
        files: files.len(),
        lines,
    })
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

fn physical_lines(source: &[u8]) -> usize {
    source.iter().filter(|byte| **byte == b'\n').count()
        + usize::from(!source.is_empty() && !source.ends_with(b"\n"))
}

fn agent_hours(agents: &[AgentStatus], since: i64, now: i64) -> f64 {
    agents
        .iter()
        .map(|agent| now.saturating_sub(agent.started_at.max(since)) as f64 / HOUR_SECS as f64)
        .sum()
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

fn now_unix_seconds() -> i64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs() as i64
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

fn short_hash(hash: &str) -> &str {
    hash.get(..8).unwrap_or(hash)
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
            workspace: "demo".into(),
            model: "agent".into(),
            state: "active".into(),
            started_at,
            last_active: 0,
            dirty: 0,
        };
        assert_eq!(agent_hours(&[agent(0), agent(5_400)], 3_600, 7_200), 1.5);
    }
}
