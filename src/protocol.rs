use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Request {
    #[serde(default)]
    pub build: String,
    #[serde(default)]
    pub generation: u64,
    #[serde(default)]
    pub actor_id: Option<String>,
    #[serde(default)]
    pub session_id: Option<String>,
    pub cwd: String,
    pub command: Command,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "verb", rename_all = "snake_case")]
pub enum Command {
    WsCreate {
        name: String,
        #[serde(default)]
        model: Option<String>,
    },
    WsList,
    WsDelete {
        name: String,
        #[serde(default)]
        force: bool,
    },
    Check {
        file: Option<String>,
        #[serde(default)]
        profile: bool,
    },
    Cancel {
        reference: String,
    },
    Search {
        query: String,
        #[serde(default)]
        max_results: Option<usize>,
        #[serde(default)]
        all: bool,
    },
    Probe {
        query: String,
    },
    Status {
        #[serde(default)]
        formalization_yaml: bool,
    },
    Sync {
        #[serde(default)]
        push: bool,
    },
    Submit {
        message: Option<String>,
        #[serde(default)]
        files: Vec<String>,
    },
    Show {
        reference: String,
        all: bool,
        #[serde(default)]
        wait: bool,
    },
    Restart,
}

impl Command {
    pub fn verb(&self) -> &'static str {
        match self {
            Self::WsCreate { .. } => "ws_create",
            Self::WsList => "ws_list",
            Self::WsDelete { .. } => "ws_delete",
            Self::Check { .. } => "check",
            Self::Cancel { .. } => "cancel",
            Self::Search { .. } => "search",
            Self::Probe { .. } => "probe",
            Self::Status { .. } => "status",
            Self::Sync { .. } => "sync",
            Self::Submit { .. } => "submit",
            Self::Show { .. } => "show",
            Self::Restart => "restart",
        }
    }

    pub fn transport_retry_safe(&self) -> bool {
        matches!(
            self,
            Self::WsList
                | Self::Status { .. }
                | Self::Check { .. }
                | Self::Search { .. }
                | Self::Probe { .. }
                | Self::Sync { .. }
                | Self::Show { .. }
                | Self::Restart
        )
    }
}

/// Machine outcomes are independent of human presentation. Older peers omit them.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SearchOutcome {
    pub resolution: String,
    pub result_count: usize,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub failure_class: Option<String>,
}

#[derive(Debug)]
pub(crate) enum DiscoveryFailure {
    InvalidRequest,
    UnavailableContext,
    Infrastructure,
}
impl std::fmt::Display for DiscoveryFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::InvalidRequest => "invalid discovery request",
            Self::UnavailableContext => "unavailable probe context",
            Self::Infrastructure => "discovery infrastructure failure",
        })
    }
}
impl std::error::Error for DiscoveryFailure {}

impl SearchOutcome {
    pub fn from_run(run: &crate::state::SearchRun) -> Self {
        let resolution =
            if run.hits.is_empty() && run.note.as_deref().is_some_and(|n| n.contains("index warming")) {
                "index_warming"
            } else if run.inference.contains("recovery") || run.inference.ends_with("-partial") {
                "partial_result"
            } else if run.inference.contains("missing") || run.inference.contains("miss") {
                if run.hits.is_empty() {
                    "no_result"
                } else {
                    "near_suggestions"
                }
            } else if run.hits.is_empty() {
                "no_result"
            } else if matches!(
                run.inference.as_str(),
                "exact" | "exact-batch" | "signature"
            ) {
                "exact_hit"
            } else if run.inference.starts_with("probe") {
                "inspection"
            } else {
                "ranked_results"
            };
        Self {
            resolution: resolution.into(),
            result_count: run.hits.len(),
            failure_class: None,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Response {
    #[serde(default)]
    pub build: String,
    #[serde(default)]
    pub generation: u64,
    #[serde(default)]
    pub retry: bool,
    pub ok: bool,
    pub summary: String,
    #[serde(default)]
    pub daemon_ms: u64,
    #[serde(default)]
    pub rss_kib: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub search_outcome: Option<SearchOutcome>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Progress {
    pub progress: String,
}

impl Response {
    pub fn ok(summary: impl Into<String>) -> Self {
        Self::new(true, false, summary)
    }

    pub fn error(summary: impl Into<String>) -> Self {
        Self::new(false, false, summary)
    }

    pub fn retry() -> Self {
        Self::new(false, true, "daemon build changed")
    }

    fn new(ok: bool, retry: bool, summary: impl Into<String>) -> Self {
        Self {
            build: crate::util::build_id().to_owned(),
            generation: crate::util::build_generation(),
            retry,
            ok,
            summary: summary.into(),
            daemon_ms: 0,
            rss_kib: None,
            search_outcome: None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn structured_search_outcomes_do_not_count_empty_or_partial_as_exact() {
        let mut run = crate::state::SearchRun {
            reference: "q1".into(),
            workspace_ref: "w1".into(),
            query: "X".into(),
            inference: "exact".into(),
            hits: vec![],
            note: None,
            duration_ms: 0,
            created_at: 0,
        };
        assert_eq!(SearchOutcome::from_run(&run).resolution, "no_result");
        run.note = Some("type index warming".into());
        assert_eq!(SearchOutcome::from_run(&run).resolution, "index_warming");
        run.note = None;
        run.inference = "source-regex-partial".into();
        assert_eq!(SearchOutcome::from_run(&run).resolution, "partial_result");
        let old: Response = serde_json::from_str(r#"{"ok":true,"summary":"old"}"#).unwrap();
        assert!(old.search_outcome.is_none());
    }

    #[test]
    fn protocol_round_trips_public_queries() {
        let response: Response =
            serde_json::from_str(r#"{"build":"old","ok":true,"summary":"ok"}"#).unwrap();
        assert!(!response.retry);
        assert_eq!(response.generation, 0);
        assert!(Response::retry().retry);

        let request: Request = serde_json::from_str(
            r#"{"build":"old","cwd":"/project","command":{"verb":"ws_list"}}"#,
        )
        .unwrap();
        assert_eq!(request.generation, 0);
        assert!(request.actor_id.is_none() && request.session_id.is_none());

        let request: Request =
            serde_json::from_str(r#"{"cwd":"/project","command":{"verb":"status"}}"#).unwrap();
        let Command::Status { formalization_yaml } = request.command else {
            panic!("expected status command");
        };
        assert!(!formalization_yaml);

        let request = Request {
            build: "test".into(),
            generation: 1,
            actor_id: Some("actor-125".into()),
            session_id: Some("session-a".into()),
            cwd: "/project".into(),
            command: Command::Search {
                query: "name:demo".into(),
                max_results: Some(12),
                all: false,
            },
        };
        let encoded = serde_json::to_string(&request).unwrap();
        let decoded: Request = serde_json::from_str(&encoded).unwrap();
        assert_eq!(decoded.actor_id.as_deref(), Some("actor-125"));
        assert_eq!(decoded.session_id.as_deref(), Some("session-a"));
        let Command::Search {
            all, max_results, ..
        } = decoded.command
        else {
            panic!("expected search command");
        };
        assert!(!all);
        assert_eq!(max_results, Some(12));

        let request: Request = serde_json::from_str(
            r#"{"cwd":"/project","command":{"verb":"cancel","reference":"c123"}}"#,
        )
        .unwrap();
        assert!(matches!(
            request.command,
            Command::Cancel { reference } if reference == "c123"
        ));

        let request: Request =
            serde_json::from_str(r#"{"cwd":"/project","command":{"verb":"sync"}}"#).unwrap();
        let Command::Sync { push } = request.command else {
            panic!("expected sync command");
        };
        assert!(!push);

        let request: Request = serde_json::from_str(
            r#"{"cwd":"/project","command":{"verb":"show","reference":"c1","all":false}}"#,
        )
        .unwrap();
        let Command::Show { wait, .. } = request.command else {
            panic!("expected show command");
        };
        assert!(!wait);

        let request: Request =
            serde_json::from_str(r#"{"cwd":"/project","command":{"verb":"restart"}}"#).unwrap();
        assert!(matches!(request.command, Command::Restart));
    }

    #[test]
    fn only_idempotent_commands_are_transport_retry_safe() {
        assert!(Command::Sync { push: false }.transport_retry_safe());
        assert!(
            Command::Status {
                formalization_yaml: false
            }
            .transport_retry_safe()
        );
        assert!(
            Command::Check {
                file: None,
                profile: false
            }
            .transport_retry_safe()
        );
        assert!(
            Command::Show {
                reference: "c1".into(),
                all: false,
                wait: true,
            }
            .transport_retry_safe()
        );
        assert!(
            Command::Probe {
                query: "Demo".into()
            }
            .transport_retry_safe()
        );
        assert!(Command::Restart.transport_retry_safe());
        assert!(
            !Command::Submit {
                message: None,
                files: Vec::new(),
            }
            .transport_retry_safe()
        );
        assert!(
            !Command::Cancel {
                reference: "c1".into()
            }
            .transport_retry_safe()
        );
        assert!(
            !Command::WsCreate {
                name: "agent".into(),
                model: None,
            }
            .transport_retry_safe()
        );
    }
}
