use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Request {
    #[serde(default)]
    pub build: String,
    #[serde(default)]
    pub generation: u64,
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
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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

        let request: Request =
            serde_json::from_str(r#"{"cwd":"/project","command":{"verb":"status"}}"#).unwrap();
        let Command::Status { formalization_yaml } = request.command else {
            panic!("expected status command");
        };
        assert!(!formalization_yaml);

        let request = Request {
            build: "test".into(),
            generation: 1,
            cwd: "/project".into(),
            command: Command::Search {
                query: "name:demo".into(),
                max_results: Some(12),
                all: false,
            },
        };
        let encoded = serde_json::to_string(&request).unwrap();
        let decoded: Request = serde_json::from_str(&encoded).unwrap();
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
        assert!(!Command::Submit { message: None }.transport_retry_safe());
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
