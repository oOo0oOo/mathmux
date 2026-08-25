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
    },
    WsList,
    WsDelete {
        name: String,
    },
    Check {
        file: Option<String>,
        #[serde(default)]
        profile: bool,
    },
    Search {
        query: String,
        #[serde(default)]
        all: bool,
    },
    Status,
    Sync,
    Submit {
        message: Option<String>,
    },
    Show {
        reference: String,
        all: bool,
    },
}

impl Command {
    pub fn verb(&self) -> &'static str {
        match self {
            Self::WsCreate { .. } => "ws_create",
            Self::WsList => "ws_list",
            Self::WsDelete { .. } => "ws_delete",
            Self::Check { .. } => "check",
            Self::Search { .. } => "search",
            Self::Status => "status",
            Self::Sync => "sync",
            Self::Submit { .. } => "submit",
            Self::Show { .. } => "show",
        }
    }

    pub fn transport_retry_safe(&self) -> bool {
        matches!(
            self,
            Self::WsList
                | Self::Status
                | Self::Check { .. }
                | Self::Search { .. }
                | Self::Sync
                | Self::Show { .. }
        )
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Response {
    #[serde(default)]
    pub build: String,
    #[serde(default)]
    pub retry: bool,
    pub ok: bool,
    pub summary: String,
    #[serde(default)]
    pub daemon_ms: u64,
    #[serde(default)]
    pub rss_kib: Option<u64>,
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
    fn legacy_responses_do_not_request_a_retry() {
        let response: Response =
            serde_json::from_str(r#"{"build":"old","ok":true,"summary":"ok"}"#).unwrap();
        assert!(!response.retry);
        assert!(Response::retry().retry);
    }

    #[test]
    fn legacy_requests_have_no_build_generation() {
        let request: Request = serde_json::from_str(
            r#"{"build":"old","cwd":"/project","command":{"verb":"ws_list"}}"#,
        )
        .unwrap();
        assert_eq!(request.generation, 0);
    }

    #[test]
    fn legacy_search_requests_are_compact() {
        let request: Request = serde_json::from_str(
            r#"{"cwd":"/project","command":{"verb":"search","query":"demo"}}"#,
        )
        .unwrap();
        let Command::Search { all, .. } = request.command else {
            panic!("expected search command");
        };
        assert!(!all);
    }

    #[test]
    fn only_idempotent_commands_are_transport_retry_safe() {
        assert!(Command::Sync.transport_retry_safe());
        assert!(Command::Status.transport_retry_safe());
        assert!(
            Command::Check {
                file: None,
                profile: false
            }
            .transport_retry_safe()
        );
        assert!(!Command::Submit { message: None }.transport_retry_safe());
        assert!(
            !Command::WsCreate {
                name: "agent".into()
            }
            .transport_retry_safe()
        );
    }
}
