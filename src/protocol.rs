use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Request {
    #[serde(default)]
    pub build: String,
    pub cwd: String,
    pub command: Command,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "verb", rename_all = "snake_case")]
pub enum Command {
    WsCreate { name: String },
    WsList,
    WsDelete { name: String },
    Check { file: Option<String> },
    Sync,
    Submit { message: Option<String> },
    Show { reference: String, all: bool },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Response {
    #[serde(default)]
    pub build: String,
    #[serde(default)]
    pub retry: bool,
    pub ok: bool,
    pub summary: String,
}

impl Response {
    pub fn ok(summary: impl Into<String>) -> Self {
        Self {
            build: crate::util::build_id().to_owned(),
            retry: false,
            ok: true,
            summary: summary.into(),
        }
    }

    pub fn error(summary: impl Into<String>) -> Self {
        Self {
            build: crate::util::build_id().to_owned(),
            retry: false,
            ok: false,
            summary: summary.into(),
        }
    }

    pub fn retry() -> Self {
        Self {
            build: crate::util::build_id().to_owned(),
            retry: true,
            ok: false,
            summary: "daemon build changed".into(),
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
}
