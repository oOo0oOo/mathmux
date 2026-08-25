use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Request {
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
    pub ok: bool,
    pub summary: String,
}

impl Response {
    pub fn ok(summary: impl Into<String>) -> Self {
        Self {
            ok: true,
            summary: summary.into(),
        }
    }

    pub fn error(summary: impl Into<String>) -> Self {
        Self {
            ok: false,
            summary: summary.into(),
        }
    }
}
