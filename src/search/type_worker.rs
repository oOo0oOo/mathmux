use super::*;
use crate::lean_service::LeanServiceProcess;

pub(super) enum TypeSearchState {
    Empty,
    Starting(std::sync::mpsc::Receiver<std::result::Result<TypeSearchWorker, String>>),
    Running(TypeSearchWorker),
    Unavailable,
}

pub(super) struct TypeSearchWorker {
    process: LeanServiceProcess,
    version: u64,
    pub(super) last_used: Instant,
    pub(super) startup_detail: String,
    cache: HashMap<(String, String), TypeSearchResult>,
}

#[derive(Clone, Default)]
pub(super) struct TypeSearchResult {
    pub(super) hits: Vec<TypeSearchHit>,
    pub(super) count: usize,
    pub(super) detail: String,
    pub(super) suggestions: Vec<String>,
    pub(super) error: Option<String>,
}

#[derive(Clone, Debug, Deserialize)]
pub(super) struct TypeSearchHit {
    pub(super) name: String,
    #[serde(rename = "type")]
    pub(super) signature: String,
    pub(super) module: Option<String>,
    pub(super) doc: Option<String>,
}

#[derive(Serialize)]
struct TypeSearchRequest<'a> {
    operation: &'static str,
    source: &'static str,
    file_name: &'static str,
    version: u64,
    line: u64,
    column: u64,
    input: &'a str,
    names: &'a [String],
}

#[derive(Deserialize)]
pub(super) struct TypeSearchResponse {
    pub(super) ok: bool,
    pub(super) detail: String,
    pub(super) count: usize,
    pub(super) hits: Vec<TypeSearchHit>,
    #[serde(default)]
    pub(super) anchors: Vec<String>,
    #[serde(default)]
    pub(super) names: Vec<String>,
    version: u64,
}

impl TypeSearchWorker {
    pub(super) fn start(repo: &Repo, workspace: &Path) -> Result<Self> {
        let arguments = vec!["type-search".to_owned(), "Mathlib".to_owned()];
        let mut process = LeanServiceProcess::start(repo, workspace, &arguments)
            .context("cannot start type search service")?;
        let ready = process
            .read_ready(Duration::from_secs(60))
            .context("type search service did not become ready")?;
        ensure!(
            ready.get("ok").and_then(Value::as_bool) == Some(true)
                && ready.get("detail").and_then(Value::as_str) == Some("ready"),
            "unexpected type search startup response: {}",
            clean_line(&ready.to_string())
        );
        let startup_detail = ready
            .get("profile")
            .and_then(Value::as_array)
            .map(|entries| {
                entries
                    .iter()
                    .filter_map(|entry| {
                        Some(format!(
                            "{}={}ms",
                            entry.get("kind")?.as_str()?,
                            entry.get("duration_ms")?.as_f64()? as u64
                        ))
                    })
                    .collect::<Vec<_>>()
                    .join(" ")
            })
            .filter(|detail| !detail.is_empty())
            .unwrap_or_else(|| "type search ready".into());
        Ok(Self {
            process,
            version: 0,
            last_used: Instant::now(),
            startup_detail,
            cache: HashMap::new(),
        })
    }

    pub(super) fn query(
        &mut self,
        query: &str,
        candidates: &[String],
        suggestions: Vec<String>,
    ) -> Result<TypeSearchResult> {
        self.last_used = Instant::now();
        let query = query.lines().collect::<Vec<_>>().join(" ");
        let cache_key = (query.clone(), hash_bytes(candidates.join("\0").as_bytes()));
        if let Some(result) = self.cache.get(&cache_key) {
            return Ok(result.clone());
        }
        let value = self.request_value("type_verify", &query, candidates)?;
        let result = if value.ok {
            TypeSearchResult {
                hits: value.hits,
                count: value.count,
                detail: value.detail,
                suggestions,
                error: None,
            }
        } else {
            TypeSearchResult {
                hits: Vec::new(),
                count: 0,
                detail: String::new(),
                suggestions,
                error: Some(value.detail),
            }
        };
        if self.cache.len() >= 64 {
            self.cache.clear();
        }
        self.cache.insert(cache_key, result.clone());
        Ok(result)
    }

    pub(super) fn prepare(&mut self, query: &str) -> Result<TypeSearchResponse> {
        self.last_used = Instant::now();
        self.request_value("type_prepare", query, &[])
    }

    fn request_value(
        &mut self,
        operation: &'static str,
        query: &str,
        names: &[String],
    ) -> Result<TypeSearchResponse> {
        self.version += 1;
        let response: TypeSearchResponse = self
            .process
            .request(
                &TypeSearchRequest {
                    operation,
                    source: "",
                    file_name: "",
                    version: self.version,
                    line: 0,
                    column: 0,
                    input: query,
                    names,
                },
                Duration::from_secs(30),
            )
            .map_err(|error| anyhow::anyhow!(error))?;
        ensure!(response.version == self.version, "stale type search response");
        Ok(response)
    }

    pub(super) fn alive(&mut self) -> bool {
        self.process.alive()
    }

    pub(super) fn rss_kib(&self) -> Option<u64> {
        self.process.rss_kib()
    }
}
