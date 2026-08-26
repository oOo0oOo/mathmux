use super::*;

impl Searcher {
    pub(super) fn goal_search(
        &self,
        workspace: &Workspace,
        location: GoalLocation,
    ) -> Result<SearchResult> {
        let source = fs::read_to_string(&location.path)?;
        if location.tail || location.more {
            return Ok(source_location_result(
                workspace, &location, &source, None, true,
            ));
        }
        if !location.probe {
            return Ok(source_location_result(
                workspace,
                &location,
                &source,
                Some("source only"),
                true,
            ));
        }
        let Some((start, end, in_tactic, indent)) = goal_probe(&source, location.line) else {
            return Ok(source_location_result(
                workspace,
                &location,
                &source,
                Some("source only"),
                false,
            ));
        };
        let mut probe = source.clone();
        probe.replace_range(
            start..end,
            &goal_probe_replacement(
                in_tactic,
                &indent,
                "first | exact? | aesop? | simp? | apply? | rw?",
            ),
        );
        let (_, rendered) = match self.checker.probe_source(workspace, &location.path, &probe) {
            Ok(result) => result,
            Err(error) => {
                return Ok(source_location_result(
                    workspace,
                    &location,
                    &source,
                    Some(&format!("goal unavailable: {error:#}")),
                    false,
                ));
            }
        };
        let goal_state = traced_goal_state(&rendered);
        let mut suggestions = Vec::new();
        if let Some(state) = &goal_state {
            for candidate in local_method_candidates(state) {
                probe = source.clone();
                probe.replace_range(
                    start..end,
                    &goal_probe_replacement(in_tactic, &indent, &candidate),
                );
                if self
                    .checker
                    .probe_source(workspace, &location.path, &probe)
                    .is_ok_and(|(ok, _)| ok)
                {
                    suggestions.push(candidate);
                    break;
                }
            }
        }
        for suggestion in try_this_suggestions(&rendered) {
            push_suggestion(&mut suggestions, &suggestion);
        }
        if suggestions.is_empty() && goal_state.is_none() {
            let detail = rendered
                .lines()
                .rev()
                .find(|line| !line.trim().is_empty())
                .map(|line| {
                    format!(
                        "goal search returned no tactic suggestion: {}",
                        clean_line(line)
                    )
                })
                .unwrap_or_else(|| "goal search returned no tactic suggestion".into());
            return Ok(source_location_result(
                workspace,
                &location,
                &source,
                Some(&detail),
                false,
            ));
        }
        let relative = location
            .path
            .strip_prefix(&workspace.path)
            .unwrap_or(&location.path)
            .to_string_lossy()
            .into_owned();
        let mut hits = Vec::new();
        if let Some(goal_state) = goal_state {
            hits.push(SearchHit {
                name: "goal".into(),
                kind: "goal-state".into(),
                signature: None,
                module: String::new(),
                path: relative.clone(),
                line: location.line,
                doc: None,
                source: Some(goal_state),
                usages: Vec::new(),
                applicable: false,
                required_import: None,
            });
        }
        hits.extend(suggestions.into_iter().map(|suggestion| SearchHit {
            name: clean_line(&suggestion),
            kind: "goal".into(),
            signature: None,
            module: String::new(),
            path: relative.clone(),
            line: location.line,
            doc: None,
            source: Some(suggestion),
            usages: Vec::new(),
            applicable: true,
            required_import: None,
        }));
        let has_suggestion = hits.iter().any(|hit| hit.applicable);
        Ok(SearchResult {
            hits,
            inference: "goal".into(),
            note: (!has_suggestion).then(|| "no tactic suggestion".into()),
            ok: true,
        })
    }
}
pub(super) struct GoalLocation {
    pub(super) path: PathBuf,
    pub(super) display_path: Option<String>,
    pub(super) line: u64,
    pub(super) tail: bool,
    pub(super) more: bool,
    pub(super) probe: bool,
}

pub(super) struct SourceOccurrenceQuery {
    pub(super) path: PathBuf,
    pub(super) main_path: Option<PathBuf>,
    pub(super) display_path: Option<String>,
    pub(super) first_line: u64,
    pub(super) last_line: u64,
    pub(super) terms: Vec<String>,
}

pub(super) struct SourceRegexQuery {
    pub(super) scope: PathBuf,
    pub(super) pattern: String,
}

pub(super) fn parse_source_regex_query(
    root: &Path,
    cwd: &Path,
    query: &str,
) -> Result<Option<SourceRegexQuery>> {
    let query = query.trim();
    let start = if query.starts_with('/') {
        0
    } else if let Some(start) = query.find(" /") {
        start + 1
    } else {
        return Ok(None);
    };
    let Some(end) = query.rfind('/') else {
        return Ok(None);
    };
    if end <= start + 1 {
        return Ok(None);
    }
    let pattern = &query[start + 1..end];
    ensure!(pattern.len() <= 500, "source regex is too long");
    Regex::new(pattern).context("invalid source regex")?;
    let scope = format!("{} {}", &query[..start], &query[end + 1..]);
    let scope = scope.trim();
    let scope = scope
        .strip_prefix('[')
        .and_then(|scope| scope.strip_suffix(']'))
        .unwrap_or(scope);
    ensure!(
        scope.split_whitespace().count() <= 1,
        "source regex accepts at most one file or directory scope"
    );
    let scope = if scope.is_empty() {
        fs::canonicalize(root)?
    } else if Path::new(scope).extension().is_some_and(|extension| extension == "lean") {
        resolve_goal_path(root, cwd, scope)?
            .map(|(path, _, _)| path)
            .with_context(|| format!("source file not found or ambiguous: {scope}"))?
    } else {
        let direct = if Path::new(scope).is_absolute() {
            PathBuf::from(scope)
        } else if cwd.join(scope).is_dir() {
            cwd.join(scope)
        } else {
            root.join(scope)
        };
        let direct = fs::canonicalize(&direct)
            .with_context(|| format!("source directory not found: {scope}"))?;
        let root = fs::canonicalize(root)?;
        ensure!(direct.starts_with(&root), "source regex scope is outside the workspace");
        ensure!(direct.is_dir(), "source regex scope is not a directory");
        direct
    };
    Ok(Some(SourceRegexQuery {
        scope,
        pattern: pattern.to_owned(),
    }))
}

pub(super) fn source_regex_result(
    workspace: &Workspace,
    query: SourceRegexQuery,
    all: bool,
) -> Result<SearchResult> {
    let regex = Regex::new(&query.pattern).context("invalid source regex")?;
    let files = if query.scope.is_file() {
        vec![query.scope.clone()]
    } else {
        project_lean_files(&query.scope)
            .into_iter()
            .map(|path| query.scope.join(path))
            .collect()
    };
    let limit = if all { SOURCE_OCCURRENCE_LIMIT } else { 12 };
    let deadline = Instant::now() + SOURCE_FALLBACK_BUDGET;
    let mut hits = Vec::new();
    let mut total = 0usize;
    let mut timed_out = false;
    for path in files {
        if Instant::now() >= deadline {
            timed_out = true;
            break;
        }
        let source = fs::read_to_string(&path)?;
        let lines = source.lines().collect::<Vec<_>>();
        for (index, line) in lines.iter().enumerate() {
            if !regex.is_match(line) {
                continue;
            }
            total += 1;
            if hits.len() >= limit {
                continue;
            }
            let first = index.saturating_sub(2);
            let last = (index + 3).min(lines.len());
            let excerpt = lines[first..last]
                .iter()
                .enumerate()
                .map(|(offset, source)| {
                    let number = first + offset + 1;
                    let marker = if number == index + 1 { '>' } else { ' ' };
                    format!("{marker}{number:>5} | {source}")
                })
                .collect::<Vec<_>>()
                .join("\n");
            let relative = path
                .strip_prefix(&workspace.path)
                .unwrap_or(&path)
                .to_string_lossy()
                .into_owned();
            hits.push(SearchHit {
                name: truncate_line(line.trim(), 200),
                kind: "source-regex".into(),
                signature: None,
                module: String::new(),
                path: relative,
                line: index as u64 + 1,
                doc: None,
                source: Some(excerpt),
                usages: Vec::new(),
                applicable: false,
                required_import: None,
            });
        }
    }
    let omitted = total.saturating_sub(hits.len());
    Ok(SearchResult {
        hits,
        inference: "source-regex".into(),
        note: if timed_out {
            Some("source regex scan timed out; narrow the scope".into())
        } else if total == 0 {
            Some("no regex source matches".into())
        } else if omitted > 0 {
            Some(if all {
                format!("+{omitted} matches omitted; narrow the scope")
            } else {
                format!("+{omitted} matches omitted; use --all")
            })
        } else {
            None
        },
        ok: true,
    })
}

pub(super) fn parse_source_occurrence_query(
    root: &Path,
    cwd: &Path,
    main_root: Option<&Path>,
    query: &str,
) -> Result<Option<SourceOccurrenceQuery>> {
    let parts = query.split_whitespace().collect::<Vec<_>>();
    let Some(_) = parts.first() else {
        return Ok(None);
    };
    let mut lean_targets = parts
        .iter()
        .enumerate()
        .filter(|(_, part)| {
            let path = part
                .rsplit_once(':')
                .filter(|(_, range)| parse_source_line_range(range).is_some())
                .map_or(**part, |(path, _)| path);
            Path::new(path).extension().and_then(|extension| extension.to_str()) == Some("lean")
        })
        .map(|(index, _)| index);
    let target_index = match (lean_targets.next(), lean_targets.next()) {
        (Some(index), None) => index,
        (Some(_), Some(_)) => {
            bail!("source queries accept one Lean file; search each file separately")
        }
        _ => 0,
    };
    let target = parts[target_index];
    let terms = parts
        .iter()
        .enumerate()
        .filter(|(index, _)| *index != target_index)
        .map(|(_, part)| *part)
        .flat_map(|part| part.split('|'))
        .map(|term| term.trim_matches(['\'', '"']))
        .filter(|term| !term.is_empty())
        .map(str::to_owned)
        .collect::<Vec<_>>();
    let (path, range) = target
        .rsplit_once(':')
        .and_then(|(path, range)| parse_source_line_range(range).map(|range| (path, range)))
        .map_or((target, None), |(path, range)| (path, Some(range)));
    if terms.is_empty() && range.is_none() {
        return Ok(None);
    }
    let requested_path = path;
    let inferred_outline_path = Path::new(path).extension().is_none()
        && terms.len() == 1
        && matches!(terms[0].to_ascii_lowercase().as_str(), "outline" | "declarations");
    if inferred_outline_path && path.eq_ignore_ascii_case("FILE") {
        bail!("FILE is a help placeholder; replace it with a Lean source path");
    }
    let resolved_path = if inferred_outline_path {
        format!("{path}.lean")
    } else {
        path.to_owned()
    };
    if Path::new(&resolved_path)
        .extension()
        .and_then(|extension| extension.to_str())
        != Some("lean")
    {
        return Ok(None);
    }
    let Some((path, display_path, _)) = resolve_goal_path(root, cwd, &resolved_path)? else {
        if inferred_outline_path {
            return Ok(None);
        }
        bail!(missing_source_message(root, main_root, requested_path)?);
    };
    let main_path = if main_root
        .is_some_and(|main_root| fs::canonicalize(root).ok() != fs::canonicalize(main_root).ok())
        && !Path::new(requested_path).is_absolute()
    {
        let main_root = main_root.expect("checked above");
        resolve_goal_path(main_root, main_root, &resolved_path)?.map(|(path, _, _)| path)
    } else {
        None
    };
    let (first_line, last_line) = range.unwrap_or((1, u64::MAX));
    Ok(Some(SourceOccurrenceQuery {
        path,
        main_path,
        display_path,
        first_line,
        last_line,
        terms,
    }))
}

pub(super) fn parse_source_line_range(range: &str) -> Option<(u64, u64)> {
    let (first, last) = range.split_once('-')?;
    let first = first.parse().ok()?;
    let last = last.parse().ok()?;
    (first > 0 && first <= last).then_some((first, last))
}

pub(super) fn source_occurrence_result(
    workspace: &Workspace,
    query: SourceOccurrenceQuery,
    all: bool,
) -> Result<SearchResult> {
    let source = fs::read_to_string(&query.path)?;
    if query.terms.len() == 1
        && matches!(query.terms[0].to_ascii_lowercase().as_str(), "outline" | "declarations")
    {
        return Ok(source_outline_result(workspace, &query, &source));
    }
    let import_query = query
        .terms
        .iter()
        .any(|term| term.eq_ignore_ascii_case("imports"));
    let match_terms = query
        .terms
        .iter()
        .filter(|term| !term.eq_ignore_ascii_case("imports"))
        .collect::<Vec<_>>();
    let source_lines = source.lines().count() as u64;
    let matches = source
        .lines()
        .enumerate()
        .filter_map(|(index, line)| {
            let number = index as u64 + 1;
            let trimmed = line.trim_start();
            let is_import = trimmed.starts_with("import ")
                || trimmed.starts_with("public import ");
            (number >= query.first_line
                && number <= query.last_line
                && if import_query {
                    is_import
                        && (match_terms.is_empty()
                            || match_terms.iter().any(|term| line.contains(*term)))
                } else {
                    query.terms.is_empty()
                        || query.terms.iter().any(|term| line.contains(term))
                })
            .then_some((number, line))
        })
        .collect::<Vec<_>>();
    let limit = if all {
        SOURCE_OCCURRENCE_ALL_LIMIT
    } else if query.terms.is_empty() {
        SOURCE_RANGE_LIMIT
    } else {
        SOURCE_OCCURRENCE_LIMIT
    };
    let excerpt = matches
        .iter()
        .take(limit)
        .map(|(line, source)| {
            if query.terms.is_empty() {
                format!("{line}\t{source}")
            } else {
                format!("{line:>5}  {source}")
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    let relative = query.display_path.unwrap_or_else(|| {
        query
            .path
            .strip_prefix(&workspace.path)
            .unwrap_or(&query.path)
            .to_string_lossy()
            .into_owned()
    });
    let omitted = matches.len().saturating_sub(limit);
    let terms_label = if import_query {
        let filters = match_terms
            .iter()
            .map(|term| term.as_str())
            .collect::<Vec<_>>()
            .join(" | ");
        if filters.is_empty() {
            "imports".to_owned()
        } else {
            format!("imports {filters}")
        }
    } else {
        query.terms.join(" | ")
    };
    let hits = (!matches.is_empty())
        .then(|| SearchHit {
            name: if query.terms.is_empty() {
                "source".into()
            } else {
                "matches".into()
            },
            kind: if query.terms.is_empty() {
                "source-range".into()
            } else {
                "source-occurrences".into()
            },
            signature: Some(if query.terms.is_empty() {
                format!("{} lines", matches.len())
            } else {
                format!(
                    "{} for {}",
                    matches.len(),
                    terms_label
                )
            }),
            module: String::new(),
            path: relative,
            line: matches.first().map_or(query.first_line, |(line, _)| *line),
            doc: None,
            source: Some(excerpt),
            usages: Vec::new(),
            applicable: false,
            required_import: None,
        })
        .into_iter()
        .collect();
    Ok(SearchResult {
        hits,
        inference: "source".into(),
        note: if matches.is_empty()
            && query.terms.is_empty()
            && source_lines < query.first_line
            && query.main_path.as_ref().is_some_and(|path| {
                fs::read_to_string(path)
                    .is_ok_and(|source| source.lines().count() as u64 >= query.first_line)
            }) {
            Some("workspace source is stale; run mathmux sync".into())
        } else if matches.is_empty() {
            Some(if query.terms.is_empty() {
                "no source lines in range".into()
            } else {
                "no literal source matches".into()
            })
        } else if omitted > 0 {
            Some(if query.terms.is_empty() {
                if all {
                    format!("+{omitted} lines omitted; narrow the range")
                } else {
                    format!("+{omitted} lines omitted; use --all")
                }
            } else if all {
                format!("+{omitted} matches omitted; narrow the query")
            } else {
                format!("+{omitted} matches omitted; use --all")
            })
        } else {
            None
        },
        ok: true,
    })
}

fn source_outline_result(
    workspace: &Workspace,
    query: &SourceOccurrenceQuery,
    source: &str,
) -> SearchResult {
    let module = project_module_name(&workspace.path, &query.path);
    let mut entries = parse_source(source, &module)
        .into_iter()
        .filter(|entry| !matches!(entry.kind.as_str(), "field" | "file" | "imports"))
        .collect::<Vec<_>>();
    entries.sort_by_key(|entry| entry.line);
    let total = entries.len();
    let source_lines = source.lines().count();
    let outline = entries
        .iter()
        .take(SOURCE_OCCURRENCE_ALL_LIMIT)
        .map(|entry| {
            let prefix = format!("{:>5}  {} {}", entry.line, entry.kind, entry.name);
            if entry.signature.is_empty() || prefix.chars().count() >= OUTLINE_LINE_CHARS {
                prefix
            } else {
                truncate_line(
                    &format!("{prefix} : {}", entry.signature),
                    OUTLINE_LINE_CHARS,
                )
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    let relative = query.display_path.clone().unwrap_or_else(|| {
        query
            .path
            .strip_prefix(&workspace.path)
            .unwrap_or(&query.path)
            .to_string_lossy()
            .into_owned()
    });
    let hits = (!entries.is_empty())
        .then(|| SearchHit {
            name: "outline".into(),
            kind: "outline".into(),
            signature: Some(format!("{total} declarations, {source_lines} lines")),
            module,
            path: relative,
            line: entries.first().map_or(1, |entry| entry.line),
            doc: None,
            source: Some(outline),
            usages: Vec::new(),
            applicable: false,
            required_import: None,
        })
        .into_iter()
        .collect();
    SearchResult {
        hits,
        inference: "source".into(),
        note: if entries.is_empty() {
            Some("no declarations in source file".into())
        } else if total > SOURCE_OCCURRENCE_ALL_LIMIT {
            Some(format!(
                "+{} declarations omitted",
                total - SOURCE_OCCURRENCE_ALL_LIMIT
            ))
        } else {
            None
        },
        ok: true,
    }
}

pub(super) fn parse_goal_location(
    root: &Path,
    cwd: &Path,
    main_root: Option<&Path>,
    query: &str,
) -> Result<Option<GoalLocation>> {
    let (query, more) = query
        .rsplit_once(char::is_whitespace)
        .filter(|(_, modifier)| modifier.eq_ignore_ascii_case("more"))
        .map_or((query, false), |(query, _)| (query.trim_end(), true));
    let mut location_tokens = query
        .split_whitespace()
        .filter(|token| is_goal_location_token(token));
    let query = match (location_tokens.next(), location_tokens.next()) {
        (Some(token), None) => token,
        _ => query,
    };
    if let Some((path, suffix)) = query.rsplit_once(':')
        && suffix.eq_ignore_ascii_case("tail")
    {
        let Some((path, display_path, probe)) = resolve_goal_path(root, cwd, path)? else {
            bail!(missing_source_message(root, main_root, path)?);
        };
        let line = fs::read_to_string(&path)?.lines().count().max(1) as u64;
        return Ok(Some(GoalLocation {
            path,
            display_path,
            line,
            tail: true,
            more,
            probe,
        }));
    }
    let mut parts = query.rsplitn(3, ':');
    let Some(last) = parts.next() else {
        return Ok(None);
    };
    let Ok(last_number) = last.parse::<u64>() else {
        return Ok(None);
    };
    let Some(second) = parts.next() else {
        return Ok(None);
    };
    let (path, line) = if let Ok(line) = second.parse::<u64>() {
        let Some(path) = parts.next() else {
            return Ok(None);
        };
        (path, line)
    } else {
        (second, last_number)
    };
    let Some((path, display_path, probe)) = resolve_goal_path(root, cwd, path)? else {
        bail!(missing_source_message(root, main_root, path)?);
    };
    ensure!(line > 0, "goal line starts at 1");
    Ok(Some(GoalLocation {
        path,
        display_path,
        line,
        tail: false,
        more,
        probe,
    }))
}

fn is_goal_location_token(token: &str) -> bool {
    let Some((prefix, suffix)) = token.rsplit_once(':') else {
        return false;
    };
    if !suffix.eq_ignore_ascii_case("tail") && suffix.parse::<u64>().is_err() {
        return false;
    }
    let path = prefix
        .rsplit_once(':')
        .filter(|(_, line)| line.parse::<u64>().is_ok())
        .map_or(prefix, |(path, _)| path);
    Path::new(path).extension().and_then(|extension| extension.to_str()) == Some("lean")
}

pub(super) fn missing_source_message(
    root: &Path,
    main_root: Option<&Path>,
    requested: &str,
) -> Result<String> {
    let Some(main_root) = main_root else {
        return Ok(format!("source file not found or ambiguous: {requested}"));
    };
    if fs::canonicalize(root).ok() == fs::canonicalize(main_root).ok() {
        return Ok(format!("source file not found or ambiguous: {requested}"));
    }
    let requested_name = Path::new(requested).file_name();
    let workspace_has_same_name = requested_name.is_some_and(|requested_name| {
        project_lean_files(root)
            .iter()
            .any(|path| path.file_name() == Some(requested_name))
    });
    if !workspace_has_same_name && resolve_goal_path(main_root, main_root, requested)?.is_some() {
        return Ok("source file is on managed main; run mathmux sync".into());
    }
    Ok(format!("source file not found or ambiguous: {requested}"))
}

pub(super) fn resolve_goal_path(
    root: &Path,
    cwd: &Path,
    path: &str,
) -> Result<Option<(PathBuf, Option<String>, bool)>> {
    let display = path.strip_prefix("<dependency>/").unwrap_or(path);
    let requested = PathBuf::from(display);
    if requested
        .extension()
        .is_none_or(|extension| extension != "lean")
    {
        return Ok(None);
    }
    let direct = if requested.is_absolute() {
        requested.clone()
    } else {
        cwd.join(&requested)
    };
    if direct.is_file() {
        let direct = fs::canonicalize(direct)?;
        if direct.starts_with(root) {
            return Ok(Some((direct, None, true)));
        }
    }

    let root = fs::canonicalize(root)?;
    let packages = fs::canonicalize(root.join(".lake/packages")).ok();
    let mut variants = vec![requested.clone()];
    if !requested.is_absolute() {
        let components = requested.components().collect::<Vec<_>>();
        if components.len() == 2
            && requested
                .parent()
                .and_then(Path::file_name)
                .zip(requested.file_stem())
                .is_some_and(|(directory, stem)| directory == stem)
            && let Some(file_name) = requested.file_name()
        {
            variants.push(PathBuf::from(file_name));
        }
        for start in 1..components.len().saturating_sub(1) {
            let mut suffix = PathBuf::new();
            for component in &components[start..] {
                suffix.push(component.as_os_str());
            }
            variants.push(suffix);
        }
        if let Some(file_name) = requested.file_name() {
            variants.push(PathBuf::from(file_name));
        }
        variants.dedup();
    }
    let requested_components = requested.components().count();
    for variant in variants.iter().filter(|variant| {
        requested_components == 1 || variant.components().count() > 1
    }) {
        let mut candidates = Vec::new();
        let project = root.join(variant);
        if project.is_file() {
            candidates.push(fs::canonicalize(project)?);
        }
        if let Some(packages) = &packages {
            let direct_package = packages.join(variant);
            if direct_package.is_file() {
                candidates.push(fs::canonicalize(direct_package)?);
            }
            for package in fs::read_dir(packages)?.flatten() {
                let candidate = package.path().join(variant);
                if candidate.is_file() {
                    candidates.push(fs::canonicalize(candidate)?);
                }
                if let Ok(source_roots) = fs::read_dir(package.path()) {
                    for source_root in source_roots.flatten() {
                        let candidate = source_root.path().join(variant);
                        if candidate.is_file() {
                            candidates.push(fs::canonicalize(candidate)?);
                        }
                    }
                }
            }
        }
        candidates.sort();
        candidates.dedup();
        let [resolved] = candidates.as_slice() else {
            if candidates.is_empty() {
                continue;
            }
            return Ok(None);
        };
        let project = resolved.starts_with(&root)
            && packages
                .as_ref()
                .is_none_or(|packages| !resolved.starts_with(packages));
        return Ok(Some((
            resolved.clone(),
            (!project).then(|| display.to_owned()),
            project,
        )));
    }
    for variant in variants.iter().skip(1) {
        let mut matches = project_lean_files(&root)
            .into_iter()
            .filter(|candidate| candidate.ends_with(variant))
            .filter_map(|candidate| fs::canonicalize(root.join(candidate)).ok())
            .collect::<Vec<_>>();
        matches.sort();
        matches.dedup();
        match matches.as_slice() {
            [resolved] => return Ok(Some((resolved.clone(), None, true))),
            [] => {}
            _ => return Ok(None),
        }
    }
    if let Some(packages) = &packages {
        for variant in variants
            .iter()
            .filter(|variant| variant.components().count() > 1)
        {
            let mut matches = WalkDir::new(packages)
                .into_iter()
                .filter_map(Result::ok)
                .filter(|entry| entry.file_type().is_file() && entry.path().ends_with(variant))
                .filter_map(|entry| fs::canonicalize(entry.path()).ok())
                .collect::<Vec<_>>();
            matches.sort();
            matches.dedup();
            match matches.as_slice() {
                [resolved] => {
                    return Ok(Some((resolved.clone(), Some(display.to_owned()), false)));
                }
                [] => {}
                _ => return Ok(None),
            }
        }
    }
    if requested.components().count() == 1 {
        let files = project_lean_files(&root);
        let mut matches = files
            .iter()
            .filter(|candidate| candidate.file_name() == requested.file_name())
            .filter_map(|candidate| fs::canonicalize(root.join(candidate)).ok())
            .collect::<Vec<_>>();
        matches.sort();
        matches.dedup();
        if let [resolved] = matches.as_slice() {
            return Ok(Some((resolved.clone(), None, true)));
        }
        if !matches.is_empty() {
            return Ok(None);
        }
        let requested_name = requested
            .file_name()
            .expect("single-component Lean path has a file name")
            .to_string_lossy();
        let mut matches = files
            .iter()
            .filter(|candidate| {
                candidate.file_name().is_some_and(|name| {
                    name.to_string_lossy()
                        .eq_ignore_ascii_case(&requested_name)
                })
            })
            .filter_map(|candidate| fs::canonicalize(root.join(candidate)).ok())
            .collect::<Vec<_>>();
        matches.sort();
        matches.dedup();
        if let [resolved] = matches.as_slice() {
            return Ok(Some((resolved.clone(), None, true)));
        }
        if matches.is_empty() {
            let requested_stem = requested
                .file_stem()
                .and_then(|stem| stem.to_str())
                .unwrap_or_default();
            let requested_parts = identifier_query_parts(requested_stem);
            if requested_parts.len() >= 2 {
                let mut matches = files
                    .iter()
                    .filter(|candidate| {
                        let parts = candidate
                            .file_stem()
                            .and_then(|stem| stem.to_str())
                            .map(identifier_query_parts)
                            .unwrap_or_default();
                        ordered_subset(&requested_parts, &parts)
                    })
                    .filter_map(|candidate| fs::canonicalize(root.join(candidate)).ok())
                    .collect::<Vec<_>>();
                matches.sort();
                matches.dedup();
                if let [resolved] = matches.as_slice() {
                    return Ok(Some((resolved.clone(), None, true)));
                }
            }
        }
    }
    Ok(None)
}

fn ordered_subset(needles: &[String], haystack: &[String]) -> bool {
    let mut needles = needles.iter();
    let Some(mut next) = needles.next() else {
        return true;
    };
    for part in haystack {
        if part == next {
            let Some(needle) = needles.next() else {
                return true;
            };
            next = needle;
        }
    }
    false
}

pub(super) fn source_location_result(
    workspace: &Workspace,
    location: &GoalLocation,
    source: &str,
    note: Option<&str>,
    ok: bool,
) -> SearchResult {
    let relative = location.display_path.clone().unwrap_or_else(|| {
        location
            .path
            .strip_prefix(&workspace.path)
            .unwrap_or(&location.path)
            .to_string_lossy()
            .into_owned()
    });
    SearchResult {
        hits: vec![SearchHit {
            name: "source".into(),
            kind: if location.more {
                "location-more"
            } else {
                "location"
            }
            .into(),
            signature: None,
            module: String::new(),
            path: relative,
            line: location.line,
            doc: None,
            source: nonempty(location_source_excerpt(
                source,
                location.line,
                if location.more {
                    LOCATION_MORE_LINES
                } else if location.tail {
                    SOURCE_PREVIEW_LINES
                } else {
                    LOCATION_PREVIEW_LINES
                },
            )),
            usages: Vec::new(),
            applicable: false,
            required_import: None,
        }],
        inference: if ok { "source" } else { "source-only" }.into(),
        note: note.map(Into::into),
        ok,
    }
}

pub(super) fn location_source_excerpt(
    source: &str,
    requested_line: u64,
    line_limit: usize,
) -> String {
    let lines = source.lines().collect::<Vec<_>>();
    if lines.is_empty() {
        return String::new();
    }
    let target = requested_line
        .saturating_sub(1)
        .min(lines.len().saturating_sub(1) as u64) as usize;
    let start = target
        .saturating_sub(6)
        .min(lines.len().saturating_sub(line_limit));
    let end = lines.len().min(start + line_limit);
    lines[start..end]
        .iter()
        .enumerate()
        .map(|(offset, line)| format!("{:>5}  {line}", start + offset + 1))
        .collect::<Vec<_>>()
        .join("\n")
}

pub(super) fn goal_probe(
    source: &str,
    requested_line: u64,
) -> Option<(usize, usize, bool, String)> {
    let lines = line_starts(source);
    let requested = requested_line.saturating_sub(1) as usize;
    for distance in 0..=2 {
        for line in [requested.saturating_sub(distance), requested + distance] {
            let start = *lines.get(line)?;
            let end = lines.get(line + 1).copied().unwrap_or(source.len());
            let text = &source[start..end];
            for placeholder in ["sorry", "admit"] {
                if let Some(local) = text.find(placeholder) {
                    let absolute = start + local;
                    let indent = text[..local]
                        .chars()
                        .take_while(|character| character.is_whitespace())
                        .collect();
                    let preceding = &source[..absolute];
                    let in_tactic = preceding
                        .lines()
                        .rev()
                        .find(|line| !line.trim().is_empty())
                        .is_some_and(|line| line.trim_end().ends_with("by"));
                    return Some((absolute, absolute + placeholder.len(), in_tactic, indent));
                }
            }
        }
    }
    None
}

pub(super) fn append_goal_tactic(
    source: &str,
    requested_line: u64,
    tactic: &str,
) -> Option<String> {
    let starts = line_starts(source);
    let requested = requested_line.saturating_sub(1) as usize;
    let line_text = |line: usize| {
        let start = *starts.get(line)?;
        let end = starts.get(line + 1).copied().unwrap_or(source.len());
        Some(&source[start..end])
    };
    let is_tactic_start = |line: usize| {
        let text = line_text(line).unwrap_or_default().trim_end();
        text == "by" || text.ends_with(":= by") || text.ends_with(" where")
    };
    let forward_end = (requested + 20).min(starts.len().saturating_sub(1));
    let tactic_line = (requested..=forward_end)
        .find(|line| is_tactic_start(*line))
        .or_else(|| {
            (requested.saturating_sub(80)..requested)
                .rev()
                .find(|line| is_tactic_start(*line))
        })?;
    let command = line_text(tactic_line)?;
    let command_indent = command
        .chars()
        .take_while(|character| character.is_whitespace())
        .count();
    let mut insertion = source.len();
    for (line, start) in starts.iter().enumerate().skip(tactic_line + 1) {
        let text = line_text(line)?;
        if text.trim().is_empty() {
            continue;
        }
        let indent = text
            .chars()
            .take_while(|character| character.is_whitespace())
            .count();
        if indent <= command_indent {
            insertion = *start;
            break;
        }
    }
    let indentation = command
        .chars()
        .take_while(|character| character.is_whitespace())
        .collect::<String>();
    let indent = format!("{indentation}  ");
    let mut probe = source.to_owned();
    let separator = if insertion > 0 && !source[..insertion].ends_with('\n') {
        "\n"
    } else {
        ""
    };
    probe.insert_str(insertion, &format!("{separator}{indent}{tactic}\n"));
    Some(probe)
}

pub(super) fn goal_probe_replacement(in_tactic: bool, indent: &str, tactic: &str) -> String {
    if in_tactic {
        format!(
            "run_tac\n{indent}  let goal ← Lean.Elab.Tactic.getMainGoal\n{indent}  let state ← Lean.Meta.ppGoal goal\n{indent}  Lean.logInfo m!\"{GOAL_STATE_BEGIN}\\n{{state}}\\n{GOAL_STATE_END}\"\n{indent}{tactic}"
        )
    } else {
        format!(
            "by\n{indent}  run_tac\n{indent}    let goal ← Lean.Elab.Tactic.getMainGoal\n{indent}    let state ← Lean.Meta.ppGoal goal\n{indent}    Lean.logInfo m!\"{GOAL_STATE_BEGIN}\\n{{state}}\\n{GOAL_STATE_END}\"\n{indent}  {tactic}"
        )
    }
}

pub(super) fn try_this_suggestions(output: &str) -> Vec<String> {
    let mut suggestions = Vec::new();
    let mut lines = output.lines().peekable();
    while let Some(line) = lines.next() {
        if let Some((_, suggestion)) = line.split_once("Try this:") {
            let suggestion = suggestion.trim();
            if !suggestion.is_empty() {
                push_suggestion(&mut suggestions, suggestion);
                continue;
            }
            while lines.peek().is_some_and(|line| line.trim().is_empty()) {
                lines.next();
            }
            let Some(first) = lines.peek() else {
                break;
            };
            let indent = first.len() - first.trim_start().len();
            if indent == 0 {
                continue;
            }
            let mut block = Vec::new();
            let mut length = 0;
            while let Some(next) = lines.peek() {
                if next.trim().is_empty() {
                    lines.next();
                    break;
                }
                let next_indent = next.len() - next.trim_start().len();
                if next_indent < indent || block.len() >= 8 || length >= 1_200 {
                    break;
                }
                let normalized = next[indent..].trim_end();
                if normalized.starts_with("-- Remaining subgoals:") {
                    break;
                }
                length += normalized.len();
                block.push(normalized);
                lines.next();
            }
            if !block.is_empty() {
                push_suggestion(&mut suggestions, &block.join("\n"));
            }
        }
    }
    suggestions
}

pub(super) fn traced_goal_state(output: &str) -> Option<String> {
    let lines = output.lines().collect::<Vec<_>>();
    let start = lines
        .iter()
        .position(|line| line.contains(GOAL_STATE_BEGIN))?
        + 1;
    let end = lines[start..]
        .iter()
        .position(|line| line.contains(GOAL_STATE_END))?
        + start;
    let state = lines[start..end]
        .iter()
        .map(|line| line.trim_end())
        .filter(|line| !line.trim().is_empty())
        .collect::<Vec<_>>();
    if state.is_empty() {
        return None;
    }
    let omitted = state.len().saturating_sub(SOURCE_PREVIEW_LINES);
    let mut rendered = state[state.len().saturating_sub(SOURCE_PREVIEW_LINES)..].join("\n");
    if omitted > 0 {
        rendered = format!("+{omitted} context lines omitted\n{rendered}");
    }
    Some(rendered)
}

pub(super) fn local_method_candidates(goal_state: &str) -> Vec<String> {
    let Some(goal) = goal_state
        .lines()
        .find_map(|line| line.trim().strip_prefix('⊢'))
        .map(str::trim)
    else {
        return Vec::new();
    };
    let Some(goal_head) = goal
        .split(|character: char| character.is_whitespace() || character == '(')
        .find(|part| !part.is_empty())
    else {
        return Vec::new();
    };
    let hypotheses = goal_state
        .lines()
        .filter_map(|line| line.trim().split_once(':'))
        .filter_map(|(name, ty)| {
            let head = ty
                .trim()
                .split(|character: char| character.is_whitespace() || character == '(')
                .find(|part| !part.is_empty())?;
            (head == goal_head)
                .then(|| name.split_whitespace().last().map(str::to_owned))
                .flatten()
        })
        .take(6)
        .collect::<Vec<_>>();
    let mut candidates = Vec::new();
    if (goal.contains('=') || goal.contains('≤') || goal.contains('<'))
        && (goal.contains('+') || goal.contains('-') || goal.contains('*'))
    {
        candidates.push("omega".into());
    }
    for left in &hypotheses {
        for right in &hypotheses {
            if left == right {
                continue;
            }
            candidates.push(format!("exact {left}.comp {right}"));
            candidates.push(format!("exact {left}.trans {right}"));
            if candidates.len() >= 8 {
                return candidates;
            }
        }
    }
    candidates
}

pub(super) fn push_suggestion(suggestions: &mut Vec<String>, suggestion: &str) {
    let suggestion = suggestion
        .strip_prefix("[apply] ")
        .or_else(|| suggestion.strip_prefix("[exact] "))
        .unwrap_or(suggestion);
    let has_placeholder = suggestion
        .split(|character: char| !(character.is_alphanumeric() || character == '_'))
        .any(|word| matches!(word, "sorry" | "admit"));
    if !has_placeholder && !suggestions.iter().any(|seen| seen == suggestion) {
        suggestions.push(suggestion.to_owned());
    }
}
