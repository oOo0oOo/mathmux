use super::*;

impl Searcher {
    pub(super) fn source_location_search(
        &self,
        workspace: &Workspace,
        location: SourceLocation,
    ) -> Result<SearchResult> {
        let source = fs::read_to_string(&location.path)?;
        Ok(source_location_result(
            workspace, &location, &source, None, false,
        ))
    }
}
pub(super) struct SourceLocation {
    pub(super) path: PathBuf,
    pub(super) display_path: Option<String>,
    pub(super) line: u64,
    pub(super) tail: bool,
    pub(super) expanded: bool,
}

pub(super) struct SourceOccurrenceQuery {
    pub(super) path: PathBuf,
    pub(super) main_path: Option<PathBuf>,
    pub(super) display_path: Option<String>,
    pub(super) first_line: u64,
    pub(super) last_line: u64,
    pub(super) additional_ranges: Vec<(u64, u64)>,
    pub(super) terms: Vec<String>,
}

pub(super) struct SourceRegexQuery {
    pub(super) scope: PathBuf,
    pub(super) pattern: String,
    pub(super) first_line: u64,
    pub(super) last_line: u64,
}

pub(super) fn parse_source_regex_query(
    root: &Path,
    cwd: &Path,
    main_root: Option<&Path>,
    query: &str,
) -> Result<Option<SourceRegexQuery>> {
    let query = query.trim();
    let (start, compact_scope) = if query.starts_with('/') {
        (0, false)
    } else if let Some(start) = query.find(" /") {
        (start + 1, false)
    } else if let Some(start) = query.find(":/") {
        (start + 1, true)
    } else {
        return Ok(None);
    };
    let end = if start == 0 {
        query[start + 1..]
            .char_indices()
            .find(|(offset, character)| {
                *character == '/'
                    && query[start + 1..start + 1 + offset]
                        .chars()
                        .rev()
                        .take_while(|character| *character == '\\')
                        .count()
                        % 2
                        == 0
            })
            .map(|(offset, _)| start + 1 + offset)
    } else {
        query.rfind('/')
    };
    let Some(end) = end else {
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
    let scope = if compact_scope {
        scope.strip_suffix(':').unwrap_or(scope)
    } else {
        scope
    };
    let scope = scope
        .strip_prefix('[')
        .and_then(|scope| scope.strip_suffix(']'))
        .unwrap_or(scope);
    if let Some(option) = scope.split_whitespace().next()
        && matches!(option, "--all" | "--limit")
    {
        let hint = if option == "--all" {
            "`mathmux search '/REGEX/' --all`"
        } else {
            "`mathmux search '/REGEX/' --limit N`"
        };
        bail!("source regex options must be outside the query; use {hint}");
    }
    if scope
        .split_whitespace()
        .next()
        .is_some_and(|token| token.eq_ignore_ascii_case("source"))
    {
        bail!("source is a help label, not a keyword; use /REGEX/ or PATH /REGEX/ directly")
    }
    ensure!(
        scope.split_whitespace().count() <= 1,
        "source regex accepts at most one file or directory scope"
    );
    let (scope, range) = scope
        .rsplit_once(':')
        .and_then(|(scope, range)| parse_source_line_range(range).map(|range| (scope, range)))
        .map_or((scope, None), |(scope, range)| (scope, Some(range)));
    let scope = if scope.is_empty() {
        fs::canonicalize(root)?
    } else if range.is_some()
        || Path::new(scope)
            .extension()
            .is_some_and(|extension| extension == "lean")
    {
        match resolve_source_path(root, cwd, scope)? {
            Some((path, _, _)) => path,
            None => bail!(missing_source_message(root, main_root, scope)?),
        }
    } else {
        resolve_source_directory(root, cwd, scope)?
    };
    let (first_line, last_line) = range.unwrap_or((1, u64::MAX));
    Ok(Some(SourceRegexQuery {
        scope,
        pattern: pattern.to_owned(),
        first_line,
        last_line,
    }))
}

fn resolve_source_directory(root: &Path, cwd: &Path, scope: &str) -> Result<PathBuf> {
    let root = fs::canonicalize(root)?;
    let requested = Path::new(scope);
    let mut candidates = if requested.is_absolute() {
        vec![requested.to_path_buf()]
    } else {
        vec![cwd.join(requested), root.join(requested)]
    };
    let packages = fs::canonicalize(root.join(".lake/packages")).ok();
    if !requested.is_absolute()
        && let Some(packages) = &packages
    {
        candidates.push(packages.join(requested));
        for package in fs::read_dir(packages)?.flatten() {
            candidates.push(package.path().join(requested));
            if let Ok(source_roots) = fs::read_dir(package.path()) {
                candidates.extend(
                    source_roots
                        .flatten()
                        .map(|source_root| source_root.path().join(requested)),
                );
            }
        }
    }
    let mut candidates = candidates
        .into_iter()
        .filter(|path| path.is_dir())
        .filter_map(|path| fs::canonicalize(path).ok())
        .collect::<Vec<_>>();
    candidates.sort();
    candidates.dedup();
    let [resolved] = candidates.as_slice() else {
        bail!("source directory not found or ambiguous: {scope}")
    };
    ensure!(
        resolved.starts_with(&root)
            || packages
                .as_ref()
                .is_some_and(|packages| resolved.starts_with(packages)),
        "source regex scope is outside the workspace"
    );
    Ok(resolved.clone())
}

pub(super) fn source_regex_result(
    workspace: &Workspace,
    query: SourceRegexQuery,
    all: bool,
) -> Result<SearchResult> {
    let regex = Regex::new(&query.pattern).context("invalid source regex")?;
    let mut files = if query.scope.is_file() {
        vec![query.scope.clone()]
    } else {
        project_lean_files(&query.scope)
            .into_iter()
            .map(|path| query.scope.join(path))
            .collect()
    };
    files.sort();
    let limit = if all { SOURCE_OCCURRENCE_LIMIT } else { 12 };
    let deadline = Instant::now() + SOURCE_FALLBACK_BUDGET;
    let dependency_root = fs::canonicalize(workspace.path.join(".lake/packages")).ok();
    let mut groups = Vec::new();
    let mut total = 0usize;
    let mut timed_out = false;
    for path in files {
        if Instant::now() >= deadline {
            timed_out = true;
            break;
        }
        let source = fs::read_to_string(&path)?;
        let lines = source.lines().collect::<Vec<_>>();
        let module = project_module_name(&workspace.path, &path);
        let spans = declaration_spans(&source, &module);
        let relative = source_display_path(workspace, dependency_root.as_deref(), &path);
        for (index, line) in lines.iter().enumerate() {
            if Instant::now() >= deadline {
                timed_out = true;
                break;
            }
            let line_number = index as u64 + 1;
            if line_number < query.first_line || line_number > query.last_line {
                continue;
            }
            if !regex.is_match(line) {
                continue;
            }
            total += 1;
            add_source_match_group(&mut groups, &relative, &spans, line_number, line);
        }
    }
    let total_groups = groups.len();
    let omitted_groups = total_groups.saturating_sub(limit);
    groups.truncate(limit);
    let displayed_matches = groups.iter().map(|group| group.count).sum::<usize>();
    let omitted_matches = total.saturating_sub(displayed_matches);
    let hits = groups.into_iter().map(SourceMatchGroup::into_hit).collect();
    Ok(SearchResult {
        hits,
        inference: "source-regex".into(),
        note: if timed_out {
            Some("source regex scan timed out; narrow the scope".into())
        } else if total == 0 {
            Some("no regex source matches".into())
        } else if omitted_groups > 0 {
            Some(format!(
                "+{omitted_matches} matches in {omitted_groups} declarations omitted; narrow the scope"
            ))
        } else {
            None
        },
        ok: true,
    })
}

#[derive(Debug)]
struct SourceMatchGroup {
    name: String,
    kind: String,
    signature: String,
    path: String,
    start: u64,
    end: u64,
    count: usize,
    matches: Vec<String>,
}

impl SourceMatchGroup {
    fn into_hit(self) -> SearchHit {
        SearchHit {
            name: self.name,
            kind: self.kind,
            signature: Some(format!(
                "{} match{}; lines {}-{}{}",
                self.count,
                if self.count == 1 { "" } else { "es" },
                self.start,
                self.end,
                if self.signature.is_empty() {
                    String::new()
                } else {
                    format!("; {}", truncate_line(&self.signature, 160))
                }
            )),
            module: String::new(),
            path: self.path,
            line: self.start,
            doc: None,
            source: Some(self.matches.join("\n")),
            usages: Vec::new(),
            applicable: false,
            required_import: None,
        }
    }
}

fn add_source_match_group(
    groups: &mut Vec<SourceMatchGroup>,
    path: &str,
    spans: &[DeclarationSpan],
    line_number: u64,
    line: &str,
) {
    let span = enclosing_declaration_span(spans, line_number);
    let (name, kind, signature, start, end) = span.map_or_else(
        || {
            (
                format!("source match at {path}:{line_number}"),
                "source-group".to_owned(),
                String::new(),
                line_number,
                line_number,
            )
        },
        |span| {
            (
                span.name.clone(),
                "source-group".to_owned(),
                span.signature.clone(),
                span.start,
                span.end,
            )
        },
    );
    let index = groups
        .iter()
        .position(|group| group.path == path && group.start == start && group.name == name);
    let group = match index {
        Some(index) => &mut groups[index],
        None => {
            groups.push(SourceMatchGroup {
                name,
                kind,
                signature,
                path: path.to_owned(),
                start,
                end,
                count: 0,
                matches: Vec::new(),
            });
            groups.last_mut().expect("source match group")
        }
    };
    group.count += 1;
    if group.matches.len() < 3 {
        group
            .matches
            .push(format!(">{line_number:>5} | {}", line.trim_end()));
    }
}

fn source_display_path(
    workspace: &Workspace,
    dependency_root: Option<&Path>,
    path: &Path,
) -> String {
    if let Ok(relative) = path.strip_prefix(&workspace.path) {
        return relative.to_string_lossy().into_owned();
    }
    if let Some(relative) = dependency_root.and_then(|root| path.strip_prefix(root).ok()) {
        let relative = relative.components().skip(1).collect::<PathBuf>();
        if !relative.as_os_str().is_empty() {
            return format!("<dependency>/{}", relative.display());
        }
    }
    path.to_string_lossy().into_owned()
}

pub(super) fn parse_source_occurrence_query(
    root: &Path,
    cwd: &Path,
    main_root: Option<&Path>,
    query: &str,
) -> Result<Option<SourceOccurrenceQuery>> {
    let alternatives = query
        .split('|')
        .map(str::trim)
        .filter(|alternative| !alternative.is_empty())
        .collect::<Vec<_>>();
    if alternatives.len() > 1 {
        let parsed = alternatives
            .iter()
            .map(|alternative| parse_source_occurrence_query(root, cwd, main_root, alternative))
            .collect::<Result<Vec<_>>>()?;
        if parsed.iter().all(Option::is_some) {
            let mut parsed = parsed.into_iter().flatten();
            let mut combined = parsed.next().expect("multiple parsed alternatives");
            for alternative in parsed {
                ensure!(
                    alternative.path == combined.path,
                    "source queries accept one Lean file; search each file separately"
                );
                if (alternative.first_line, alternative.last_line)
                    == (combined.first_line, combined.last_line)
                {
                    combined.terms.extend(alternative.terms);
                } else {
                    ensure!(
                        combined.terms.is_empty() && alternative.terms.is_empty(),
                        "source alternatives with terms must use one line range"
                    );
                    combined
                        .additional_ranges
                        .push((alternative.first_line, alternative.last_line));
                    combined
                        .additional_ranges
                        .extend(alternative.additional_ranges);
                }
            }
            combined.terms.sort();
            combined.terms.dedup();
            let mut ranges = vec![(combined.first_line, combined.last_line)];
            ranges.append(&mut combined.additional_ranges);
            ranges.sort_unstable();
            ranges.dedup();
            (combined.first_line, combined.last_line) = ranges.remove(0);
            combined.additional_ranges = ranges;
            return Ok(Some(combined));
        }
    }
    let parts = query
        .split(|character: char| character.is_whitespace() || character == '|')
        .filter(|part| !part.is_empty())
        .collect::<Vec<_>>();
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
            Path::new(path)
                .extension()
                .and_then(|extension| extension.to_str())
                == Some("lean")
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
        if Path::new(target)
            .extension()
            .and_then(|extension| extension.to_str())
            == Some("lean")
        {
            bail!(
                "source file query needs a line, range, or facet: {target}; use {target}:LINE, {target}:START-END, or {target} outline/imports/dependents"
            );
        }
        return Ok(None);
    }
    let requested_path = path;
    let inferred_outline_path = Path::new(path).extension().is_none()
        && terms.len() == 1
        && matches!(
            terms[0].to_ascii_lowercase().as_str(),
            "outline" | "declarations"
        );
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
    let Some((path, display_path, _)) = resolve_source_path(root, cwd, &resolved_path)? else {
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
        resolve_source_path(main_root, main_root, &resolved_path)?.map(|(path, _, _)| path)
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
        additional_ranges: Vec::new(),
        terms,
    }))
}

pub(super) fn parse_source_line_range(range: &str) -> Option<(u64, u64)> {
    let (first, last) = range.split_once('-')?;
    let first = first.parse().ok()?;
    let last = last.parse().ok()?;
    (first > 0 && first <= last).then_some((first, last))
}

pub(super) fn reject_colon_attached_source_facet(query: &str) -> Result<()> {
    for token in query.split_whitespace() {
        let Some((path, facet)) = token.rsplit_once(':') else {
            continue;
        };
        if Path::new(path)
            .extension()
            .and_then(|extension| extension.to_str())
            == Some("lean")
            && matches!(
                facet.to_ascii_lowercase().as_str(),
                "outline" | "declarations" | "imports" | "dependents"
            )
        {
            bail!("source facets use a space: {path} {facet}");
        }
    }
    Ok(())
}

pub(super) fn source_occurrence_result(
    workspace: &Workspace,
    query: SourceOccurrenceQuery,
    all: bool,
) -> Result<SearchResult> {
    let source = fs::read_to_string(&query.path)?;
    if query.terms.len() == 1
        && matches!(
            query.terms[0].to_ascii_lowercase().as_str(),
            "outline" | "declarations"
        )
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
            let in_range = (number >= query.first_line && number <= query.last_line)
                || query
                    .additional_ranges
                    .iter()
                    .any(|(first, last)| number >= *first && number <= *last);
            let trimmed = line.trim_start();
            let is_import = trimmed.starts_with("import ") || trimmed.starts_with("public import ");
            (in_range
                && if import_query {
                    is_import
                        && (match_terms.is_empty()
                            || match_terms.iter().any(|term| line.contains(*term)))
                } else {
                    query.terms.is_empty() || query.terms.iter().any(|term| line.contains(term))
                })
            .then_some((number, line))
        })
        .collect::<Vec<_>>();
    let limit = if all && query.terms.is_empty() {
        SOURCE_RANGE_ALL_LIMIT
    } else if all {
        SOURCE_OCCURRENCE_ALL_LIMIT
    } else if query.terms.is_empty() {
        SOURCE_RANGE_LIMIT
    } else {
        SOURCE_OCCURRENCE_LIMIT
    };
    let relative = query.display_path.unwrap_or_else(|| {
        query
            .path
            .strip_prefix(&workspace.path)
            .unwrap_or(&query.path)
            .to_string_lossy()
            .into_owned()
    });
    let continuation_path = relative.clone();
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
    let (hits, omitted, omitted_groups) = if query.terms.is_empty() || import_query {
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
        let spans = declaration_spans(&source, &project_module_name(&workspace.path, &query.path));
        let enclosing = matches
            .first()
            .and_then(|(line, _)| enclosing_declaration_span(&spans, *line));
        let signature = enclosing.map_or_else(
            || {
                if import_query {
                    format!("{} for {terms_label}", matches.len())
                } else {
                    format!("{} lines", matches.len())
                }
            },
            |span| {
                format!(
                    "{} lines; inside {} lines {}-{}",
                    matches.len(),
                    span.name,
                    span.start,
                    span.end
                )
            },
        );
        let hits = (!matches.is_empty())
            .then(|| SearchHit {
                name: enclosing
                    .map_or("source", |span| span.name.as_str())
                    .to_owned(),
                kind: "source-range".into(),
                signature: Some(signature),
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
        (hits, matches.len().saturating_sub(limit), 0)
    } else {
        let spans = declaration_spans(&source, &project_module_name(&workspace.path, &query.path));
        let mut groups = Vec::new();
        for (line, source) in &matches {
            add_source_match_group(&mut groups, &relative, &spans, *line, source);
        }
        let group_limit = if all { SOURCE_OCCURRENCE_LIMIT } else { 12 };
        let omitted_groups = groups.len().saturating_sub(group_limit);
        groups.truncate(group_limit);
        let displayed = groups.iter().map(|group| group.count).sum::<usize>();
        let omitted = matches.len().saturating_sub(displayed);
        (
            groups.into_iter().map(SourceMatchGroup::into_hit).collect(),
            omitted,
            omitted_groups,
        )
    };
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
                    let next_line = matches.get(limit).map_or(
                        query.first_line.saturating_add(limit as u64),
                        |(line, _)| *line,
                    );
                    format!(
                        "+{omitted} lines omitted; next: mathmux search {continuation_path}:{next_line}-{}",
                        query.last_line
                    )
                }
            } else {
                format!(
                    "+{omitted} matches in {omitted_groups} declarations omitted; narrow the query"
                )
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

pub(super) fn parse_source_location(
    root: &Path,
    cwd: &Path,
    main_root: Option<&Path>,
    query: &str,
) -> Result<Option<SourceLocation>> {
    let expanded = false;
    let mut location_tokens = query
        .split_whitespace()
        .filter(|token| is_source_location_token(token));
    let query = match (location_tokens.next(), location_tokens.next()) {
        (Some(token), None) => token,
        _ => query,
    };
    if query
        .rsplit_once(':')
        .and_then(|(prefix, column)| {
            column
                .parse::<u64>()
                .ok()
                .and_then(|_| prefix.rsplit_once(':'))
        })
        .is_some_and(|(_, line)| line.parse::<u64>().is_ok())
    {
        bail!("positions use FILE:LINE; columns are not supported");
    }
    if let Some((path, suffix)) = query.rsplit_once(':')
        && suffix.eq_ignore_ascii_case("tail")
    {
        let Some((path, display_path, _)) = resolve_source_path(root, cwd, path)? else {
            bail!(missing_source_message(root, main_root, path)?);
        };
        let line = fs::read_to_string(&path)?.lines().count().max(1) as u64;
        return Ok(Some(SourceLocation {
            path,
            display_path,
            line,
            tail: true,
            expanded,
        }));
    }
    let Some((path, line)) = query.rsplit_once(':') else {
        return Ok(None);
    };
    let Ok(line) = line.parse::<u64>() else {
        return Ok(None);
    };
    let Some((path, display_path, _)) = resolve_source_path(root, cwd, path)? else {
        bail!(missing_source_message(root, main_root, path)?);
    };
    ensure!(line > 0, "source line starts at 1");
    Ok(Some(SourceLocation {
        path,
        display_path,
        line,
        tail: false,
        expanded,
    }))
}

fn is_source_location_token(token: &str) -> bool {
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
    Path::new(path)
        .extension()
        .and_then(|extension| extension.to_str())
        == Some("lean")
}

pub(super) fn missing_source_message(
    root: &Path,
    main_root: Option<&Path>,
    requested: &str,
) -> Result<String> {
    let Some(main_root) = main_root else {
        return Ok(missing_source_with_nearby(root, requested));
    };
    if fs::canonicalize(root).ok() == fs::canonicalize(main_root).ok() {
        return Ok(missing_source_with_nearby(root, requested));
    }
    let requested_name = Path::new(requested).file_name();
    let workspace_has_same_name = requested_name.is_some_and(|requested_name| {
        project_lean_files(root)
            .iter()
            .any(|path| path.file_name() == Some(requested_name))
    });
    if !workspace_has_same_name && resolve_source_path(main_root, main_root, requested)?.is_some() {
        return Ok("source file is on managed main; run mathmux sync".into());
    }
    Ok(missing_source_with_nearby(root, requested))
}

fn missing_source_with_nearby(root: &Path, requested: &str) -> String {
    let mut message = format!("source file not found or ambiguous: {requested}");
    let nearby = nearby_source_paths(root, requested);
    if !nearby.is_empty() {
        message.push_str("\nnearby sources:");
        for path in nearby {
            message.push_str(&format!("\n  {path}"));
        }
    }
    message
}

fn nearby_source_paths(root: &Path, requested: &str) -> Vec<String> {
    let Some(requested) = source_request_path(requested) else {
        return Vec::new();
    };
    let requested_stem = requested
        .file_stem()
        .and_then(|stem| stem.to_str())
        .unwrap_or_default();
    let requested_parts = identifier_query_parts(requested_stem);
    let requested_lower = requested_stem.to_lowercase();
    let mut candidates = project_lean_files(root)
        .into_iter()
        .filter_map(|candidate| {
            let stem = candidate.file_stem()?.to_str()?;
            let parts = identifier_query_parts(stem);
            let shared = requested_parts
                .iter()
                .filter(|part| parts.contains(part))
                .count();
            let distance = edit_distance(&requested_lower, &stem.to_lowercase());
            let related_parts =
                requested_parts.len() >= 2 && shared.saturating_add(1) >= requested_parts.len();
            let close_name = distance <= 2.max(requested_lower.chars().count() / 5);
            if !related_parts && !close_name {
                return None;
            }
            let same_directory = candidate.parent() == requested.parent();
            Some((same_directory, shared, distance, candidate))
        })
        .collect::<Vec<_>>();
    candidates.sort_by(|left, right| {
        right
            .0
            .cmp(&left.0)
            .then_with(|| right.1.cmp(&left.1))
            .then_with(|| left.2.cmp(&right.2))
            .then_with(|| left.3.cmp(&right.3))
    });
    candidates
        .into_iter()
        .take(5)
        .map(|(_, _, _, path)| path.to_string_lossy().into_owned())
        .collect()
}

fn source_request_path(display: &str) -> Option<PathBuf> {
    let path = Path::new(display);
    if !display.contains(['/', '\\'])
        && display.contains('.')
        && path.extension().is_none_or(|extension| extension != "lean")
    {
        Some(PathBuf::from(format!("{}.lean", display.replace('.', "/"))))
    } else if path.extension().is_none() {
        Some(PathBuf::from(format!("{display}.lean")))
    } else {
        (path.extension()? == "lean").then(|| path.to_path_buf())
    }
}

pub(super) fn resolve_source_path(
    root: &Path,
    cwd: &Path,
    path: &str,
) -> Result<Option<(PathBuf, Option<String>, bool)>> {
    let display = path.strip_prefix("<dependency>/").unwrap_or(path);
    let Some(requested) = source_request_path(display) else {
        return Ok(None);
    };
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
    let project_files = std::cell::OnceCell::new();
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
    for variant in variants
        .iter()
        .filter(|variant| requested_components == 1 || variant.components().count() > 1)
    {
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
        let files = project_files.get_or_init(|| project_lean_files(&root));
        let mut matches = files
            .iter()
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
        let files = project_files.get_or_init(|| project_lean_files(&root));
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
                    name.to_string_lossy().eq_ignore_ascii_case(&requested_name)
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
    location: &SourceLocation,
    source: &str,
    note: Option<&str>,
    source_only: bool,
) -> SearchResult {
    let relative = location.display_path.clone().unwrap_or_else(|| {
        location
            .path
            .strip_prefix(&workspace.path)
            .unwrap_or(&location.path)
            .to_string_lossy()
            .into_owned()
    });
    let module = project_module_name(&workspace.path, &location.path);
    let spans = declaration_spans(source, &module);
    let enclosing = enclosing_declaration_span(&spans, location.line);
    let line_limit = if location.expanded {
        LOCATION_EXPANDED_LINES
    } else if location.tail {
        SOURCE_PREVIEW_LINES
    } else {
        LOCATION_PREVIEW_LINES
    };
    let (shown_start, shown_end) = location_excerpt_bounds(source, location.line, line_limit);
    SearchResult {
        hits: vec![SearchHit {
            name: enclosing
                .map_or("source", |span| span.name.as_str())
                .to_owned(),
            kind: if location.expanded {
                "location-expanded"
            } else {
                "location"
            }
            .into(),
            signature: Some(enclosing.map_or_else(
                || format!("showing lines {shown_start}-{shown_end}"),
                |span| {
                    format!(
                        "inside {} lines {}-{}; showing {}-{}",
                        span.kind, span.start, span.end, shown_start, shown_end
                    )
                },
            )),
            module: String::new(),
            path: relative,
            line: location.line,
            doc: None,
            source: nonempty(location_source_excerpt(source, location.line, line_limit)),
            usages: Vec::new(),
            applicable: false,
            required_import: None,
        }],
        inference: if source_only { "source-only" } else { "source" }.into(),
        note: note.map(Into::into),
        ok: true,
    }
}

fn location_excerpt_bounds(source: &str, requested_line: u64, line_limit: usize) -> (u64, u64) {
    let line_count = source.lines().count();
    if line_count == 0 {
        return (0, 0);
    }
    let target = requested_line
        .saturating_sub(1)
        .min(line_count.saturating_sub(1) as u64) as usize;
    let start = target
        .saturating_sub(6)
        .min(line_count.saturating_sub(line_limit));
    let end = line_count.min(start + line_limit);
    (start as u64 + 1, end as u64)
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
