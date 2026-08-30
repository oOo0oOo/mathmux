use super::*;

pub(super) struct SourceEntry {
    pub(super) line: u64,
    pub(super) name: String,
    pub(super) kind: String,
    pub(super) signature: String,
    pub(super) docs: String,
    pub(super) body: String,
}

#[derive(Debug, Clone)]
pub(super) struct DeclarationSpan {
    pub(super) start: u64,
    pub(super) end: u64,
    pub(super) name: String,
    pub(super) kind: String,
    pub(super) signature: String,
}

pub(super) fn declaration_spans(source: &str, module: &str) -> Vec<DeclarationSpan> {
    let last_line = source.lines().count().max(1) as u64;
    let mut entries = parse_source(source, module)
        .into_iter()
        .filter(|entry| {
            !matches!(
                entry.kind.as_str(),
                "field"
                    | "file"
                    | "imports"
                    | "notation"
                    | "infix"
                    | "infixl"
                    | "infixr"
                    | "prefix"
                    | "postfix"
            )
        })
        .collect::<Vec<_>>();
    entries.sort_by_key(|entry| entry.line);
    entries.dedup_by(|left, right| left.line == right.line && left.name == right.name);
    entries
        .iter()
        .enumerate()
        .map(|(index, entry)| DeclarationSpan {
            start: entry.line,
            end: entries
                .get(index + 1)
                .map_or(last_line, |next| next.line.saturating_sub(1))
                .max(entry.line),
            name: entry.name.clone(),
            kind: entry.kind.clone(),
            signature: entry.signature.clone(),
        })
        .collect()
}

pub(super) fn enclosing_declaration_span(
    spans: &[DeclarationSpan],
    line: u64,
) -> Option<&DeclarationSpan> {
    spans
        .iter()
        .rev()
        .find(|span| line >= span.start && line <= span.end)
}

pub(super) fn source_entry_is_private(entry: &SourceEntry) -> bool {
    entry.body.lines().any(|line| {
        let line = line.trim_start();
        line.starts_with("private ") && line.split_whitespace().any(|word| word == entry.kind)
    })
}

pub(super) fn submission_entry_score(entry: &SourceEntry, tokens: &[String]) -> usize {
    let searchable = format!("{} {} {}", entry.name, entry.signature, entry.docs).to_lowercase();
    tokens
        .iter()
        .filter(|token| searchable.contains(token.as_str()))
        .map(String::len)
        .sum()
}

fn mask_comments(source: &str) -> String {
    let bytes = source.as_bytes();
    let mut masked = bytes.to_vec();
    let mut block_depth = 0;
    let mut line_comment = false;
    let mut string = false;
    let mut escaped = false;
    let mut index = 0;
    while index < bytes.len() {
        if line_comment {
            if bytes[index] == b'\n' {
                line_comment = false;
            } else {
                masked[index] = b' ';
            }
            index += 1;
            continue;
        }
        if block_depth > 0 {
            if bytes[index..].starts_with(b"/-") {
                masked[index..index + 2].fill(b' ');
                block_depth += 1;
                index += 2;
            } else if bytes[index..].starts_with(b"-/") {
                masked[index..index + 2].fill(b' ');
                block_depth -= 1;
                index += 2;
            } else {
                if bytes[index] != b'\n' {
                    masked[index] = b' ';
                }
                index += 1;
            }
            continue;
        }
        if string {
            if escaped {
                escaped = false;
            } else if bytes[index] == b'\\' {
                escaped = true;
            } else if bytes[index] == b'"' {
                string = false;
            }
            index += 1;
            continue;
        }
        if bytes[index..].starts_with(b"--") {
            masked[index..index + 2].fill(b' ');
            line_comment = true;
            index += 2;
        } else if bytes[index..].starts_with(b"/-") {
            masked[index..index + 2].fill(b' ');
            block_depth = 1;
            index += 2;
        } else {
            string = bytes[index] == b'"';
            index += 1;
        }
    }
    String::from_utf8(masked).expect("masking preserves UTF-8")
}

pub(super) fn parse_source(source: &str, module: &str) -> Vec<SourceEntry> {
    let code = mask_comments(source);
    let declaration = declaration_regex();
    let matches = declaration.captures_iter(&code).collect::<Vec<_>>();
    let lines = line_starts(source);
    let namespaces = namespaces_by_line(&code);
    let contexts = ambient_contexts_by_line(&code);
    let mut entries = Vec::new();
    for (index, capture) in matches.iter().enumerate() {
        let complete = capture.get(0).expect("declaration match");
        let kind = capture
            .name("kind")
            .map(|value| value.as_str())
            .unwrap_or("declaration");
        let raw_name = capture.name("name").map(|value| value.as_str());
        if raw_name.is_none() && kind != "instance" {
            continue;
        }
        let line = offset_line(&lines, complete.start());
        let end = matches
            .get(index + 1)
            .and_then(|next| next.get(0))
            .map(|next| next.start())
            .unwrap_or(source.len());
        let block = declaration_block(&source[complete.start()..end]);
        let header_end = declaration_header_end(block);
        let header = block[..header_end].trim();
        let name_end = raw_name
            .and_then(|raw_name| header.find(raw_name).map(|start| start + raw_name.len()))
            .or_else(|| header.find(kind).map(|start| start + kind.len()))
            .unwrap_or(header.len());
        let mut signature = header[name_end..]
            .trim()
            .trim_start_matches(':')
            .trim()
            .to_owned();
        if signature.is_empty()
            && matches!(kind, "abbrev" | "def")
            && let Some(value) = block[header_end..].strip_prefix(":=")
            && let Some(value) = value.lines().next()
        {
            signature = format!(":= {}", value.trim());
        }
        if block.lines().next().is_some_and(|line| {
            line.split_whitespace()
                .take_while(|word| *word != kind)
                .any(|word| word == "private")
        }) {
            signature = format!("[private] {signature}");
        }
        let namespace = namespaces
            .get(line.saturating_sub(1))
            .cloned()
            .unwrap_or_default();
        let name = match raw_name {
            Some(raw_name) if raw_name.starts_with("_root_.") || namespace.is_empty() => {
                raw_name.to_owned()
            }
            Some(raw_name) => format!("{}.{}", namespace.join("."), raw_name),
            None if namespace.is_empty() => format!("instance@{line}"),
            None => format!("{}.instance@{line}", namespace.join(".")),
        };
        if matches!(kind, "class" | "structure")
            && let Some(projection) = generated_parent_projection(&name, &signature)
        {
            signature.push_str(&format!("; generated parent projection: {projection}"));
        }
        let context = contexts
            .get(line.saturating_sub(1))
            .cloned()
            .unwrap_or_default();
        let body = if context.is_empty() {
            block.to_owned()
        } else {
            format!("-- ambient context\n{}\n\n{block}", context.join("\n"))
        };
        entries.push(SourceEntry {
            line: line as u64,
            name,
            kind: kind.to_owned(),
            signature: single_line(&signature),
            docs: preceding_doc(source, complete.start()).unwrap_or_default(),
            body: body.chars().take(16_000).collect(),
        });
        if matches!(kind, "class" | "structure") {
            entries.extend(parse_structure_fields(
                block,
                &entries.last().expect("structure entry").name,
                line as u64,
            ));
        }
    }
    entries.extend(parse_notations(source, &code, &lines, &namespaces));
    let imports = code
        .lines()
        .zip(source.lines())
        .enumerate()
        .filter(|(_, (line, _))| {
            let line = line.trim_start();
            line.starts_with("import ") || line.starts_with("public import ")
        })
        .map(|(line, (_, original))| (line, original))
        .collect::<Vec<_>>();
    if let Some((first, _)) = imports.first() {
        entries.push(SourceEntry {
            line: (*first + 1) as u64,
            name: format!("{module}.imports"),
            kind: "imports".into(),
            signature: format!("{} imports", imports.len()),
            docs: String::new(),
            body: imports
                .into_iter()
                .map(|(_, line)| line.trim())
                .collect::<Vec<_>>()
                .join("\n"),
        });
    }
    entries.push(SourceEntry {
        line: 1,
        name: module.to_owned(),
        kind: "file".into(),
        signature: String::new(),
        docs: String::new(),
        body: source.chars().take(256_000).collect(),
    });
    entries
}

pub(super) fn parse_structure_fields(
    block: &str,
    structure: &str,
    structure_line: u64,
) -> Vec<SourceEntry> {
    let header_end = declaration_header_end(block);
    let Some(body_start) = block[header_end..]
        .strip_prefix("where")
        .map(|_| header_end + "where".len())
    else {
        return Vec::new();
    };
    let body_end = block[body_start..]
        .match_indices('\n')
        .filter_map(|(newline, _)| {
            let offset = body_start + newline + 1;
            let line = block[offset..].lines().next().unwrap_or_default();
            (!line.trim().is_empty() && line.len() == line.trim_start().len()).then_some(offset)
        })
        .next()
        .unwrap_or(block.len());
    let field_block = &block[..body_end];
    let mut fields = field_block[body_start..]
        .match_indices('\n')
        .filter_map(|(newline, _)| {
            let offset = body_start + newline + 1;
            let line = block[offset..].lines().next().unwrap_or_default();
            structure_field_header(line)
                .map(|(indent, name_end, name)| (offset, indent, name_end, name.to_owned()))
        })
        .collect::<Vec<_>>();
    let Some(field_indent) = fields.iter().map(|(_, indent, _, _)| *indent).min() else {
        return Vec::new();
    };
    fields.retain(|(_, indent, _, _)| *indent == field_indent);
    fields
        .iter()
        .enumerate()
        .map(|(index, (offset, _, name_end, name))| {
            let end = fields
                .get(index + 1)
                .map(|(offset, _, _, _)| *offset)
                .unwrap_or(field_block.len());
            let mut field = field_block[*offset..end].trim_end();
            if let Some(doc) = field.rfind("/--")
                && field[doc..].contains("-/")
            {
                field = field[..doc].trim_end();
            }
            let signature = field
                .get(*name_end..)
                .unwrap_or_default()
                .trim()
                .trim_start_matches(':')
                .trim();
            SourceEntry {
                line: structure_line + block[..*offset].matches('\n').count() as u64,
                name: format!("{structure}.{name}"),
                kind: "field".into(),
                signature: single_line(signature),
                docs: preceding_doc(block, *offset).unwrap_or_default(),
                body: field.to_owned(),
            }
        })
        .collect()
}

pub(super) fn structure_field_header(line: &str) -> Option<(usize, usize, &str)> {
    let indent = line.len() - line.trim_start_matches([' ', '\t']).len();
    if indent == 0 {
        return None;
    }
    let mut start = indent;
    while line[start..].starts_with("@[") {
        start += line[start..].find(']')? + 1;
        start += line[start..].len() - line[start..].trim_start().len();
    }
    if let Some(rest) = line[start..].strip_prefix("protected ") {
        start = line.len() - rest.len();
    }
    let rest = &line[start..];
    let mut characters = rest.char_indices();
    let (_, first) = characters.next()?;
    if !(first.is_alphabetic() || first == '_') {
        return None;
    }
    let name_end = characters
        .find(|(_, character)| !(character.is_alphanumeric() || matches!(character, '_' | '\'')))
        .map(|(offset, _)| offset)
        .unwrap_or(rest.len());
    let name = &rest[..name_end];
    let mut depth = 0usize;
    let mut has_type = false;
    for (offset, character) in rest[name_end..].char_indices() {
        match character {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth = depth.saturating_sub(1),
            ':' if depth == 0 && !rest[name_end + offset..].starts_with(":=") => {
                has_type = true;
                break;
            }
            _ => {}
        }
    }
    has_type.then_some((indent, start + name_end, name))
}

pub(super) fn parse_notations(
    source: &str,
    code: &str,
    lines: &[usize],
    namespaces: &[Vec<String>],
) -> Vec<SourceEntry> {
    static COMMAND: OnceLock<Regex> = OnceLock::new();
    static LITERAL: OnceLock<Regex> = OnceLock::new();
    let command = COMMAND.get_or_init(|| {
        Regex::new(
            r#"(?m)^[ \t]*(?:(?:scoped|local)[ \t]+)*(?P<kind>notation|infixl|infixr|infix|prefix|postfix)(?::[0-9]+)?(?P<body>[^\n]*)"#,
        )
        .expect("valid notation command regex")
    });
    let literal = LITERAL
        .get_or_init(|| Regex::new(r#"\"([^\"]+)\""#).expect("valid notation literal regex"));
    command
        .captures_iter(code)
        .filter_map(|capture| {
            let complete = capture.get(0)?;
            let notation = literal
                .captures_iter(capture.name("body")?.as_str())
                .filter_map(|literal| literal.get(1))
                .map(|literal| literal.as_str().trim())
                .filter(|literal| !literal.is_empty())
                .collect::<Vec<_>>()
                .join(" ");
            if notation.is_empty() {
                return None;
            }
            let line = offset_line(lines, complete.start());
            let original = &source[complete.start()..complete.end()];
            let namespace = namespaces
                .get(line.saturating_sub(1))
                .cloned()
                .unwrap_or_default();
            let label = format!("notation {notation}");
            Some(SourceEntry {
                line: line as u64,
                name: if namespace.is_empty() {
                    label
                } else {
                    format!("{}.{}", namespace.join("."), label)
                },
                kind: capture.name("kind")?.as_str().to_owned(),
                signature: single_line(original.trim()),
                docs: preceding_doc(source, complete.start()).unwrap_or_default(),
                body: original.trim().to_owned(),
            })
        })
        .collect()
}

pub(super) fn generated_parent_projection(name: &str, signature: &str) -> Option<String> {
    let extension = signature.split_once("extends ")?.1.trim_start();
    let parent = extension
        .split(|character: char| !(character.is_alphanumeric() || matches!(character, '_' | '.')))
        .next()?;
    if parent.is_empty() {
        return None;
    }
    let remainder = extension[parent.len()..].trim_start();
    if remainder.chars().next().is_some_and(|character| {
        !character.is_alphanumeric() && !matches!(character, '(' | '[' | '{')
    }) {
        return None;
    }
    Some(format!("{name}.to{}", parent.replace('.', "")))
}

pub(super) fn declaration_regex() -> &'static Regex {
    static REGEX: OnceLock<Regex> = OnceLock::new();
    REGEX.get_or_init(|| {
        Regex::new(
            r"(?m)^[ \t]*(?:@\[[^\n]*\][ \t]*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)[ \t]+)*(?P<kind>theorem|lemma|def|abbrev|opaque|axiom|structure|class|inductive|instance)[ \t]+(?:\([ \t]*priority[ \t]*:=[^\n)]*\)[ \t]+)?(?P<name>[\p{L}_][\p{L}\p{N}\p{M}_'.]*)?",
        )
        .expect("valid declaration regex")
    })
}

pub(super) fn declaration_header_end(block: &str) -> usize {
    let mut delimiters = Vec::new();
    for (index, character) in block.char_indices() {
        match character {
            '(' | '[' | '{' => delimiters.push(character),
            ')' | ']' | '}' => {
                delimiters.pop();
            }
            ':' if delimiters.is_empty() && block[index..].starts_with(":=") => return index,
            'w' if delimiters.is_empty()
                && block[index..].starts_with("where")
                && block[..index]
                    .chars()
                    .next_back()
                    .is_some_and(char::is_whitespace)
                && block[index + "where".len()..]
                    .chars()
                    .next()
                    .is_none_or(char::is_whitespace) =>
            {
                return index;
            }
            _ => {}
        }
    }
    block.find('\n').unwrap_or(block.len())
}

pub(super) fn declaration_block(block: &str) -> &str {
    let end = block
        .match_indices('\n')
        .map(|(index, _)| index + 1)
        .find(|start| {
            let line = block[*start..].lines().next().unwrap_or_default();
            let trimmed = line.trim_start();
            line.len() == trimmed.len() && (trimmed == "end" || trimmed.starts_with("end "))
        })
        .unwrap_or(block.len());
    block[..end].trim()
}

pub(super) fn namespaces_by_line(source: &str) -> Vec<Vec<String>> {
    let mut scopes: Vec<Option<Vec<String>>> = Vec::new();
    let mut result = Vec::new();
    for line in source.lines() {
        result.push(
            scopes
                .iter()
                .filter_map(Option::as_ref)
                .flatten()
                .cloned()
                .collect(),
        );
        let trimmed = line.trim();
        if let Some(name) = trimmed.strip_prefix("namespace ") {
            if let Some(name) = name.split_whitespace().next() {
                scopes.push(Some(name.split('.').map(str::to_owned).collect()));
            }
        } else if trimmed == "section" || trimmed.starts_with("section ") {
            scopes.push(None);
        } else if trimmed == "end" || trimmed.starts_with("end ") {
            scopes.pop();
        }
    }
    result
}

pub(super) fn ambient_contexts_by_line(source: &str) -> Vec<Vec<String>> {
    let mut scopes = vec![Vec::<String>::new()];
    let mut result = Vec::new();
    for line in source.lines() {
        let flattened = scopes
            .iter()
            .flatten()
            .rev()
            .take(16)
            .cloned()
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect();
        result.push(flattened);
        let trimmed = line.trim();
        if trimmed.starts_with("namespace ") {
            scopes.push(Vec::new());
        } else if trimmed == "section" || trimmed.starts_with("section ") {
            scopes.push(vec![single_line(trimmed)]);
        } else if trimmed == "end" || trimmed.starts_with("end ") {
            if scopes.len() > 1 {
                scopes.pop();
            }
        } else if ["universe ", "variable ", "include ", "omit "]
            .iter()
            .any(|prefix| trimmed.starts_with(prefix))
            && !trimmed.ends_with(" in")
        {
            scopes
                .last_mut()
                .expect("root context scope")
                .push(single_line(trimmed));
        }
    }
    result
}

pub(super) fn preceding_doc(source: &str, offset: usize) -> Option<String> {
    let prefix = &source[..offset];
    let end = prefix.rfind("-/")? + 2;
    let suffix = prefix[end..].trim();
    let separated_only_by_attributes = suffix.chars().all(|character| character == ']')
        || (suffix.starts_with("@[") && suffix.ends_with(']'));
    if !suffix.is_empty() && !separated_only_by_attributes {
        return None;
    }
    let start = prefix[..end].rfind("/--")?;
    Some(
        prefix[start + 3..end - 2]
            .lines()
            .map(|line| line.trim().trim_start_matches('*').trim())
            .collect::<Vec<_>>()
            .join(" "),
    )
}

pub(super) fn line_starts(source: &str) -> Vec<usize> {
    std::iter::once(0)
        .chain(source.match_indices('\n').map(|(index, _)| index + 1))
        .collect()
}

pub(super) fn offset_line(lines: &[usize], offset: usize) -> usize {
    lines.partition_point(|start| *start <= offset).max(1)
}
pub(super) fn source_entry(path: &Path, kind: SourceKind) -> bool {
    let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
        return true;
    };
    match kind {
        SourceKind::Project => !matches!(name, ".git" | ".lake" | "target"),
        SourceKind::Dependency => !matches!(name, ".git" | ".lake" | "target"),
        SourceKind::Stdlib => !matches!(name, ".git" | "build"),
    }
}

pub(super) fn display_path(path: &Path, workspace: &Path, root: &Path, kind: SourceKind) -> String {
    match kind {
        SourceKind::Project | SourceKind::Dependency => path
            .strip_prefix(workspace)
            .or_else(|_| path.strip_prefix(root))
            .unwrap_or(path)
            .to_string_lossy()
            .into_owned(),
        SourceKind::Stdlib => format!(
            "<stdlib>/{}",
            path.strip_prefix(root).unwrap_or(path).display()
        ),
    }
}

pub(super) fn module_name(path: &Path, root: &Path, kind: SourceKind) -> String {
    let relative = path.strip_prefix(root).unwrap_or(path);
    let relative = if matches!(kind, SourceKind::Dependency) {
        let components = relative.components().collect::<Vec<_>>();
        components
            .iter()
            .position(|component| {
                matches!(
                    component.as_os_str().to_str(),
                    Some("Mathlib" | "Batteries" | "Cli" | "Qq" | "Plausible")
                )
            })
            .map(|index| components[index..].iter().collect::<PathBuf>())
            .unwrap_or_else(|| relative.to_path_buf())
    } else {
        relative.to_path_buf()
    };
    let mut module = relative;
    module.set_extension("");
    module
        .components()
        .filter_map(|component| component.as_os_str().to_str())
        .collect::<Vec<_>>()
        .join(".")
}

pub(super) fn shared_owner(label: &str, root: &Path) -> String {
    format!("{label}:{}", hash_bytes(root.to_string_lossy().as_bytes()))
}

pub(super) fn package_scopes(workspace: &Path) -> HashSet<String> {
    let Ok(packages) = fs::canonicalize(workspace.join(".lake/packages")) else {
        return HashSet::new();
    };
    [
        shared_owner("packages", &packages),
        shared_owner("artifact-packages", &packages),
    ]
    .into_iter()
    .collect()
}

pub(super) fn lean_source_root(repo: &Repo, root: &Path) -> Option<PathBuf> {
    let output = lake_command(repo, root)
        .args(["env", "lean", "--print-prefix"])
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let prefix = PathBuf::from(String::from_utf8_lossy(&output.stdout).trim());
    [prefix.join("src/lean"), prefix.join("src/lean4")]
        .into_iter()
        .find(|path| path.is_dir())
}

pub(super) fn modified_ns(metadata: &fs::Metadata) -> i64 {
    metadata
        .modified()
        .ok()
        .and_then(|time| time.duration_since(std::time::UNIX_EPOCH).ok())
        .map(|duration| duration.as_nanos().min(i64::MAX as u128) as i64)
        .unwrap_or(0)
}

pub(super) fn delete_search_origin(
    connection: &Connection,
    owner: &str,
    origin: &str,
) -> Result<()> {
    connection.execute(
        "DELETE FROM search_fts WHERE rowid IN (
            SELECT rowid FROM search_origins WHERE owner = ?1 AND origin = ?2
         )",
        params![owner, origin],
    )?;
    connection.execute(
        "DELETE FROM search_origins WHERE owner = ?1 AND origin = ?2",
        params![owner, origin],
    )?;
    Ok(())
}

pub(super) fn record_file(
    transaction: &rusqlite::Transaction<'_>,
    owner: &str,
    path: &Path,
    kind: &str,
) -> Result<()> {
    let metadata = fs::metadata(path)?;
    transaction.execute(
        "INSERT INTO search_files(owner, path, kind, modified_ns, size)
         VALUES (?1, ?2, ?3, ?4, ?5)
         ON CONFLICT(owner, path, kind) DO UPDATE SET
            modified_ns = excluded.modified_ns, size = excluded.size",
        params![
            owner,
            path.to_string_lossy(),
            kind,
            modified_ns(&metadata),
            metadata.len() as i64,
        ],
    )?;
    Ok(())
}

pub(super) fn reference_name(encoded: &str) -> Option<String> {
    serde_json::from_str::<Value>(encoded)
        .ok()?
        .get("c")?
        .get("n")?
        .as_str()
        .map(str::to_owned)
}

pub(super) fn generated_ilean_declarations(value: &Value) -> Vec<(String, u64)> {
    // Generated aliases (notably `to_additive` names) have no entry in `decls`;
    // their reference record still carries the declaration range.
    let declarations = value.get("decls").and_then(Value::as_object);
    let Some(references) = value.get("references").and_then(Value::as_object) else {
        return Vec::new();
    };
    let mut names = HashSet::new();
    let mut generated = references
        .iter()
        .filter_map(|(encoded, reference)| {
            let name = reference_name(encoded)?;
            if declarations.is_some_and(|declarations| declarations.contains_key(&name))
                || !indexable_declaration_name(&name)
            {
                return None;
            }
            let line = reference.get("definition")?.as_array()?.first()?.as_u64()? + 1;
            names.insert(name.clone()).then_some((name, line))
        })
        .collect::<Vec<_>>();
    generated.sort();
    generated
}

fn indexable_declaration_name(name: &str) -> bool {
    !name.is_empty()
        && !name.starts_with('.')
        && !name.ends_with('.')
        && name.split('.').all(|part| {
            !part.is_empty()
                && part
                    .chars()
                    .all(|character| character.is_alphanumeric() || matches!(character, '_' | '\''))
        })
}

pub(super) fn reference_display_path(module: &str, workspace: &Workspace) -> String {
    let relative = PathBuf::from(format!("{}.lean", module.replace('.', "/")));
    if workspace.path.join(&relative).is_file() {
        relative.to_string_lossy().into_owned()
    } else {
        format!("<dependency>/{}", relative.display())
    }
}

pub(super) fn source_excerpt_with_limit(
    source: &str,
    query: &str,
    tokens: &[String],
    declaration_line: u64,
    file_hit: bool,
    line_limit: usize,
) -> (Option<String>, u64) {
    if source.trim().is_empty() {
        return (None, declaration_line);
    }
    let lines = source.lines().collect::<Vec<_>>();
    let query = query.to_lowercase();
    let matched = lines
        .iter()
        .position(|line| line.to_lowercase().contains(&query))
        .or_else(|| best_source_match(&lines, tokens))
        .unwrap_or(0);
    if file_hit && let Some(excerpt) = dispersed_file_excerpt(&lines, tokens, matched, line_limit) {
        return (Some(excerpt), matched as u64 + 1);
    }
    let start = matched.saturating_sub(2);
    let excerpt = lines[start..lines.len().min(start + line_limit)].join("\n");
    let line = if file_hit {
        matched as u64 + 1
    } else {
        declaration_line
    };
    (nonempty(excerpt), line)
}

pub(super) fn dispersed_file_excerpt(
    lines: &[&str],
    tokens: &[String],
    primary: usize,
    line_limit: usize,
) -> Option<String> {
    let preview_limit = line_limit.min(SOURCE_PREVIEW_LINES);
    if preview_limit < 8 || tokens.len() < 2 {
        return None;
    }
    let lowered = lines
        .iter()
        .map(|line| line.to_lowercase())
        .collect::<Vec<_>>();
    let primary_start = primary.saturating_sub(2);
    let primary_end = lowered.len().min(primary_start + preview_limit);
    let uncovered = tokens
        .iter()
        .filter(|token| {
            lowered[primary_start..primary_end]
                .iter()
                .all(|line| !line.contains(token.as_str()))
        })
        .cloned()
        .collect::<Vec<_>>();
    let secondary = best_source_match(lines, &uncovered)?;
    if (primary_start..primary_end).contains(&secondary) {
        return None;
    }

    let window_lines = preview_limit.saturating_sub(3) / 2;
    let render_window = |center: usize| {
        let start = center.saturating_sub(1);
        let end = lines.len().min(start + window_lines);
        format!(
            "[lines {}-{}]\n{}",
            start + 1,
            end,
            lines[start..end].join("\n")
        )
    };
    Some(format!(
        "{}\n…\n{}",
        render_window(primary),
        render_window(secondary)
    ))
}

pub(super) fn best_source_match(lines: &[&str], tokens: &[String]) -> Option<usize> {
    const MATCH_CONTEXT_LINES: usize = 16;
    let lowered = lines
        .iter()
        .map(|line| line.to_lowercase())
        .collect::<Vec<_>>();
    let mut best = None;
    for (index, line) in lowered.iter().enumerate() {
        if !tokens.iter().any(|token| line.contains(token)) {
            continue;
        }
        let start = index.saturating_sub(2);
        let end = lowered.len().min(start + MATCH_CONTEXT_LINES);
        let score = tokens
            .iter()
            .filter(|token| lowered[start..end].iter().any(|line| line.contains(*token)))
            .count();
        if best.is_none_or(|(_, best_score)| score > best_score) {
            best = Some((index, score));
        }
    }
    best.map(|(index, _)| index)
}

pub(super) fn detailed_source_excerpt(
    body: &str,
    query: &str,
    tokens: &[String],
    declaration_line: u64,
    kind: &str,
    name: &str,
) -> (Option<String>, u64) {
    if matches!(kind, "class" | "inductive" | "structure") {
        let declaration = body
            .split("\n\n/--")
            .next()
            .unwrap_or(body)
            .split("\n\n/-!")
            .next()
            .unwrap_or(body);
        let excerpt = declaration
            .lines()
            .take(DECLARATION_DETAIL_LINES)
            .collect::<Vec<_>>()
            .join("\n");
        return (nonempty(excerpt), declaration_line);
    }
    if kind == "imports" {
        let excerpt = body.lines().take(64).collect::<Vec<_>>().join("\n");
        return (nonempty(excerpt), declaration_line);
    }
    let name = name.to_lowercase();
    let leaf = name.rsplit('.').next().unwrap_or(&name);
    if body.starts_with("-- ambient context")
        && (query.eq_ignore_ascii_case(&name) || query.eq_ignore_ascii_case(leaf))
    {
        let excerpt = body
            .lines()
            .take(DECLARATION_DETAIL_LINES)
            .collect::<Vec<_>>()
            .join("\n");
        return (nonempty(excerpt), declaration_line);
    }
    let focused_tokens = tokens
        .iter()
        .filter(|token| token.as_str() != name && token.as_str() != leaf)
        .cloned()
        .collect::<Vec<_>>();
    let body_lines = body.lines().collect::<Vec<_>>();
    let focused_tokens =
        if focused_tokens.is_empty() || best_source_match(&body_lines, &focused_tokens).is_none() {
            tokens
        } else {
            &focused_tokens
        };
    source_excerpt_with_limit(
        body,
        query,
        focused_tokens,
        declaration_line,
        kind == "file",
        DECLARATION_DETAIL_LINES,
    )
}

pub(super) fn fallback_source_candidates(
    workspace: &Path,
    query: &str,
    query_tokens: &[String],
) -> Result<Vec<Candidate>> {
    let started = Instant::now();
    let scan_deadline = started + SOURCE_SCAN_BUDGET;
    let fallback_deadline = started + SOURCE_FALLBACK_BUDGET;
    let workspace = fs::canonicalize(workspace)?;
    let packages = fs::canonicalize(workspace.join(".lake/packages")).ok();
    let symbolic_term = symbolic_source_term(query);
    let mut terms = symbolic_term.iter().cloned().collect::<Vec<_>>();
    if symbolic_term.is_none() {
        terms.extend(
            query_tokens
                .iter()
                .flat_map(|token| std::iter::once(token.as_str()).chain(token.split(['.', '_'])))
                .map(str::to_lowercase)
                .filter(|term| {
                    term.len() >= 3
                        && !matches!(
                            term.as_str(),
                            "class"
                                | "constructor"
                                | "constructors"
                                | "def"
                                | "instance"
                                | "lemma"
                                | "name"
                                | "structure"
                                | "theorem"
                        )
                }),
        );
    }
    let named_argument_terms = named_argument_terms(query);
    terms.extend(named_argument_terms.iter().cloned());
    for term in terms.clone() {
        for suffix in ["_symm_apply", "_apply"] {
            if let Some(stem) = term.strip_suffix(suffix)
                && stem.len() >= 3
            {
                terms.push(stem.to_owned());
            }
        }
        if let Some(alias) = match term.as_str() {
            "addition" => Some("add"),
            "continuity" => Some("continuous"),
            "islinear" => Some("linear"),
            "positive" => Some("pos"),
            "projection" => Some("proj"),
            "scaling" => Some("smul"),
            "trivializationat" => Some("trivialization"),
            "weighted" => Some("weight"),
            _ => None,
        } {
            terms.push(alias.to_owned());
        }
    }
    terms.sort();
    terms.dedup();
    if terms.is_empty() {
        return Ok(Vec::new());
    }
    let mut scanned =
        source_scan_path_counts(&workspace, packages.as_deref(), &terms, scan_deadline)?;
    scanned.sort_by(|(left_path, left_score), (right_path, right_score)| {
        right_score.cmp(left_score).then_with(|| {
            let left_dependency = packages
                .as_ref()
                .is_some_and(|packages| left_path.starts_with(packages));
            let right_dependency = packages
                .as_ref()
                .is_some_and(|packages| right_path.starts_with(packages));
            left_dependency
                .cmp(&right_dependency)
                .then_with(|| left_path.cmp(right_path))
        })
    });
    let mut paths = direct_module_paths(&workspace, packages.as_deref(), query);
    let direct_path_set = paths.iter().cloned().collect::<HashSet<_>>();
    let mut seen_paths = paths.iter().cloned().collect::<HashSet<_>>();
    for (path, _) in scanned {
        if seen_paths.insert(path.clone()) {
            paths.push(path);
        }
    }
    let mut ranked = Vec::new();
    let imports_query = query_tokens
        .iter()
        .any(|token| matches!(token.as_str(), "import" | "imports"));
    'paths: for path in paths
        .into_iter()
        .take(SEARCH_TUNING.retrieval.fallback_paths)
    {
        if Instant::now() >= fallback_deadline {
            break;
        }
        let path = if path.is_absolute() {
            path
        } else {
            workspace.join(path)
        };
        let source = fs::read_to_string(&path)?;
        let source_lower = source.to_lowercase();
        let file_coverage = terms
            .iter()
            .filter(|term| source_lower.contains(*term))
            .count();
        let (root, kind) = packages
            .as_ref()
            .filter(|packages| path.starts_with(packages))
            .map(|packages| (packages.as_path(), SourceKind::Dependency))
            .unwrap_or((workspace.as_path(), SourceKind::Project));
        let module = module_name(&path, root, kind);
        for entry in parse_source(&source, &module) {
            if Instant::now() >= fallback_deadline {
                break 'paths;
            }
            let searchable =
                format!("{} {} {}", entry.name, entry.signature, entry.body).to_lowercase();
            let score = terms
                .iter()
                .filter(|term| searchable.contains(*term))
                .count();
            if score == 0 {
                continue;
            }
            let named_argument_score = named_argument_terms
                .iter()
                .filter(|term| entry.signature.to_lowercase().contains(*term))
                .count();
            let symbolic_name_match = symbolic_term
                .as_ref()
                .is_some_and(|term| entry.name.to_lowercase().contains(term));
            let is_file = entry.kind == "file";
            let is_direct_path = direct_path_set.contains(&path);
            let is_imports = entry.kind == "imports";
            let display_path = display_path(&path, &workspace, root, kind);
            let row = IndexedRow {
                owner: String::new(),
                path: display_path.clone(),
                module: module.clone(),
                line: entry.line,
                name: entry.name,
                kind: entry.kind,
                signature: entry.signature,
                docs: entry.docs,
                body: entry.body,
                rank: 0.0,
            };
            let (excerpt, matched_line) =
                detailed_source_excerpt(&row.body, query, &terms, row.line, &row.kind, &row.name);
            let score = lexical_score(query, query_tokens, &row)
                + named_argument_score as f64 * SEARCH_TUNING.source.fallback_named_argument
                + if symbolic_name_match {
                    SEARCH_TUNING.source.fallback_symbolic_name
                } else {
                    0.0
                }
                + if is_direct_path {
                    SEARCH_TUNING.source.fallback_direct_path
                } else {
                    0.0
                }
                + if is_imports && imports_query {
                    SEARCH_TUNING.source.fallback_imports
                } else {
                    0.0
                }
                + file_coverage as f64 * SEARCH_TUNING.source.fallback_file_coverage;
            ranked.push(Candidate {
                hit: SearchHit {
                    name: row.name,
                    kind: row.kind,
                    signature: if is_file {
                        file_query_coverage_signature(&source_lower, query_tokens)
                    } else {
                        nonempty(row.signature)
                    },
                    module: row.module,
                    path: display_path,
                    line: matched_line,
                    doc: nonempty(row.docs),
                    source: excerpt,
                    usages: Vec::new(),
                    applicable: false,
                    required_import: None,
                },
                score,
                origins: CandidateOrigin::FallbackSource as u8,
            });
        }
    }
    ranked.sort_by(|left, right| {
        right
            .score
            .partial_cmp(&left.score)
            .unwrap_or(Ordering::Equal)
    });
    ranked.truncate(RESULT_LIMIT * SEARCH_PRESENTATION.fallback_candidate_multiplier);
    Ok(ranked)
}

pub(super) fn file_query_coverage_signature(source: &str, tokens: &[String]) -> Option<String> {
    let mut tokens = tokens.iter().map(String::as_str).collect::<Vec<_>>();
    tokens.sort_unstable();
    tokens.dedup();
    if tokens.len() < 2 {
        return None;
    }
    let missing = tokens
        .iter()
        .filter(|token| !source.contains(**token))
        .copied()
        .collect::<Vec<_>>();
    if missing.is_empty() {
        return None;
    }
    Some(format!(
        "partial source match {}/{}",
        tokens.len() - missing.len(),
        tokens.len()
    ))
}

pub(super) fn symbolic_source_term(query: &str) -> Option<String> {
    let query = query.trim();
    (!query.is_empty()
        && !query.chars().any(char::is_whitespace)
        && (query.chars().count() > 1 || !query.is_ascii())
        && query.chars().any(|character| {
            !character.is_alphanumeric() && !matches!(character, '_' | '.' | '\'')
        }))
    .then(|| query.to_lowercase())
}

pub(super) fn named_argument_terms(query: &str) -> Vec<String> {
    static REGEX: OnceLock<Regex> = OnceLock::new();
    let regex = REGEX.get_or_init(|| {
        Regex::new(r"\(([\p{L}_][\p{L}\p{N}\p{M}_']*)\s*:=").expect("valid named argument regex")
    });
    regex
        .captures_iter(query)
        .filter_map(|capture| capture.get(1))
        .map(|name| format!("({} :", name.as_str().to_lowercase()))
        .collect()
}

pub(super) fn direct_module_paths(
    workspace: &Path,
    packages: Option<&Path>,
    query: &str,
) -> Vec<PathBuf> {
    let mut roots = vec![workspace.to_path_buf()];
    if let Some(packages) = packages
        && let Ok(entries) = fs::read_dir(packages)
    {
        roots.extend(entries.flatten().map(|entry| entry.path()));
    }
    let mut paths = Vec::new();
    let tokens = query
        .split(|character: char| {
            !character.is_alphanumeric() && character != '_' && character != '.'
        })
        .filter(|token| !token.is_empty())
        .collect::<Vec<_>>();
    for token in tokens.iter().filter(|token| token.contains('.')) {
        let relative = if token.ends_with(".lean") {
            PathBuf::from(token)
        } else {
            PathBuf::from(format!("{}.lean", token.replace('.', "/")))
        };
        for root in &roots {
            let candidate = root.join(&relative);
            if candidate.is_file()
                && let Ok(candidate) = fs::canonicalize(candidate)
                && !paths.contains(&candidate)
            {
                paths.push(candidate);
            }
        }
    }
    for path in project_lean_files(workspace) {
        let Some(stem) = path.file_stem().and_then(|stem| stem.to_str()) else {
            continue;
        };
        if tokens.iter().any(|token| stem.eq_ignore_ascii_case(token)) {
            let candidate = workspace.join(path);
            if let Ok(candidate) = fs::canonicalize(candidate)
                && !paths.contains(&candidate)
            {
                paths.push(candidate);
            }
        }
    }
    paths
}

pub(super) fn source_scan_path_counts(
    workspace: &Path,
    packages: Option<&Path>,
    terms: &[String],
    deadline: Instant,
) -> Result<Vec<(PathBuf, usize)>> {
    let Some(timeout) = source_scan_timeout(deadline) else {
        return Ok(Vec::new());
    };
    if terms.is_empty() {
        return Ok(Vec::new());
    }
    let mut command = std::process::Command::new("timeout");
    command.args([
        "--signal=KILL",
        &timeout,
        "rg",
        "-c",
        "-i",
        "-F",
        "--glob",
        "*.lean",
    ]);
    for term in terms {
        command.args(["-e", term]);
    }
    command.arg(workspace);
    if let Some(packages) = packages {
        command.arg(packages);
    }
    let output = command.stdin(Stdio::null()).output()?;
    if !output.status.success() && !matches!(output.status.code(), Some(1 | 124 | 137)) {
        bail!(
            "local source coverage scan failed: {}",
            clean_line(&String::from_utf8_lossy(&output.stderr))
        );
    }
    Ok(String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| {
            let (path, count) = line.rsplit_once(':')?;
            Some((PathBuf::from(path), count.parse().ok()?))
        })
        .collect())
}

fn source_scan_timeout(deadline: Instant) -> Option<String> {
    deadline
        .checked_duration_since(Instant::now())
        .filter(|remaining| !remaining.is_zero())
        .map(|remaining| format!("{:.3}s", remaining.as_secs_f64().max(0.001)))
}
