use super::*;

pub(super) enum SearchPlan {
    StoredContext,
    Location(SourceLocation),
    SourceRegex(SourceRegexQuery),
    Source(SourceOccurrenceQuery),
    Text(TextSearchPlan),
}

#[derive(Clone, Copy)]
pub(super) enum TextSearchPlan {
    ExactFirst,
    Type,
    ForcedType,
    Discovery,
}

pub(super) struct PlannedSearch {
    pub(super) query: String,
    pub(super) plan: SearchPlan,
}

pub(super) fn plan_search(
    workspace: &Workspace,
    cwd: &Path,
    main_root: &Path,
    query: &str,
    has_context: bool,
) -> Result<PlannedSearch> {
    let location = parse_source_location(&workspace.path, cwd, Some(main_root), query)?;
    let query = query.trim().to_owned();
    ensure!(!query.is_empty() || has_context, "search query is empty");
    let plan = if query.is_empty() {
        SearchPlan::StoredContext
    } else if let Some(location) = location {
        SearchPlan::Location(location)
    } else if let Some(source) =
        parse_source_regex_query(&workspace.path, cwd, Some(main_root), &query)?
    {
        SearchPlan::SourceRegex(source)
    } else if let Some(source) =
        parse_source_occurrence_query(&workspace.path, cwd, Some(main_root), &query)?
    {
        SearchPlan::Source(source)
    } else {
        SearchPlan::Text(text_search_plan(&query))
    };
    Ok(PlannedSearch { query, plan })
}

pub(super) fn text_search_plan(query: &str) -> TextSearchPlan {
    let type_search = type_shaped(query);
    if type_search {
        TextSearchPlan::Type
    } else if field_inventory_query(query).is_some()
        || exact_plan(query, false).is_some()
        || explicit_declaration_name(query).is_some_and(declaration_name_query)
    {
        TextSearchPlan::ExactFirst
    } else {
        TextSearchPlan::Discovery
    }
}
