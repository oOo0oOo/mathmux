use super::*;

pub(super) enum SearchPlan {
    ContextOnly,
    Goal(GoalLocation),
    SourceRegex(SourceRegexQuery),
    Source(SourceOccurrenceQuery),
    Text(TextSearchPlan),
}

#[derive(Clone, Copy)]
pub(super) enum TextSearchPlan {
    ExactFirst,
    Type,
    Discovery,
}

pub(super) struct PlannedSearch {
    pub(super) query: String,
    pub(super) more: bool,
    pub(super) plan: SearchPlan,
}

pub(super) fn plan_search(
    workspace: &Workspace,
    cwd: &Path,
    main_root: &Path,
    query: &str,
    has_context: bool,
) -> Result<PlannedSearch> {
    let location = parse_goal_location(&workspace.path, cwd, Some(main_root), query)?;
    let more = location.is_none() && search_more_requested(query);
    let query = strip_search_modifiers(query);
    ensure!(!query.is_empty() || has_context, "search query is empty");
    let plan = if query.is_empty() {
        SearchPlan::ContextOnly
    } else if let Some(location) = location {
        SearchPlan::Goal(location)
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
    Ok(PlannedSearch { query, more, plan })
}

pub(super) fn text_search_plan(query: &str) -> TextSearchPlan {
    let type_search = type_search_enabled() && type_shaped(query);
    if type_search {
        TextSearchPlan::Type
    } else if field_inventory_query(query).is_some() || exact_plan(query, false).is_some() {
        TextSearchPlan::ExactFirst
    } else {
        TextSearchPlan::Discovery
    }
}
