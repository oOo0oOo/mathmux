#[derive(Clone, Copy)]
pub(crate) struct SearchPresentation {
    pub result_limit: usize,
    pub summary_limit: usize,
    pub related_result_limit: usize,
    pub declaration_detail_lines: usize,
    pub fallback_candidate_multiplier: usize,
    pub source_range_all_lines: usize,
}

pub(crate) const SEARCH_PRESENTATION: SearchPresentation = SearchPresentation {
    result_limit: 24,
    summary_limit: 5,
    related_result_limit: 8,
    declaration_detail_lines: 48,
    fallback_candidate_multiplier: 8,
    source_range_all_lines: 512,
};

pub(crate) const SOURCE_PREVIEW_LINES: usize = 16;
pub(crate) const BUILD_OUTPUT_LINES: usize = 120;
pub(crate) const BUILD_OUTPUT_TAIL_LINES: usize = 30;
pub(crate) const CHECK_DIAGNOSTIC_CHARS: usize = 1_200;
pub(crate) const CHECK_ADDITIONAL_DIAGNOSTIC_CHARS: usize = 320;
pub(crate) const CHECK_ADDITIONAL_DIAGNOSTICS: usize = 3;

pub(crate) fn bounded_head_tail(
    value: &str,
    line_limit: usize,
    tail_lines: usize,
    omitted_label: &str,
) -> String {
    let lines = value.trim().lines().collect::<Vec<_>>();
    if lines.len() <= line_limit {
        return lines.join("\n");
    }
    let tail_lines = tail_lines.min(line_limit);
    let head_lines = line_limit - tail_lines;
    let omitted = lines.len() - line_limit;
    let mut selected = lines[..head_lines].to_vec();
    let marker = format!("... {omitted} {omitted_label} omitted ...");
    selected.push(&marker);
    selected.extend_from_slice(&lines[lines.len() - tail_lines..]);
    selected.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bounded_output_keeps_head_and_tail() {
        let value = (1..=10)
            .map(|line| line.to_string())
            .collect::<Vec<_>>()
            .join("\n");
        let bounded = bounded_head_tail(&value, 6, 2, "lines");
        assert_eq!(
            bounded.lines().collect::<Vec<_>>(),
            ["1", "2", "3", "4", "... 4 lines omitted ...", "9", "10"]
        );
    }
}
