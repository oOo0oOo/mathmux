//! Manually tuned search policy.
//!
//! Keep correctness checks and hard resource guards in ordinary code. Values here
//! are semantic ranking or recall choices: change one coherent group at a time and
//! replay the search corpus before shipping.

#[derive(Clone, Copy)]
pub(super) struct SearchTuning {
    /// Candidate breadth and the corresponding SQL `LIMIT`s.
    pub(super) retrieval: RetrievalTuning,
    /// SQLite FTS5 BM25 column weights.
    pub(super) fts: FtsTuning,
    /// Additive name, token, declaration, and workspace scores.
    pub(super) lexical: LexicalTuning,
    /// Namespace/member and qualified-path affinity.
    pub(super) qualified: QualifiedTuning,
    /// Structural type and Loogle source calibration.
    pub(super) type_score: TypeScoreTuning,
    /// Dirty-project and bounded source-fallback calibration.
    pub(super) source: SourceTuning,
    /// Post-score promotion, grouping, and import-context rules.
    pub(super) promotion: PromotionTuning,
    /// Final result breadth and detail budgets.
    pub(super) presentation: PresentationTuning,
}

#[derive(Clone, Copy)]
pub(super) struct RetrievalTuning {
    pub(super) type_rows: usize,
    pub(super) name_query_rows: usize,
    pub(super) discovery_rows: usize,
    pub(super) name_rows: usize,
    pub(super) qualified_rows: usize,
    pub(super) exact_rows: usize,
    pub(super) field_rows: usize,
    pub(super) context_rows: usize,
    pub(super) module_rows: usize,
    pub(super) module_count: usize,
    pub(super) name_contains_rows: usize,
    pub(super) continuation_rows: usize,
    pub(super) name_suggestions: usize,
    pub(super) dirty_files: usize,
    pub(super) fallback_paths: usize,
}

#[derive(Clone, Copy)]
pub(super) struct FtsTuning {
    pub(super) name: f64,
    pub(super) signature: f64,
    pub(super) docs: f64,
    pub(super) body: f64,
}

#[derive(Clone, Copy)]
pub(super) struct LexicalTuning {
    pub(super) exact_name: f64,
    pub(super) exact_leaf: f64,
    pub(super) suffix: f64,
    pub(super) prefix: f64,
    pub(super) substring: f64,
    pub(super) exact_token: f64,
    pub(super) exact_case_name: f64,
    pub(super) exact_case_leaf: f64,
    pub(super) token_in_name: f64,
    pub(super) token_in_body: f64,
    pub(super) identifier_part: f64,
    pub(super) conceptual_part: f64,
    pub(super) declaration: f64,
    pub(super) file_penalty: f64,
    pub(super) workspace: f64,
    pub(super) exact_resolution: f64,
    pub(super) symbolic_name: f64,
}

#[derive(Clone, Copy)]
pub(super) struct QualifiedTuning {
    pub(super) member: f64,
    pub(super) shared_part: f64,
    pub(super) affix_ignored: usize,
    pub(super) affix_cap: usize,
    pub(super) affix_character: f64,
    pub(super) approximate_leaf: f64,
    pub(super) shared_owner_part: f64,
    pub(super) direct_leaf_path: f64,
}

#[derive(Clone, Copy)]
pub(super) struct TypeScoreTuning {
    pub(super) base: f64,
    pub(super) conclusion: f64,
    pub(super) shape: f64,
    pub(super) exact_arrows: f64,
    pub(super) compatible_arrows: f64,
    pub(super) token: f64,
    pub(super) loogle_applicable: f64,
    pub(super) loogle_related: f64,
}

#[derive(Clone, Copy)]
pub(super) struct SourceTuning {
    pub(super) dirty_base: f64,
    pub(super) dirty_relevance: f64,
    pub(super) dirty_relevance_cap: usize,
    pub(super) dirty_name: f64,
    pub(super) dirty_exact: f64,
    pub(super) dirty_file_penalty: f64,
    pub(super) dirty_import_file_penalty: f64,
    pub(super) fallback_named_argument: f64,
    pub(super) fallback_symbolic_name: f64,
    pub(super) fallback_direct_path: f64,
    pub(super) fallback_imports: f64,
    pub(super) fallback_file_coverage: f64,
}

#[derive(Clone, Copy)]
pub(super) struct PromotionTuning {
    pub(super) coverage_token_chars: usize,
    pub(super) body_token_chars: usize,
    pub(super) context_name_coverage: usize,
    pub(super) context_group_size: usize,
    pub(super) missing_term_limit: usize,
    pub(super) exact_source_enrichment: usize,
    pub(super) import_available: f64,
    pub(super) import_missing: f64,
}

#[derive(Clone, Copy)]
pub(super) struct PresentationTuning {
    pub(super) result_limit: usize,
    pub(super) summary_limit: usize,
    pub(super) related_result_limit: usize,
    pub(super) declaration_detail_lines: usize,
    pub(super) fallback_candidate_multiplier: usize,
    pub(super) source_range_all_lines: usize,
}

pub(super) const SEARCH_TUNING: SearchTuning = SearchTuning {
    retrieval: RetrievalTuning {
        type_rows: 20_000,
        name_query_rows: 256,
        discovery_rows: 1_000,
        name_rows: 128,
        qualified_rows: 256,
        exact_rows: 128,
        field_rows: 256,
        context_rows: 2_048,
        module_rows: 512,
        module_count: 6,
        name_contains_rows: 128,
        continuation_rows: 128,
        name_suggestions: 2_048,
        dirty_files: 256,
        fallback_paths: 96,
    },
    fts: FtsTuning {
        name: 12.0,
        signature: 7.0,
        docs: 3.0,
        body: 1.0,
    },
    lexical: LexicalTuning {
        exact_name: 600.0,
        exact_leaf: 105.0,
        suffix: 95.0,
        prefix: 75.0,
        substring: 55.0,
        exact_token: 100.0,
        exact_case_name: 200.0,
        exact_case_leaf: 160.0,
        token_in_name: 12.0,
        token_in_body: 3.0,
        identifier_part: 40.0,
        conceptual_part: 35.0,
        declaration: 20.0,
        file_penalty: 40.0,
        workspace: 8.0,
        exact_resolution: 900.0,
        symbolic_name: 600.0,
    },
    qualified: QualifiedTuning {
        member: 300.0,
        shared_part: 250.0,
        affix_ignored: 3,
        affix_cap: 10,
        affix_character: 4.0,
        approximate_leaf: 60.0,
        shared_owner_part: 100.0,
        direct_leaf_path: 280.0,
    },
    type_score: TypeScoreTuning {
        base: 20.0,
        conclusion: 80.0,
        shape: 50.0,
        exact_arrows: 24.0,
        compatible_arrows: 10.0,
        token: 5.0,
        loogle_applicable: 280.0,
        loogle_related: 180.0,
    },
    source: SourceTuning {
        dirty_base: 320.0,
        dirty_relevance: 4.0,
        dirty_relevance_cap: 20,
        dirty_name: 45.0,
        dirty_exact: 140.0,
        dirty_file_penalty: 300.0,
        dirty_import_file_penalty: 60.0,
        fallback_named_argument: 200.0,
        fallback_symbolic_name: 600.0,
        fallback_direct_path: 400.0,
        fallback_imports: 200.0,
        fallback_file_coverage: 4.0,
    },
    promotion: PromotionTuning {
        coverage_token_chars: 3,
        body_token_chars: 6,
        context_name_coverage: 2,
        context_group_size: 4,
        missing_term_limit: 4,
        exact_source_enrichment: 3,
        import_available: 30.0,
        import_missing: 10.0,
    },
    presentation: PresentationTuning {
        result_limit: 24,
        summary_limit: 5,
        related_result_limit: 8,
        declaration_detail_lines: 48,
        fallback_candidate_multiplier: 8,
        source_range_all_lines: 512,
    },
};

/// SQL stays visible here because FTS column weights are among the most useful
/// manual tuning controls. Retrieval predicates remain next to their call sites.
pub(super) fn indexed_rows_sql(tail: &str) -> String {
    format!(
        "SELECT owner, file, module, line, name, kind, signature, docs, body, 0.0 \
         FROM search_fts {tail}"
    )
}

pub(super) fn fts_rank_sql() -> String {
    let weights = SEARCH_TUNING.fts;
    format!(
        "bm25(search_fts, 0.0, 0.0, 0.0, 0.0, 0.0, {}, 0.0, {}, {}, {})",
        weights.name, weights.signature, weights.docs, weights.body
    )
}

pub(super) fn ranked_rows_sql(tail: &str) -> String {
    format!(
        "SELECT owner, file, module, line, name, kind, signature, docs, body, {} \
         FROM search_fts {tail}",
        fts_rank_sql()
    )
}
