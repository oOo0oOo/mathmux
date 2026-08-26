use super::*;

#[test]
fn source_parser_qualifies_names_and_keeps_types() {
    let source = r#"namespace Demo
/-- Converts a hypothesis. -/
theorem useful (h : P) : Q := by
  sorry
def pairValue (value : α × β) : α × β := value
end Demo
"#;
    let entries = parse_source(source, "Demo");
    let theorem = entries
        .iter()
        .find(|entry| entry.kind == "theorem")
        .unwrap();
    assert_eq!(theorem.name, "Demo.useful");
    assert_eq!(theorem.signature, "(h : P) : Q");
    assert_eq!(theorem.docs, "Converts a hypothesis.");
    assert!(
        entries
            .iter()
            .any(|entry| entry.name == "Demo.pairValue" && entry.signature.contains('×'))
    );
    let named_argument = parse_source(
        "theorem configured (x : α) : f (R := 𝕜) x = x := by simp\n",
        "Demo",
    );
    assert_eq!(named_argument[0].signature, "(x : α) : f (R := 𝕜) x = x");
    let inferred_abbrev = parse_source("abbrev ZeroFiber := EuclideanSpace ℂ (Fin 0)\n", "Demo");
    assert_eq!(inferred_abbrev[0].signature, ":= EuclideanSpace ℂ (Fin 0)");

    let sectioned = parse_source(
        "namespace Outer\nsection First\ndef before := 1\nend First\nsection Second\ndef after := 2\nend Second\nend Outer\n",
        "Outer",
    );
    assert!(sectioned.iter().any(|entry| entry.name == "Outer.before"));
    assert!(sectioned.iter().any(|entry| entry.name == "Outer.after"));

    let unicode = parse_source(
        "namespace LinearMap\ndef mkContinuous₂ (f : α) := f\nend LinearMap\n",
        "LinearMap",
    );
    assert!(
        unicode
            .iter()
            .any(|entry| entry.name == "LinearMap.mkContinuous₂")
    );

    let additive_doc = parse_source(
        "/-- Multiplicative support. -/\n@[to_additive /-- Additive support around zero. -/]\ntheorem mulSupportFact : True := trivial\n",
        "Demo",
    );
    assert_eq!(additive_doc[0].docs, "Additive support around zero.");

    let priority_instance = parse_source(
        "namespace VectorBundle\ninstance (priority := 100) trivialization_linear [VectorBundle R F E] : e.IsLinear R := inferInstance\nend VectorBundle\n",
        "VectorBundle",
    );
    assert!(priority_instance.iter().any(|entry| {
        entry.kind == "instance" && entry.name == "VectorBundle.trivialization_linear"
    }));

    let anonymous_instance = parse_source(
        "namespace ComplexVectorBundle\ninstance (V : ComplexVectorBundle B) : NormedAddCommGroup V.F := V.normedAddCommGroup\nend ComplexVectorBundle\n",
        "ComplexVectorBundle",
    );
    assert!(anonymous_instance.iter().any(|entry| {
        entry.kind == "instance"
            && entry.name.starts_with("ComplexVectorBundle.instance@")
            && entry.signature.contains("NormedAddCommGroup V.F")
    }));

    let structure = parse_source(
        "structure InnerProductSpace.Core extends PreInnerProductSpace.Core where\n  definite : True\n",
        "InnerProductSpace",
    );
    assert!(structure[0].signature.contains(
        "generated parent projection: InnerProductSpace.Core.toPreInnerProductSpaceCore"
    ));
    let infix_parent = parse_source(
        "structure Homeomorph (X Y : Type*) extends X ≃ Y where\n  continuous_toFun : True\n",
        "Homeomorph",
    );
    assert!(
        !infix_parent[0]
            .signature
            .contains("generated parent projection")
    );

    let bundle_hom = parse_source(
        "namespace Demo\nstructure BundleHom (E₁ E₂ : B → Type*) where\n  toFun : ∀ b, E₁ b → E₂ b\n  /-- The maps vary continuously. -/\n  continuous_toFun :\n    Continuous (fun b ↦ toFun b)\n\nnamespace BundleHom\ntheorem use : True := trivial\nend BundleHom\nend Demo\n",
        "Demo",
    );
    let continuous = bundle_hom
        .iter()
        .find(|entry| entry.name == "Demo.BundleHom.continuous_toFun")
        .unwrap();
    assert_eq!(continuous.kind, "field");
    assert_eq!(continuous.line, 5);
    assert_eq!(continuous.docs, "The maps vary continuously.");
    assert_eq!(continuous.signature, "Continuous (fun b ↦ toFun b)");
    assert!(!continuous.body.contains("namespace BundleHom"));

    let contextual = parse_source(
        "namespace Demo\nuniverse u\nvariable {α : Type u} [Group α]\nsection Closed\nvariable [TopologicalSpace α]\nend Closed\nstructure Box where\n  value : α\nend Demo\n",
        "Demo",
    );
    let boxed = contextual
        .iter()
        .find(|entry| entry.name == "Demo.Box")
        .unwrap();
    assert!(boxed.body.contains("universe u"));
    assert!(boxed.body.contains("variable {α : Type u} [Group α]"));
    assert!(!boxed.body.contains("variable [TopologicalSpace α]"));

    let grouped = parse_source(
        "namespace Demo\nsection Adapter\nvariable {α : Type} [Group α]\ntheorem useful : True := by trivial\nend Adapter\nend Demo\n",
        "Demo",
    );
    let useful = grouped
        .iter()
        .find(|entry| entry.name == "Demo.useful")
        .unwrap();
    assert!(useful.body.contains("section Adapter"));
    assert!(!useful.body.contains("end Adapter"));

    let notation = parse_source(
        "namespace Bundle\nnotation:100 E₁ \" ×ᵇ \" E₂ => fun x => E₁ x × E₂ x\nend Bundle\n",
        "Demo",
    );
    let notation = notation
        .iter()
        .find(|entry| entry.name == "Bundle.notation ×ᵇ")
        .unwrap();
    assert_eq!(notation.kind, "notation");
    assert_eq!(notation.line, 2);
}

#[test]
fn pipe_alternatives_short_circuit_after_one_indexed_hit_covers_a_group() {
    let hit = SearchHit {
        name: "MatrixGL.gl_pathConnectedSpace".into(),
        kind: "theorem".into(),
        signature: Some("PathConnectedSpace (Matrix.GeneralLinearGroup n C)".into()),
        module: "Demo.GLPaths".into(),
        path: "Demo/GLPaths.lean".into(),
        line: 1,
        doc: None,
        source: None,
        usages: Vec::new(),
        applicable: false,
        required_import: None,
    };
    assert!(pipe_alternative_covered(
        "GeneralLinearGroup connected|unrelated missing",
        [&hit].into_iter()
    ));
    assert!(!pipe_alternative_covered(
        "GeneralLinearGroup compact|unrelated missing",
        [&hit].into_iter()
    ));
}

#[test]
fn lean_inspection_syntax_normalizes_to_search_terms() {
    assert_eq!(
        normalize_lean_inspection_query("@Demo.useful"),
        "Demo.useful"
    );
    assert_eq!(
        normalize_lean_inspection_query("@Demo.useful x y MORE"),
        "Demo.useful MORE"
    );
    assert_eq!(
        normalize_lean_inspection_query("#check Demo.useful"),
        "Demo.useful"
    );
    assert_eq!(
        normalize_lean_inspection_query("#print @Demo.useful x"),
        "Demo.useful"
    );
    assert_eq!(
        normalize_lean_inspection_query("#synth TopologicalSpace X"),
        "TopologicalSpace X"
    );
    assert_eq!(
        normalize_lean_inspection_query("⊢ Continuous f"),
        "⊢ Continuous f"
    );
    assert_eq!(
        normalize_lean_inspection_query(r"Finset.min\x27_mem|Finset.isLeast_min\'"),
        "Finset.min'_mem|Finset.isLeast_min'"
    );
}

#[test]
fn inference_reserves_positions_and_recognizes_type_patterns() {
    assert!(type_shaped("_ → Injective _"));
    assert!(!type_shaped("injective function"));
    assert!(!type_shaped("norm_inner_le_norm"));
    assert!(structural_type_score("_ → Injective _", "Bijective f → Injective f") > 0.0);
    assert!(
        structural_type_score(
            "⊢ Continuous (_ ∘ _)",
            "{f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f)",
        ) > structural_type_score(
            "⊢ Continuous (_ ∘ _)",
            "(e : LocalTrivialization F E) [e.IsLinear 𝕜]",
        )
    );
    assert!(conclusion_query("⊢ _ → Injective _"));
    assert!(!conclusion_query("_ → Injective _"));
    assert_eq!(fts_query("List.map"), "\"list.map\"*");
    assert!(declaration_name_query("Finsupp.sum_add_index"));
    assert!(declaration_name_query("Ring.inverse_eq_inv'"));
    assert!(declaration_name_query("transportAmbient"));
    assert!(!declaration_name_query("Finsupp.sum add"));
    assert_eq!(
        declaration_list_terms("matrixFinBlockClass matrixFinBlockClass_one"),
        Some(vec!["matrixFinBlockClass", "matrixFinBlockClass_one"])
    );
    assert_eq!(declaration_list_terms("continuous support"), None);
    assert_eq!(
        explicit_declaration_name("theorem Bundle.Trivialization.apply_mk_symm"),
        Some("Bundle.Trivialization.apply_mk_symm")
    );
    assert_eq!(
        explicit_declaration_name("def Demo.useful proof body"),
        Some("Demo.useful")
    );
    assert_eq!(
        explicit_declaration_name("structure ContinuousLinearBundleHom fields"),
        Some("ContinuousLinearBundleHom")
    );
    assert_eq!(
        explicit_declaration_name("inductive List constructors"),
        Some("List")
    );
    assert_eq!(explicit_declaration_name("theorem search terms"), None);
    assert_eq!(
        declaration_suffix_base("Demo.longDeclaration_E"),
        Some("Demo.longDeclaration")
    );
    assert_eq!(declaration_suffix_base("short_E"), Some("short"));
    assert_eq!(declaration_suffix_base("abc_E"), None);
    assert_eq!(declaration_suffix_base("Demo.longDeclaration"), None);
    assert_eq!(more_search_reference("q4246 MORE"), Some("q4246"));
    assert_eq!(
        more_search_reference("projectionRangeInclusionHom q4246 MORE"),
        Some("q4246")
    );
    assert_eq!(more_search_reference("q4246 comp"), None);
    assert!(search_more_requested("declaration MORE"));
    assert!(search_more_requested("File.lean:1-120 more"));
    assert!(!search_more_requested("moreover"));
    assert_eq!(
        strip_search_modifiers("declaration terms MORE"),
        "declaration terms"
    );
    assert_eq!(
        strip_search_modifiers("declaration MORE terms more"),
        "declaration terms"
    );
    assert_eq!(
        strip_search_modifiers("VectorBundle FILE:LINE MORE"),
        "VectorBundle"
    );
    assert_eq!(
        strip_search_modifiers("declaration terms"),
        "declaration terms"
    );
    assert_eq!(strip_search_modifiers("MORE"), "");
    let contextual_hit = SearchHit {
        name: "Demo.projectionRange_nearby_isomorphic".into(),
        kind: "theorem".into(),
        signature: Some("Isomorphic X Y".into()),
        module: "Demo.Pullback".into(),
        path: "Demo/Pullback.lean".into(),
        line: 1,
        doc: None,
        source: None,
        usages: Vec::new(),
        applicable: false,
        required_import: None,
    };
    assert_eq!(
        hit_query_coverage(
            &contextual_hit,
            &[
                "projectionrange".into(),
                "pullback".into(),
                "isomorphic".into()
            ]
        ),
        (3, 33, 2, 25)
    );
    let mut ranked = vec![
        RankedHit {
            hit: SearchHit {
                name: "circleMap_neg_radius".into(),
                signature: Some("circleMap c r".into()),
                ..contextual_hit.clone()
            },
            score: 100.0,
        },
        RankedHit {
            hit: SearchHit {
                name: "Demo.CircleSeparatedOnRadius.continuousOn_resolvent".into(),
                signature: None,
                ..contextual_hit.clone()
            },
            score: 10.0,
        },
    ];
    let tokens = meaningful_query_tokens("CircleSeparatedOnRadius circleMap");
    promote_query_coverage(&mut ranked, &tokens);
    assert!(ranked[0].hit.name.contains("CircleSeparatedOnRadius"));
    assert_eq!(symbolic_source_term("*ᵥ"), Some("*ᵥ".to_owned()));
    assert_eq!(symbolic_source_term("≤"), Some("≤".to_owned()));
    assert_eq!(symbolic_source_term("*"), None);
    assert_eq!(symbolic_source_term("ordinary"), None);
    assert_eq!(symbolic_source_term("A *ᵥ x"), None);
    assert!(declaration_glob_query("FiberBundle.*equiv"));
    assert!(!declaration_glob_query("*ᵥ"));
    assert!(declaration_glob_matches(
        "Demo.FiberBundle.local_equiv",
        "FiberBundle.*equiv"
    ));
    assert!(declaration_glob_matches(
        "Demo.matrixToEuclideanCLM_mul",
        "matrixToEuclideanCLM.*mul"
    ));
    assert!(declaration_glob_matches(
        "Demo.projectionRangePretrivializationAt_totalSpaceMk_isInducing",
        "projectionRange.*IsInducing"
    ));
    assert!(declaration_glob_matches(
        "Demo.projectionRangeInclusionHom",
        "projectionRange.*Inclusion*"
    ));
    assert!(!declaration_glob_matches(
        "Demo.FiberBundle.local_equiv_apply",
        "FiberBundle.*equiv"
    ));
    let mut relational = vec![RankedHit {
        hit: SearchHit {
            name: "ContinuousLinearMap.intervalIntegral_comp_comm".into(),
            ..contextual_hit.clone()
        },
        score: 10.0,
    }];
    assert!(apply_declaration_glob(&mut relational, "Matrix.*integral"));
    assert_eq!(relational.len(), 1);
    relational.push(RankedHit {
        hit: SearchHit {
            name: "Demo.Matrix_entry_integral".into(),
            ..contextual_hit.clone()
        },
        score: 5.0,
    });
    assert!(!apply_declaration_glob(&mut relational, "Matrix.*integral"));
    assert_eq!(relational.len(), 1);
    assert_eq!(relational[0].hit.name, "Demo.Matrix_entry_integral");
    assert!(qualified_name_matches(
        "AtiyahSinger.ComplexVectorSubbundle.transportAmbient",
        "ComplexVectorSubbundle.transportAmbient"
    ));
    assert!(!qualified_name_matches(
        "AtiyahSinger.ComplexVectorSubbundle.transportAmbient",
        "VectorSubbundle.transportAmbient"
    ));
    let resolved = resolved_exact_candidates(
        vec![
            RankedHit {
                hit: SearchHit {
                    name: "NumberField.Units".into(),
                    ..contextual_hit.clone()
                },
                score: 20.0,
            },
            RankedHit {
                hit: SearchHit {
                    name: "Units".into(),
                    ..contextual_hit.clone()
                },
                score: 10.0,
            },
        ],
        "Units",
    )
    .unwrap();
    assert_eq!(resolved.len(), 1);
    assert_eq!(resolved[0].hit.name, "Units");
    assert_eq!(result_limit(true, false), RELATED_RESULT_LIMIT);
    assert_eq!(result_limit(true, true), RESULT_LIMIT);
    assert_eq!(result_limit(false, false), RESULT_LIMIT);
    assert!(direct_continuation_name_matches(
        "AtiyahSinger.Topology.VectorBundle.MatrixGL.circleResolventFunction_commutes_on_sphere",
        "circleResolventFunction_commutes"
    ));
    assert!(direct_continuation_name_matches(
        "AtiyahSinger.Topology.VectorBundle.MatrixGL.circleResolventFunction_commutes_on_sphere",
        "MatrixGL.circleResolventFunction_commutes"
    ));
    assert!(direct_continuation_name_matches(
        "WithLp.ext_iff",
        "WithLp.ext"
    ));
    assert!(!direct_continuation_name_matches(
        "AtiyahSinger.Topology.VectorBundle.Other.circleResolventFunction_commutes_on_sphere",
        "MatrixGL.circleResolventFunction_commutes"
    ));
    assert_eq!(meaningful_query_tokens("precomp (L :=)"), vec!["precomp"]);
    assert_eq!(
        meaningful_query_tokens("exact? eTarget.symm"),
        vec!["etarget.symm"]
    );
    assert_eq!(
        meaningful_query_tokens("simpa only [precomp_classOf, ContinuousMap.comp_assoc]"),
        vec![
            "precomp_classof",
            "continuousmap.comp_assoc",
            "precomp",
            "comp",
            "assoc"
        ]
    );
    assert_eq!(
        meaningful_query_tokens("name LinearEquiv.ofFinrankEq"),
        vec!["linearequiv.offinrankeq", "finrank"]
    );
    let (anchor, refinements, requested) =
        anchored_api_query("bottProjectionMatrix selfAdjoint|conjTranspose|mul_self|one_sub")
            .unwrap();
    assert_eq!(anchor, "bottProjectionMatrix");
    assert!(refinements.contains(&"mul_self".into()));
    assert_eq!(
        requested,
        vec!["conjtranspose", "mul_self", "one_sub", "selfadjoint"]
    );
    assert!(anchored_api_query("continuous map compact support").is_none());
    assert_eq!(
        meaningful_query_tokens("LinearEquiv.ofFinrankEq --all"),
        vec!["linearequiv.offinrankeq", "finrank"]
    );
    assert_eq!(
        meaningful_query_tokens("LinearMap.rangeEquiv"),
        vec!["linearmap.rangeequiv", "range", "equiv"]
    );
    assert!(
        qualified_member_score("LinearMap.rangeEquiv", "LinearMap.quotKerEquivRange")
            > qualified_member_score("LinearMap.rangeEquiv", "Algebra.linearMap")
    );
    assert!(
        qualified_member_score("LinearMap.rangeEquiv", "LinearMap.kerComplementEquivRange")
            > qualified_member_score("LinearMap.rangeEquiv", "LinearMap.range")
    );
    assert!(qualified_member_score("LinearEquiv.ofSurjective", "LinearEquiv.ofBijective") > 90.0);
    assert_eq!(
        qualified_leaf_path_score(
            "KZero.add",
            "AtiyahSinger.ComplexVectorBundle.add",
            "AtiyahSinger.ComplexVectorBundleKZero",
            "AtiyahSinger/ComplexVectorBundleKZero.lean"
        ),
        280.0
    );
    assert_eq!(
        qualified_leaf_path_score(
            "BundleClass.add",
            "AtiyahSinger.ComplexVectorBundle.add",
            "AtiySinger.ComplexVectorBundleKZero",
            "AtiyahSinger/ComplexVectorBundleKZero.lean"
        ),
        60.0
    );
    assert_eq!(
        meaningful_query_tokens("finite_trivialization_cover proof body"),
        vec![
            "finite_trivialization_cover",
            "finite",
            "trivialization",
            "cover"
        ]
    );
    assert_eq!(
        meaningful_query_tokens("elementaryTransvectionLoop_homotopic_one"),
        vec![
            "elementarytransvectionloop_homotopic_one",
            "elementary",
            "transvection",
            "loop",
            "homotopic",
            "one"
        ]
    );
    assert_eq!(
        meaningful_query_tokens("adapter weights to complex"),
        vec!["adapter", "weights", "complex"]
    );
    assert_eq!(
        source_specific_query_tokens("ContinuousMap IsUnit unitsLift"),
        vec!["unitslift"]
    );
    assert_eq!(
        specific_query_tokens("projectionRangeComplexVectorBundleConstant"),
        vec!["projectionrangecomplexvectorbundleconstant"]
    );
    assert!(specific_query_tokens("Homeomorph").is_empty());
    assert!(words_match("weight", "weights"));
    assert!(hit_name_matches(
        "Matrix.conjTranspose_mul",
        "matrix.conjtranspose_mul"
    ));
    assert!(declaration_leaf_matches(
        "AtiyahSinger.ContinuousLinearBundleHom.matrixEquiv",
        "ContinuousLinearBundleHom matrixEquiv"
    ));
    assert!(!declaration_leaf_matches(
        "AtiyahSinger.ContinuousLinearBundleHom.matrixEquiv_apply",
        "ContinuousLinearBundleHom matrixEquiv"
    ));
    let named_row = |name: &str| IndexedRow {
        owner: "workspace:w1".into(),
        path: "Demo.lean".into(),
        module: "Demo".into(),
        line: 1,
        name: name.into(),
        kind: "structure".into(),
        signature: String::new(),
        docs: String::new(),
        body: String::new(),
        rank: 0.0,
    };
    let tokens = meaningful_query_tokens("HermitianBundleMetric");
    assert!(
        lexical_score(
            "HermitianBundleMetric",
            &tokens,
            &named_row("AtiyahSinger.HermitianBundleMetric")
        ) > lexical_score(
            "HermitianBundleMetric",
            &tokens,
            &named_row("AtiyahSinger.Bundle.Trivial.hermitianBundleMetric")
        )
    );
    let summary = render_summary(&SearchRun {
        reference: "q1".into(),
        workspace_ref: "w1".into(),
        query: "demo".into(),
        inference: "hybrid".into(),
        hits: Vec::new(),
        note: None,
        duration_ms: 123,
        created_at: 0,
    });
    assert_eq!(summary, "q1 no results");
}

#[test]
fn search_summary_keeps_definition_body_after_ambient_context() {
    let summary = render_summary(&SearchRun {
            reference: "q2".into(),
            workspace_ref: "w1".into(),
            query: "matrixLaurentShift".into(),
            inference: "hybrid".into(),
            hits: vec![SearchHit {
                name: "Demo.matrixLaurentShift".into(),
                kind: "def".into(),
                signature: Some("Nat → Nat".into()),
                module: "Demo".into(),
                path: "Demo.lean".into(),
                line: 10,
                doc: None,
                source: Some(
                    "-- ambient context\nuniverse u\nvariable {B : Type u}\nsection\nvariable (n : Nat)\n\ndef matrixLaurentShift : Nat :=\n  n + 1"
                        .into(),
                ),
                usages: Vec::new(),
                applicable: false,
                required_import: None,
            }],
            note: None,
            duration_ms: 1,
            created_at: 0,
        });
    assert!(summary.contains("source:\n-- ambient context"));
    assert!(summary.contains("\n  n + 1"));
    assert!(!summary.contains("matrixLaurentShift : Nat → Nat"));
}

#[test]
fn structure_summary_points_to_complete_field_inventory() {
    let source = std::iter::once("structure Demo.Config where".to_owned())
        .chain((1..=20).map(|index| format!("  field{index} : Nat")))
        .collect::<Vec<_>>()
        .join("\n");
    let structure = SearchHit {
        name: "Demo.Config".into(),
        kind: "structure".into(),
        signature: None,
        module: "Demo".into(),
        path: "Demo.lean".into(),
        line: 1,
        doc: None,
        source: Some(source),
        usages: Vec::new(),
        applicable: false,
        required_import: None,
    };
    let summary = render_summary(&SearchRun {
        reference: "q-fields".into(),
        workspace_ref: "w1".into(),
        query: "Demo.Config".into(),
        inference: "exact".into(),
        hits: vec![structure],
        note: None,
        duration_ms: 1,
        created_at: 0,
    });
    assert!(summary.contains("+5 lines; search Demo.Config fields"));

    let fields = SearchHit {
        name: "Demo.Config fields".into(),
        kind: "fields".into(),
        signature: None,
        module: "Demo".into(),
        path: "Demo.lean".into(),
        line: 1,
        doc: None,
        source: Some(
            (1..=20)
                .map(|index| format!("field{index} : Nat"))
                .collect::<Vec<_>>()
                .join("\n"),
        ),
        usages: Vec::new(),
        applicable: false,
        required_import: None,
    };
    let summary = render_summary(&SearchRun {
        reference: "q-inventory".into(),
        workspace_ref: "w1".into(),
        query: "Demo.Config fields".into(),
        inference: "exact".into(),
        hits: vec![fields],
        note: None,
        duration_ms: 1,
        created_at: 0,
    });
    assert!(summary.contains("\nfield20 : Nat"));
    assert!(!summary.contains("source:"));
}

#[test]
fn stale_workspace_source_queries_recommend_sync() {
    let main = tempfile::tempdir().unwrap();
    let workspace = tempfile::tempdir().unwrap();
    fs::create_dir_all(main.path().join("Demo/Topology")).unwrap();
    fs::write(
        main.path().join("Demo/Topology/Recent.lean"),
        "def recent := true\n",
    )
    .unwrap();

    let error = match parse_source_occurrence_query(
        workspace.path(),
        workspace.path(),
        Some(main.path()),
        "Demo/Topology/Recent.lean:1-2 recent",
    ) {
        Err(error) => error,
        Ok(_) => panic!("stale source unexpectedly resolved"),
    };
    assert_eq!(
        error.to_string(),
        "source file is on managed main; run mathmux sync"
    );

    fs::write(
        main.path().join("Demo/Topology/Shared.lean"),
        "line 1\nline 2\nline 3\nline 4\n",
    )
    .unwrap();
    fs::create_dir_all(workspace.path().join("Demo/Topology")).unwrap();
    fs::write(
        workspace.path().join("Demo/Topology/Shared.lean"),
        "line 1\nline 2\n",
    )
    .unwrap();
    let stale_range = parse_source_occurrence_query(
        workspace.path(),
        workspace.path(),
        Some(main.path()),
        "Demo/Topology/Shared.lean:3-4",
    )
    .unwrap()
    .unwrap();
    let stale_range = source_occurrence_result(
        &Workspace {
            reference: "w1".into(),
            name: "demo".into(),
            path: workspace.path().to_path_buf(),
            branch: "demo".into(),
        },
        stale_range,
        false,
    )
    .unwrap();
    assert_eq!(
        stale_range.note.as_deref(),
        Some("workspace source is stale; run mathmux sync")
    );

    let error = match parse_goal_location(
        workspace.path(),
        workspace.path(),
        Some(main.path()),
        "Demo/Topology/Missing.lean:1",
    ) {
        Err(error) => error,
        Ok(_) => panic!("missing source unexpectedly resolved"),
    };
    assert_eq!(
        error.to_string(),
        "source file not found or ambiguous: Demo/Topology/Missing.lean"
    );
}

#[test]
fn explicit_body_query_keeps_alternatives_compact() {
    let hit = |name: &str, source: &str| SearchHit {
        name: name.into(),
        kind: "theorem".into(),
        signature: Some("True".into()),
        module: "Demo".into(),
        path: "Demo.lean".into(),
        line: 1,
        doc: None,
        source: Some(source.into()),
        usages: Vec::new(),
        applicable: false,
        required_import: None,
    };
    let summary = render_summary(&SearchRun {
        reference: "q3".into(),
        workspace_ref: "w1".into(),
        query: "theorem proof".into(),
        inference: "hybrid".into(),
        hits: vec![
            hit("Demo.proof", "requested body"),
            hit("Other.proof", "alternative body"),
        ],
        note: None,
        duration_ms: 1,
        created_at: 0,
    });
    assert!(summary.contains("requested body"));
    assert!(summary.contains("Demo.proof : True"));
    assert!(summary.contains("Other.proof : True"));
    assert!(!summary.contains("alternative body"));

    let related = render_summary(&SearchRun {
        reference: "q-related".into(),
        workspace_ref: "w1".into(),
        query: "Demo.missingProof".into(),
        inference: "hybrid".into(),
        hits: vec![hit("Demo.closestProof", "unrelated proof body")],
        note: Some("related results (no exact match)".into()),
        duration_ms: 1,
        created_at: 0,
    });
    assert!(related.contains("Demo.closestProof : True"));
    assert!(!related.contains("unrelated proof body"));
}

#[test]
fn name_contains_fallback_batches_tokens_and_respects_scopes() {
    let connection = Connection::open_in_memory().unwrap();
    connection
        .execute_batch(
            "CREATE VIRTUAL TABLE search_fts USING fts5(
                    owner UNINDEXED, origin UNINDEXED, file UNINDEXED,
                    module UNINDEXED, line UNINDEXED, name, kind UNINDEXED,
                    signature, docs, body
                 );",
        )
        .unwrap();
    for (owner, name) in [
        ("workspace:w1", "Demo.prefixAlphaSuffix"),
        ("packages:demo", "Demo.prefixBetaSuffix"),
        ("workspace:w2", "Demo.prefixGammaSuffix"),
    ] {
        connection
            .execute(
                "INSERT INTO search_fts(
                        owner, origin, file, module, line, name, kind, signature, docs, body
                     ) VALUES (?1, '', 'Demo.lean', 'Demo', 1, ?2, 'def', '', '', '')",
                params![owner, name],
            )
            .unwrap();
    }
    install_active_scopes(
        &connection,
        &HashSet::from(["workspace:w1".into(), "packages:demo".into()]),
    )
    .unwrap();
    let hits = name_contains_candidates(&connection, &["alphasuffix".into(), "betasuffix".into()])
        .unwrap();
    assert_eq!(
        hits.into_iter().map(|hit| hit.name).collect::<Vec<_>>(),
        ["Demo.prefixAlphaSuffix", "Demo.prefixBetaSuffix"]
    );
}

#[test]
fn import_context_marks_only_unavailable_results() {
    let hit = |module: &str| RankedHit {
        hit: SearchHit {
            name: format!("{module}.useful"),
            kind: "theorem".into(),
            signature: Some("True".into()),
            module: module.into(),
            path: format!("{}.lean", module.replace('.', "/")),
            line: 1,
            doc: None,
            source: None,
            usages: Vec::new(),
            applicable: false,
            required_import: None,
        },
        score: 10.0,
    };
    let context = ImportContext {
        accessible: HashSet::from(["Demo.Available".into()]),
        complete: true,
    };
    let mut available = hit("Demo.Available");
    apply_import_context(&mut available, &context);
    assert_eq!(available.score, 40.0);
    assert!(available.hit.required_import.is_none());

    let mut unavailable = hit("Demo.Extra");
    apply_import_context(&mut unavailable, &context);
    assert_eq!(
        unavailable.hit.required_import.as_deref(),
        Some("Demo.Extra")
    );
}

#[test]
fn references_decode_from_ilean_keys() {
    let key = r#"{"c":{"m":"Demo","n":"Demo.useful"}}"#;
    assert_eq!(reference_name(key).as_deref(), Some("Demo.useful"));
}

#[test]
fn goal_suggestions_accept_leans_multiline_output() {
    assert_eq!(
        try_this_suggestions("Try this:\n  [apply] exact useful h\n"),
        vec!["exact useful h"]
    );
    assert_eq!(
        try_this_suggestions(
            "Try this:\n  [apply] obtain ⟨value, property⟩ := b\n  simp_all only [Prod.mk.injEq,\n    true_and]\n\nwarning: later\n"
        ),
        vec!["obtain ⟨value, property⟩ := b\nsimp_all only [Prod.mk.injEq,\n  true_and]"]
    );
    assert_eq!(
        try_this_suggestions(
            "Try this:\n  [apply] refine useful ?_\n  -- Remaining subgoals:\n  -- ⊢ True\n"
        ),
        vec!["refine useful ?_"]
    );
    assert!(try_this_suggestions("Try this: simp_all; sorry\n").is_empty());
    assert!(try_this_suggestions("Try this:\n  exact h\n  admit\n").is_empty());
    assert_eq!(
        traced_goal_state(
            "MATHMUX_GOAL_BEGIN\nX : Type\nh : True\n⊢ True\nMATHMUX_GOAL_END\nTry this: exact h"
        )
        .as_deref(),
        Some("X : Type\nh : True\n⊢ True")
    );
    assert_eq!(
        local_method_candidates(
            "f g : X → X\nhf : Continuous f\nhg : Continuous g\n⊢ Continuous (f ∘ g)"
        )
        .first()
        .map(String::as_str),
        Some("exact hf.comp hg")
    );
    assert_eq!(
        goal_refinement_query("hf : Continuous f\n⊢ Continuous (f ∘ g)", "comp"),
        "Continuous.comp"
    );
    assert_eq!(edit_distance("compp", "comp"), 1);
    assert_eq!(
        diagnostic_goal_query(
            "⊢ Continuous fun a => Matrix.fromBlocks (A a) 0 0 (D a) (finSumFinEquiv.symm i)",
            &HashSet::from(["a", "A", "D", "i"])
        ),
        "Matrix.fromBlocks finSumFinEquiv.symm Continuous"
    );
    assert_eq!(
        refined_search_query("Homeomorph", "constructors"),
        "Homeomorph.mk"
    );
    assert_eq!(
        refined_search_query("Homeomorph", "fields"),
        "Homeomorph fields"
    );
    assert_eq!(refined_search_query("Homeomorph", "usages"), "Homeomorph");
    assert_eq!(field_inventory_query("Homeomorph fields"), Some("Homeomorph"));
    assert_eq!(
        field_inventory_query("structure Homeomorph projections"),
        Some("Homeomorph")
    );
    assert_eq!(field_inventory_query("Homeomorph constructors"), None);
    assert_eq!(
        diagnostic_position(
            "Demo/Proof.lean:42:7: error: unsolved goals",
            Some("Fallback.lean")
        ),
        (Some("Demo/Proof.lean".into()), 42)
    );
    assert_eq!(
        diagnostic_position(
            "Demo.Proof:43:8: error: unsolved goals",
            Some("Demo/Proof.lean")
        ),
        (Some("Demo/Proof.lean".into()), 43)
    );
    assert!(diagnostic_context("error: mismatch", Some(">   42 | bad")).contains("42 | bad"));
    let mismatch = diagnostic_type_detail(
            "Demo:1:1: error: Type mismatch\nterm\nhas type\n  @Map A oldTopology oldInstance\nbut is expected to have type\n  @Map A newTopology oldInstance\nin the application\n  use term",
        )
        .unwrap();
    assert!(mismatch.contains("actual: oldTopology"));
    assert!(mismatch.contains("expected: newTopology"));
    assert!(!mismatch.contains("oldInstance"));
    assert_eq!(
            diagnostic_type_detail(
                "Demo:1:1: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n  TopologicalSpace (Fiber x)\n\nHint: inspect it"
            )
            .as_deref(),
            Some("instance goal\nTopologicalSpace (Fiber x)")
        );
    assert_eq!(
        append_goal_tactic(
            "example (h : True) : True := by\n  skip\n\nexample : True := by\n  trivial\n",
            1,
            "exact h"
        )
        .unwrap(),
        "example (h : True) : True := by\n  skip\n\n  exact h\nexample : True := by\n  trivial\n"
    );
    assert_eq!(
        diagnostic_search_query(
            "error: unsolved goals\nX : Type\nf g : X → X\nhf : Continuous f\n⊢ Continuous (f ∘ g)\n   3 | example"
        ),
        "⊢ Continuous (_ ∘ _)"
    );
    assert_eq!(
        diagnostic_search_query(
            "Demo:12:4: error: Tactic `rfl` failed: The left-hand side\n  (projectionRangePullbackMapAt P x) ((Trivialization.symmL ℂ e x) v)\nis not definitionally equal to the right-hand side\n  (Trivialization.symmL ℂ e' x) v\n\ncase refl\nP : C X Y"
        ),
        "projectionRangePullbackMapAt Trivialization.symmL"
    );
    let source = (1..=30)
        .map(|line| format!("line {line}"))
        .collect::<Vec<_>>()
        .join("\n");
    let excerpt = location_source_excerpt(&source, 15, LOCATION_PREVIEW_LINES);
    assert!(excerpt.contains("   15  line 15"));
    assert_eq!(excerpt.lines().count(), 30);

    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("Demo.lean"), &source).unwrap();
    let duplicated_root = resolve_goal_path(directory.path(), directory.path(), "Demo/Demo.lean")
        .unwrap()
        .unwrap();
    assert_eq!(
        duplicated_root.0,
        fs::canonicalize(directory.path().join("Demo.lean")).unwrap()
    );
    fs::create_dir_all(directory.path().join("Actual/Topology")).unwrap();
    fs::write(
        directory.path().join("Actual/Topology/Unique.lean"),
        "def unique := true\n",
    )
    .unwrap();
    let recovered_suffix = resolve_goal_path(
        directory.path(),
        directory.path(),
        "Wrong/Topology/Unique.lean",
    )
    .unwrap()
    .unwrap();
    assert_eq!(
        recovered_suffix.0,
        fs::canonicalize(directory.path().join("Actual/Topology/Unique.lean")).unwrap()
    );
    fs::create_dir_all(directory.path().join("Other/Topology")).unwrap();
    fs::write(
        directory.path().join("Other/Topology/Unique.lean"),
        "def other := true\n",
    )
    .unwrap();
    assert!(
        resolve_goal_path(
            directory.path(),
            directory.path(),
            "Wrong/Topology/Unique.lean",
        )
        .unwrap()
        .is_none()
    );
    let location = parse_goal_location(directory.path(), directory.path(), None, "Demo.lean:tail")
        .unwrap()
        .unwrap();
    assert_eq!(location.line, 30);
    assert!(location.tail);
    assert!(!location.more);
    assert!(location.probe);
    assert!(location.display_path.is_none());
    let tail = location_source_excerpt(&source, location.line, SOURCE_PREVIEW_LINES);
    assert_eq!(tail.lines().count(), 16);
    assert!(tail.contains("   30  line 30"));

    let more = parse_goal_location(
        directory.path(),
        directory.path(),
        None,
        "Demo.lean:15 MORE",
    )
    .unwrap()
    .unwrap();
    assert_eq!(more.line, 15);
    assert!(!more.tail);
    assert!(more.more);

    fs::write(
        directory.path().join("Markers.lean"),
        "plain\n/- open\ninside /-! doc\n-/ close\nplain\n",
    )
    .unwrap();
    let occurrences = parse_source_occurrence_query(
        directory.path(),
        directory.path(),
        None,
        "Markers.lean:2-4 /- | -/ | /-!",
    )
    .unwrap()
    .unwrap();
    assert_eq!((occurrences.first_line, occurrences.last_line), (2, 4));
    assert_eq!(occurrences.terms, ["/-", "-/", "/-!"]);
    let result = source_occurrence_result(
        &Workspace {
            reference: "w1".into(),
            name: "demo".into(),
            path: directory.path().to_path_buf(),
            branch: "demo".into(),
        },
        occurrences,
        false,
    )
    .unwrap();
    assert_eq!(result.hits.len(), 1);
    let matches = result.hits[0].source.as_deref().unwrap();
    assert!(matches.contains("    2  /- open"));
    assert!(matches.contains("    3  inside /-! doc"));
    assert!(matches.contains("    4  -/ close"));
    let range =
        parse_source_occurrence_query(directory.path(), directory.path(), None, "Markers.lean:2-4")
            .unwrap()
            .unwrap();
    assert!(range.terms.is_empty());
    let range = source_occurrence_result(
        &Workspace {
            reference: "w1".into(),
            name: "demo".into(),
            path: directory.path().to_path_buf(),
            branch: "demo".into(),
        },
        range,
        false,
    )
    .unwrap();
    assert_eq!(range.hits[0].signature.as_deref(), Some("3 source lines"));
    assert_eq!(range.hits[0].kind, "source-range");
    assert_eq!(
        range.hits[0].source.as_deref(),
        Some("/- open\ninside /-! doc\n-/ close")
    );

    let long_source = (1..=250)
        .map(|line| format!("line {line}"))
        .collect::<Vec<_>>()
        .join("\n");
    fs::write(directory.path().join("Long.lean"), long_source).unwrap();
    let long_range =
        parse_source_occurrence_query(directory.path(), directory.path(), None, "Long.lean:1-250")
            .unwrap()
            .unwrap();
    let long_range = source_occurrence_result(
        &Workspace {
            reference: "w1".into(),
            name: "demo".into(),
            path: directory.path().to_path_buf(),
            branch: "demo".into(),
        },
        long_range,
        false,
    )
    .unwrap();
    assert_eq!(
        long_range.hits[0]
            .source
            .as_deref()
            .unwrap()
            .lines()
            .count(),
        SOURCE_OCCURRENCE_ALL_LIMIT
    );
    assert_eq!(
        long_range.note.as_deref(),
        Some("+50 lines omitted; narrow the range")
    );
    let long_summary = render_summary(&SearchRun {
        reference: "q-range".into(),
        workspace_ref: "w1".into(),
        query: "Long.lean:1-250".into(),
        inference: long_range.inference.clone(),
        hits: long_range.hits.clone(),
        note: long_range.note.clone(),
        duration_ms: 1,
        created_at: 0,
    });
    assert!(long_summary.contains("\nline 200\n"));
    assert!(!long_summary.contains("\nline 201\n"));
    assert!(long_summary.ends_with("+50 lines omitted; narrow the range"));
    assert_eq!(parse_source_line_range("3-3"), Some((3, 3)));
    assert_eq!(parse_source_line_range("4-3"), None);
    assert_eq!(parse_source_line_range("0-3"), None);

    let project = directory.path().join("Project");
    fs::create_dir_all(&project).unwrap();
    fs::write(project.join("Nested.lean"), &source).unwrap();
    let recovered = parse_source_occurrence_query(
        directory.path(),
        directory.path(),
        None,
        "Mathlib/Project/Nested.lean:4-6",
    )
    .unwrap()
    .unwrap();
    assert_eq!(
        recovered.path,
        fs::canonicalize(project.join("Nested.lean")).unwrap()
    );
    assert!(recovered.display_path.is_none());
    let recovered =
        parse_source_occurrence_query(directory.path(), directory.path(), None, "Nested.lean:4-6")
            .unwrap()
            .unwrap();
    assert_eq!(
        recovered.path,
        fs::canonicalize(project.join("Nested.lean")).unwrap()
    );
    assert!(
            parse_source_occurrence_query(
                directory.path(),
                directory.path(),
                None,
                "Missing.lean:4-6",
            )
            .err()
            .unwrap()
            .to_string()
            .contains("source file not found or ambiguous")
        );

    let dependency = directory
        .path()
        .join(".lake/packages/mathlib/Mathlib/Topology");
    fs::create_dir_all(&dependency).unwrap();
    fs::write(dependency.join("Basic.lean"), &source).unwrap();
    let dependency = parse_goal_location(
        directory.path(),
        directory.path(),
        None,
        "Mathlib/Topology/Basic.lean:15 MORE",
    )
    .unwrap()
    .unwrap();
    assert_eq!(dependency.line, 15);
    assert!(dependency.more);
    assert!(!dependency.probe);
    assert_eq!(
        dependency.display_path.as_deref(),
        Some("Mathlib/Topology/Basic.lean")
    );
}

#[test]
fn missing_dependency_sources_are_detected_from_the_manifest() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("lake-manifest.json"), "{}").unwrap();
    assert!(dependency_sources_missing(directory.path()));
    fs::create_dir_all(directory.path().join(".lake/packages")).unwrap();
    assert!(!dependency_sources_missing(directory.path()));
}

#[test]
fn source_excerpts_center_the_match_and_report_file_lines() {
    let source = (1..=20)
        .map(|line| {
            if line == 12 {
                "theorem exact_match := by simp".to_owned()
            } else {
                format!("-- line {line}")
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    let (excerpt, line) =
        source_excerpt_with_limit(&source, "exact_match", &["exact_match".into()], 1, true, 8);
    let excerpt = excerpt.unwrap();
    assert_eq!(line, 12);
    assert!(excerpt.starts_with("-- line 10"));
    assert!(excerpt.contains("theorem exact_match"));
    assert_eq!(excerpt.lines().count(), 8);

    let dispersed = (1..=40)
        .map(|line| match line {
            5 => "def firstNeedle := 1".to_owned(),
            35 => "theorem secondNeedle : True := trivial".to_owned(),
            _ => format!("-- line {line}"),
        })
        .collect::<Vec<_>>()
        .join("\n");
    let (excerpt, line) = source_excerpt_with_limit(
        &dispersed,
        "firstNeedle secondNeedle",
        &["firstneedle".into(), "secondneedle".into()],
        1,
        true,
        48,
    );
    let excerpt = excerpt.unwrap();
    assert_eq!(line, 5);
    assert!(excerpt.contains("def firstNeedle"));
    assert!(excerpt.contains("theorem secondNeedle"));
    assert!(excerpt.lines().count() <= SOURCE_PREVIEW_LINES);
    assert_eq!(
        file_query_coverage_signature(
            "the first needle is present",
            &["first".into(), "second".into()]
        )
        .as_deref(),
        Some("partial source match 1/2")
    );

    let structure = "structure Config where\n  first : Nat\n  second : String\n  third : Bool\n\n/-- The next declaration. -/\ndef next := 1\n";
    let (excerpt, line) = detailed_source_excerpt(
        structure,
        "Config",
        &["config".into()],
        10,
        "structure",
        "Demo.Config",
    );
    assert_eq!(line, 10);
    let excerpt = excerpt.unwrap();
    assert!(excerpt.contains("third : Bool"));
    assert!(!excerpt.contains("next declaration"));

    let proof = (1..=20)
        .map(|line| format!("proof line {line}"))
        .collect::<Vec<_>>()
        .join("\n");
    let (excerpt, _) = detailed_source_excerpt(
        &proof,
        "proof line 1",
        &["proof".into()],
        1,
        "theorem",
        "Demo.proof",
    );
    assert_eq!(excerpt.unwrap().lines().count(), 20);
}

#[test]
fn source_excerpts_prefer_local_context_covering_the_query() {
    let source = "rw [Finsupp.sum_add_index]\nsimp [smul_eq_mul]\ntheorem Demo.outer : True := by\n  step 1\n  step 2\n  step 3\n  step 4\n  step 5\n  step 6\n  step 7\n  step 8\n  step 9\n  step 10\n  step 11\n  step 12\n  step 13\n  step 14\n  step 15\n  step 16\n  have hpush (q : α) : True := by\n    rw [Finsupp.sum_add_index]\n    simp\n    simp [smul_eq_mul]\n  exact hpush q\n  simp_rw [hpush]\n";
    let query = "Demo.outer hpush Finsupp.sum_add_index smul_eq_mul";
    let tokens = meaningful_query_tokens(query);
    let (excerpt, _) = detailed_source_excerpt(source, query, &tokens, 1, "theorem", "Demo.outer");
    let excerpt = excerpt.unwrap();
    assert!(excerpt.contains("have hpush"));
    assert!(excerpt.contains("Finsupp.sum_add_index"));
    assert!(excerpt.contains("smul_eq_mul"));

    let ambient = (1..=20)
        .map(|line| format!("variable (ambient{line} : Nat)"))
        .collect::<Vec<_>>()
        .join("\n");
    let source = format!("-- ambient context\n{ambient}\n\ndef requestedDefinition : Nat :=\n  42");
    let query = "missingLocalTerm requestedDefinition";
    let tokens = meaningful_query_tokens(query);
    let (excerpt, _) = detailed_source_excerpt(
        &source,
        query,
        &tokens,
        1,
        "def",
        "Demo.requestedDefinition",
    );
    let excerpt = excerpt.unwrap();
    assert!(excerpt.contains("def requestedDefinition"));
    assert!(excerpt.contains("42"));
}

#[test]
fn warming_fallback_finds_local_dependency_declarations() {
    let directory = tempfile::tempdir().unwrap();
    let package = directory.path().join(".lake/packages/demo/Demo");
    fs::create_dir_all(&package).unwrap();
    fs::write(
            package.join("Api.lean"),
            "namespace Bundle.ContinuousLinearMap\n\nclass topologicalSpaceTotalSpace : Prop where\n  value : True\n\nend Bundle.ContinuousLinearMap\n",
        )
        .unwrap();
    let hits = fallback_source_hits(
        directory.path(),
        "Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace",
        &["bundle.continuouslinearmap.topologicalspacetotalspace".into()],
    )
    .unwrap();
    assert!(
        hits.iter()
            .any(|hit| { hit.hit.name == "Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace" })
    );
}

#[test]
fn fallback_finds_symbolic_notation_literally() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("Notation.lean"),
        "def vectorAction (a : α) (v : β) := a *ᵥ v\n",
    )
    .unwrap();
    let query = "*ᵥ";
    let hits =
        fallback_source_hits(directory.path(), query, &meaningful_query_tokens(query)).unwrap();
    assert!(hits.iter().any(|hit| hit.hit.name == "vectorAction"));
}

#[test]
fn fallback_prefers_declarations_over_whole_file_matches() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
            directory.path().join("Support.lean"),
            "theorem continuous_of_support (f : α → β) : Continuous f := by sorry\n-- closure support zero neighborhood\n",
        )
        .unwrap();
    let tokens = meaningful_query_tokens("continuous support closure zero neighborhood");
    let hits = fallback_source_hits(
        directory.path(),
        "continuous support closure zero neighborhood",
        &tokens,
    )
    .unwrap();
    assert_eq!(hits[0].hit.name, "continuous_of_support");
}

#[test]
fn fallback_opens_an_explicit_module_before_broad_matches() {
    let directory = tempfile::tempdir().unwrap();
    let package = directory
        .path()
        .join(".lake/packages/demo/Mathlib/Topology");
    fs::create_dir_all(&package).unwrap();
    fs::write(
        package.join("Support.lean"),
        "theorem support_fact : True := trivial\n",
    )
    .unwrap();
    let query = "Mathlib.Topology.Support Function.support";
    let hits =
        fallback_source_hits(directory.path(), query, &meaningful_query_tokens(query)).unwrap();
    assert!(hits.iter().any(|hit| hit.hit.name == "support_fact"));
}

#[test]
fn fallback_keeps_lower_camel_declarations_in_broad_queries() {
    let directory = tempfile::tempdir().unwrap();
    let package = directory
        .path()
        .join(".lake/packages/mathlib/Mathlib/Topology/ContinuousMap");
    fs::create_dir_all(&package).unwrap();
    fs::write(
            package.join("Units.lean"),
            "namespace ContinuousMap\ndef unitsLift : True := trivial\ntheorem isUnit_iff_forall_isUnit : True := trivial\nend ContinuousMap\n",
        )
        .unwrap();
    let query = "ContinuousMap pointwise IsUnit iff global IsUnit and unitsLift construction";
    let hits =
        fallback_source_hits(directory.path(), query, &meaningful_query_tokens(query)).unwrap();
    assert!(
        hits.iter()
            .take(5)
            .any(|hit| hit.hit.name == "ContinuousMap.unitsLift")
    );
    assert!(
        hits.iter()
            .take(5)
            .any(|hit| hit.hit.name == "ContinuousMap.isUnit_iff_forall_isUnit")
    );
}

#[test]
fn fallback_opens_explicit_lean_file_import_lists() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("Root.lean"),
        "import Demo.One\nimport Demo.Two\n",
    )
    .unwrap();
    let query = "root Root.lean import list";
    let hits =
        fallback_source_hits(directory.path(), query, &meaningful_query_tokens(query)).unwrap();
    assert_eq!(hits[0].hit.name, "Root.imports");
    assert_eq!(
        hits[0].hit.source.as_deref(),
        Some("import Demo.One\nimport Demo.Two")
    );
}

#[test]
fn fallback_reserves_tied_coverage_for_project_sources() {
    let directory = tempfile::tempdir().unwrap();
    let dependencies = directory.path().join(".lake/packages/demo/Mathlib");
    fs::create_dir_all(&dependencies).unwrap();
    for index in 0..100 {
        fs::write(
            dependencies.join(format!("Noise{index}.lean")),
            format!("theorem noise{index} : True := by trivial\n-- finite continuous sum\n"),
        )
        .unwrap();
    }
    fs::write(
        directory.path().join("Metric.lean"),
        "theorem project_weightedSum : True := by trivial\n-- finite continuous sum\n",
    )
    .unwrap();
    let query = "finite continuous sum";
    let hits =
        fallback_source_hits(directory.path(), query, &meaningful_query_tokens(query)).unwrap();
    assert!(hits.iter().any(|hit| hit.hit.name == "project_weightedSum"));
}

#[test]
fn fallback_connects_trivialization_at_to_linearity_instance() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
            directory.path().join("Basic.lean"),
            "namespace VectorBundle\ninstance (priority := 100) trivialization_linear : e.IsLinear R := inferInstance\nend VectorBundle\n",
        )
        .unwrap();
    let query = "linear_trivializationAt isLinear_trivializationAt VectorBundle.trivializationAt";
    let hits =
        fallback_source_hits(directory.path(), query, &meaningful_query_tokens(query)).unwrap();
    assert!(
        hits.iter()
            .any(|hit| hit.hit.name == "VectorBundle.trivialization_linear")
    );
}

#[test]
fn fallback_connects_conceptual_inner_product_api_terms() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
            directory.path().join("Inner.lean"),
            "namespace InnerProductSpace\ndef ofCore (c : Core K E) : InnerProductSpace K E := by sorry\nend InnerProductSpace\nnamespace Submodule\ntheorem sup_orthogonal_of_hasOrthogonalProjection [K.HasOrthogonalProjection] : K ⊔ Kᗮ = ⊤ := by sorry\nend Submodule\n",
        )
        .unwrap();
    for (query, expected) in [
        (
            "InnerProductSpace.Core.toInnerProductSpace constructor",
            "InnerProductSpace.ofCore",
        ),
        (
            "orthogonal complement finite dimensional sup top",
            "Submodule.sup_orthogonal_of_hasOrthogonalProjection",
        ),
    ] {
        let hits =
            fallback_source_hits(directory.path(), query, &meaningful_query_tokens(query)).unwrap();
        assert!(hits.iter().any(|hit| hit.hit.name == expected));
    }
}

#[test]
fn fallback_respects_qualified_member_owner_order() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
            directory.path().join("Core.lean"),
            "structure PreInnerProductSpace.Core where\n  conj_inner_symm : True\nstructure InnerProductSpace.Core extends PreInnerProductSpace.Core where\n  definite : True\n",
        )
        .unwrap();
    let query = "InnerProductSpace.Core.definite PreInnerProductSpace.Core.conj_inner_symm";
    let hits =
        fallback_source_hits(directory.path(), query, &meaningful_query_tokens(query)).unwrap();
    assert_eq!(hits[0].hit.name, "InnerProductSpace.Core");
    assert!(
        hits[0]
            .hit
            .signature
            .as_deref()
            .unwrap()
            .contains("InnerProductSpace.Core.toPreInnerProductSpaceCore")
    );
}

#[test]
fn fallback_includes_root_qualified_member_owner_structure() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
            directory.path().join("Metric.lean"),
            "namespace AtiyahSinger\nstructure HermitianBundleMetric where\n  inner : True\n  continuous : True\nnamespace HermitianBundleMetric\ntheorem pos_inner : True := trivial\nend HermitianBundleMetric\nend AtiyahSinger\n",
        )
        .unwrap();
    let query = "HermitianBundleMetric.pos_inner continuity WhitneySquare";
    let hits =
        fallback_source_hits(directory.path(), query, &meaningful_query_tokens(query)).unwrap();
    assert_eq!(hits[0].hit.name, "AtiyahSinger.HermitianBundleMetric");
    assert!(
        hits[0]
            .hit
            .source
            .as_deref()
            .unwrap()
            .contains("continuous : True")
    );
}

#[test]
fn fallback_honors_named_argument_queries() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
            directory.path().join("Precomp.lean"),
            "namespace CategoryTheory\ndef precomp (α : X) := α\nend CategoryTheory\nnamespace ContinuousLinearMap\ndef precomp (G) (L : E → F) := L\nend ContinuousLinearMap\n",
        )
        .unwrap();
    let query = "precomp (L :=)";
    let hits =
        fallback_source_hits(directory.path(), query, &meaningful_query_tokens(query)).unwrap();
    assert_eq!(hits[0].hit.name, "ContinuousLinearMap.precomp");
    assert!(
        hits[0]
            .hit
            .signature
            .as_deref()
            .unwrap()
            .contains("(L : E → F)")
    );
}
