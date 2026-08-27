//! Small manual replay corpus distilled from real fleet searches.

pub(super) struct ReplayCase {
    pub(super) query: &'static str,
    pub(super) candidates: &'static [(&'static str, f64)],
    pub(super) top_one: &'static str,
    pub(super) required_top_five: &'static [&'static str],
}

pub(super) const SEARCH_REPLAY_CASES: &[ReplayCase] = &[
    ReplayCase {
        query: "matrixToeplitzOperator_add|matrixToeplitzOperator_smul",
        candidates: &[
            ("smul_add_smul_le_smul_add_smul", 500.0),
            ("AtiyahSinger.matrixToeplitzOperator_isFredholm", 100.0),
            ("AtiyahSinger.matrixToeplitzOperator_add", 50.0),
        ],
        top_one: "AtiyahSinger.matrixToeplitzOperator_add",
        required_top_five: &["AtiyahSinger.matrixToeplitzOperator_isFredholm"],
    },
    ReplayCase {
        query: "Bundle.Trivial.continuousLinearMapAt|continuousLinearMapAt_trivial",
        candidates: &[
            ("Bundle.Trivial", 500.0),
            ("Bundle.Trivial.continuousLinearMapAt_trivialization", 100.0),
        ],
        top_one: "Bundle.Trivial.continuousLinearMapAt_trivialization",
        required_top_five: &["Bundle.Trivial"],
    },
    ReplayCase {
        query: "CircleClutching.*homotopy|TransitionHomotopy|ClutchingBundle.*homotopy",
        candidates: &[
            (
                "AtiyahSinger.ComplexVectorBundle.thickOverlapTransition_homotopyClass_eq",
                500.0,
            ),
            (
                "AtiyahSinger.CircleClutchingTransitionHomotopy.forward_homotopy",
                80.0,
            ),
            ("AtiyahSinger.CircleClutchingTransitionHomotopy", 70.0),
            ("AtiyahSinger.circleClutchingArcHomotopy", 60.0),
        ],
        top_one: "AtiyahSinger.CircleClutchingTransitionHomotopy.forward_homotopy",
        required_top_five: &[
            "AtiyahSinger.CircleClutchingTransitionHomotopy",
            "AtiyahSinger.circleClutchingArcHomotopy",
        ],
    },
    ReplayCase {
        query: "ContinuousLinearMap.stabilizationAssembly_apply|ContinuousLinearMap.prodMap_apply|matrixToeplitzOperatorGLParametric_apply",
        candidates: &[
            (
                "AtiyahSinger.ContinuousLinearMap.stabilizationKernelEquiv",
                500.0,
            ),
            (
                "AtiyahSinger.ContinuousLinearMap.stabilizationAssembly_apply",
                80.0,
            ),
            (
                "AtiyahSinger.matrixToeplitzOperatorGLParametric_apply",
                70.0,
            ),
        ],
        top_one: "AtiyahSinger.ContinuousLinearMap.stabilizationAssembly_apply",
        required_top_five: &["AtiyahSinger.matrixToeplitzOperatorGLParametric_apply"],
    },
];
