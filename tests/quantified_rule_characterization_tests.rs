use std::collections::HashSet;

use rustc_hash::FxHashMap;
use smt2parser::vmt::ReadsAndWrites;
use yardbird::cost_functions::array::ArrayAstSize;
use yardbird::problem_context::ArrayCandidateCatalog;
use yardbird::theories::array::{
    array_axioms::{
        expr_to_term, saturate_with_array_types, ArrayExpr, ArrayLanguage,
        ArraySaturationInstrumentation, ArraySaturationOptions,
    },
    array_conflict_scheduler::ArrayArtifactCapture,
    candidate_scope::CandidateScope,
};
use yardbird::{
    model_from_options, Driver, ProofLoopResult, SolverBackend, Strategy, YardbirdOptions,
};

fn generated_array_instances(expression: &str) -> Vec<String> {
    let expression = expression.parse::<ArrayExpr>().unwrap();
    let mut egraph = egg::EGraph::<ArrayLanguage, ()>::default();
    egraph.add_expr(&expression);
    egraph.rebuild();

    let cost = ArrayAstSize {
        current_bmc_depth: 0,
        init_and_transition_system_terms: vec![],
        property_terms: vec![],
        reads_writes: ReadsAndWrites::default(),
    };
    let result = saturate_with_array_types(
        &mut egraph,
        cost,
        &[("Int".to_string(), "Int".to_string())],
        ArraySaturationOptions {
            candidate_catalog: ArrayCandidateCatalog::default(),
            candidate_scope: CandidateScope::AllCandidates,
            excluded_instantiations: HashSet::new(),
            refinement_step: 0,
            selection_counts: FxHashMap::default(),
            depth: 0,
            instrumentation: ArraySaturationInstrumentation {
                artifact_capture: ArrayArtifactCapture::default(),
                profiling: None,
            },
        },
    );

    result
        .instantiations
        .into_iter()
        .chain(result.const_instantiations)
        .map(|instance| expr_to_term(instance.expression).to_string())
        .collect()
}

fn run_abstract_german_depth_two() -> ProofLoopResult {
    let mut config = z3::Config::new();
    config.set_model_generation(true);

    z3::with_z3_config(&config, || {
        let mut options = YardbirdOptions::from_filename(
            "examples/distributed_protocols/german/german.vmt".to_string(),
        );
        options.depth = 2;
        options.strategy = Strategy::Abstract;
        options.solver = SolverBackend::Z3;

        let model = model_from_options(&options);
        let instantiation_strategy = options.build_instantiation_strategy();
        let mut driver = Driver::new(model, instantiation_strategy, options.solver);

        driver
            .check_strategy(options.depth, options.build_array_strategy())
            .expect("German should be bounded-safe through depth 1")
    })
}

#[test]
fn german_depth_two_characterizes_current_array_refinement() {
    let result = run_abstract_german_depth_two();
    let used_instances = result
        .used_instances
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>();

    assert_eq!(result.total_refinement_steps, 4);
    assert_eq!(result.total_instantiations_added, 5);
    assert!(!result.counterexample);
    assert!(!result.found_proof);
    assert_eq!(
        used_instances,
        vec![
            "(= (Read_client_Bool (ConstArr_client_Bool homeCurrentReqExclusive+0) yardbird_herbrand_0+0) homeCurrentReqExclusive+0)",
            "(=> (not (= yardbird_herbrand_0+1 |fml:cl+0|)) (= (Read_client_Bool (Write_client_Bool cacheShared+1 |fml:cl+0| receiveExclusiveGrantRule+0) yardbird_herbrand_0+1) (Read_client_Bool cacheShared+1 yardbird_herbrand_0+1)))",
            "(= (Read_client_Bool (ConstArr_client_Bool grantExclusiveRule+0) homeCurrentclient+0) grantExclusiveRule+0)",
        ]
    );
}

/// Regression boundary for the direct-searcher implementation: all three
/// quantified rules must continue to emit the same ground SMT formulas.
#[test]
fn array_saturation_characterizes_all_three_ground_rules() {
    assert_eq!(
        generated_array_instances("(Read Int Int (Write Int Int A i v) j)"),
        vec!["(=> (not (= j i)) (= (Read_Int_Int (Write_Int_Int A i v) j) (Read_Int_Int A j)))"]
    );
    assert_eq!(
        generated_array_instances("(Read Int Int (Write Int Int A i v) i)"),
        vec!["(= (Read_Int_Int (Write_Int_Int A i v) i) v)"]
    );
    assert_eq!(
        generated_array_instances("(Read Int Int (ConstArr Int Int v) i)"),
        vec!["(= (Read_Int_Int (ConstArr_Int_Int v) i) v)"]
    );
}
