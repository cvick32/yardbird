use rustc_hash::FxHashMap;
use smt2parser::vmt::ReadsAndWrites;
use smt2parser::vmt::VMTModel;
use yardbird::cost_functions::array::ArrayAstSize;
use yardbird::problem_context::ArrayCandidateCatalog;
use yardbird::quantified_rule::{
    QuantifiedRuleKind, QuantifiedRuleProvenance, TransitionGuardRule,
};
use yardbird::theories::array::{
    array_axioms::{
        expr_to_term, generate_array_instantiation_candidates, ArrayExpr,
        ArrayInstantiationInstrumentation, ArrayInstantiationOptions, ArrayLanguage,
    },
    array_rule_instantiator::ArrayArtifactCapture,
    candidate_scope::CandidateScope,
    transition_guard_instantiator::supports_transition_guard,
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
    let result = generate_array_instantiation_candidates(
        &egraph,
        cost,
        &[("Int".to_string(), "Int".to_string())],
        ArrayInstantiationOptions {
            candidate_catalog: ArrayCandidateCatalog::default(),
            candidate_scope: CandidateScope::AllCandidates,
            refinement_step: 0,
            selection_counts: FxHashMap::default(),
            depth: 0,
            instrumentation: ArrayInstantiationInstrumentation {
                artifact_capture: ArrayArtifactCapture::default(),
                profiling: None,
            },
        },
    );

    result
        .candidates
        .into_iter()
        .map(|instance| expr_to_term(instance.expression).to_string())
        .collect()
}

fn run_abstract_german(depth: u16) -> ProofLoopResult {
    let mut config = z3::Config::new();
    config.set_model_generation(true);

    z3::with_z3_config(&config, || {
        let mut options = YardbirdOptions::from_filename(
            "examples/distributed_protocols/german/german.vmt".to_string(),
        );
        options.depth = depth;
        options.strategy = Strategy::Abstract;
        options.solver = SolverBackend::Z3;

        let model = model_from_options(&options);
        let instantiation_strategy = options.build_instantiation_strategy();
        let mut driver = Driver::new(model, instantiation_strategy, options.solver);

        driver
            .check_strategy(options.depth, options.build_array_strategy())
            .expect("German should be bounded-safe through the requested depth")
    })
}

#[test]
fn german_catalogs_only_its_quantified_transition_guard() {
    let model = VMTModel::from_path("examples/distributed_protocols/german/german.vmt").unwrap();
    let (abstracted_model, _) = model.abstract_array_theory();
    let guards = abstracted_model
        .get_transition_guards()
        .into_iter()
        .enumerate()
        .map(|(ordinal, guard)| TransitionGuardRule::from_parsed(guard, ordinal))
        .collect::<Vec<_>>();

    assert_eq!(guards.len(), 1);
    let guard = &guards[0];
    assert_eq!(
        guard.metadata().name(),
        "transition-guard-grantExclusiveRule-0"
    );
    assert_eq!(guard.metadata().kind(), QuantifiedRuleKind::TransitionGuard);
    assert_eq!(
        guard.metadata().provenance(),
        &QuantifiedRuleProvenance::TransitionGuard {
            action: "grantExclusiveRule".to_string(),
            ordinal: 0,
        }
    );
    assert_eq!(
        guard.quantified_formula().to_string(),
        "(forall ((|I:client| client)) (not (Read_client_Bool homeSharerList |I:client|)))"
    );
}

#[test]
fn german_abstraction_removes_its_supported_transition_guard() {
    let model = VMTModel::from_path("examples/distributed_protocols/german/german.vmt").unwrap();
    let (abstracted_model, _) = model.abstract_array_theory();
    let rules = abstracted_model
        .get_transition_guards()
        .into_iter()
        .enumerate()
        .map(|(ordinal, guard)| TransitionGuardRule::from_parsed(guard, ordinal))
        .filter(supports_transition_guard)
        .collect::<Vec<_>>();
    let selected = rules
        .iter()
        .map(|rule| rule.parsed().clone())
        .collect::<Vec<_>>();

    let (abstracted_model, removed) = abstracted_model.abstract_transition_guards(&selected);

    assert_eq!(removed, selected);
    assert!(abstracted_model.get_transition_guards().is_empty());
    assert!(!abstracted_model
        .get_trans_condition_for_yardbird()
        .to_string()
        .contains("I:client"));
}

#[test]
fn german_depth_two_characterizes_current_array_refinement() {
    let result = run_abstract_german(2);
    let used_instances = result
        .used_instances
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    assert_eq!(result.total_refinement_steps, 4);
    assert_eq!(result.total_instantiations_added, 4);
    assert!(!result.counterexample);
    assert!(!result.found_proof);
    assert_eq!(used_instances.len(), 2);
    assert!(used_instances
        .iter()
        .any(|instance| { instance.contains("(ConstArr_client_Bool homeCurrentReqExclusive+0)") }));
    assert!(used_instances
        .iter()
        .any(|instance| instance.contains("(ConstArr_client_Bool grantExclusiveRule+0)")));
}

#[test]
fn german_depth_five_does_not_force_an_unneeded_transition_guard() {
    let result = run_abstract_german(5);
    let guard_instances = result
        .used_instances
        .iter()
        .map(ToString::to_string)
        .filter(|instance| instance.starts_with("(=> grantExclusiveRule+"))
        .collect::<Vec<_>>();
    assert!(guard_instances.is_empty());
    assert!(!result.counterexample);
}

/// Regression boundary for the direct-searcher implementation: all three
/// quantified rules must continue to emit the same ground SMT formulas.
#[test]
fn array_generation_characterizes_all_three_ground_rules() {
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
