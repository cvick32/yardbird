use smt2parser::{concrete::SyntaxBuilder, vmt::VMTModel, CommandStream};
use yardbird::{
    auxiliary_synthesis::{AuxSynthesisConfig, ConditionalHistory, GuardPolicy, SynthesisTrigger},
    cost_functions::array::{AdaptiveArrayCost, ArrayBMCCost},
    instantiation_strategy::full_unroll::FullUnrollStrategy,
    strategies::{Abstract, ConcreteArrayZ3, ProofStrategy},
    theories::array::array_rule_instantiator::ArrayArtifactCapture,
    Driver, Error, SolverBackend,
};

fn parse_vmt(property: &str) -> VMTModel {
    let input = format!(
        r#"
        (declare-fun a () (Array Int Int))
        (declare-fun a_next () (Array Int Int))
        (define-fun .a () (Array Int Int) (! a :next a_next))

        (define-fun init () Bool (! true :init true))
        (define-fun transition () Bool (! (= a_next a) :trans true))
        (define-fun property () Bool (! {property} :invar-property 0))
        "#
    );
    let commands = CommandStream::new(input.as_bytes(), SyntaxBuilder, None)
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    VMTModel::checked_from(commands).unwrap()
}

fn check_abstract_model(
    model: VMTModel,
    depth: u16,
) -> yardbird::Result<yardbird::ProofLoopResult> {
    check_abstract_model_with_aux(model, depth, AuxSynthesisConfig::default())
}

fn check_abstract_model_with_aux(
    model: VMTModel,
    depth: u16,
    aux_config: AuxSynthesisConfig,
) -> yardbird::Result<yardbird::ProofLoopResult> {
    let aux_enabled = !aux_config.is_off();
    let mut driver = Driver::new(
        model,
        Box::new(FullUnrollStrategy::new()),
        SolverBackend::Z3,
    );
    if aux_enabled {
        driver.add_extension(ConditionalHistory::<ArrayBMCCost>::new(aux_config, ()));
    }
    let strategy: Box<dyn ProofStrategy<_>> = Box::new(
        Abstract::<ArrayBMCCost>::new(depth, false, (), false).with_artifact_capture(
            ArrayArtifactCapture {
                conflicts: aux_enabled,
                ..ArrayArtifactCapture::default()
            },
        ),
    );
    driver.check_strategy(depth, strategy)
}

fn check_concrete_model(
    model: VMTModel,
    depth: u16,
) -> yardbird::Result<yardbird::ProofLoopResult> {
    let mut driver = Driver::new(
        model,
        Box::new(FullUnrollStrategy::new()),
        SolverBackend::Z3,
    );
    let strategy: Box<dyn ProofStrategy<_>> = Box::new(ConcreteArrayZ3::new(false));
    driver.check_strategy(depth, strategy)
}

fn check_adaptive_model_with_aux(
    model: VMTModel,
    depth: u16,
    aux_config: AuxSynthesisConfig,
) -> yardbird::Result<yardbird::ProofLoopResult> {
    let mut driver = Driver::new(
        model,
        Box::new(FullUnrollStrategy::new()),
        SolverBackend::Z3,
    );
    driver.add_extension(ConditionalHistory::<AdaptiveArrayCost>::new(aux_config, ()));
    let strategy: Box<dyn ProofStrategy<_>> = Box::new(
        Abstract::<AdaptiveArrayCost>::new(depth, false, (), false).with_artifact_capture(
            ArrayArtifactCapture {
                conflicts: true,
                ..ArrayArtifactCapture::default()
            },
        ),
    );
    driver.check_strategy(depth, strategy)
}

#[test]
fn no_refinements_trigger_a_concrete_counterexample_check() {
    let model = parse_vmt("(= (select a 0) 1)");

    assert!(matches!(
        check_abstract_model(model, 1),
        Err(Error::Counterexample)
    ));
}

#[test]
fn concrete_unsat_stall_is_reported_as_abstraction_exhaustion() {
    // The abstract Write function may return a different array, but native
    // array semantics prove that storing the value already at an index is a no-op.
    let model = parse_vmt("(= (store a 0 (select a 0)) a)");

    assert!(matches!(
        check_abstract_model(model, 1),
        Err(Error::AbstractionExhausted { depth: 0 })
    ));
}

#[test]
fn buggy_generated_array_copy_is_confirmed_concretely() {
    let model = VMTModel::from_path("examples/counterexamples/array_copy_bug.vmt").unwrap();

    assert!(matches!(
        check_abstract_model(model, 3),
        Err(Error::Counterexample)
    ));
}

#[test]
fn german_concrete_does_not_use_integer_array_logic() {
    let model = VMTModel::from_path("examples/distributed_protocols/german/german.vmt").unwrap();

    let result = check_concrete_model(model, 2).unwrap();

    assert!(!result.counterexample);
}

#[test]
fn german_abstract_is_discharged_through_depth_eight_without_concrete_fallback() {
    let model = VMTModel::from_path("examples/distributed_protocols/german/german.vmt").unwrap();

    let result = check_abstract_model(model, 9).unwrap();

    assert!(!result.counterexample);
    assert_eq!(
        result
            .solver_statistics
            .get_f64("concrete_validation_checks"),
        Some(0.0),
        "German should be discharged by abstract refinement without concrete fallback"
    );
}

#[test]
fn abstract_herbrandization_keeps_array_sorted_witnesses_abstract() {
    let model = parse_vmt("(forall ((b (Array Int Int))) (= (select b 0) (select b 0)))");

    let result = check_abstract_model(model, 1).unwrap();

    assert!(!result.counterexample);
}

#[test]
fn true_guard_auxiliary_candidate_is_synthesized_after_concrete_validation() {
    let model = VMTModel::from_path("examples/array/array_init_increm_two_arrs_const.vmt").unwrap();
    let result = check_abstract_model_with_aux(
        model,
        6,
        AuxSynthesisConfig {
            trigger: SynthesisTrigger::NonLocal,
            guard_policy: GuardPolicy::True,
            ..AuxSynthesisConfig::default()
        },
    )
    .unwrap();

    assert_eq!(
        result
            .solver_statistics
            .get_f64("concrete_validation_checks"),
        Some(1.0)
    );
    assert_eq!(result.auxiliary_records.len(), 1);
    assert!(result.used_instances.iter().any(|term| {
        let term = term.to_string();
        term.contains("(not (= i+4 i+0))") && term.contains("(Write_Int_Int b+0 i+0")
    }));
}

#[test]
fn interpolant_guard_is_classified_ranked_and_installed() {
    let model = VMTModel::from_path("examples/array/array_init_increm_two_arrs_const.vmt").unwrap();
    let result = check_abstract_model_with_aux(
        model,
        6,
        AuxSynthesisConfig {
            trigger: SynthesisTrigger::NonLocal,
            guard_policy: GuardPolicy::Interpolant,
            ..AuxSynthesisConfig::default()
        },
    )
    .unwrap();

    assert_eq!(
        result
            .solver_statistics
            .get_f64("concrete_validation_checks"),
        Some(1.0)
    );
    assert_eq!(result.auxiliary_records.len(), 1);
    let record = &result.auxiliary_records[0];
    assert_eq!(record.guard_policy, GuardPolicy::Interpolant);
    assert_eq!(record.capture_guard, "(and (= pc 2) (= 1 i))");
    assert_eq!(
        record.capture_mode,
        yardbird::auxiliary_synthesis::HistoryCaptureMode::LastOccurrence
    );
    let selection = record.interpolant_guard_selection.as_ref().unwrap();
    assert_eq!(selection.predicate_index, 37);
    assert_eq!(selection.ranker, "ArrayBMCCost");
    assert!(selection.structurally_scored);
    assert!(selection.eligible_count > 0);
    assert!(!selection.rejected.is_empty());
    assert!(result.used_instances.iter().any(|term| {
        let term = term.to_string();
        term.contains("(not (= i+4 i+0))") && term.contains("(Write_Int_Int b+0 i+0")
    }));
}

#[test]
fn hybr_sum_matches_the_paper_capture_epoch_and_property_guard() {
    let model = VMTModel::from_path("examples/array/array_hybr_sum.vmt").unwrap();
    let result = check_adaptive_model_with_aux(
        model,
        6,
        AuxSynthesisConfig {
            trigger: SynthesisTrigger::NonLocal,
            guard_policy: GuardPolicy::Interpolant,
            ..AuxSynthesisConfig::default()
        },
    )
    .unwrap();

    assert_eq!(result.auxiliary_records.len(), 1);
    let record = &result.auxiliary_records[0];
    assert_eq!(record.capture_term, "i");
    assert_eq!(record.capture_guard, "(and (= pc 1) (<= 0 j))");
    assert_eq!(
        record.capture_mode,
        yardbird::auxiliary_synthesis::HistoryCaptureMode::LastOccurrence
    );
    let selection = record.interpolant_guard_selection.as_ref().unwrap();
    assert_eq!(selection.predicate, "(<= 0 j)");
    assert!(selection.property_overlap);
}
