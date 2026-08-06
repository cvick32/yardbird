use smt2parser::{concrete::SyntaxBuilder, vmt::VMTModel, CommandStream};
use yardbird::{
    auxiliary_synthesis::AuxSynthesisConfig,
    cost_functions::array::ArrayBMCCost,
    instantiation_strategy::full_unroll::FullUnrollStrategy,
    strategies::{Abstract, ProofStrategy},
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
    let mut driver = Driver::new(
        model,
        Box::new(FullUnrollStrategy::new()),
        SolverBackend::Z3,
    );
    let strategy: Box<dyn ProofStrategy<_>> = Box::new(Abstract::<ArrayBMCCost>::new(
        depth,
        false,
        (),
        AuxSynthesisConfig::default(),
        false,
    ));
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
fn concrete_unsat_stall_advances_to_the_next_depth() {
    // The abstract Write function may return a different array, but native
    // array semantics prove that storing the value already at an index is a no-op.
    let model = parse_vmt("(= (store a 0 (select a 0)) a)");

    let result = check_abstract_model(model, 1).unwrap();

    assert!(!result.counterexample);
    assert_eq!(result.total_refinement_steps, 1);
    assert_eq!(result.total_instantiations_added, 0);
}

#[test]
fn buggy_generated_array_copy_is_confirmed_concretely() {
    let model = VMTModel::from_path("examples/counterexamples/array_copy_bug.vmt").unwrap();

    assert!(matches!(
        check_abstract_model(model, 3),
        Err(Error::Counterexample)
    ));
}
