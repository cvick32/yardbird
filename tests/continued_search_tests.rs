use smt2parser::{concrete::SyntaxBuilder, CommandStream};
use std::time::Duration;
use yardbird::policy::term_selection::array::ArrayBMCCost;
use yardbird::smtlib_problem::{RefinementLimits, SMTLIBProblem, SmtlibRefinementRunner};
use yardbird::strategies::Abstract;
use yardbird::{SolverBackend, YardbirdPolicy};

fn problem(source: &str) -> SMTLIBProblem {
    let commands = CommandStream::new(source.as_bytes(), SyntaxBuilder, None)
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    SMTLIBProblem::from_commands(commands).unwrap()
}

#[test]
fn smtlib_stalled_refinement_times_out_without_repeating_concrete_validation() {
    // Equality of entire arrays requires extensionality, which these three
    // built-in axioms do not provide. Keep searching, with no false SAT/UNSAT.
    let input = problem(
        "(set-logic QF_AUFLIA)
         (declare-fun a () (Array Int Int))
         (assert (not (= (store a 0 (select a 0)) a)))
         (check-sat)",
    );
    let (result, _) = SmtlibRefinementRunner::execute(
        &input,
        Box::new(Abstract::<ArrayBMCCost>::new(
            0,
            false,
            YardbirdPolicy::new(()),
            false,
        )),
        SolverBackend::Z3,
        RefinementLimits {
            wall_timeout: Some(Duration::from_secs(2)),
            ..Default::default()
        },
        false,
        None,
        None,
    )
    .unwrap();
    assert_eq!(result.run_progress.unwrap().termination_reason, "timeout");
    assert!(!result.found_proof && !result.counterexample);
    assert!(result.total_refinement_steps > 0);
    assert!(u64::from(result.total_refinement_steps) <= result.total_instantiations_added + 1);
    assert_eq!(
        result
            .solver_statistics
            .get_f64("concrete_validation_checks"),
        Some(1.0)
    );
}

#[test]
fn smtlib_explicit_refinement_limit_is_inconclusive() {
    let input = problem(
        "(set-logic QF_AUFLIA) (declare-fun a () (Array Int Int)) (assert false) (check-sat)",
    );
    let (result, _) = SmtlibRefinementRunner::execute(
        &input,
        Box::new(Abstract::<ArrayBMCCost>::new(
            0,
            false,
            YardbirdPolicy::new(()),
            false,
        )),
        SolverBackend::Z3,
        RefinementLimits {
            max_refinements: Some(0),
            ..Default::default()
        },
        false,
        None,
        None,
    )
    .unwrap();
    assert_eq!(
        result.run_progress.unwrap().termination_reason,
        "refinement_limit"
    );
    assert!(!result.found_proof && !result.counterexample);
    assert_eq!(result.total_refinement_steps, 0);
}
