use smt2parser::concrete::Term;

use crate::profiling::{SolverCheckMeasurement, SolverCheckPhase, SolverCheckTimer};

use super::{SolverCheckResult, YardbirdSolver};

/// Describes the solver-side work that belongs to one satisfiability check.
///
/// The three Yardbird execution modes differ in their surrounding state, but
/// share this lifecycle. VMT checks provide a temporary property, refinement
/// checks provide model terms, and direct SMT-LIB commands provide neither.
pub(crate) struct SolverCheckRequest<'a> {
    pub profiling_enabled: bool,
    pub assertion_count: u64,
    pub temporary_negated_property: Option<&'a Term>,
    pub model_terms: Option<&'a [Term]>,
    pub capture_unsat_core: bool,
}

pub(crate) struct SolverCheckOutcome {
    pub result: SolverCheckResult,
    pub measurement: Option<SolverCheckMeasurement>,
}

/// Execute and measure one solver check.
///
/// Callers remain responsible for `complete_check()`: direct SMT-LIB
/// `check-sat-assuming` must first remove its temporary assumption scope so
/// that the capture transcript associates that pop with the completed check.
pub(crate) fn run_solver_check(
    solver: &mut dyn YardbirdSolver,
    request: SolverCheckRequest<'_>,
) -> SolverCheckOutcome {
    let mut timer =
        SolverCheckTimer::new(request.profiling_enabled, || solver.get_solver_statistics());

    if let Some(property) = request.temporary_negated_property {
        timer.measure(SolverCheckPhase::PropertyPush, || {
            solver.push();
            solver
                .assert_not_term(property)
                .expect("solver should assert the negated property");
        });
    }

    let (result, raw_check_elapsed) = timer.measure_raw(|| solver.check_sat());

    if result == SolverCheckResult::Sat {
        if let Some(model_terms) = request.model_terms {
            timer.measure(SolverCheckPhase::ModelAcquisition, || {
                solver
                    .capture_model(model_terms)
                    .expect("solver should capture a model after SAT");
            });
        }
    }

    timer.measure(SolverCheckPhase::ProofCoreAccess, || {
        let _ = solver.inspect_last_proof();
        if request.capture_unsat_core && result == SolverCheckResult::Unsat {
            let _ = solver.capture_unsat_core();
        }
    });
    let reason_unknown = (result == SolverCheckResult::Unknown)
        .then(|| solver.get_reason_unknown())
        .flatten();

    if request.temporary_negated_property.is_some() {
        timer.measure(SolverCheckPhase::PropertyPop, || solver.pop(1));
    }

    timer.measure(SolverCheckPhase::StatisticsCollection, || {
        solver.record_statistics(raw_check_elapsed);
    });
    let measurement = timer.finish(result, reason_unknown, request.assertion_count, || {
        solver.get_solver_statistics()
    });

    SolverCheckOutcome {
        result,
        measurement,
    }
}
