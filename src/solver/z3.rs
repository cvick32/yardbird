use smt2parser::concrete::{Command, Sort, Symbol, Term};
use std::time::Duration;
use z3::ast::Bool;

use super::{z3_ext::ModelExt, z3_var_context::Z3VarContext};
use crate::{
    proof_tree::ProofTree,
    solver::{SolverCheckResult, YardbirdSolver},
    utils::{SolverStatistics, StatisticsValue},
    SolverBackend,
};

impl From<z3::SatResult> for SolverCheckResult {
    fn from(result: z3::SatResult) -> Self {
        match result {
            z3::SatResult::Sat => SolverCheckResult::Sat,
            z3::SatResult::Unsat => SolverCheckResult::Unsat,
            z3::SatResult::Unknown => SolverCheckResult::Unknown,
        }
    }
}

pub struct Z3SolverBackend {
    z3_var_context: Z3VarContext,
    solver: z3::Solver,
    solver_statistics: SolverStatistics,
    last_result: Option<SolverCheckResult>,
    model_captured: bool,
    newest_model: Option<z3::Model>,
}

impl Z3SolverBackend {
    pub(crate) fn new(logic: &str) -> Self {
        let solver = z3::Solver::new_for_logic(logic).unwrap();
        configure_z3_solver(&solver);
        Self {
            z3_var_context: Z3VarContext::new(),
            solver,
            solver_statistics: SolverStatistics::new(),
            last_result: None,
            model_captured: false,
            newest_model: None,
        }
    }
}

fn configure_z3_solver(solver: &z3::Solver) {
    // Yardbird's abstraction is model-driven, so pin the solver seed to keep
    // counterexample models reproducible across runs.
    z3::set_global_param("smt.random_seed", "0");
    z3::set_global_param("sat.random_seed", "0");

    let mut params = z3::Params::new();
    params.set_u32("random_seed", 0);
    solver.set_params(&params);
}

fn join_from_z3_statistics(stats: &mut SolverStatistics, z3_stats: z3::Statistics) {
    for entry in z3_stats.entries() {
        let value = match entry.value {
            z3::StatisticsValue::UInt(int_num) => StatisticsValue::UInt(int_num.into()),
            z3::StatisticsValue::Double(float_num) => StatisticsValue::Double(float_num),
        };
        stats.insert(entry.key, value);
    }
}

impl YardbirdSolver for Z3SolverBackend {
    fn backend(&self) -> SolverBackend {
        SolverBackend::Z3
    }

    fn accept_command(&mut self, command: &Command) -> anyhow::Result<()> {
        let _ = command.clone().accept(&mut self.z3_var_context);
        Ok(())
    }

    fn create_variable(&mut self, symbol: &Symbol, sort: &Sort) -> anyhow::Result<()> {
        self.z3_var_context.create_variable(symbol, sort);
        Ok(())
    }

    fn assert_term(&mut self, term: &Term) -> anyhow::Result<()> {
        let z3_term = self.z3_var_context.rewrite_term(term);
        self.solver.assert(z3_term.as_bool().unwrap());
        Ok(())
    }

    fn assert_not_term(&mut self, term: &Term) -> anyhow::Result<()> {
        let z3_term = self.z3_var_context.rewrite_term(term);
        let negated = Bool::not(&z3_term.as_bool().unwrap());
        self.solver.assert(&negated);
        Ok(())
    }

    fn assert_terms_conjunctively(&mut self, terms: &[Term]) -> anyhow::Result<()> {
        match terms {
            [] => {}
            [term] => self.assert_term(term)?,
            _ => {
                let z3_terms = terms
                    .iter()
                    .map(|term| {
                        self.z3_var_context
                            .rewrite_term(term)
                            .as_bool()
                            .expect("[Z3] instantiation term must be boolean")
                    })
                    .collect();
                let conjunction = self.z3_var_context.make_and(z3_terms);
                self.solver.assert(&conjunction);
            }
        }
        Ok(())
    }

    fn assert_tracked_term(&mut self, term: &Term, label: &str) -> anyhow::Result<()> {
        let z3_term = self.z3_var_context.rewrite_term(term);
        let tracked_bool = Bool::new_const(label);
        self.solver
            .assert_and_track(z3_term.as_bool().unwrap(), &tracked_bool);
        Ok(())
    }

    fn push(&mut self) {
        self.solver.push();
    }

    fn pop(&mut self, levels: u32) {
        self.solver.pop(levels);
    }

    fn check_sat(&mut self) -> SolverCheckResult {
        let result = SolverCheckResult::from(self.solver.check());
        self.last_result = Some(result);
        self.model_captured = false;
        if result != SolverCheckResult::Sat {
            self.newest_model = None;
        }
        result
    }

    fn capture_model(&mut self, _terms: &[Term]) -> anyhow::Result<()> {
        if self.last_result != Some(SolverCheckResult::Sat) {
            anyhow::bail!("a Z3 model can only be captured after SAT");
        }
        let model = self
            .solver
            .get_model()
            .ok_or_else(|| anyhow::anyhow!("Z3 returned SAT without an available model"))?;
        self.newest_model = Some(model);
        self.model_captured = true;
        Ok(())
    }

    fn record_statistics(&mut self, solver_elapsed: Duration) {
        join_from_z3_statistics(&mut self.solver_statistics, self.solver.get_statistics());
        self.solver_statistics
            .add_time("solver_time", solver_elapsed.as_secs_f64());
    }

    fn inspect_last_proof(&self) -> anyhow::Result<()> {
        match self.solver.get_proof() {
            Some(proof) => {
                ProofTree::new(proof);
            }
            None => log::debug!("NO PROOF!"),
        }
        Ok(())
    }

    fn has_model(&self) -> bool {
        self.model_captured && self.newest_model.is_some()
    }

    fn eval_to_string(&self, term: &Term) -> anyhow::Result<String> {
        if !self.model_captured {
            anyhow::bail!("no solver model has been captured for the latest check");
        }
        let model = self
            .newest_model
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("no solver model is available"))?;
        let solver_term = self.z3_var_context.rewrite_term(term);
        let interpretation = self.z3_var_context.get_interpretation(model, &solver_term);
        Ok(interpretation.to_string())
    }

    fn model_to_string(&self) -> anyhow::Result<String> {
        if !self.model_captured {
            return Ok("<no model>".to_string());
        }
        match &self.newest_model {
            Some(model) => model.dump_sorted(),
            None => Ok("<no model>".to_string()),
        }
    }

    fn get_solver_statistics(&self) -> SolverStatistics {
        self.solver_statistics.clone()
    }

    fn statistics_ref(&self) -> &SolverStatistics {
        &self.solver_statistics
    }

    fn get_reason_unknown(&self) -> Option<String> {
        self.solver.get_reason_unknown()
    }

    fn get_unsat_core(&self) -> anyhow::Result<Vec<String>> {
        Ok(self
            .solver
            .get_unsat_core()
            .iter()
            .map(ToString::to_string)
            .collect())
    }

    fn to_smt2_string(&self) -> anyhow::Result<String> {
        Ok(self.solver.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn raw_check_does_not_capture_a_z3_model() {
        let mut solver = Z3SolverBackend::new("QF_UF");
        solver
            .assert_term(&"true".parse::<Term>().unwrap())
            .unwrap();

        assert_eq!(solver.check_sat(), SolverCheckResult::Sat);
        assert!(!solver.has_model());
        assert!(solver.model_to_string().unwrap().contains("no model"));

        solver.capture_model(&[]).unwrap();
        assert!(solver.has_model());
    }

    #[test]
    fn solver_time_is_finalized_before_model_capture() {
        let mut solver = Z3SolverBackend::new("QF_UF");
        solver
            .assert_term(&"true".parse::<Term>().unwrap())
            .unwrap();

        assert_eq!(
            solver.check_sat_and_record_statistics(),
            SolverCheckResult::Sat
        );
        assert!(!solver.has_model());
        let raw_solver_time = solver
            .get_solver_statistics()
            .get_f64("solver_time")
            .expect("raw check should record solver_time");

        solver.capture_model(&[]).unwrap();

        assert!(solver.has_model());
        assert_eq!(
            solver
                .get_solver_statistics()
                .get_f64("solver_time")
                .expect("model capture must not remove solver_time"),
            raw_solver_time,
            "model acquisition must not be included in solver_time"
        );
    }

    #[test]
    fn z3_model_capture_requires_a_sat_result() {
        let mut solver = Z3SolverBackend::new("QF_UF");
        assert!(solver.capture_model(&[]).is_err());

        solver
            .assert_term(&"false".parse::<Term>().unwrap())
            .unwrap();
        assert_eq!(solver.check_sat(), SolverCheckResult::Unsat);
        assert!(solver.capture_model(&[]).is_err());
        assert!(!solver.has_model());
    }
}
