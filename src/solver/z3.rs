use smt2parser::concrete::{Command, Term};
use std::time::Instant;
use z3::ast::Bool;

use super::{z3_ext::ModelExt, z3_var_context::Z3VarContext};
use crate::{
    instantiation_strategy::InstantiationAssertionSink,
    proof_tree::ProofTree,
    solver::SolverCheckResult,
    utils::{SolverStatistics, StatisticsValue},
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
            newest_model: None,
        }
    }

    pub(crate) fn accept_command(&mut self, command: Command) {
        let _ = command.accept(&mut self.z3_var_context);
    }

    pub(crate) fn create_variable(
        &mut self,
        symbol: &smt2parser::concrete::Symbol,
        sort: &smt2parser::concrete::Sort,
    ) {
        self.z3_var_context.create_variable(symbol, sort);
    }

    pub(crate) fn assert_term(&mut self, term: &Term) {
        let z3_term = self.z3_var_context.rewrite_term(term);
        self.solver.assert(z3_term.as_bool().unwrap());
    }

    pub(crate) fn assert_not_term(&mut self, term: &Term) {
        let z3_term = self.z3_var_context.rewrite_term(term);
        let negated = Bool::not(&z3_term.as_bool().unwrap());
        self.solver.assert(&negated);
    }

    pub(crate) fn assert_tracked_term(&mut self, term: &Term, label: &str) {
        let z3_term = self.z3_var_context.rewrite_term(term);
        let tracked_bool = Bool::new_const(label);
        self.solver
            .assert_and_track(z3_term.as_bool().unwrap(), &tracked_bool);
    }

    pub(crate) fn push(&mut self) {
        self.solver.push();
    }

    pub(crate) fn pop(&mut self, levels: u32) {
        self.solver.pop(levels);
    }

    pub(crate) fn check(&mut self) -> SolverCheckResult {
        let result = self.solver.check();
        self.newest_model = self.solver.get_model();
        result.into()
    }

    pub(crate) fn check_and_record_statistics(&mut self) -> SolverCheckResult {
        let start_time = Instant::now();
        let result = self.check();
        self.record_statistics_since(start_time);
        result
    }

    pub(crate) fn record_statistics_since(&mut self, start_time: Instant) {
        self.solver_statistics
            .join_from_z3_statistics(self.solver.get_statistics());
        self.solver_statistics
            .add_time("solver_time", start_time.elapsed().as_secs_f64());
    }

    pub(crate) fn inspect_last_proof(&self) {
        match self.solver.get_proof() {
            Some(proof) => {
                ProofTree::new(proof);
            }
            None => log::debug!("NO PROOF!"),
        }
    }

    pub(crate) fn get_model(&self) -> &Option<z3::Model> {
        &self.newest_model
    }

    #[allow(dead_code)]
    pub(crate) fn model_to_string(&self) -> anyhow::Result<String> {
        match &self.newest_model {
            Some(model) => model.dump_sorted(),
            None => Ok("<no model>".to_string()),
        }
    }

    pub(crate) fn rewrite_term(&self, term: &Term) -> Dynamic {
        self.z3_var_context.rewrite_term(term)
    }

    pub(crate) fn get_interpretation(&self, model: &z3::Model, z3_term: &Dynamic) -> Dynamic {
        self.z3_var_context.get_interpretation(model, z3_term)
    }

    pub(crate) fn get_solver_statistics(&self) -> SolverStatistics {
        self.solver_statistics.clone()
    }

    pub(crate) fn statistics_ref(&self) -> &SolverStatistics {
        &self.solver_statistics
    }

    pub(crate) fn get_reason_unknown(&self) -> Option<String> {
        self.solver.get_reason_unknown()
    }

    pub(crate) fn get_unsat_core(&self) -> Vec<String> {
        self.solver
            .get_unsat_core()
            .iter()
            .map(ToString::to_string)
            .collect()
    }

    pub(crate) fn to_smt2_string(&self) -> String {
        self.solver.to_string()
    }

    pub(crate) fn z3_parts_mut(&mut self) -> (&mut Z3VarContext, &mut z3::Solver) {
        (&mut self.z3_var_context, &mut self.solver)
    }
}
