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

    pub(crate) fn assert_terms_conjunctively(&mut self, terms: &[Term]) {
        match terms {
            [] => {}
            [term] => self.assert_term(term),
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
        join_from_z3_statistics(&mut self.solver_statistics, self.solver.get_statistics());
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

    pub(crate) fn has_model(&self) -> bool {
        self.newest_model.is_some()
    }

    pub(crate) fn model_to_string(&self) -> anyhow::Result<String> {
        match &self.newest_model {
            Some(model) => model.dump_sorted(),
            None => Ok("<no model>".to_string()),
        }
    }

    pub(crate) fn eval_to_string(&self, term: &Term) -> anyhow::Result<String> {
        let model = self
            .newest_model
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("no solver model is available"))?;
        let solver_term = self.z3_var_context.rewrite_term(term);
        let interpretation = self.z3_var_context.get_interpretation(model, &solver_term);
        Ok(interpretation.to_string())
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
            z3::StatisticsValue::UInt(int_num) => StatisticsValue::UInt(int_num),
            z3::StatisticsValue::Double(float_num) => StatisticsValue::Double(float_num),
        };
        stats.insert(entry.key, value);
    }
}

impl InstantiationAssertionSink for Z3SolverBackend {
    fn register_quantified_variables(&mut self, term: &Term) {
        if let Term::Forall { vars, term: _ } = term {
            for (symbol, sort) in vars {
                self.create_variable(symbol, sort);
            }
        }
    }

    fn assert_instantiation_batch(&mut self, terms: &[Term]) {
        self.assert_terms_conjunctively(terms);
    }

    fn assert_tracked_instantiation(&mut self, label: &str, term: &Term) {
        self.assert_tracked_term(term, label);
    }
}
