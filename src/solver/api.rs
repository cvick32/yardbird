use std::time::Instant;

use smt2parser::concrete::{Command, Sort, Symbol, Term};

use crate::{utils::SolverStatistics, SolverBackend};

#[derive(Copy, Clone, Debug, Eq, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum SolverCheckResult {
    Sat,
    Unsat,
    Unknown,
}

pub trait YardbirdSolver {
    fn backend(&self) -> SolverBackend;

    fn accept_command(&mut self, command: &Command) -> anyhow::Result<()>;
    fn create_variable(&mut self, symbol: &Symbol, sort: &Sort) -> anyhow::Result<()>;

    fn assert_term(&mut self, term: &Term) -> anyhow::Result<()>;
    fn assert_not_term(&mut self, term: &Term) -> anyhow::Result<()>;
    fn assert_terms_conjunctively(&mut self, terms: &[Term]) -> anyhow::Result<()>;
    fn assert_tracked_term(&mut self, term: &Term, label: &str) -> anyhow::Result<()>;

    fn push(&mut self);
    fn pop(&mut self, levels: u32);

    fn check(&mut self) -> SolverCheckResult;
    fn check_and_record_statistics(&mut self) -> SolverCheckResult;
    fn record_statistics_since(&mut self, start_time: Instant);
    fn inspect_last_proof(&self) -> anyhow::Result<()> {
        Ok(())
    }

    fn has_model(&self) -> bool;
    fn eval_to_string(&self, term: &Term) -> anyhow::Result<String>;
    fn model_to_string(&self) -> anyhow::Result<String>;

    fn get_solver_statistics(&self) -> SolverStatistics;
    fn statistics_ref(&self) -> &SolverStatistics;
    fn get_reason_unknown(&self) -> Option<String>;
    fn get_unsat_core(&self) -> anyhow::Result<Vec<String>>;
    fn to_smt2_string(&self) -> anyhow::Result<String>;
}
