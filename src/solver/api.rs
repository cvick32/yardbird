use std::{
    collections::BTreeMap,
    time::{Duration, Instant},
};

use smt2parser::concrete::{Command, Sort, Symbol, Term};

use crate::{utils::SolverStatistics, SolverBackend};

#[derive(
    Copy,
    Clone,
    Debug,
    Default,
    Eq,
    PartialEq,
    clap::ValueEnum,
    serde::Serialize,
    serde::Deserialize,
)]
#[clap(rename_all = "kebab_case")]
#[serde(rename_all = "kebab-case")]
pub enum PropertyCheckMode {
    /// Temporarily push and assert the negated property around each check.
    #[default]
    Scoped,
    /// Permanently guard each negated property and enable it as an assumption.
    Assumptions,
    /// Start each depth with a scoped check, then use an assumption after SAT
    /// indicates that refinement will re-query the same depth.
    RefinementAssumptions,
}

impl std::fmt::Display for PropertyCheckMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Scoped => write!(f, "scoped"),
            Self::Assumptions => write!(f, "assumptions"),
            Self::RefinementAssumptions => write!(f, "refinement-assumptions"),
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum SolverCheckResult {
    Sat,
    Unsat,
    Unknown,
}

pub trait YardbirdSolver {
    fn backend(&self) -> SolverBackend;
    fn solver_parameters(&self) -> BTreeMap<String, String> {
        BTreeMap::new()
    }
    fn random_seeds(&self) -> BTreeMap<String, u64> {
        BTreeMap::new()
    }

    fn accept_command(&mut self, command: &Command) -> anyhow::Result<()>;
    fn create_variable(&mut self, symbol: &Symbol, sort: &Sort) -> anyhow::Result<()>;

    fn assert_term(&mut self, term: &Term) -> anyhow::Result<()>;
    fn assert_not_term(&mut self, term: &Term) -> anyhow::Result<()>;
    fn assert_terms_conjunctively(&mut self, terms: &[Term]) -> anyhow::Result<()>;
    fn assert_tracked_term(&mut self, term: &Term, label: &str) -> anyhow::Result<()>;

    fn register_quantified_variables(&mut self, term: &Term) -> anyhow::Result<()> {
        if let Term::Forall { vars, term: _ } = term {
            for (symbol, sort) in vars {
                self.create_variable(symbol, sort)?;
            }
        }
        Ok(())
    }

    fn assert_instantiation_batch(&mut self, terms: &[Term]) -> anyhow::Result<()> {
        self.assert_terms_conjunctively(terms)
    }

    fn assert_tracked_instantiation(&mut self, label: &str, term: &Term) -> anyhow::Result<()> {
        self.assert_tracked_term(term, label)
    }

    fn push(&mut self);
    fn pop(&mut self, levels: u32);

    /// Run the solver without acquiring a model.
    fn check_sat(&mut self) -> SolverCheckResult;

    /// Run the solver under temporary Boolean assumptions without changing its
    /// assertion stack.
    fn check_sat_assuming(&mut self, assumptions: &[Term]) -> SolverCheckResult;

    /// Mark the end of all solver-side work associated with the most recent
    /// check. Capture decorators use this to separate post-check operations
    /// from setup for the next incremental check.
    fn complete_check(&mut self) {}

    /// Capture the model produced by the most recent SAT check, including the
    /// values of any terms that the backend must preserve before a scope pop.
    ///
    /// Callers must invoke this before popping the scope used for the check.
    fn capture_model(&mut self, terms: &[Term]) -> anyhow::Result<()>;

    fn check_sat_and_record_statistics(&mut self) -> SolverCheckResult {
        let start_time = Instant::now();
        let result = self.check_sat();
        self.record_statistics(start_time.elapsed());
        self.complete_check();
        result
    }

    fn record_statistics(&mut self, solver_elapsed: Duration);
    fn inspect_last_proof(&self) -> anyhow::Result<()> {
        Ok(())
    }

    /// Acquire and preserve the UNSAT core from the latest check.
    ///
    /// Backends that expose cores lazily can use the default implementation.
    /// Backends whose core becomes unavailable after a scope pop should cache
    /// it here for the later read-only `get_unsat_core` call.
    fn capture_unsat_core(&mut self) -> anyhow::Result<()> {
        self.get_unsat_core().map(|_| ())
    }

    fn has_model(&self) -> bool;
    fn eval_to_string(&self, term: &Term) -> anyhow::Result<String>;
    fn model_to_string(&self) -> anyhow::Result<String>;

    fn get_solver_statistics(&self) -> SolverStatistics;
    fn statistics_ref(&self) -> &SolverStatistics;
    fn get_reason_unknown(&self) -> Option<String>;
    /// Read the core acquired for the most recent UNSAT check.
    fn get_unsat_core(&self) -> anyhow::Result<Vec<String>>;
    fn to_smt2_string(&self) -> anyhow::Result<String>;
}
