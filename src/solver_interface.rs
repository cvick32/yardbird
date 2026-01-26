use smt2parser::concrete::Term;
use smt2parser::vmt::{quantified_instantiator::Instance, variable::Variable, ReadsAndWrites};
use std::any::Any;
use z3::ast::Dynamic;

use crate::utils::SolverStatistics;

/// Common interface for solvers that strategies can work with
/// Implemented by both SMTProblem and SMTLIBSMTProblem
pub trait SolverInterface {
    /// Enable downcasting to concrete types
    fn as_any(&self) -> &dyn Any;
    fn get_model(&self) -> &Option<z3::Model>;
    fn rewrite_term(&self, term: &Term) -> Dynamic;
    fn get_all_subterms(&self) -> Vec<&Term>;
    fn get_interpretation(&self, model: &z3::Model, z3_term: &Dynamic) -> Dynamic;
    fn get_solver_statistics(&self) -> SolverStatistics;
    fn get_reason_unknown(&self) -> Option<String>;

    // Methods for instantiation management
    fn add_instantiation(&mut self, inst: Instance) -> bool;
    fn get_instantiations(&self) -> Vec<Term>;
    fn get_variables(&self) -> &[Variable];
    fn get_number_instantiations_added(&self) -> u64;

    // Methods for cost functions
    /// Get subterms from initial state and transition relation (VMT-specific, empty for SMTLIB)
    fn get_init_and_transition_subterms(&self) -> Vec<String>;
    /// Get subterms from property (for SMTLIB, this is all assertion subterms)
    fn get_property_subterms(&self) -> Vec<String>;
    /// Get reads and writes from the problem
    fn get_reads_and_writes(&self) -> ReadsAndWrites;

    /// Get discovered array types (index_sort, value_sort) pairs
    fn get_array_types(&self) -> Vec<(String, String)>;
}
