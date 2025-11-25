use smt2parser::concrete::{Command, Term};

/// Trait representing a verification problem that can be solved by yardbird.
/// This abstracts over different input formats (VMT, SMTLIB) and allows
/// strategies to work generically over problem types.
pub trait Problem: Clone + std::fmt::Debug {
    /// Returns the sort declarations needed for this problem
    fn get_sorts(&self) -> Vec<Command>;

    /// Returns function declarations needed for this problem
    fn get_function_definitions(&self) -> Vec<Command>;

    /// Returns the SMT logic string (e.g., "UFLIA", "QF_BV")
    /// This is used to configure the Z3 solver with the appropriate theory
    fn get_logic(&self) -> Option<String>;

    /// Returns true if this problem requires temporal unrolling (BMC-style)
    /// VMT problems need unrolling (transition systems), SMTLIB problems do not
    fn requires_unrolling(&self) -> bool;

    /// Returns all commands that make up this problem
    /// Used for model transformation and abstraction
    fn as_commands(&self) -> Vec<Command>;
}

/// Trait for problems that support bounded model checking with unrolling
/// VMT problems implement this; SMTLIB problems do not
pub trait UnrollableProblem: Problem {
    /// Get the initial condition term
    fn get_initial_condition(&self) -> Term;

    /// Get the transition relation term
    fn get_transition_condition(&self) -> Term;

    /// Get the property to verify (negated for counterexample search)
    fn get_property_condition(&self) -> Term;

    /// Returns the names of all current state variables
    fn get_all_current_variable_names(&self) -> Vec<String>;

    /// Returns mapping from next-state variable names to current-state names
    fn get_next_to_current_variable_names(&self) -> std::collections::HashMap<String, String>;

    /// Add a quantifier instantiation to the model
    /// Returns true if successful
    fn add_instantiation(&mut self, term: &Term) -> bool;
}
