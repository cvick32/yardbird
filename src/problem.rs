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

    fn check(&mut self) -> z3::SatResult;

    fn unroll(&mut self, depth: u16);

    fn add_instantiation(&self, term: &Term);
}
