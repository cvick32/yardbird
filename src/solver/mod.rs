pub mod api;
mod cvc5;
mod z3;
mod z3_ext;
mod z3_var_context;

use crate::SolverBackend;

use self::cvc5::Cvc5SolverBackend;
use self::z3::Z3SolverBackend;
pub use api::{SolverCheckResult, YardbirdSolver};

pub fn new_solver_backend(backend: SolverBackend, logic: &str) -> Box<dyn YardbirdSolver> {
    match backend {
        SolverBackend::Z3 => Box::new(Z3SolverBackend::new(logic)),
        SolverBackend::Cvc5 => Box::new(Cvc5SolverBackend::new(logic)),
    }
}
