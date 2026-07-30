pub mod api;
mod capture;
#[cfg(feature = "cvc5-backend")]
mod cvc5;
mod z3;
mod z3_ext;
mod z3_var_context;

use crate::SolverBackend;

#[cfg(feature = "cvc5-backend")]
use self::cvc5::Cvc5SolverBackend;
use self::z3::Z3SolverBackend;
pub use api::{SolverCheckResult, YardbirdSolver};
pub use capture::{
    CaptureArtifacts, SolverCapture, SolverSessionCheckIndex, SolverSessionIndex,
    SolverSessionManifest,
};

pub fn new_solver_backend(
    backend: SolverBackend,
    logic: &str,
    capture: Option<SolverCapture>,
) -> Box<dyn YardbirdSolver> {
    let solver: Box<dyn YardbirdSolver> = match backend {
        SolverBackend::Z3 => Box::new(Z3SolverBackend::new(logic)),
        #[cfg(feature = "cvc5-backend")]
        SolverBackend::Cvc5 => Box::new(Cvc5SolverBackend::new(logic)),
        #[cfg(not(feature = "cvc5-backend"))]
        SolverBackend::Cvc5 => {
            panic!("yardbird was built without the cvc5-backend Cargo feature")
        }
    };
    match capture {
        Some(capture) => capture.wrap(solver, logic),
        None => solver,
    }
}
