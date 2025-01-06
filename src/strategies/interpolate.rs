use log::{debug, info, warn};
use z3::ast::Ast;

use crate::{utils::run_smtinterpol, z3_var_context::Z3VarContext};

use super::{AbstractRefinementState, ProofStrategyExt};

pub struct Interpolating;

impl ProofStrategyExt<AbstractRefinementState> for Interpolating {
    fn unsat(
        &mut self,
        state: &mut AbstractRefinementState,
        _solver: &z3::Solver,
        z3_var_context: &Z3VarContext,
    ) -> anyhow::Result<()> {
        let interpolants = run_smtinterpol(&state.smt);
        match interpolants {
            Ok(interps) => {
                for interp in interps {
                    let z3_interp = z3_var_context.rewrite_term(&interp.simplified_term);
                    let z3_interp_str = z3_interp.to_string();
                    let simple = z3_interp.simplify();
                    info!(
                        "Reduced Z3 interpolant length from {} to {} -- {}%",
                        z3_interp_str.len(),
                        simple.to_string().len(),
                        ((simple.to_string().len() as f64 - z3_interp_str.len() as f64)
                            / z3_interp_str.len() as f64)
                            * 100.0
                    );
                    debug!("Interpolant {}: {}", interp.interpolant_number, simple);
                }
            }
            Err(err) => warn!("Error when computing interpolants: {err}"),
        }
        Ok(())
    }
}
