use log::info;
use z3::ast::Ast;

use crate::utils::run_smtinterpol;

use super::{AbstractRefinementState, ProofAction, ProofStrategyExt};

/// TODO: this should be abstract over proving strategies, so that we can
/// use interpolants when we can use either an Abstract or Concrete strategy
pub struct Interpolating;

impl ProofStrategyExt<'_, AbstractRefinementState<'_>> for Interpolating {
    fn unsat(
        &mut self,
        state: &mut AbstractRefinementState<'_>,
        _solver: &z3::Solver,
    ) -> anyhow::Result<ProofAction> {
        let interpolants = run_smtinterpol(&state.smt);
        match interpolants {
            Ok(interps) => {
                for interp in interps {
                    let z3_interp = state.z3_var_context.rewrite_term(&interp.simplified_term);
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
                    println!("Interpolant {}: {}", interp.interpolant_number, simple);
                }
            }
            Err(err) => println!("Error when computing interpolants: {err}"),
        }
        Ok(ProofAction::Continue)
    }
}
