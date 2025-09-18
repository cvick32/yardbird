use log::{debug, info, warn};
use z3::ast::Ast;

use crate::{smt_problem::SMTProblem, strategies::ListRefinementState, utils::run_smtinterpol};

use super::{ArrayRefinementState, ProofStrategyExt};

pub struct Interpolating;

impl ProofStrategyExt<ArrayRefinementState> for Interpolating {
    fn unsat(&mut self, _state: &mut ArrayRefinementState, smt: &SMTProblem) -> anyhow::Result<()> {
        let interpolants = run_smtinterpol(smt);
        match interpolants {
            Ok(interps) => {
                for interp in interps {
                    let z3_interp = smt.rewrite_term(&interp.simplified_term);
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

impl ProofStrategyExt<ListRefinementState> for Interpolating {
    fn unsat(&mut self, _state: &mut ListRefinementState, smt: &SMTProblem) -> anyhow::Result<()> {
        let interpolants = run_smtinterpol(smt);
        match interpolants {
            Ok(interps) => {
                for interp in interps {
                    let z3_interp = smt.rewrite_term(&interp.simplified_term);
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
