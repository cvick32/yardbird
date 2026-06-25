use log::{debug, info, warn};

use crate::{smt_problem::SMTProblem, strategies::ListRefinementState, utils::run_smtinterpol};

use super::{ArrayRefinementState, ProofStrategyExt};

pub struct Interpolating;

impl ProofStrategyExt<ArrayRefinementState> for Interpolating {
    fn unsat(
        &mut self,
        _state: &mut ArrayRefinementState,
        smt: &dyn crate::solver_interface::SolverInterface,
    ) -> anyhow::Result<()> {
        // Downcast to SMTProblem for VMT-specific interpolation
        let smt_problem = smt
            .as_any()
            .downcast_ref::<SMTProblem>()
            .expect("Interpolation requires SMTProblem");
        let interpolants = run_smtinterpol(smt_problem);
        match interpolants {
            Ok(interps) => {
                for interp in interps {
                    info!(
                        "Interpolant {} length: {}",
                        interp.interpolant_number,
                        interp.simplified_term.to_string().len()
                    );
                    debug!(
                        "Interpolant {}: {}",
                        interp.interpolant_number, interp.simplified_term
                    );
                }
            }
            Err(err) => warn!("Error when computing interpolants: {err}"),
        }
        Ok(())
    }
}

impl ProofStrategyExt<ListRefinementState> for Interpolating {
    fn unsat(
        &mut self,
        _state: &mut ListRefinementState,
        smt: &dyn crate::solver_interface::SolverInterface,
    ) -> anyhow::Result<()> {
        // Downcast to SMTProblem for VMT-specific interpolation
        let smt_problem = smt
            .as_any()
            .downcast_ref::<SMTProblem>()
            .expect("Interpolation requires SMTProblem");
        let interpolants = run_smtinterpol(smt_problem);
        match interpolants {
            Ok(interps) => {
                for interp in interps {
                    info!(
                        "Interpolant {} length: {}",
                        interp.interpolant_number,
                        interp.simplified_term.to_string().len()
                    );
                    debug!(
                        "Interpolant {}: {}",
                        interp.interpolant_number, interp.simplified_term
                    );
                }
            }
            Err(err) => warn!("Error when computing interpolants: {err}"),
        }
        Ok(())
    }
}
