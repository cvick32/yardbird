use log::{debug, info, warn};

use crate::{
    strategies::ListRefinementState, utils::run_smtinterpol, vmt_bmc_session::VmtBmcSession,
};

use super::{ArrayRefinementState, ProofStrategyExt};

pub struct Interpolating;

impl ProofStrategyExt<ArrayRefinementState> for Interpolating {
    fn unsat(
        &mut self,
        _state: &mut ArrayRefinementState,
        smt: &dyn crate::problem_context::ProblemContext,
    ) -> anyhow::Result<()> {
        // Downcast to VmtBmcSession for VMT-specific interpolation
        let smt_problem = smt
            .as_any()
            .downcast_ref::<VmtBmcSession>()
            .expect("Interpolation requires VmtBmcSession");
        let interpolants = run_smtinterpol(smt_problem);
        match interpolants {
            Ok(interps) => {
                for interp in interps {
                    info!(
                        "Interpolant {} length: {}",
                        interp.interpolant_number,
                        interp.term.to_string().len()
                    );
                    debug!("Interpolant {}: {}", interp.interpolant_number, interp.term);
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
        smt: &dyn crate::problem_context::ProblemContext,
    ) -> anyhow::Result<()> {
        // Downcast to VmtBmcSession for VMT-specific interpolation
        let smt_problem = smt
            .as_any()
            .downcast_ref::<VmtBmcSession>()
            .expect("Interpolation requires VmtBmcSession");
        let interpolants = run_smtinterpol(smt_problem);
        match interpolants {
            Ok(interps) => {
                for interp in interps {
                    info!(
                        "Interpolant {} length: {}",
                        interp.interpolant_number,
                        interp.term.to_string().len()
                    );
                    debug!("Interpolant {}: {}", interp.interpolant_number, interp.term);
                }
            }
            Err(err) => warn!("Error when computing interpolants: {err}"),
        }
        Ok(())
    }
}
