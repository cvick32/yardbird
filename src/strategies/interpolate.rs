use log::{debug, info, warn};
use rerun::{archetypes::TextLog, RecordingStreamBuilder};
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
        let raw_interpolants = run_smtinterpol(&state.smt);
        match raw_interpolants {
            Ok(interps) => {
                // Start a new recording session
                let rec = RecordingStreamBuilder::new("Interpolant Logger").spawn()?;
                for interp in interps {
                    let z3_interp = z3_var_context.rewrite_term(&interp._original_term);
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
                    if simple.decl().name() != "or" {
                        rec.log(
                            format!("Step {} Interpolant", interp.interpolant_number),
                            &TextLog::new(simple.to_string()),
                        )?;
                    } else {
                        // Here, the Z3 interpolant should be a top-level or of conjunctions.
                        // So, we'll do a case split and show each case seperately.
                        let mut cases: Vec<String> = vec![];
                        for (i, case) in simple.children().iter().enumerate() {
                            cases.push(format!("Case {}: {}", i + 1, case));
                        }
                        rec.log(
                            format!("Step {} Interpolant", interp.interpolant_number),
                            &TextLog::new(cases.join("\n")),
                        )?;
                    }

                    debug!("Interpolant {}: {}", interp.interpolant_number, simple);
                }
            }
            Err(err) => warn!("Error when computing interpolants: {err}"),
        }
        Ok(())
    }
}
