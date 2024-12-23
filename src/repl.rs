use anyhow::anyhow;
use dialoguer::{theme::SimpleTheme, MultiSelect};
use log::{debug, info};
use smt2parser::vmt::VMTModel;

use crate::{
    analysis::SaturationInequalities, array_axioms::ArrayLanguage, cost::BestVariableSubstitution,
    egg_utils::Saturate, sort_model, update_egraph_from_model,
    update_egraph_with_non_array_function_terms, z3_var_context::Z3VarContext, Driver,
    ProofLoopResult, YardbirdOptions,
};

pub struct Repl<'a> {
    driver: Driver<'a>,
}

impl<'a> Repl<'a> {
    pub fn new(options: &'a YardbirdOptions, config: &z3::Config, vmt_model: VMTModel) -> Self {
        Repl {
            driver: Driver::new(options, config, vmt_model),
        }
    }

    pub fn start(mut self, target_depth: u8, n_refines: u32) -> anyhow::Result<ProofLoopResult> {
        for depth in 0..target_depth {
            info!("STARTING BMC FOR DEPTH {depth}");
            'refine: for i in 0..n_refines {
                info!("  refining loop: {i}/{n_refines}");
                // TODO: find a way to write this more clearly
                match self.refine_model(depth)? {
                    z3::SatResult::Unsat => break 'refine,
                    z3::SatResult::Sat if i == n_refines - 1 => {
                        return Err(anyhow!("Failed to rule out counter-examples"))
                    }
                    z3::SatResult::Sat => continue 'refine,
                    z3::SatResult::Unknown => todo!(),
                }
            }
        }
        Ok(ProofLoopResult {
            model: self.driver.vmt_model,
            used_instances: self.driver.used_instances,
            const_instances: self.driver.const_instances,
            counterexample: false,
        })
    }

    fn refine_model(&mut self, depth: u8) -> anyhow::Result<z3::SatResult> {
        let smt = self.driver.vmt_model.unroll(depth);
        let z3_var_context = Z3VarContext::from(&self.driver.context, &smt);
        let solver = z3::Solver::new(&self.driver.context);
        solver.from_string(smt.to_bmc());
        // debug!("smt2lib program:\n{}", smt.to_bmc());
        // TODO: abstract this out somehow
        let mut egraph: egg::EGraph<ArrayLanguage, _> =
            egg::EGraph::new(SaturationInequalities).with_explanations_enabled();
        for term in smt.get_assert_terms() {
            egraph.add_expr(&term.parse()?);
        }
        match solver.check() {
            res @ z3::SatResult::Unsat => {
                info!("RULED OUT ALL COUNTEREXAMPLES OF DEPTH {}", depth);
                Ok(res)
            }
            z3::SatResult::Unknown => {
                // CV: I've seen Z3 return unknown then re-run Z3 and gotten SAT or UNSAT.
                // This might be a place to retry at least once before panicking.
                panic!("Z3 RETURNED UNKNOWN!");
            }
            res @ z3::SatResult::Sat => {
                // find Array theory fact(s) that rules out counterexample
                let model = solver.get_model().ok_or(anyhow!("No z3 model"))?;
                debug!("model:\n{}", sort_model(&model)?);
                update_egraph_from_model(&mut egraph, &model)?;
                update_egraph_with_non_array_function_terms(
                    &mut egraph,
                    &smt,
                    &z3_var_context,
                    &model,
                )?;
                egraph.rebuild();
                let cost_fn = BestVariableSubstitution {
                    current_frame_number: depth as u32,
                    property_terms: smt.get_property_terms(),
                };
                let (instantiations, const_instantiations) = egraph.saturate(cost_fn);
                let selection = MultiSelect::with_theme(&SimpleTheme)
                    .with_prompt("Pick instantiations")
                    .items(&instantiations)
                    .interact()
                    .unwrap();

                self.driver
                    .const_instances
                    .extend_from_slice(&const_instantiations);

                // add all instantiations to the model,
                // if we have already seen all instantiations, break
                // TODO: not sure if this is correct...
                let no_progress = selection
                    .into_iter()
                    .map(|i| instantiations[i].to_string())
                    .all(|inst| {
                        !self
                            .driver
                            .vmt_model
                            .add_instantiation(inst, &mut self.driver.used_instances)
                    });
                if no_progress {
                    Err(anyhow!("Failed to add new instantations"))
                } else {
                    Ok(res)
                }
            }
        }
    }
}
