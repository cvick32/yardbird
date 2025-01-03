use std::mem;

use anyhow::anyhow;
use log::{debug, info};
use smt2parser::vmt::{smt::SMTProblem, VMTModel};

use crate::{
    analysis::SaturationInequalities, array_axioms::ArrayLanguage, cost::BestVariableSubstitution,
    egg_utils::Saturate, z3_ext::ModelExt, z3_var_context::Z3VarContext, ProofLoopResult,
};

use super::{ProofAction, ProofStrategy};

/// Global state carried across different BMC depths
#[derive(Default)]
pub struct Abstract {
    used_instantiations: Vec<String>,
    const_instantiations: Vec<String>,
}

/// State for the inner refinement looop
pub struct AbstractRefinementState<'ctx> {
    pub smt: SMTProblem,
    pub depth: u8,
    pub egraph: egg::EGraph<ArrayLanguage, SaturationInequalities>,
    pub instantiations: Vec<String>,
    pub const_instantiations: Vec<String>,
    pub z3_var_context: Z3VarContext<'ctx>,
}

impl<'ctx> ProofStrategy<'ctx, AbstractRefinementState<'ctx>> for Abstract {
    fn configure_model(&mut self, model: VMTModel) -> VMTModel {
        model.abstract_array_theory()
    }

    fn setup(
        &mut self,
        context: &'ctx z3::Context,
        smt: SMTProblem,
        depth: u8,
    ) -> anyhow::Result<AbstractRefinementState<'ctx>> {
        let mut egraph = egg::EGraph::new(SaturationInequalities).with_explanations_enabled();
        for term in smt.get_assert_terms() {
            egraph.add_expr(&term.parse()?);
        }
        let z3_var_context = Z3VarContext::from(context, &smt);
        Ok(AbstractRefinementState {
            smt,
            depth,
            egraph,
            instantiations: vec![],
            const_instantiations: vec![],
            z3_var_context,
        })
    }

    fn unsat(
        &mut self,
        state: &mut AbstractRefinementState<'ctx>,
        _solver: &z3::Solver,
    ) -> anyhow::Result<ProofAction> {
        info!("RULED OUT ALL COUNTEREXAMPLES OF DEPTH {}", state.depth);
        Ok(ProofAction::NextDepth)
    }

    fn sat(
        &mut self,
        state: &mut AbstractRefinementState<'ctx>,
        solver: &z3::Solver,
    ) -> anyhow::Result<ProofAction> {
        let model = solver.get_model().ok_or(anyhow!("No z3 model"))?;
        debug!("model:\n{}", model.dump_sorted()?);
        state.update_from_model(&model)?;
        state.update_with_non_array_function_terms(&model)?;
        state.egraph.rebuild();
        let cost_fn = BestVariableSubstitution {
            current_frame_number: state.depth as u32,
            property_terms: state.smt.get_property_terms(),
        };
        let (inst, const_inst) = state.egraph.saturate(cost_fn);
        state.instantiations.extend_from_slice(&inst);
        state.const_instantiations.extend_from_slice(&const_inst);
        Ok(ProofAction::Continue)
    }

    fn finish(
        &mut self,
        model: &mut VMTModel,
        state: AbstractRefinementState<'ctx>,
    ) -> anyhow::Result<()> {
        self.const_instantiations
            .extend_from_slice(&state.const_instantiations);
        let no_progress = state
            .instantiations
            .into_iter()
            .all(|inst| !model.add_instantiation(inst, &mut self.used_instantiations));
        if no_progress {
            Err(anyhow!("Failed to add new instantations"))
        } else {
            Ok(())
        }
    }

    fn result(&mut self) -> ProofLoopResult {
        ProofLoopResult {
            model: None,
            used_instances: mem::take(&mut self.used_instantiations),
            const_instances: mem::take(&mut self.const_instantiations),
            counterexample: false,
        }
    }
}

impl AbstractRefinementState<'_> {
    fn update_from_model(&mut self, model: &z3::Model<'_>) -> anyhow::Result<()> {
        for func_decl in model.sorted_iter() {
            if func_decl.arity() == 0 {
                // VARIABLE
                // Apply no arguments to the constant so we can call get_const_interp.
                let func_decl_ast = func_decl.apply(&[]);
                let var = func_decl.name().parse()?;
                let var_id = self.egraph.add_expr(&var);
                let value = model.get_const_interp(&func_decl_ast).ok_or(anyhow!(
                    "Could not find interpretation for variable: {func_decl}"
                ))?;
                let expr = value.to_string().parse()?;
                let value_id = self.egraph.add_expr(&expr);
                self.egraph.union(var_id, value_id);
            } else {
                // FUNCTION DEF
                let interpretation = model
                    .get_func_interp(&func_decl)
                    .ok_or(anyhow!("No function interpretation for: {func_decl}"))?;
                for entry in interpretation.get_entries() {
                    let function_call = format!(
                        "({} {})",
                        func_decl.name(),
                        entry
                            .get_args()
                            .iter()
                            .map(ToString::to_string)
                            .collect::<Vec<_>>()
                            .join(" ")
                    );
                    let funcall = function_call.parse()?;
                    let expr = entry.get_value().to_string().parse()?;
                    let function_id = self.egraph.add_expr(&funcall);
                    let value_id = self.egraph.add_expr(&expr);
                    self.egraph.union(function_id, value_id);
                }
            }
            self.egraph.rebuild();
        }
        Ok(())
    }

    pub fn update_with_non_array_function_terms(
        &mut self,
        model: &z3::Model,
    ) -> anyhow::Result<()> {
        for term in self.smt.get_eq_terms() {
            let term_id = self.egraph.add_expr(&term.to_string().parse()?);
            let z3_term = self.z3_var_context.rewrite_term(&term);
            let model_interp = model
                .eval(&z3_term, false)
                .unwrap_or_else(|| panic!("Term not found in model: {term}"));
            let interp_id = self.egraph.add_expr(&model_interp.to_string().parse()?);
            debug!("Adding: {} = {}", term, model_interp);
            self.egraph.union(term_id, interp_id);
            self.egraph.rebuild();
        }
        Ok(())
    }
}
