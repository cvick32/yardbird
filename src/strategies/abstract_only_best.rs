use std::mem;

use anyhow::anyhow;
use egg::CostFunction;
use itertools::Itertools;
use log::info;
use smt2parser::vmt::{smt::SMTProblem, VMTModel};

use crate::{
    analysis::SaturationInequalities, array_axioms::ArrayLanguage,
    cost_functions::symbol_cost::BestSymbolSubstitution, egg_utils::Saturate,
    z3_var_context::Z3VarContext, ProofLoopResult,
};

use super::{AbstractRefinementState, ProofAction, ProofStrategy};

/// Global state carried across different BMC depths
#[derive(Default)]
pub struct AbstractOnlyBest {
    used_instantiations: Vec<String>,
    const_instantiations: Vec<String>,
    bmc_depth: u8,
}

impl AbstractOnlyBest {
    pub fn new(bmc_depth: u8) -> Self {
        Self {
            bmc_depth,
            ..Default::default()
        }
    }
}

impl ProofStrategy<'_, AbstractRefinementState> for AbstractOnlyBest {
    fn configure_model(&mut self, model: VMTModel) -> VMTModel {
        model
            .abstract_array_theory()
            .abstract_constants_over(self.bmc_depth)
    }

    fn setup(&mut self, smt: SMTProblem, depth: u8) -> anyhow::Result<AbstractRefinementState> {
        let mut egraph = egg::EGraph::new(SaturationInequalities).with_explanations_enabled();
        for term in smt.get_assert_terms() {
            egraph.add_expr(&term.to_string().parse()?);
        }
        Ok(AbstractRefinementState {
            smt,
            depth,
            egraph,
            instantiations: vec![],
            const_instantiations: vec![],
        })
    }

    fn unsat(
        &mut self,
        state: &mut AbstractRefinementState,
        _solver: &z3::Solver,
    ) -> anyhow::Result<ProofAction> {
        info!("RULED OUT ALL COUNTEREXAMPLES OF DEPTH {}", state.depth);
        Ok(ProofAction::NextDepth)
    }

    fn sat(
        &mut self,
        state: &mut AbstractRefinementState,
        solver: &z3::Solver,
        z3_var_context: &Z3VarContext,
    ) -> anyhow::Result<ProofAction> {
        let model = solver.get_model().ok_or(anyhow!("No z3 model"))?;
        state.update_with_subterms(&model, z3_var_context)?;
        state.egraph.rebuild();
        let mut cost_fn = BestSymbolSubstitution {
            current_bmc_depth: state.depth as u32,
            transition_system_terms: state.smt.get_transition_system_subterms(),
            property_terms: state.smt.get_property_subterms(),
            reads_writes: state.smt.get_reads_and_writes(),
        };
        let (insts, const_insts) = state.egraph.saturate(cost_fn.clone());
        let insts: Vec<String> = insts
            .into_iter()
            .map(|inst| inst.parse::<egg::RecExpr<ArrayLanguage>>().unwrap())
            .sorted_by_key(|rec_expr| cost_fn.cost_rec(rec_expr))
            .map(|rec_expr| rec_expr.to_string())
            .collect();
        if let Some(inst) = insts.first() {
            state.instantiations.push(inst.clone());
        }
        state.const_instantiations.extend_from_slice(&const_insts);
        Ok(ProofAction::Continue)
    }

    fn finish(
        &mut self,
        model: &mut VMTModel,
        state: AbstractRefinementState,
    ) -> anyhow::Result<()> {
        self.const_instantiations
            .extend_from_slice(&state.const_instantiations);

        let no_progress = state
            .instantiations
            .into_iter()
            .all(|inst| !model.add_instantiation(inst, &mut self.used_instantiations));
        let const_progress = state
            .const_instantiations
            .into_iter()
            .all(|inst| !model.add_instantiation(inst, &mut self.used_instantiations));
        if no_progress && const_progress {
            Err(anyhow!("Failed to add new instantations"))
        } else {
            Ok(())
        }
    }

    fn result(&mut self, vmt_model: VMTModel) -> ProofLoopResult {
        ProofLoopResult {
            model: Some(vmt_model),
            used_instances: mem::take(&mut self.used_instantiations),
            const_instances: mem::take(&mut self.const_instantiations),
            counterexample: false,
            result_type: crate::driver::ProofLoopResultType::Success,
        }
    }

    fn no_progress_result(&mut self, vmt_model: VMTModel) -> ProofLoopResult {
        ProofLoopResult {
            model: Some(vmt_model),
            used_instances: mem::take(&mut self.used_instantiations),
            const_instances: mem::take(&mut self.const_instantiations),
            counterexample: false,
            result_type: crate::driver::ProofLoopResultType::NoProgress,
        }
    }
}
