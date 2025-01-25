use std::mem;

use anyhow::anyhow;
use egg::CostFunction;
use itertools::Itertools;
use log::info;
use smt2parser::{
    concrete::Term,
    vmt::{smt::SMTProblem, QuantifiedInstantiator, VMTModel},
};

use crate::{
    analysis::SaturationInequalities,
    array_axioms::{expr_to_term, ArrayExpr},
    cost_functions::symbol_cost::BestSymbolSubstitution,
    driver,
    egg_utils::Saturate,
    z3_var_context::Z3VarContext,
    Error, ProofLoopResult,
};

use super::{AbstractRefinementState, ProofAction, ProofStrategy};

/// Global state carried across different BMC depths
#[derive(Default)]
pub struct AbstractOnlyBest {
    used_instantiations: Vec<Term>,
    const_instantiations: Vec<Term>,
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

    fn setup(&mut self, smt: SMTProblem, depth: u8) -> driver::Result<AbstractRefinementState> {
        let mut egraph = egg::EGraph::new(SaturationInequalities).with_explanations_enabled();
        for term in smt.get_assert_terms() {
            if let Ok(parsed) = &term.to_string().parse() {
                egraph.add_expr(parsed);
            }
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
    ) -> driver::Result<ProofAction> {
        info!("RULED OUT ALL COUNTEREXAMPLES OF DEPTH {}", state.depth);
        Ok(ProofAction::NextDepth)
    }

    fn sat(
        &mut self,
        state: &mut AbstractRefinementState,
        solver: &z3::Solver,
        z3_var_context: &Z3VarContext,
    ) -> driver::Result<ProofAction> {
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
        let insts: Vec<ArrayExpr> = insts
            .into_iter()
            .sorted_by_key(|rec_expr| cost_fn.cost_rec(rec_expr))
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
    ) -> driver::Result<()> {
        self.const_instantiations
            .extend(state.const_instantiations.iter().cloned().map(expr_to_term));

        let no_progress = state
            .instantiations
            .into_iter()
            // .inspect(|x| println!("x: {x}"))
            .map(expr_to_term)
            .map(QuantifiedInstantiator::rewrite_quantified)
            .all(|inst| !model.add_instantiation(inst, &mut self.used_instantiations));
        let const_progress = state
            .const_instantiations
            .into_iter()
            .map(expr_to_term)
            .map(QuantifiedInstantiator::rewrite_quantified)
            .all(|inst| !model.add_instantiation(inst, &mut self.used_instantiations));
        if no_progress && const_progress {
            Err(Error::NoProgress {
                depth: state.depth,
                instantiations: self.used_instantiations.clone(),
            })
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
        }
    }
}
