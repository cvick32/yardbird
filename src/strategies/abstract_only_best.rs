use std::mem;

use egg::CostFunction;
use itertools::Itertools;
use log::info;
use smt2parser::{
    concrete::Term,
    vmt::{QuantifiedInstantiator, VMTModel},
};

use crate::{
    analysis::SaturationInequalities,
    array_axioms::{expr_to_term, ArrayExpr},
    cost_functions::symbol_cost::BestSymbolSubstitution,
    driver,
    egg_utils::Saturate,
    smt_problem::SMTProblem,
    Error, ProofLoopResult,
};

use super::{AbstractRefinementState, ProofAction, ProofStrategy};

/// Global state carried across different BMC depths
#[derive(Default)]
pub struct AbstractOnlyBest {
    used_instantiations: Vec<Term>,
    const_instantiations: Vec<Term>,
    bmc_depth: u16,
}

impl AbstractOnlyBest {
    pub fn new(bmc_depth: u16) -> Self {
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

    fn setup(&mut self, smt: &SMTProblem, depth: u16) -> driver::Result<AbstractRefinementState> {
        let mut egraph = egg::EGraph::new(SaturationInequalities).with_explanations_enabled();
        for term_string in smt.get_assert_strings() {
            if let Ok(parsed) = &term_string.parse() {
                egraph.add_expr(parsed);
            }
        }
        Ok(AbstractRefinementState {
            depth,
            egraph,
            instantiations: vec![],
            const_instantiations: vec![],
        })
    }

    fn unsat(
        &mut self,
        state: &mut AbstractRefinementState,
        _solver: &SMTProblem,
    ) -> driver::Result<ProofAction> {
        info!("RULED OUT ALL COUNTEREXAMPLES OF DEPTH {}", state.depth);
        Ok(ProofAction::NextDepth)
    }

    fn sat(
        &mut self,
        state: &mut AbstractRefinementState,
        smt: &SMTProblem,
    ) -> driver::Result<ProofAction> {
        let model = match smt.get_model() {
            Some(model) => model,
            None => todo!("No Z3 model available for SAT instance"),
        };
        state.update_with_subterms(model, smt)?;
        state.egraph.rebuild();
        let mut cost_fn = BestSymbolSubstitution {
            current_bmc_depth: state.depth as u32,
            init_and_transition_system_terms: smt.get_init_and_transition_subterms(),
            property_terms: smt.get_property_subterms(),
            reads_writes: smt.get_reads_and_writes(),
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
        state: AbstractRefinementState,
        smt: &mut SMTProblem,
    ) -> driver::Result<()> {
        self.const_instantiations
            .extend(state.const_instantiations.into_iter().map(expr_to_term));
        let variables = smt.variables.clone();
        let terms: Vec<Term> = state.instantiations.into_iter().map(expr_to_term).collect();
        let no_progress = terms
            .clone()
            .into_iter()
            .flat_map(|term| QuantifiedInstantiator::rewrite_quantified(term, variables.clone()))
            .all(|inst| !smt.add_instantiation(inst));

        if no_progress {
            Err(Error::NoProgress {
                depth: state.depth,
                instantiations: self.used_instantiations.clone(),
            })
        } else {
            Ok(())
        }
    }

    fn result(&mut self, vmt_model: VMTModel, smt: &SMTProblem) -> ProofLoopResult {
        ProofLoopResult {
            model: Some(vmt_model),
            used_instances: mem::take(&mut smt.get_instantiations()),
            const_instances: mem::take(&mut self.const_instantiations),
            counterexample: false,
        }
    }

    fn abstract_array_theory(&self) -> bool {
        true
    }
}
