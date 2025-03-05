use std::mem;

use anyhow::anyhow;
use log::{debug, info};
use smt2parser::{
    concrete::Term,
    vmt::{QuantifiedInstantiator, VMTModel},
};

use crate::{
    analysis::SaturationInequalities,
    array_axioms::ArrayLanguage,
    cost_functions::symbol_cost::BestSymbolSubstitution,
    driver::{self, Error},
    egg_utils::Saturate,
    smt_problem::SMTProblem,
    ProofLoopResult,
};

use super::{ProofAction, ProofStrategy};

/// Global state carried across different BMC depths
#[derive(Default)]
pub struct Abstract {
    used_instantiations: Vec<String>,
    const_instantiations: Vec<String>,
    bmc_depth: u8,
}

impl Abstract {
    pub fn new(bmc_depth: u8) -> Self {
        Self {
            bmc_depth,
            ..Default::default()
        }
    }
}

/// State for the inner refinement looop
pub struct AbstractRefinementState {
    pub depth: u8,
    pub egraph: egg::EGraph<ArrayLanguage, SaturationInequalities>,
    pub instantiations: Vec<String>,
    pub const_instantiations: Vec<String>,
}

impl ProofStrategy<'_, AbstractRefinementState> for Abstract {
    fn configure_model(&mut self, model: VMTModel) -> VMTModel {
        model
            .abstract_array_theory()
            .abstract_constants_over(self.bmc_depth)
    }

    fn setup(&mut self, smt: &SMTProblem, depth: u8) -> driver::Result<AbstractRefinementState> {
        let mut egraph = egg::EGraph::new(SaturationInequalities).with_explanations_enabled();
        for term in smt.get_assert_terms() {
            // TODO: we don't want to add instantiations
            if let Ok(parsed) = &term.to_string().parse() {
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
        let model = smt.get_model().ok_or(anyhow!("No z3 model"))?;
        debug!("counter example:\n{model}");
        state.update_with_subterms(&model, smt)?;
        // state.egraph.rebuild();
        let cost_fn = BestSymbolSubstitution {
            current_bmc_depth: state.depth as u32,
            transition_system_terms: smt.get_transition_system_subterms(),
            property_terms: smt.get_property_subterms(),
            reads_writes: smt.get_reads_and_writes(),
        };
        let (insts, const_insts) = state.egraph.saturate(cost_fn);
        state.instantiations.extend_from_slice(&insts);
        state.const_instantiations.extend_from_slice(&const_insts);
        Ok(ProofAction::Continue)
    }

    #[allow(clippy::unnecessary_fold)]
    fn finish(
        &mut self,
        model: &mut VMTModel,
        state: AbstractRefinementState,
    ) -> driver::Result<()> {
        self.const_instantiations
            .extend_from_slice(&state.const_instantiations);

        let terms: Vec<Term> = state
            .instantiations
            .into_iter()
            // .all(|inst| !model.add_instantiation(inst, &mut self.used_instantiations));
            .flat_map(|inst| inst.parse())
            .collect();

        // first try without quantifiers
        let no_progress = terms
            .clone()
            .into_iter()
            .flat_map(QuantifiedInstantiator::rewrite_no_prophecy)
            .map(|term| !model.add_instantiation(term, &mut self.used_instantiations))
            .fold(true, |a, b| a && b);

        // if that didn't work, try with quantifiers
        if no_progress {
            let no_quant_progress = terms
                .into_iter()
                .map(QuantifiedInstantiator::rewrite_quantified)
                .map(|term| !model.add_instantiation(term, &mut self.used_instantiations))
                .fold(true, |a, b| a && b);

            if no_quant_progress {
                return Err(Error::NoProgress {
                    depth: state.depth,
                    instantiations: self.used_instantiations.clone(),
                });
            }
        }

        Ok(())
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

impl AbstractRefinementState {
    pub fn update_with_subterms(
        &mut self,
        model: &z3::Model,
        smt: &SMTProblem,
    ) -> anyhow::Result<()> {
        for term in smt.get_all_subterms() {
            let term_id = self.egraph.add_expr(&term.to_string().parse()?);
            let z3_term = smt.rewrite_term(&term);
            let model_interp = model
                .eval(&z3_term, false)
                .unwrap_or_else(|| panic!("Term not found in model: {term}"));
            let interp_id = self.egraph.add_expr(&model_interp.to_string().parse()?);
            self.egraph.union(term_id, interp_id);
        }
        self.egraph.rebuild();
        Ok(())
    }
}

/* let mut full_false_insts = vec![];
let mut full_const_insts = vec![];
let mut i = 0;
loop {
    if i > 15 {
        break;
    }
    state.egraph.rebuild();
    let cost_fn = BestVariableSubstitution {
        current_bmc_depth: state.depth as u32,
        transition_system_terms: state.smt.get_transition_system_subterms(),
        property_terms: state.smt.get_property_subterms(),
    };

    let (insts, const_insts) = state.egraph.saturate(cost_fn);
    let (false_insts, true_insts) =
        self._check_found_instantiations(z3_var_context, &model, insts);
    if false_insts.is_empty() {
        for (lhs, rhs) in true_insts {
            println!("Add: {} = {}", lhs, rhs);
            state._add_true_instantiation(lhs, rhs)?;
        }
    } else {
        full_false_insts.extend_from_slice(&false_insts);
        full_const_insts.extend_from_slice(&const_insts);
        break;
    }
    i += 1;
}
println!("ACTUALLY FALSE INSTS: {:#?}", full_false_insts); */
