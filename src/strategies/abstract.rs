use std::mem;

use log::info;
use smt2parser::{
    concrete::Term,
    vmt::{QuantifiedInstantiator, VMTModel},
};

use crate::{
    analysis::SaturationInequalities,
    array_axioms::{expr_to_term, translate_term, ArrayExpr, ArrayLanguage},
    cost_functions::YardbirdCostFunction,
    driver::{self, Error},
    egg_utils::Saturate,
    ic3ia::{call_ic3ia, ic3ia_output_contains_proof},
    smt_problem::SMTProblem,
    ProofLoopResult,
};

use super::{ProofAction, ProofStrategy};

/// Global state carried across different BMC depths
pub struct Abstract<F>
where
    F: YardbirdCostFunction,
{
    const_instantiations: Vec<Term>,
    bmc_depth: u16,
    run_ic3ia: bool,
    cost_fn_factory: fn(&SMTProblem, u32) -> F,
}

impl<F> Abstract<F>
where
    F: YardbirdCostFunction,
{
    pub fn new(
        bmc_depth: u16,
        run_ic3ia: bool,
        cost_fn_factory: fn(&SMTProblem, u32) -> F,
    ) -> Self {
        Self {
            bmc_depth,
            run_ic3ia,
            const_instantiations: vec![],
            cost_fn_factory,
        }
    }
}

/// State for the inner refinement looop
pub struct AbstractRefinementState {
    pub depth: u16,
    pub egraph: egg::EGraph<ArrayLanguage, SaturationInequalities>,
    pub instantiations: Vec<ArrayExpr>,
    pub const_instantiations: Vec<ArrayExpr>,
}

impl<F> ProofStrategy<'_, AbstractRefinementState> for Abstract<F>
where
    F: YardbirdCostFunction + 'static,
{
    fn configure_model(&mut self, model: VMTModel) -> VMTModel {
        model
            .abstract_array_theory()
            .abstract_constants_over(self.bmc_depth)
    }

    fn setup(&mut self, _smt: &SMTProblem, depth: u16) -> driver::Result<AbstractRefinementState> {
        let egraph = egg::EGraph::new(SaturationInequalities).with_explanations_enabled();
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
        let cost_fn = (self.cost_fn_factory)(smt, state.depth as u32);
        let (insts, const_insts) = state.egraph.saturate(cost_fn);
        state.instantiations.extend_from_slice(&insts);
        state.const_instantiations.extend_from_slice(&const_insts);
        Ok(ProofAction::Continue)
    }

    #[allow(clippy::unnecessary_fold)]
    fn finish(
        &mut self,
        state: AbstractRefinementState,
        smt: &mut SMTProblem,
    ) -> driver::Result<()> {
        self.const_instantiations
            .extend(state.const_instantiations.into_iter().map(expr_to_term));

        let terms: Vec<Term> = state
            .instantiations
            .into_iter()
            .flat_map(|inst| inst.to_string().parse())
            .collect();
        let variables = smt.variables.clone();
        let no_quant_progress = terms
            .into_iter()
            .flat_map(|term| QuantifiedInstantiator::rewrite_quantified(term, variables.clone()))
            .map(|inst| !smt.add_instantiation(inst))
            .fold(true, |a, b| a && b);

        if no_quant_progress {
            return Err(Error::NoProgress {
                depth: state.depth,
                instantiations: smt.get_instantiations().clone(),
            });
        }
        Ok(())
    }

    fn result(&mut self, vmt_model: &mut VMTModel, smt: &SMTProblem) -> ProofLoopResult {
        for instantiation_term in &smt.get_instantiations() {
            vmt_model.add_instantiation(instantiation_term);
        }
        let found_proof = if self.run_ic3ia {
            match call_ic3ia(vmt_model.clone()) {
                Ok(out) => {
                    info!("IC3IA OUT: {out}");
                    ic3ia_output_contains_proof(out)
                }
                Err(_) => false,
            }
        } else {
            false
        };
        ProofLoopResult {
            model: Some(vmt_model.clone()),
            used_instances: mem::take(&mut smt.get_instantiations()),
            const_instances: mem::take(&mut self.const_instantiations),
            solver_statistics: smt.get_solver_statistics(),
            counterexample: false,
            found_proof,
        }
    }

    fn abstract_array_theory(&self) -> bool {
        true
    }
}

impl AbstractRefinementState {
    pub fn update_with_subterms(
        &mut self,
        model: &z3::Model,
        smt: &SMTProblem,
    ) -> anyhow::Result<()> {
        for term in smt.get_all_subterms() {
            let z3_term = smt.rewrite_term(term);
            let model_interp = smt.get_interpretation(model, &z3_term);
            let term_id = self.egraph.add_expr(&translate_term(term.clone()).unwrap());
            let interp_id = self.egraph.add_expr(&model_interp.to_string().parse()?);
            self.egraph.union(term_id, interp_id);
        }
        self.egraph.rebuild();
        Ok(())
    }
}
