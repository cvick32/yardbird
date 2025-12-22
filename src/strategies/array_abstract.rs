use std::mem;

use log::info;
use smt2parser::{
    concrete::Term,
    vmt::{quantified_instantiator::UnquantifiedInstantiator, VMTModel},
};

use crate::{
    analysis::SaturationInequalities,
    cost_functions::YardbirdCostFunction,
    driver::{self},
    ic3ia::{call_ic3ia, ic3ia_output_contains_proof},
    smt_problem::SMTProblem,
    theories::array::{
        array_axioms::{
            expr_to_term, saturate_with_array_types, translate_term, ArrayExpr, ArrayLanguage,
        },
        array_conflict_scheduler::preprocess_array_expr,
    },
    theory_support::{ArrayTheorySupport, TheorySupport},
    ProofLoopResult,
};

use super::{ProofAction, ProofStrategy};

/// Global state carried across different BMC depths
pub struct Abstract<F>
where
    F: YardbirdCostFunction<ArrayLanguage>,
{
    const_instantiations: Vec<Term>,
    _bmc_depth: u16,
    run_ic3ia: bool,
    cost_fn_factory: fn(&SMTProblem, u32) -> F,
    discovered_array_types: Vec<(String, String)>,
}

impl<F> Abstract<F>
where
    F: YardbirdCostFunction<ArrayLanguage>,
{
    pub fn new(
        bmc_depth: u16,
        run_ic3ia: bool,
        cost_fn_factory: fn(&SMTProblem, u32) -> F,
    ) -> Self {
        Self {
            _bmc_depth: bmc_depth,
            run_ic3ia,
            const_instantiations: vec![],
            cost_fn_factory,
            discovered_array_types: vec![],
        }
    }
}

/// State for the inner refinement looop
pub struct ArrayRefinementState {
    pub depth: u16,
    pub egraph: egg::EGraph<ArrayLanguage, SaturationInequalities>,
    pub instantiations: Vec<ArrayExpr>,
    pub const_instantiations: Vec<ArrayExpr>,
    pub array_types: Vec<(String, String)>,
}

impl ArrayRefinementState {
    pub fn update_with_subterms(
        &mut self,
        model: &z3::Model,
        smt: &SMTProblem,
    ) -> anyhow::Result<()> {
        for term in smt.get_all_subterms() {
            let z3_term = smt.rewrite_term(term);
            let model_interp = smt.get_interpretation(model, &z3_term);
            let interp_str = model_interp.to_string();
            let term_id = self.egraph.add_expr(&translate_term(term.clone()).unwrap());
            let preprocessed = preprocess_array_expr(&interp_str);
            let interp_id = self.egraph.add_expr(&preprocessed.parse()?);
            self.egraph.union(term_id, interp_id);
        }
        self.egraph.rebuild();
        Ok(())
    }
}

impl<F> ProofStrategy<'_, ArrayRefinementState> for Abstract<F>
where
    F: YardbirdCostFunction<ArrayLanguage> + 'static,
{
    fn get_theory_support(&self) -> Box<dyn TheorySupport> {
        Box::new(ArrayTheorySupport::new(self.discovered_array_types.clone()))
    }

    fn configure_model(&mut self, model: VMTModel) -> VMTModel {
        let (abstracted_model, discovered_types) = model.abstract_array_theory();
        self.discovered_array_types = discovered_types;
        abstracted_model
        //     .abstract_constants_over(self.bmc_depth)
    }

    fn setup(&mut self, _smt: &SMTProblem, depth: u16) -> driver::Result<ArrayRefinementState> {
        let egraph = egg::EGraph::new(SaturationInequalities);
        Ok(ArrayRefinementState {
            depth,
            egraph,
            instantiations: vec![],
            const_instantiations: vec![],
            array_types: self.discovered_array_types.clone(),
        })
    }

    fn unsat(
        &mut self,
        state: &mut ArrayRefinementState,
        _solver: &SMTProblem,
    ) -> driver::Result<ProofAction> {
        info!("RULED OUT ALL COUNTEREXAMPLES OF DEPTH {}", state.depth);
        Ok(ProofAction::NextDepth)
    }

    fn sat(
        &mut self,
        state: &mut ArrayRefinementState,
        smt: &SMTProblem,
        refinement_step: u32,
    ) -> driver::Result<ProofAction> {
        let model = match smt.get_model() {
            Some(model) => model,
            None => todo!("No Z3 model available for SAT instance"),
        };
        state.update_with_subterms(model, smt)?;
        let cost_fn = (self.cost_fn_factory)(smt, state.depth as u32);
        let (insts, const_insts) = saturate_with_array_types(
            &mut state.egraph,
            cost_fn,
            refinement_step,
            &state.array_types,
        );
        state.instantiations.extend_from_slice(&insts);
        state.const_instantiations.extend_from_slice(&const_insts);
        Ok(ProofAction::Continue)
    }

    #[allow(clippy::unnecessary_fold)]
    fn finish(&mut self, state: ArrayRefinementState, smt: &mut SMTProblem) -> driver::Result<()> {
        let const_terms: Vec<Term> = state
            .const_instantiations
            .iter()
            .map(|inst| expr_to_term(inst.clone()))
            .collect();
        let variables = smt.variables.clone();
        for term in &const_terms {
            if let Some(inst) =
                UnquantifiedInstantiator::rewrite_unquantified(term.clone(), variables.clone())
            {
                smt.add_instantiation(inst);
            }
        }
        self.const_instantiations
            .extend(state.const_instantiations.into_iter().map(expr_to_term));

        let terms: Vec<Term> = state.instantiations.into_iter().map(expr_to_term).collect();
        let variables = smt.variables.clone();
        let _ = terms
            .into_iter()
            .flat_map(|term| {
                UnquantifiedInstantiator::rewrite_unquantified(term, variables.clone())
            })
            .map(|inst| !smt.add_instantiation(inst))
            .fold(true, |a, b| a && b);

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
            total_instantiations_added: smt.get_number_instantiations_added(),
            solver_statistics: smt.get_solver_statistics(),
            counterexample: false,
            found_proof,
        }
    }
}
