use std::mem;

use log::info;
use smt2parser::{concrete::Term, vmt::VMTModel};

use crate::{
    cost_functions::array::YardbirdCostFunction,
    driver::{self},
    ic3ia::{call_ic3ia, ic3ia_output_contains_proof},
    smt_problem::SMTProblem,
    strategies::AbstractRefinementState,
    theory_support::{ListTheorySupport, TheorySupport},
    ProofLoopResult,
};

use super::{ProofAction, ProofStrategy};

/// Global state carried across different BMC depths for List theory
pub struct ListAbstract<F>
where
    F: YardbirdCostFunction,
{
    const_instantiations: Vec<Term>,
    bmc_depth: u16,
    run_ic3ia: bool,
    cost_fn_factory: fn(&SMTProblem<'_>, u32) -> F,
}

impl<F> ListAbstract<F>
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

impl<F> ProofStrategy<'_, AbstractRefinementState> for ListAbstract<F>
where
    F: YardbirdCostFunction + 'static,
{
    fn get_theory_support(&self) -> Box<dyn TheorySupport> {
        Box::new(ListTheorySupport)
    }

    fn configure_model(&mut self, model: VMTModel) -> VMTModel {
        self.get_theory_support()
            .abstract_model(model)
            .abstract_constants_over(self.bmc_depth)
    }

    fn setup(&mut self, _smt: &SMTProblem, depth: u16) -> driver::Result<AbstractRefinementState> {
        use crate::analysis::SaturationInequalities;
        let egraph = egg::EGraph::new(SaturationInequalities);
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
        _state: &mut AbstractRefinementState,
        smt: &SMTProblem,
    ) -> driver::Result<ProofAction> {
        let _ = match smt.get_model() {
            Some(model) => model,
            None => todo!("No Z3 model available for SAT instance"),
        };
        (self.cost_fn_factory)(smt, 0);
        // For now, we'll use a simplified approach that doesn't use list-specific reasoning
        // TODO: Implement proper list model interpretation
        info!("List theory: found model, continuing with basic strategy");
        Ok(ProofAction::Continue)
    }

    #[allow(clippy::unnecessary_fold)]
    fn finish(
        &mut self,
        _state: AbstractRefinementState,
        _smt: &mut SMTProblem,
    ) -> driver::Result<()> {
        // For now, we don't add any instantiations
        // TODO: Implement proper list instantiation generation
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
}
