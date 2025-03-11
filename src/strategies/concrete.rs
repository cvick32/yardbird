use log::info;
use smt2parser::vmt::VMTModel;

use crate::{
    driver,
    ic3ia::{self, ic3ia_output_contains_proof},
    smt_problem::SMTProblem,
    z3_ext::ModelExt,
    ProofLoopResult,
};

use super::{AbstractRefinementState, ProofAction, ProofStrategy};

#[derive(Default)]
pub struct ConcreteZ3 {
    run_ic3ia: bool,
}

impl ProofStrategy<'_, AbstractRefinementState> for ConcreteZ3 {
    fn n_refines(&mut self) -> u32 {
        1
    }

    fn setup(&mut self, _smt: &SMTProblem, depth: u16) -> driver::Result<AbstractRefinementState> {
        Ok(AbstractRefinementState {
            depth,
            egraph: egg::EGraph::default(),
            instantiations: vec![],
            const_instantiations: vec![],
        })
    }

    fn sat(
        &mut self,
        state: &mut AbstractRefinementState,
        smt: &SMTProblem,
    ) -> driver::Result<ProofAction> {
        info!("Concrete Counterexample Found at depth: {}!", state.depth);
        let model = match smt.get_model() {
            Some(model) => model,
            None => todo!("No Z3 model available for SAT instance"),
        };
        info!("Counterexample:\n{}", model.dump_sorted()?);
        Ok(ProofAction::FoundCounterexample)
    }

    fn finish(
        &mut self,
        _state: AbstractRefinementState,
        _smt: &mut SMTProblem,
    ) -> driver::Result<()> {
        Ok(())
    }

    fn result(&mut self, vmt_model: &mut VMTModel, _smt: &SMTProblem) -> ProofLoopResult {
        let found_proof = if self.run_ic3ia {
            let result = ic3ia::call_ic3ia(vmt_model.clone());
            match result {
                Ok(out) => ic3ia_output_contains_proof(out),
                Err(_) => false,
            }
        } else {
            false
        };

        ProofLoopResult {
            model: Some(vmt_model.clone()),
            used_instances: vec![],
            const_instances: vec![],
            counterexample: true,
            found_proof,
        }
    }

    fn unsat(
        &mut self,
        state: &mut AbstractRefinementState,
        _smt: &SMTProblem,
    ) -> driver::Result<ProofAction> {
        info!("RULED OUT ALL COUNTEREXAMPLES OF DEPTH {}", state.depth);
        Ok(ProofAction::NextDepth)
    }

    fn abstract_array_theory(&self) -> bool {
        false
    }
}
