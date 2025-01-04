use anyhow::anyhow;
use log::info;
use smt2parser::vmt::{smt::SMTProblem, VMTModel};

use crate::{z3_ext::ModelExt, z3_var_context::Z3VarContext, ProofLoopResult};

use super::{r#abstract::AbstractRefinementState, ProofAction, ProofStrategy};

#[derive(Default)]
pub struct ConcreteZ3 {
    model: Option<VMTModel>,
}

impl<'ctx> ProofStrategy<'ctx, AbstractRefinementState> for ConcreteZ3 {
    fn n_refines(&mut self) -> u32 {
        1
    }

    fn setup(&mut self, smt: SMTProblem, depth: u8) -> anyhow::Result<AbstractRefinementState> {
        Ok(AbstractRefinementState {
            smt,
            depth,
            egraph: egg::EGraph::default(),
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
        Ok(ProofAction::Continue)
    }

    fn sat(
        &mut self,
        state: &mut AbstractRefinementState,
        solver: &z3::Solver,
        _z3_var_context: &Z3VarContext,
    ) -> anyhow::Result<ProofAction> {
        info!("Concrete Counterexample Found at depth: {}!", state.depth);
        let model = solver.get_model().ok_or(anyhow!("No z3 model"))?;
        info!("{}", model.dump_sorted()?);
        Ok(ProofAction::Stop)
    }

    fn finish(
        &mut self,
        model: &mut VMTModel,
        _state: AbstractRefinementState,
    ) -> anyhow::Result<()> {
        self.model = Some(model.clone());
        Ok(())
    }

    fn result(&mut self) -> ProofLoopResult {
        ProofLoopResult {
            model: None,
            used_instances: vec![],
            const_instances: vec![],
            counterexample: true,
        }
    }
}
