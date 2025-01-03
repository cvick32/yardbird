use anyhow::anyhow;
use smt2parser::vmt::{smt::SMTProblem, VMTModel};

use crate::ProofLoopResult;

pub enum ProofAction {
    Continue,
    NextDepth,
    Stop,
}

pub trait ProofStrategy<'ctx, S> {
    fn configure_model(&mut self, model: VMTModel) -> VMTModel {
        model
    }

    fn n_refines(&mut self) -> u32 {
        10
    }

    fn setup(
        &mut self,
        context: &'ctx z3::Context,
        smt: SMTProblem,
        depth: u8,
    ) -> anyhow::Result<S>;

    fn unsat(&mut self, state: &mut S, solver: &z3::Solver) -> anyhow::Result<ProofAction>;

    fn sat(&mut self, state: &mut S, solver: &z3::Solver) -> anyhow::Result<ProofAction>;

    #[allow(unused_variables)]
    fn unknown(&mut self, state: &mut S, solver: &z3::Solver) -> anyhow::Result<ProofAction> {
        Err(anyhow!(
            "{}",
            solver
                .get_reason_unknown()
                .unwrap_or("Solver returned unknown!".to_string())
        ))
    }

    #[allow(unused_variables)]
    fn finish(&mut self, model: &mut VMTModel, state: S) -> anyhow::Result<()> {
        Ok(())
    }

    fn result(&mut self) -> ProofLoopResult;
}

pub trait ProofStrategyExt<'ctx, S> {
    #[allow(unused_variables)]
    fn unsat(&mut self, state: &mut S, solver: &z3::Solver) -> anyhow::Result<ProofAction> {
        Ok(ProofAction::Continue)
    }

    #[allow(unused_variables)]
    fn sat(&mut self, state: &mut S, solver: &z3::Solver) -> anyhow::Result<ProofAction> {
        Ok(ProofAction::Continue)
    }

    #[allow(unused_variables)]
    fn unknown(&mut self, state: &mut S, solver: &z3::Solver) -> anyhow::Result<ProofAction> {
        Ok(ProofAction::Continue)
    }

    #[allow(unused_variables)]
    fn finish(&mut self, model: &mut VMTModel, state: &mut S) -> anyhow::Result<()> {
        Ok(())
    }
}
