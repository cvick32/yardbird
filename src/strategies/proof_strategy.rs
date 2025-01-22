use smt2parser::vmt::{smt::SMTProblem, VMTModel};

use crate::{
    driver::{self, Error},
    z3_var_context::Z3VarContext,
    ProofLoopResult,
};

pub enum ProofAction {
    Continue,
    NextDepth,
    Stop,
}

/// Describes how to respond to the solver returning `unsat`, `unknown`, or `sat` at
/// each depth of the proof loop.
///
/// Additionally, we can setup any per-refinement loop state with `setup` and do any
/// finalizing steps with `finish`. The `result` method describes how to construct a
/// `ProofLoopResult` from `self`.
pub trait ProofStrategy<'ctx, S> {
    fn configure_model(&mut self, model: VMTModel) -> VMTModel {
        model
    }

    fn n_refines(&mut self) -> u32 {
        10
    }

    fn setup(&mut self, smt: SMTProblem, depth: u8) -> driver::Result<S>;

    fn unsat(&mut self, state: &mut S, solver: &z3::Solver) -> driver::Result<ProofAction>;

    fn sat(
        &mut self,
        state: &mut S,
        solver: &z3::Solver,
        z3_var_context: &Z3VarContext,
    ) -> driver::Result<ProofAction>;

    #[allow(unused_variables)]
    fn unknown(&mut self, state: &mut S, solver: &z3::Solver) -> driver::Result<ProofAction> {
        Err(Error::SolverUnknown(solver.get_reason_unknown()))
    }

    #[allow(unused_variables)]
    fn finish(&mut self, model: &mut VMTModel, state: S) -> driver::Result<()> {
        Ok(())
    }

    fn result(&mut self, model: VMTModel) -> ProofLoopResult;
}

/// Allows easy modification of some other proof strategy. These methods corrrespond
/// to methods on `ProofStrategy` and get run before the underlying method on
/// `ProofStrategy`. Good for additional processing / adding some kind of interface
/// to a proof strategy.
pub trait ProofStrategyExt<S> {
    #[allow(unused_variables)]
    fn unsat(
        &mut self,
        state: &mut S,
        solver: &z3::Solver,
        z3_var_context: &Z3VarContext,
    ) -> anyhow::Result<()> {
        Ok(())
    }

    #[allow(unused_variables)]
    fn sat(&mut self, state: &mut S, solver: &z3::Solver) -> anyhow::Result<()> {
        Ok(())
    }

    #[allow(unused_variables)]
    fn unknown(&mut self, state: &mut S, solver: &z3::Solver) -> anyhow::Result<()> {
        Ok(())
    }

    #[allow(unused_variables)]
    fn finish(&mut self, model: &mut VMTModel, state: &mut S) -> anyhow::Result<()> {
        Ok(())
    }
}
