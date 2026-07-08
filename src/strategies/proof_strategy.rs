use smt2parser::vmt::VMTModel;

use crate::{
    driver::{self, Error},
    problem_context::ProblemContext,
    profiling::ProfilingRecord,
    theory_support::TheorySupport,
    training::{AbstractInstantiationRecord, DecisionRecord},
    ProofLoopResult,
};

pub enum ProofAction {
    Continue,
    NextDepth,
    FoundCounterexample,
    FoundProof,
}

/// Describes how to respond to the solver returning `unsat`, `unknown`, or `sat` at
/// each depth of the proof loop.
///
/// Additionally, we can setup any per-refinement loop state with `setup` and do any
/// finalizing steps with `finish`. The `result` method describes how to construct a
/// `ProofLoopResult` from `self`.
pub trait ProofStrategy<'ctx, S> {
    fn get_theory_support(&self) -> Box<dyn TheorySupport>;

    fn configure_model(&mut self, model: VMTModel) -> VMTModel {
        model
    }

    fn n_refines(&mut self) -> u32 {
        250
    }

    fn setup(&mut self, smt: &dyn ProblemContext, depth: u16) -> driver::Result<S>;

    fn unsat(&mut self, state: &mut S, smt: &dyn ProblemContext) -> driver::Result<ProofAction>;

    fn sat(
        &mut self,
        state: &mut S,
        smt: &dyn ProblemContext,
        refinement_step: u32,
    ) -> driver::Result<ProofAction>;

    #[allow(unused_variables)]
    fn unknown(&mut self, state: &mut S, smt: &dyn ProblemContext) -> driver::Result<ProofAction> {
        Err(Error::SolverUnknown(smt.get_reason_unknown()))
    }

    #[allow(unused_variables)]
    fn finish(&mut self, state: S, smt: &mut dyn ProblemContext) -> driver::Result<()> {
        Ok(())
    }

    fn take_logging_artifacts(
        &mut self,
    ) -> (Vec<DecisionRecord>, Vec<AbstractInstantiationRecord>) {
        (vec![], vec![])
    }

    fn take_profiling_records(&mut self) -> Vec<ProfilingRecord> {
        vec![]
    }

    fn profiling_enabled(&self) -> bool {
        false
    }

    fn result(&mut self, model: &mut VMTModel, smt: &dyn ProblemContext) -> ProofLoopResult;
}

/// Allows easy modification of some other proof strategy. These methods corrrespond
/// to methods on `ProofStrategy` and get run before the underlying method on
/// `ProofStrategy`. Good for additional processing / adding some kind of interface
/// to a proof strategy.
pub trait ProofStrategyExt<S> {
    #[allow(unused_variables)]
    fn unsat(&mut self, state: &mut S, smt: &dyn ProblemContext) -> anyhow::Result<()> {
        Ok(())
    }

    #[allow(unused_variables)]
    fn sat(
        &mut self,
        state: &mut S,
        smt: &dyn ProblemContext,
        refinement_step: u32,
    ) -> anyhow::Result<()> {
        Ok(())
    }

    #[allow(unused_variables)]
    fn unknown(&mut self, state: &mut S, smt: &dyn ProblemContext) -> anyhow::Result<()> {
        Ok(())
    }

    #[allow(unused_variables)]
    fn finish(&mut self, model: &mut VMTModel, state: &mut S) -> anyhow::Result<()> {
        Ok(())
    }
}
