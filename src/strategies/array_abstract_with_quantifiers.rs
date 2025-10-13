use log::info;
use smt2parser::vmt::VMTModel;

use crate::{
    driver::{self},
    ic3ia::{self, ic3ia_output_contains_proof},
    smt_problem::SMTProblem,
    strategies::ArrayRefinementState,
    theory_support::{ArrayWithQuantifiersTheorySupport, TheorySupport},
    z3_ext::ModelExt,
    ProofLoopResult,
};

use super::{ProofAction, ProofStrategy};

pub struct AbstractArrayWithQuantifiers {
    run_ic3ia: bool,
}

impl AbstractArrayWithQuantifiers {
    pub fn new(run_ic3ia: bool) -> Self {
        Self { run_ic3ia }
    }
}

impl ProofStrategy<'_, ArrayRefinementState> for AbstractArrayWithQuantifiers {
    fn get_theory_support(&self) -> Box<dyn TheorySupport> {
        Box::new(ArrayWithQuantifiersTheorySupport)
    }

    fn configure_model(&mut self, model: VMTModel) -> VMTModel {
        self.get_theory_support().abstract_model(model)
    }

    fn setup(&mut self, _smt: &SMTProblem, depth: u16) -> driver::Result<ArrayRefinementState> {
        Ok(ArrayRefinementState {
            depth,
            egraph: egg::EGraph::default(),
            instantiations: vec![],
            const_instantiations: vec![],
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
        _: u32,
    ) -> driver::Result<ProofAction> {
        info!("Concrete Counterexample Found at depth: {}!", state.depth);
        let model = match smt.get_model() {
            Some(model) => model,
            None => todo!("No Z3 model available for SAT instance"),
        };
        info!("Counterexample:\n{}", model.dump_sorted()?);
        Ok(ProofAction::FoundCounterexample)
    }

    #[allow(clippy::unnecessary_fold)]
    fn finish(&mut self, _: ArrayRefinementState, _: &mut SMTProblem) -> driver::Result<()> {
        Ok(())
    }

    fn result(&mut self, vmt_model: &mut VMTModel, smt: &SMTProblem) -> ProofLoopResult {
        let found_proof = if self.run_ic3ia {
            match ic3ia::call_ic3ia(vmt_model.clone()) {
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
            used_instances: vec![],
            const_instances: vec![],
            solver_statistics: smt.get_solver_statistics(),
            counterexample: false,
            found_proof,
        }
    }
}
