use log::info;
use smt2parser::vmt::VMTModel;

use crate::ic3ia::ic3ia_output_contains_proof;
use crate::solver::PropertyCheckMode;
use crate::strategies::RefinementState;
use crate::theory_support::{ArrayWithQuantifiersTheorySupport, TheorySupport};
use crate::{driver, ic3ia, ProofLoopResult};

use super::{ProofAction, ProofStrategy};

pub struct AbstractArrayWithQuantifiers {
    run_ic3ia: bool,
    eager: Option<Box<dyn super::eager::InstanceSeeder>>,
    discovered_array_types: Vec<(String, String)>,
    preprocess_exact_read_after_write: bool,
    property_check_mode: PropertyCheckMode,
}

impl AbstractArrayWithQuantifiers {
    pub fn new(run_ic3ia: bool) -> Self {
        Self {
            run_ic3ia,
            eager: None,
            discovered_array_types: vec![],
            preprocess_exact_read_after_write: false,
            property_check_mode: PropertyCheckMode::Scoped,
        }
    }

    pub fn with_exact_read_after_write_preprocessing(mut self, enabled: bool) -> Self {
        self.preprocess_exact_read_after_write = enabled;
        self
    }

    pub fn with_eager_policy<F: crate::policy::term_selection::TermCostFactory + 'static>(
        mut self,
        policy: &crate::YardbirdPolicy<F>,
    ) -> Self {
        self.eager = policy.eager_seeder();
        self
    }

    pub fn with_property_check_mode(mut self, mode: PropertyCheckMode) -> Self {
        self.property_check_mode = mode;
        self
    }
}

impl ProofStrategy<'_, RefinementState> for AbstractArrayWithQuantifiers {
    fn instance_seeder(&mut self) -> Option<&mut (dyn super::eager::InstanceSeeder + '_)> {
        match self.eager.as_mut() {
            Some(seeder) => Some(seeder.as_mut()),
            None => None,
        }
    }

    fn property_check_mode(&self) -> PropertyCheckMode {
        self.property_check_mode
    }

    fn get_theory_support(&self) -> Box<dyn TheorySupport> {
        Box::new(ArrayWithQuantifiersTheorySupport::new(
            self.discovered_array_types.clone(),
        ))
    }

    fn configure_model(&mut self, model: VMTModel) -> VMTModel {
        if let Some(seeder) = &mut self.eager {
            seeder.configure_vmt(&model, true);
        }
        let (model, types) =
            model.abstract_array_theory_with_preprocessing(self.preprocess_exact_read_after_write);
        self.discovered_array_types = types;
        model
    }

    fn preprocess_exact_read_after_write(&self) -> bool {
        self.preprocess_exact_read_after_write
    }

    fn setup(
        &mut self,
        _smt: &dyn crate::problem_context::ProblemContext,
        depth: u16,
    ) -> driver::Result<RefinementState> {
        Ok(RefinementState {
            binder_search: None,
            model_version: 0,
            graph_version: 0,
            array_expansion: None,
            array_exhausted: false,
            model_reported: false,
            depth,
            egraph: crate::refinement_graph::RefinementGraph::default(),
            candidates: vec![],
            guarded_read_updates: vec![],
            array_types: vec![],
            egraph_builder:
                Box::<crate::theories::array::array_egraph_builder::FullEGraphBuilder>::default(),
        })
    }

    fn unsat(
        &mut self,
        state: &mut RefinementState,
        _solver: &dyn crate::problem_context::ProblemContext,
    ) -> driver::Result<ProofAction> {
        info!("RULED OUT ALL COUNTEREXAMPLES OF DEPTH {}", state.depth);
        Ok(ProofAction::NextDepth)
    }

    fn sat(
        &mut self,
        state: &mut RefinementState,
        smt: &dyn crate::problem_context::ProblemContext,
        _: u32,
    ) -> driver::Result<ProofAction> {
        info!("Concrete Counterexample Found at depth: {}!", state.depth);
        info!("Counterexample:\n{}", smt.model_to_string()?);
        Ok(ProofAction::FoundCounterexample)
    }

    #[allow(clippy::unnecessary_fold)]
    fn finish(
        &mut self,
        _: RefinementState,
        _: &mut dyn crate::problem_context::ProblemContext,
    ) -> driver::Result<()> {
        Ok(())
    }

    fn result(
        &mut self,
        vmt_model: &mut VMTModel,
        smt: &dyn crate::problem_context::ProblemContext,
    ) -> ProofLoopResult {
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
            used_instances: smt.get_instantiations(),
            solver_statistics: smt.get_solver_statistics(),
            counterexample: false,
            found_proof,
            total_instantiations_added: smt.get_number_instantiations_added(),
            total_refinement_steps: 0,
            unsat_core: None, // VMT mode unsat core tracked separately via dump-unsat-core
            decision_data: vec![],
            abstract_instantiations: vec![],
            indexed_instantiations: vec![],
            unsat_events: vec![],
            auxiliary_records: smt.get_auxiliary_records(),
            run_progress: None,
            profiling: crate::profiling::ProfilingRunRecord::default(),
        }
    }
}
