use log::info;
use smt2parser::vmt::VMTModel;

use crate::{
    driver,
    ic3ia::{self, ic3ia_output_contains_proof},
    solver::PropertyCheckMode,
    theory_support::{ConcreteArrayTheory, TheorySupport},
    ProofLoopResult,
};

use super::{ProofAction, ProofStrategy, RefinementState};

#[derive(Default)]
pub struct ConcreteArrayZ3 {
    run_ic3ia: bool,
    eager: Option<Box<dyn super::eager::InstanceSeeder>>,
    discovered_array_types: Vec<(String, String)>,
    property_check_mode: PropertyCheckMode,
}
impl ConcreteArrayZ3 {
    pub fn new(run_ic3ia: bool) -> Self {
        Self {
            run_ic3ia,
            eager: None,
            discovered_array_types: vec![],
            property_check_mode: PropertyCheckMode::Scoped,
        }
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

impl ProofStrategy<'_, RefinementState> for ConcreteArrayZ3 {
    fn instance_seeder(&mut self) -> Option<&mut (dyn super::eager::InstanceSeeder + '_)> {
        match self.eager.as_mut() {
            Some(seeder) => Some(seeder.as_mut()),
            None => None,
        }
    }

    fn property_check_mode(&self) -> PropertyCheckMode {
        self.property_check_mode
    }

    fn configure_model(&mut self, model: VMTModel) -> VMTModel {
        if let Some(seeder) = &mut self.eager {
            seeder.configure_vmt(&model, false);
        }
        let (_, discovered_array_types) = model.abstract_array_theory();
        self.discovered_array_types = discovered_array_types;
        model
    }

    fn refinement_limit(&self) -> Option<u32> {
        Some(1)
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

    fn sat(
        &mut self,
        state: &mut RefinementState,
        smt: &dyn crate::problem_context::ProblemContext,
        _refinement_step: u32,
    ) -> driver::Result<ProofAction> {
        info!("Concrete Counterexample Found at depth: {}!", state.depth);
        info!("Counterexample:\n{}", smt.model_to_string()?);
        Ok(ProofAction::FoundCounterexample)
    }

    fn finish(
        &mut self,
        _state: RefinementState,
        _smt: &mut dyn crate::problem_context::ProblemContext,
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

    fn unsat(
        &mut self,
        state: &mut RefinementState,
        _smt: &dyn crate::problem_context::ProblemContext,
    ) -> driver::Result<ProofAction> {
        info!("RULED OUT ALL COUNTEREXAMPLES OF DEPTH {}", state.depth);
        Ok(ProofAction::NextDepth)
    }

    fn get_theory_support(&self) -> Box<dyn TheorySupport> {
        Box::new(ConcreteArrayTheory::new(
            self.discovered_array_types.clone(),
        ))
    }
}
