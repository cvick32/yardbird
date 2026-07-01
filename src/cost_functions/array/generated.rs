use smt2parser::vmt::ReadsAndWrites;

use crate::{
    cost_functions::{array::ArrayCostFactory, YardbirdCostFunction},
    problem_context::ProblemContext,
    theories::array::array_axioms::ArrayLanguage,
};

#[derive(Clone, Debug)]
pub struct ArrayGenerated {
    pub current_bmc_depth: u32,
    pub init_and_transition_system_terms: Vec<String>,
    pub property_terms: Vec<String>,
    pub reads_writes: ReadsAndWrites,
}

impl ArrayCostFactory for ArrayGenerated {
    type Config = ();

    fn from_context(smt: &dyn ProblemContext, depth: u32, _config: &Self::Config) -> Self {
        Self {
            current_bmc_depth: depth,
            init_and_transition_system_terms: smt.get_init_and_transition_subterms(),
            property_terms: smt.get_property_subterms(),
            reads_writes: smt.get_reads_and_writes(),
        }
    }
}

impl egg::CostFunction<ArrayLanguage> for ArrayGenerated {
    type Cost = u32;

    fn cost<C>(&mut self, _enode: &ArrayLanguage, mut _costs: C) -> Self::Cost
    where
        C: FnMut(egg::Id) -> Self::Cost,
    {
        1
    }
}

impl YardbirdCostFunction<ArrayLanguage> for ArrayGenerated {
    fn get_string_terms(&self) -> Vec<String> {
        self.init_and_transition_system_terms
            .clone()
            .into_iter()
            .chain(self.property_terms.clone())
            .collect::<Vec<String>>()
    }

    fn get_transition_terms(&self) -> Vec<String> {
        self.init_and_transition_system_terms.clone()
    }

    fn get_property_terms(&self) -> Vec<String> {
        self.property_terms.clone()
    }

    fn get_reads_and_writes(&self) -> ReadsAndWrites {
        self.reads_writes.clone()
    }
}
