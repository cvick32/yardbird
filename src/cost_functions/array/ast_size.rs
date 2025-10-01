use egg::Language;
use smt2parser::vmt::ReadsAndWrites;

use crate::{cost_functions::YardbirdCostFunction, theories::array::array_axioms::ArrayLanguage};

#[derive(Clone, Debug)]
pub struct ArrayAstSize {
    pub current_bmc_depth: u32,
    pub init_and_transition_system_terms: Vec<String>,
    pub property_terms: Vec<String>,
    pub reads_writes: ReadsAndWrites,
}

impl egg::CostFunction<ArrayLanguage> for ArrayAstSize {
    type Cost = u32;

    fn cost<C>(&mut self, enode: &ArrayLanguage, mut costs: C) -> Self::Cost
    where
        C: FnMut(egg::Id) -> Self::Cost,
    {
        enode.fold(enode.to_string().len() as u32, |sum, id| sum + costs(id))
    }
}

impl YardbirdCostFunction<ArrayLanguage> for ArrayAstSize {
    fn get_string_terms(&self) -> Vec<String> {
        self.init_and_transition_system_terms
            .clone()
            .into_iter()
            .chain(self.property_terms.clone())
            .collect::<Vec<String>>()
    }

    fn get_reads_and_writes(&self) -> ReadsAndWrites {
        self.reads_writes.clone()
    }
}
