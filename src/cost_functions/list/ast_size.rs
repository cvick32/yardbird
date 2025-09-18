use smt2parser::vmt::ReadsAndWrites;

use crate::{cost_functions::YardbirdCostFunction, theories::list::list_axioms::ListLanguage};

#[derive(Clone, Debug)]
pub struct ListAstSize {
    pub current_bmc_depth: u32,
    pub init_and_transition_system_terms: Vec<String>,
    pub property_terms: Vec<String>,
    pub reads_writes: ReadsAndWrites,
}

impl egg::CostFunction<ListLanguage> for ListAstSize {
    type Cost = u32;

    fn cost<C>(&mut self, enode: &ListLanguage, _costs: C) -> Self::Cost
    where
        C: FnMut(egg::Id) -> Self::Cost,
    {
        enode.to_string().len() as u32
    }
}

impl YardbirdCostFunction<ListLanguage> for ListAstSize {
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
