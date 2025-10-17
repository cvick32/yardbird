use egg::Language;
use smt2parser::vmt::ReadsAndWrites;

use crate::{
    cost_functions::YardbirdCostFunction,
    theories::{array::array_axioms::ArrayLanguage, list::list_axioms::ListLanguage},
};

#[derive(Clone)]
pub struct ArrayPreferWrite {
    pub current_bmc_depth: u32,
    pub init_and_transition_system_terms: Vec<String>,
    pub property_terms: Vec<String>,
    pub reads_writes: ReadsAndWrites,
}

impl egg::CostFunction<ArrayLanguage> for ArrayPreferWrite {
    type Cost = u32;

    fn cost<C>(&mut self, enode: &ArrayLanguage, mut costs: C) -> Self::Cost
    where
        C: FnMut(egg::Id) -> Self::Cost,
    {
        let op_cost = match enode {
            ArrayLanguage::Write(_) => 0,
            _ => 20,
        };

        enode.fold(op_cost, |sum, id| sum + costs(id))
    }
}

impl egg::CostFunction<ListLanguage> for ArrayPreferWrite {
    type Cost = u32;

    fn cost<C>(&mut self, _enode: &ListLanguage, _costs: C) -> Self::Cost
    where
        C: FnMut(egg::Id) -> Self::Cost,
    {
        todo!()
    }
}

impl YardbirdCostFunction<ArrayLanguage> for ArrayPreferWrite {
    fn get_string_terms(&self) -> Vec<String> {
        self.init_and_transition_system_terms
            .iter()
            .chain(self.property_terms.iter())
            .map(|sym| sym.as_str().to_string())
            .collect()
    }

    fn get_reads_and_writes(&self) -> ReadsAndWrites {
        self.reads_writes.clone()
    }
}
