use egg::Language;
use smt2parser::vmt::ReadsAndWrites;

use crate::policy::term_selection::context::TermCostContext;
use crate::policy::term_selection::{TermCostFactory, YardbirdCostFunction};
use crate::terms::language::TermLanguage;
use crate::theories::list::list_axioms::ListLanguage;

#[derive(Clone)]
pub struct ArrayPreferRead {
    pub current_bmc_depth: u32,
    pub init_and_transition_system_terms: Vec<String>,
    pub property_terms: Vec<String>,
    pub reads_writes: ReadsAndWrites,
}

impl TermCostFactory for ArrayPreferRead {
    type Config = ();

    fn from_context(smt: &TermCostContext, depth: u32, _config: &Self::Config) -> Self {
        Self {
            current_bmc_depth: depth,
            init_and_transition_system_terms: smt.get_init_and_transition_subterms(),
            property_terms: smt.get_property_subterms(),
            reads_writes: smt.get_reads_and_writes(),
        }
    }
}

impl egg::CostFunction<TermLanguage> for ArrayPreferRead {
    type Cost = u32;

    fn cost<C>(&mut self, enode: &TermLanguage, mut costs: C) -> Self::Cost
    where
        C: FnMut(egg::Id) -> Self::Cost,
    {
        let op_cost = match enode {
            TermLanguage::ReadTyped(_) => 0,
            _ => 20,
        };

        enode.fold(op_cost, |sum, id| sum + costs(id))
    }
}

impl egg::CostFunction<ListLanguage> for ArrayPreferRead {
    type Cost = u32;

    fn cost<C>(&mut self, _enode: &ListLanguage, _costs: C) -> Self::Cost
    where
        C: FnMut(egg::Id) -> Self::Cost,
    {
        todo!()
    }
}

impl YardbirdCostFunction<TermLanguage> for ArrayPreferRead {
    fn get_string_terms(&self) -> Vec<String> {
        self.init_and_transition_system_terms
            .iter()
            .chain(self.property_terms.iter())
            .map(|sym| sym.as_str().to_string())
            .collect()
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
