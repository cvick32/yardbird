use egg::Language;
use smt2parser::vmt::{ReadsAndWrites, VARIABLE_FRAME_DELIMITER};

use crate::{
    cost_functions::YardbirdCostFunction,
    theories::{array::array_axioms::ArrayLanguage, list::list_axioms::ListLanguage},
};

/// Cost function describing how to extract terms from an eclass while we are
/// instantiating a rule violation with concrete terms.
#[derive(Clone, Debug)]
pub struct ArrayBestSymbolSubstitution {
    pub current_bmc_depth: u32,
    pub init_and_transition_system_terms: Vec<String>,
    pub property_terms: Vec<String>,
    pub reads_writes: ReadsAndWrites,
}

impl egg::CostFunction<ArrayLanguage> for ArrayBestSymbolSubstitution {
    type Cost = u32;

    fn cost<C>(&mut self, enode: &ArrayLanguage, mut costs: C) -> Self::Cost
    where
        C: FnMut(egg::Id) -> Self::Cost,
    {
        let op_cost = match enode {
            ArrayLanguage::Num(num) => {
                let num_string = num.to_string();
                let in_trans = self.init_and_transition_system_terms.contains(&num_string);
                let in_prop = self.property_terms.contains(&num_string);
                if in_trans {
                    // If the constant is just in the transition system, we assign a low cost.
                    4
                } else if in_prop {
                    // If the constant is just property term, we assign a lower cost.
                    3
                } else {
                    // Otherwise, 100.
                    100
                }
            }
            ArrayLanguage::ConstArr(_) => 0,
            // NOTE: try changing the value of Write from 0 to 10 for
            // `array_init_var.vmt`. Notice that when we allow Write terms
            // to be used in axiom instantiations we end up with a chain of
            // rewrites that use `Write`. When we change it to 10, we automatically
            // rule out these very specific chains of Writes and are able to
            // generate a single instance that generalizes immediately.
            ArrayLanguage::Write(_) => 1,
            ArrayLanguage::Read(_) => 1,
            ArrayLanguage::And(_) => 1,
            ArrayLanguage::Not(_) => 1,
            ArrayLanguage::Or(_) => 1,
            ArrayLanguage::Implies(_) => 1,
            ArrayLanguage::Eq(_) => 1,
            ArrayLanguage::Geq(_) => 1,
            ArrayLanguage::Gt(_) => 1,
            ArrayLanguage::Leq(_) => 1,
            ArrayLanguage::Lt(_) => 1,
            ArrayLanguage::Plus(_) => 1,
            ArrayLanguage::Negate(_) => 1,
            ArrayLanguage::Times(_) => 1,
            ArrayLanguage::Mod(_) => 1,
            ArrayLanguage::Div(_) => 1,
            ArrayLanguage::Symbol(sym) => {
                let symbol_str = sym.as_str().to_string();
                let in_trans = self.init_and_transition_system_terms.contains(&symbol_str);
                let in_prop = self.property_terms.contains(&symbol_str);

                if let Some((name, frame_number)) =
                    sym.as_str().split_once(VARIABLE_FRAME_DELIMITER)
                {
                    if name == "pc" {
                        // Never instantiate with the program counter.
                        return 10000;
                    } else if in_prop {
                        return 0;
                    } else if in_trans {
                        return 3;
                    }
                    // Prefer terms that are close to the property check.
                    match frame_number.parse::<u32>() {
                        Ok(n) => self.current_bmc_depth - n,
                        Err(_) => panic!("Couldn't parse `{frame_number}`"),
                    }
                } else {
                    // TODO: extend language to uninterpreted sort constants to
                    // constants instead of symbols.
                    // Ex: Array-Int-Int!val!0 is currently a symbol when it should be a
                    // constant.
                    10000
                }
            }
        };
        enode.fold(op_cost, |sum, id| sum + costs(id))
    }
}

impl egg::CostFunction<ListLanguage> for ArrayBestSymbolSubstitution {
    type Cost = u32;

    fn cost<C>(&mut self, _enode: &ListLanguage, _costs: C) -> Self::Cost
    where
        C: FnMut(egg::Id) -> Self::Cost,
    {
        todo!()
    }
}

impl YardbirdCostFunction<ArrayLanguage> for ArrayBestSymbolSubstitution {
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
