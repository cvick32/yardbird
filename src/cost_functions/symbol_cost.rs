use egg::Language;
use smt2parser::vmt::VARIABLE_FRAME_DELIMITER;

use crate::array_axioms::ArrayLanguage;

/// Cost function describing how to extract terms from an eclass while we are
/// instantiating a rule violation with concrete terms.
#[derive(Clone)]
pub struct BestSymbolSubstitution {
    pub current_bmc_depth: u32,
    pub transition_system_terms: Vec<String>,
    pub property_terms: Vec<String>,
}

impl egg::CostFunction<ArrayLanguage> for BestSymbolSubstitution {
    type Cost = u32;

    fn cost<C>(&mut self, enode: &ArrayLanguage, mut costs: C) -> Self::Cost
    where
        C: FnMut(egg::Id) -> Self::Cost,
    {
        let op_cost = match enode {
            ArrayLanguage::Num(num) => {
                let num_string = num.to_string();
                let in_trans = self.transition_system_terms.contains(&num_string);
                let in_prop = self.property_terms.contains(&num_string);
                if in_trans {
                    // If the constant is just in the transition system, we assign a low cost.
                    1
                } else if in_prop {
                    // If the constant is just property term, we assign a lower cost.
                    0
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
            ArrayLanguage::Symbol(sym) => {
                let symbol_str = sym.as_str().to_string();
                let in_trans = self.transition_system_terms.contains(&symbol_str);
                let in_prop = self.property_terms.contains(&symbol_str);

                if in_trans && in_prop {
                    // Prefer terms that are in both the transition system and property
                    return 0;
                }

                if let Some((_name, frame_number)) =
                    sym.as_str().split_once(VARIABLE_FRAME_DELIMITER)
                {
                    // Prefer terms that are close to the property check.
                    self.current_bmc_depth - frame_number.parse::<u32>().unwrap()
                } else {
                    // TODO: extend language to uninterpreted sort constants to
                    // constants instead of symbols.
                    // Ex: Array-Int-Int!val!0 is currently a symbol when it should be a
                    // constant.
                    100
                }
            }
        };
        enode.fold(op_cost, |sum, id| sum + costs(id))
    }
}
