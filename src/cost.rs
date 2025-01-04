use egg::Language;
use smt2parser::vmt::VARIABLE_FRAME_DELIMITER;

use crate::array_axioms::ArrayLanguage;

/// Cost function describing how to extract terms from an eclass while we are
/// instantiating a rule violation with concrete terms.
#[derive(Clone)]
pub struct BestVariableSubstitution {
    pub current_frame_number: u32,
    pub property_terms: Vec<String>,
}

impl egg::CostFunction<ArrayLanguage> for BestVariableSubstitution {
    type Cost = u32;

    fn cost<C>(&mut self, enode: &ArrayLanguage, mut costs: C) -> Self::Cost
    where
        C: FnMut(egg::Id) -> Self::Cost,
    {
        // TODO: fiddle with the cost function to get what we want.
        //       right now all I am doing is preferring everything else
        //       over Nums
        let op_cost = match enode {
            // Scale cost of term w.r.t size of constant. This will only work when we want
            // small values like adding one or something.
            ArrayLanguage::Num(_) => 100, //u32::try_from(*num).ok().unwrap(),
            ArrayLanguage::ConstArr(_) => 0,
            // NOTE: try changing the value of Write from 0 to 10 for
            // `array_init_var.vmt`. Notice that when we allow Write terms
            // to be used in axiom instantiations we end up with a chain of
            // rewrites that use `Write`. When we change it to 10, we automatically
            // rule out these very specific chains of Writes and are able to
            // generate a single instance that generalizes immediately.
            ArrayLanguage::Write(_) => 100,
            ArrayLanguage::Read(_) => 100,
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
                let symbol_str = sym.as_str();
                if self.property_terms.contains(&symbol_str.to_string()) {
                    return 0;
                }
                if let Some((_name, frame_number)) =
                    sym.as_str().split_once(VARIABLE_FRAME_DELIMITER)
                {
                    self.current_frame_number - frame_number.parse::<u32>().unwrap()
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
