use egg::Symbol;
use rustc_hash::FxHashSet;
use smt2parser::vmt::ReadsAndWrites;

use crate::{
    cost_functions::{
        array::{ArrayBMCCost, ArrayCostContext, ArrayCostFactory},
        YardbirdCostFunction,
    },
    theories::array::array_axioms::ArrayLanguage,
};

/// BMC scoring with free Boolean literals for protocol instantiations.
///
/// Prefer `true` and `false` over incidental rule guards that share their model
/// value. Other symbols have a minimum cost of one so property and current-frame
/// variables cannot tie with the literals. Otherwise scoring follows BMC.
#[derive(Clone, Debug)]
pub struct ProtocolBmcCost {
    base: ArrayBMCCost,
}

impl ProtocolBmcCost {
    pub fn new(
        current_bmc_depth: u32,
        init_and_transition_system_terms: FxHashSet<Symbol>,
        property_terms: FxHashSet<Symbol>,
        reads_writes: ReadsAndWrites,
    ) -> Self {
        Self {
            base: ArrayBMCCost::new(
                current_bmc_depth,
                init_and_transition_system_terms,
                property_terms,
                reads_writes,
            ),
        }
    }
}

impl ArrayCostFactory for ProtocolBmcCost {
    type Config = ();

    fn from_context(smt: &ArrayCostContext, depth: u32, config: &Self::Config) -> Self {
        Self {
            base: ArrayBMCCost::from_context(smt, depth, config),
        }
    }
}

impl egg::CostFunction<ArrayLanguage> for ProtocolBmcCost {
    type Cost = u32;

    fn cost<C>(&mut self, enode: &ArrayLanguage, costs: C) -> Self::Cost
    where
        C: FnMut(egg::Id) -> Self::Cost,
    {
        match enode {
            ArrayLanguage::Symbol(sym) if matches!(sym.as_str(), "true" | "false") => 0,
            ArrayLanguage::Symbol(_) => self.base.cost(enode, costs).max(1),
            _ => self.base.cost(enode, costs),
        }
    }
}

impl YardbirdCostFunction<ArrayLanguage> for ProtocolBmcCost {
    fn get_string_terms(&self) -> Vec<String> {
        self.base.get_string_terms()
    }

    fn get_transition_terms(&self) -> Vec<String> {
        self.base.get_transition_terms()
    }

    fn get_property_terms(&self) -> Vec<String> {
        self.base.get_property_terms()
    }

    fn get_reads_and_writes(&self) -> ReadsAndWrites {
        self.base.get_reads_and_writes()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use egg::{CostFunction, EGraph, Extractor, RecExpr};

    fn protocol_cost() -> ProtocolBmcCost {
        ProtocolBmcCost::new(
            3,
            ["grant_exclusive_rule@0".into(), "2".into()]
                .into_iter()
                .collect(),
            ["property@3".into(), "1".into()].into_iter().collect(),
            ReadsAndWrites::default(),
        )
    }

    #[test]
    fn boolean_literals_are_cheaper_than_bmc_and_rule_guards() {
        let mut cost = protocol_cost();
        for literal in ["true", "false"] {
            let expr: RecExpr<ArrayLanguage> = literal.parse().unwrap();
            assert_eq!(cost.cost_rec(&expr), 0);
            assert!(cost.cost_rec(&expr) < cost.base.cost_rec(&expr));
            let guard = "grant_exclusive_rule@0".parse().unwrap();
            assert!(cost.cost_rec(&expr) < cost.cost_rec(&guard));
        }
    }

    #[test]
    fn extraction_prefers_literal_values_in_boolean_arrays() {
        for literal in ["true", "false"] {
            let mut egraph = EGraph::<ArrayLanguage, ()>::default();
            let guard = egraph.add_expr(&"grant_exclusive_rule@3".parse().unwrap());
            let value = egraph.add_expr(&literal.parse().unwrap());
            egraph.union(guard, value);
            for template in [
                "(ConstArr Int Bool VALUE)",
                "(Write Int Bool a@0 i@0 VALUE)",
            ] {
                let original = template.replace("VALUE", "grant_exclusive_rule@3");
                let root = egraph.add_expr(&original.parse().unwrap());
                egraph.rebuild();
                let (_, best) = Extractor::new(&egraph, protocol_cost()).find_best(root);
                assert_eq!(best.to_string(), template.replace("VALUE", literal));
            }
        }
    }

    #[test]
    fn terms_without_zero_cost_symbols_keep_bmc_scoring() {
        let mut cost = protocol_cost();
        for term in [
            "1",
            "2",
            "42",
            "pc@0",
            "grant_exclusive_rule@0",
            "other@0",
            "true@0",
            "false_flag@0",
            "Array_Int_Int!val!0",
            "(+ i@0 1)",
            "(Read Int Int (Write Int Int a@0 i@0 2) j@1)",
        ] {
            let expr: RecExpr<ArrayLanguage> = term.parse().unwrap();
            assert_eq!(cost.cost_rec(&expr), cost.base.cost_rec(&expr), "{term}");
        }
    }

    #[test]
    fn boolean_literals_beat_property_and_current_frame_symbols() {
        let mut cost = protocol_cost();
        for term in ["property@3", "grant_exclusive_rule@3"] {
            let expr: RecExpr<ArrayLanguage> = term.parse().unwrap();
            assert_eq!(cost.base.cost_rec(&expr), 0);
            assert_eq!(cost.cost_rec(&expr), 1);
            for literal in ["true", "false"] {
                assert!(cost.cost_rec(&literal.parse().unwrap()) < cost.cost_rec(&expr));
            }
        }
    }
}
