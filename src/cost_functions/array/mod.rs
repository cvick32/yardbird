pub mod ast_size;
pub mod symbol_cost;

use egg::CostFunction;
use smt2parser::vmt::ReadsAndWrites;

use crate::cost_functions::array::{ast_size::AstSize, symbol_cost::BestSymbolSubstitution};
use crate::smt_problem::SMTProblem;
use crate::theories::array_axioms::ArrayLanguage;

/// A helper trait alias for cost functions over `ArrayLanguage`
pub trait YardbirdCostFunction: CostFunction<ArrayLanguage, Cost = u32> + Clone {
    fn get_string_terms(&self) -> Vec<String>;
    fn get_reads_and_writes(&self) -> ReadsAndWrites;
}

pub fn best_symbol_cost_factory(smt: &SMTProblem, depth: u32) -> BestSymbolSubstitution {
    BestSymbolSubstitution {
        current_bmc_depth: depth,
        init_and_transition_system_terms: smt.get_init_and_transition_subterms(),
        property_terms: smt.get_property_subterms(),
        reads_writes: smt.get_reads_and_writes(),
    }
}

pub fn ast_size_cost_factory(smt: &SMTProblem, depth: u32) -> AstSize {
    AstSize {
        current_bmc_depth: depth,
        init_and_transition_system_terms: smt.get_init_and_transition_subterms(),
        property_terms: smt.get_property_subterms(),
        reads_writes: smt.get_reads_and_writes(),
    }
}
