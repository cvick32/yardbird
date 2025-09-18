use crate::{
    cost_functions::array::{ast_size::ArrayAstSize, symbol_cost::ArrayBestSymbolSubstitution},
    smt_problem::SMTProblem,
};

pub mod ast_size;
pub mod symbol_cost;

pub fn array_best_symbol_cost_factory(smt: &SMTProblem, depth: u32) -> ArrayBestSymbolSubstitution {
    ArrayBestSymbolSubstitution {
        current_bmc_depth: depth,
        init_and_transition_system_terms: smt.get_init_and_transition_subterms(),
        property_terms: smt.get_property_subterms(),
        reads_writes: smt.get_reads_and_writes(),
    }
}

pub fn array_ast_size_cost_factory(smt: &SMTProblem, depth: u32) -> ArrayAstSize {
    ArrayAstSize {
        current_bmc_depth: depth,
        init_and_transition_system_terms: smt.get_init_and_transition_subterms(),
        property_terms: smt.get_property_subterms(),
        reads_writes: smt.get_reads_and_writes(),
    }
}
