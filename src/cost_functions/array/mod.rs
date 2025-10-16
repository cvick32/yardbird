use egg::Symbol;
use rustc_hash::FxHashSet;

use crate::{
    cost_functions::array::{
        adaptive_cost::AdaptiveArrayCost, ast_size::ArrayAstSize,
        prefer_constants::ArrayPreferConstants, prefer_read::ArrayPreferRead,
        prefer_write::ArrayPreferWrite, split_cost::SplitArrayCost,
        symbol_cost::ArrayBestSymbolSubstitution,
    },
    smt_problem::SMTProblem,
};

pub mod adaptive_cost;
pub mod ast_size;
pub mod prefer_constants;
pub mod prefer_read;
pub mod prefer_write;
pub mod split_cost;
pub mod symbol_cost;

pub fn array_best_symbol_cost_factory(smt: &SMTProblem, depth: u32) -> ArrayBestSymbolSubstitution {
    let init_and_transition_system_terms: FxHashSet<Symbol> = smt
        .get_init_and_transition_subterms()
        .into_iter()
        .map(|s| s.into())
        .collect();

    let property_terms: FxHashSet<Symbol> = smt
        .get_property_subterms()
        .into_iter()
        .map(|s| s.into())
        .collect();

    ArrayBestSymbolSubstitution::new(
        depth,
        init_and_transition_system_terms,
        property_terms,
        smt.get_reads_and_writes(),
    )
}

pub fn array_ast_size_cost_factory(smt: &SMTProblem, depth: u32) -> ArrayAstSize {
    ArrayAstSize {
        current_bmc_depth: depth,
        init_and_transition_system_terms: smt.get_init_and_transition_subterms(),
        property_terms: smt.get_property_subterms(),
        reads_writes: smt.get_reads_and_writes(),
    }
}

pub fn adaptive_array_cost_factory(smt: &SMTProblem, depth: u32) -> AdaptiveArrayCost {
    AdaptiveArrayCost::new(
        depth,
        smt.get_init_and_transition_subterms(),
        smt.get_property_subterms(),
        smt.get_reads_and_writes(),
    )
}

pub fn split_array_cost_factory(smt: &SMTProblem, depth: u32) -> SplitArrayCost {
    SplitArrayCost::new(
        depth,
        smt.get_init_and_transition_subterms(),
        smt.get_property_subterms(),
        smt.get_reads_and_writes(),
    )
}

pub fn array_prefer_read_factory(smt: &SMTProblem, depth: u32) -> ArrayPreferRead {
    ArrayPreferRead {
        current_bmc_depth: depth,
        init_and_transition_system_terms: smt.get_init_and_transition_subterms(),
        property_terms: smt.get_property_subterms(),
        reads_writes: smt.get_reads_and_writes(),
    }
}

pub fn array_prefer_write_factory(smt: &SMTProblem, depth: u32) -> ArrayPreferWrite {
    ArrayPreferWrite {
        current_bmc_depth: depth,
        init_and_transition_system_terms: smt.get_init_and_transition_subterms(),
        property_terms: smt.get_property_subterms(),
        reads_writes: smt.get_reads_and_writes(),
    }
}

pub fn array_prefer_constants(smt: &SMTProblem, depth: u32) -> ArrayPreferConstants {
    ArrayPreferConstants {
        current_bmc_depth: depth,
        init_and_transition_system_terms: smt.get_init_and_transition_subterms(),
        property_terms: smt.get_property_subterms(),
        reads_writes: smt.get_reads_and_writes(),
    }
}
