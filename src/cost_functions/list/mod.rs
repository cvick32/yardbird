pub mod ast_size;

use crate::{cost_functions::list::ast_size::ListAstSize, solver_interface::SolverInterface};

pub fn list_ast_size_cost_factory(smt: &dyn SolverInterface, depth: u32) -> ListAstSize {
    ListAstSize {
        current_bmc_depth: depth,
        init_and_transition_system_terms: smt.get_init_and_transition_subterms(),
        property_terms: smt.get_property_subterms(),
        reads_writes: smt.get_reads_and_writes(),
    }
}
