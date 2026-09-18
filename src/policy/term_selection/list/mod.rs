pub mod ast_size;

use crate::policy::term_selection::list::ast_size::ListAstSize;
use crate::problem_context::ProblemContext;

pub fn list_ast_size_cost_factory(smt: &dyn ProblemContext, depth: u32) -> ListAstSize {
    ListAstSize {
        current_bmc_depth: depth,
        init_and_transition_system_terms: smt.get_init_and_transition_subterms(),
        property_terms: smt.get_property_subterms(),
        reads_writes: smt.get_reads_and_writes(),
    }
}
