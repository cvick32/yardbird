pub mod full_unroll;
pub mod no_unroll_on_loop;
use smt2parser::{
    concrete::Term,
    vmt::{bmc::BMCBuilder, quantified_instantiator::Instance},
};

use crate::{subterm_handler::SubtermHandler, z3_var_context::Z3VarContext};

/// Trait for controlling how quantifier instantiations are added and unrolled in BMC problems.
pub trait InstantiationStrategy: std::fmt::Debug + Send {
    /// Clone the strategy into a boxed trait object
    fn clone_box(&self) -> Box<dyn InstantiationStrategy>;
    /// Called when a new instance is generated (replaces current add_instantiation logic).
    ///
    /// This method should:
    /// - Check if the instance should be added (e.g., avoid duplicates)
    /// - Register any quantified variables with Z3VarContext
    /// - Add the instance to the solver with appropriate unrolling
    /// - Register instantiation terms with SubtermHandler
    #[allow(clippy::too_many_arguments)]
    fn on_generate(
        &mut self,
        inst: Instance,
        instantiations: &mut Vec<Instance>,
        depth: u16,
        bmc_builder: &mut BMCBuilder,
        z3_var_context: &mut Z3VarContext,
        solver: &mut z3::Solver,
        subterm_handler: &mut SubtermHandler,
        track_instantiations: bool,
        tracked_labels: &mut Vec<(String, Term)>,
        num_quantifiers_instantiated: &mut u64,
    );

    /// Called at each BMC depth unrolling (in unroll() method).
    ///
    /// This method can process existing instantiations at the new depth,
    /// but does not add new instances to the list.
    #[allow(clippy::too_many_arguments)]
    fn on_loop(
        &mut self,
        depth: u16,
        instantiations: &[Instance],
        bmc_builder: &mut BMCBuilder,
        z3_var_context: &mut Z3VarContext,
        solver: &mut z3::Solver,
        track_instantiations: bool,
        tracked_labels: &mut Vec<(String, Term)>,
        num_quantifiers_instantiated: &mut u64,
    );
}
