pub mod full_unroll;
pub mod no_unroll_on_loop;
use smt2parser::{
    concrete::Term,
    vmt::{bmc::BMCBuilder, quantified_instantiator::Instance},
};

use crate::{subterm_handler::SubtermHandler, training::IndexedInstantiationRecord};

#[derive(Clone, Debug)]
pub struct StoredInstantiation {
    pub inst: Instance,
    pub abstract_instantiation_id: Option<String>,
}

/// Backend-neutral assertion operations used by instantiation strategies.
pub trait InstantiationAssertionSink {
    fn register_quantified_variables(&mut self, term: &Term);
    fn assert_instantiation_batch(&mut self, terms: &[Term]);
    fn assert_tracked_instantiation(&mut self, label: &str, term: &Term);
}

/// Trait for controlling how quantifier instantiations are added and unrolled in BMC problems.
pub trait InstantiationStrategy: std::fmt::Debug + Send {
    /// Clone the strategy into a boxed trait object
    fn clone_box(&self) -> Box<dyn InstantiationStrategy>;
    /// Called when a new instance is generated (replaces current add_instantiation logic).
    ///
    /// This method should:
    /// - Check if the instance should be added (e.g., avoid duplicates)
    /// - Register any quantified variables with the solver backend
    /// - Add the instance to the solver with appropriate unrolling
    /// - Register instantiation terms with SubtermHandler
    #[allow(clippy::too_many_arguments)]
    fn on_generate(
        &mut self,
        inst: Instance,
        instantiations: &mut Vec<StoredInstantiation>,
        abstract_instantiation_id: Option<String>,
        depth: u16,
        bmc_builder: &mut BMCBuilder,
        assertion_sink: &mut dyn InstantiationAssertionSink,
        subterm_handler: &mut SubtermHandler,
        track_instantiations: bool,
        tracked_labels: &mut Vec<IndexedInstantiationRecord>,
        asserted_instantiations: &mut Vec<Term>,
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
        instantiations: &[StoredInstantiation],
        bmc_builder: &mut BMCBuilder,
        assertion_sink: &mut dyn InstantiationAssertionSink,
        track_instantiations: bool,
        tracked_labels: &mut Vec<IndexedInstantiationRecord>,
        asserted_instantiations: &mut Vec<Term>,
        num_quantifiers_instantiated: &mut u64,
    );
}
