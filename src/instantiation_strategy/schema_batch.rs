use std::collections::HashSet;

use crate::{
    instantiation_provenance::{InstantiationInstallResult, InstantiationRequest},
    SolverBackend,
};

use super::{InstantiationContext, InstantiationStrategy};

/// Retains abstract schemas and installs only placements violated by a SAT model.
///
/// Model-true placements are reconsidered after later checks. Placements that
/// have been asserted, or are already covered by an equivalent assertion, are
/// never evaluated again.
#[derive(Clone, Debug, Default)]
pub struct SchemaBatchStrategy {
    covered_placements: HashSet<(String, u16)>,
    last_scanned_check: Option<u64>,
}

impl SchemaBatchStrategy {
    pub fn new() -> Self {
        Self::default()
    }
}

impl InstantiationStrategy for SchemaBatchStrategy {
    fn clone_box(&self) -> Box<dyn InstantiationStrategy> {
        Box::new(self.clone())
    }

    fn on_generate(
        &mut self,
        request: InstantiationRequest,
        context: &mut InstantiationContext<'_>,
    ) -> InstantiationInstallResult {
        // CVC5 does not retain a detached model after the property scope is
        // popped. Preserve the established eager behavior on that backend.
        if context.solver_backend() != SolverBackend::Z3 {
            return context.install_new(request);
        }

        // Revisit retained schemas once for each captured model. A refinement
        // batch can generate several new schemas, but they all see the same
        // model and should not repeatedly rescan its true placements.
        let check_epoch = context.solver_check_epoch();
        if self.last_scanned_check != Some(check_epoch) {
            context
                .install_model_violated_schemas(&mut self.covered_placements)
                .expect("captured Z3 model should evaluate retained schema placements");
            self.last_scanned_check = Some(check_epoch);
        }

        let Some(stored) = context.store_new(request) else {
            return InstantiationInstallResult::default();
        };
        let mut result = context
            .install_model_violated_schema(stored, &mut self.covered_placements)
            .expect("captured Z3 model should evaluate the new schema placements");
        result.abstract_instance_added = true;
        result
    }

    fn on_loop(&mut self, depth: u16, context: &mut InstantiationContext<'_>) {
        if context.solver_backend() != SolverBackend::Z3 {
            context.install_existing_at_current_depth(depth);
        }
    }
}
