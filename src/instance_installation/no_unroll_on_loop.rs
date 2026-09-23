use super::{InstantiationContext, InstantiationStrategy};

/// Disables automatic replay of refinement instances; fixed eager seeds still replay.
#[derive(Clone, Debug, Default)]
pub struct NoUnrollOnLoop;

impl NoUnrollOnLoop {
    pub fn new() -> Self {
        Self
    }
}

impl InstantiationStrategy for NoUnrollOnLoop {
    fn clone_box(&self) -> Box<dyn InstantiationStrategy> {
        Box::new(self.clone())
    }

    fn on_loop(&mut self, depth: u16, context: &mut InstantiationContext<'_>) {
        context.install_existing_at_current_depth(depth, false);
    }
}
