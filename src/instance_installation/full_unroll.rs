use super::{InstantiationContext, InstantiationStrategy};

/// Replays all stored instances whenever the BMC depth advances.
#[derive(Clone, Debug, Default)]
pub struct FullUnrollStrategy;

impl FullUnrollStrategy {
    pub fn new() -> Self {
        Self
    }
}

impl InstantiationStrategy for FullUnrollStrategy {
    fn clone_box(&self) -> Box<dyn InstantiationStrategy> {
        Box::new(self.clone())
    }

    fn on_loop(&mut self, depth: u16, context: &mut InstantiationContext<'_>) {
        context.install_existing_at_current_depth(depth);
    }
}
