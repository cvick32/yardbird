use super::{InstantiationContext, InstantiationStrategy};

/// Installs new instances at existing frames without replaying them later.
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

    fn on_loop(&mut self, _depth: u16, _context: &mut InstantiationContext<'_>) {}
}
