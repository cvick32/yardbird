use dialoguer::{theme::SimpleTheme, MultiSelect};
use smt2parser::vmt::VMTModel;

use crate::strategies::{AbstractRefinementState, ProofStrategyExt};

pub struct Repl;

impl ProofStrategyExt<AbstractRefinementState> for Repl {
    fn finish(
        &mut self,
        _model: &mut VMTModel,
        state: &mut AbstractRefinementState,
    ) -> anyhow::Result<()> {
        if state.instantiations.is_empty() {
            return Ok(());
        }

        let selection = MultiSelect::with_theme(&SimpleTheme)
            .with_prompt("Pick instantiations")
            .items(&state.instantiations)
            .interact()
            .unwrap();

        // replace instantiations with instantiations from selection
        state.instantiations = selection
            .into_iter()
            .map(|i| state.instantiations[i].clone())
            .collect();

        Ok(())
    }
}
