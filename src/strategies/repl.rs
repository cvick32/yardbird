use dialoguer::{theme::SimpleTheme, MultiSelect};
use smt2parser::vmt::VMTModel;

use crate::strategies::{ArrayRefinementState, ListRefinementState, ProofStrategyExt};

pub struct Repl;

impl ProofStrategyExt<ArrayRefinementState> for Repl {
    fn finish(
        &mut self,
        _model: &mut VMTModel,
        state: &mut ArrayRefinementState,
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

impl ProofStrategyExt<ListRefinementState> for Repl {
    fn finish(
        &mut self,
        _model: &mut VMTModel,
        state: &mut ListRefinementState,
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
