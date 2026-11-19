use serde::{Deserialize, Serialize};
use std::path::PathBuf;

#[derive(clap::ValueEnum, Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BatchPlacement {
    Schema,
    Exact,
}

#[derive(clap::Args, Clone, Debug, Serialize, Deserialize)]
#[serde(default)]
pub struct OneShotOptions {
    /// Ask Bedrock for batches, retrying with solver feedback until all bounds close or time expires.
    #[arg(long, requires = "agent", conflicts_with_all = ["agent_stdio", "replay_instantiations", "export_instantiations"])]
    pub one_shot: bool,
    /// Validate and replay the exact ground instances recorded by a native run; no LLM.
    #[arg(long, conflicts_with_all = ["agent", "agent_stdio", "export_instantiations"])]
    pub replay_instantiations: Option<PathBuf>,
    /// Record the native run's ground instances in a fresh replay artifact.
    #[arg(long, conflicts_with_all = ["agent", "agent_stdio"])]
    pub export_instantiations: Option<PathBuf>,
    /// Output-token budget per batch response; there is no proposal-count cap.
    #[arg(long, default_value_t = 32768, requires = "one_shot")]
    pub one_shot_output_tokens: u32,
    /// Replace the bundled one-shot instructions with this UTF-8 prompt; exact text is logged.
    #[arg(long, requires = "one_shot")]
    pub one_shot_prompt: Option<PathBuf>,
    /// Frame placement: schema reuses native temporal normalization/replay; exact keeps supplied frames.
    #[arg(long, value_enum)]
    pub one_shot_placement: Option<BatchPlacement>,
}

impl Default for OneShotOptions {
    fn default() -> Self {
        Self {
            one_shot: false,
            replay_instantiations: None,
            export_instantiations: None,
            one_shot_output_tokens: 32768,
            one_shot_prompt: None,
            one_shot_placement: None,
        }
    }
}

impl OneShotOptions {
    pub fn placement(&self) -> BatchPlacement {
        self.one_shot_placement.unwrap_or(if self.one_shot {
            BatchPlacement::Schema
        } else {
            BatchPlacement::Exact
        })
    }

    pub fn active(&self) -> bool {
        self.one_shot || self.replay_instantiations.is_some()
    }

    pub fn validate(&self, run: &crate::YardbirdOptions) -> anyhow::Result<()> {
        anyhow::ensure!(
            self.one_shot_placement.is_none() || self.active(),
            "--one-shot-placement requires --one-shot or --replay-instantiations"
        );
        if !self.active() && self.export_instantiations.is_none() {
            return Ok(());
        }
        anyhow::ensure!(
            run.depth > 0
                && run.require_filename()?.ends_with(".vmt")
                && run.theory.legacy_theory().is_none()
                && run.solver == crate::SolverBackend::Z3
                && matches!(run.strategy, crate::Strategy::Abstract),
            "one-shot/replay/export requires abstract Z3 VMT verification"
        );
        anyhow::ensure!(
            !run.agent.agent_stdio,
            "one-shot/replay/export cannot use --agent-stdio"
        );
        anyhow::ensure!(
            !self.one_shot
                || (run.agent.mode == Some(crate::agent_interaction::AgentMode::Bedrock)
                    && self.replay_instantiations.is_none()
                    && self.export_instantiations.is_none()),
            "--one-shot requires --agent bedrock and cannot replay/export a native run"
        );
        anyhow::ensure!(
            (self.replay_instantiations.is_none() && self.export_instantiations.is_none())
                || run.agent.mode.is_none(),
            "native replay/export cannot enable an agent"
        );
        anyhow::ensure!(
            self.replay_instantiations.is_none() || self.export_instantiations.is_none(),
            "replay and export are separate runs"
        );
        anyhow::ensure!(!self.active() || (!run.repl && !run.interpolate && !run.run_ic3ia && !run.eager && !run.split_property_checks && !run.reuse_proved_properties),
            "one-shot/replay does not use REPL, interpolation, IC3IA, eager discovery, property splitting or proved-property reuse");
        anyhow::ensure!(
            self.one_shot_output_tokens > 0,
            "one-shot output-token budget must be positive"
        );
        anyhow::ensure!(!self.one_shot || (run.agent.agent_start_depth == 0
            && run.agent.agent_trigger == crate::agent_interaction::AgentTrigger::Stall),
            "one-shot covers the entire target and cannot use a start-depth prelude or adaptive assessments");
        if let Some(path) = &self.export_instantiations {
            anyhow::ensure!(!path.exists(), "export already exists: {}", path.display());
        }
        Ok(())
    }
}
