use std::path::PathBuf;

use crate::{policy::NamedPolicy, SolverBackend, Theory, TheorySelection, YardbirdOptions};
use serde::{Deserialize, Serialize};

#[derive(clap::ValueEnum, Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum LlmProvider {
    #[default]
    Openai,
    Anthropic,
}

impl LlmProvider {
    pub(super) fn key_env(self) -> &'static str {
        match self {
            Self::Openai => "OPENAI_API_KEY",
            Self::Anthropic => "ANTHROPIC_API_KEY",
        }
    }

    pub(super) fn endpoint(self) -> &'static str {
        match self {
            Self::Openai => "https://api.openai.com/v1/responses",
            Self::Anthropic => "https://api.anthropic.com/v1/messages",
        }
    }
}

#[derive(clap::Args, Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(default)]
pub struct LlmOptions {
    #[command(flatten)]
    pub pricing: super::cost::LlmPricing,
    /// Explicit cache boundaries on reusable context; false uses provider defaults.
    #[arg(long, default_value_t = true, action = clap::ArgAction::Set)]
    pub llm_explicit_cache: bool,
    /// Provider for joint axiom-and-binding inference.
    #[arg(long, value_enum, default_value_t = LlmProvider::Openai)]
    pub llm_provider: LlmProvider,
    /// Explicit provider model ID (required with --policy llm-one-shot).
    #[arg(long)]
    pub llm_model: Option<String>,
    /// New JSONL file containing requests, responses, usage, and validation outcomes.
    #[arg(long)]
    pub llm_log: Option<PathBuf>,
    /// Log complete requests and use ordinary refinement without network calls.
    #[arg(long)]
    pub llm_dry_run: bool,
    /// Complete-proposal attempts per countermodel, including feedback retries.
    #[arg(long, default_value_t = 1)]
    pub llm_attempts: usize,
    /// Per-request deadline; the driver wall timeout remains cooperative.
    #[arg(long, default_value_t = 120)]
    pub llm_timeout_secs: u64,
    /// Skip oversized requests without truncating the source, model, or catalogue.
    #[arg(long, default_value_t = 2_097_152)]
    pub llm_max_request_bytes: usize,
    /// Provider output-token limit, including reasoning/thinking tokens.
    #[arg(long, default_value_t = 4096)]
    pub llm_max_output_tokens: u32,
    /// Optional provider effort value. Support depends on the chosen model.
    #[arg(long)]
    pub llm_reasoning_effort: Option<String>,
    /// Enable adaptive thinking on an Anthropic model that supports it.
    #[arg(long)]
    pub llm_adaptive_thinking: bool,
}

impl Default for LlmOptions {
    fn default() -> Self {
        Self {
            pricing: Default::default(),
            llm_explicit_cache: true,
            llm_provider: LlmProvider::Openai,
            llm_model: None,
            llm_log: None,
            llm_dry_run: false,
            llm_attempts: 1,
            llm_timeout_secs: 120,
            llm_max_request_bytes: 2_097_152,
            llm_max_output_tokens: 4096,
            llm_reasoning_effort: None,
            llm_adaptive_thinking: false,
        }
    }
}

impl LlmOptions {
    pub fn validate(&self, run: &YardbirdOptions) -> anyhow::Result<()> {
        if run.policy != Some(NamedPolicy::LlmOneShot) {
            anyhow::ensure!(
                self == &Self::default(),
                "--llm-* options require --policy llm-one-shot"
            );
            return Ok(());
        }
        anyhow::ensure!(
            run.filename.as_deref().is_some_and(|f| f.ends_with(".vmt")),
            "LLM policy requires a VMT input"
        );
        anyhow::ensure!(
            run.solver == SolverBackend::Z3
                && (run.theory == TheorySelection::Auto
                    || run.theory == TheorySelection::Explicit(vec![Theory::Array])),
            "LLM policy requires Z3 and --theory auto or array"
        );
        anyhow::ensure!(!run.eager && run.countermodel_trace_work == 0 &&
            run.synthesis_trigger == crate::SynthesisTrigger::Off && !run.prefer_axioms,
            "LLM policy does not support eager seeding, countermodel tracing, auxiliary synthesis, or prefer-axioms");
        anyhow::ensure!(
            self.llm_model
                .as_ref()
                .is_some_and(|m| !m.trim().is_empty()),
            "LLM policy requires --llm-model <MODEL_ID>"
        );
        anyhow::ensure!(
            self.llm_attempts > 0
                && self.llm_timeout_secs > 0
                && self.llm_max_request_bytes > 0
                && self.llm_max_output_tokens > 0,
            "LLM limits must be positive"
        );
        anyhow::ensure!(
            self.llm_reasoning_effort
                .as_ref()
                .is_none_or(|v| !v.trim().is_empty()),
            "LLM reasoning effort must not be empty"
        );
        anyhow::ensure!(
            !self.llm_adaptive_thinking || self.llm_provider == LlmProvider::Anthropic,
            "--llm-adaptive-thinking requires --llm-provider anthropic"
        );
        self.pricing.validate()?;
        let log = self
            .llm_log
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("LLM policy requires --llm-log <NEW_JSONL_FILE>"))?;
        anyhow::ensure!(
            !log.exists(),
            "LLM log already exists: {}; choose a new path",
            log.display()
        );
        if !self.llm_dry_run {
            let key = self.llm_provider.key_env();
            anyhow::ensure!(
                std::env::var(key).is_ok_and(|v| !v.trim().is_empty()),
                "set {key}, or use --llm-dry-run to inspect requests without inference"
            );
        }
        Ok(())
    }
}
