use crate::policy::llm::{LlmOptions, LlmProvider};
use clap::Args;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;

/// Older Garden runs stored agent settings under a separate advisor key.
pub(crate) fn migrate_saved_options(options: &mut serde_json::Value) -> anyhow::Result<()> {
    use serde_json::Value;

    anyhow::ensure!(
        options.pointer("/agent/agent_stdio") != Some(&Value::Bool(true)),
        "this run requested the removed --agent-stdio mode"
    );
    let Some(legacy) = options.as_object_mut().and_then(|o| o.remove("advisor")) else {
        return Ok(());
    };
    let Value::Object(legacy) = legacy else {
        anyhow::bail!("expected an object for saved advisor options");
    };
    if options.get("agent").is_none() {
        options["agent"] = Value::Object(Default::default());
    }
    let agent = options["agent"]
        .as_object_mut()
        .ok_or_else(|| anyhow::anyhow!("expected an object for saved agent options"))?;
    for (key, value) in legacy {
        let name = if key == "advisor" {
            "mode".to_owned()
        } else if let Some(suffix) = key.strip_prefix("advisor_") {
            format!("agent_{suffix}")
        } else {
            continue;
        };
        if value.is_null() {
            continue;
        }
        if let Some(existing) = agent.get(&name) {
            anyhow::ensure!(
                existing.is_null() || existing == &value,
                "conflicting saved values for agent.{name}"
            );
        }
        agent.insert(name, value);
    }
    Ok(())
}

#[derive(clap::ValueEnum, Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum AgentMode {
    None,
    Bedrock,
}

#[derive(clap::ValueEnum, Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum AgentTrigger {
    /// Start advice after a depth remains unresolved for the stall threshold.
    Stall,
    /// Ask the LLM whether to continue symbolic work or open an advice episode.
    Adaptive,
}

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
#[serde(default)]
pub struct AgentOptions {
    /// Attach a Bedrock agent, or use "none" to measure attachment overhead.
    #[arg(long = "agent", id = "agent", value_name = "MODE", value_enum)]
    pub mode: Option<AgentMode>,
    /// Override the bundled Bedrock provider JSON (llm_* configuration).
    #[arg(long, requires = "agent")]
    pub agent_config: Option<PathBuf>,
    /// First depth eligible for advice (ordinary verification never pauses).
    #[arg(long, default_value_t = 0, requires = "agent")]
    pub agent_start_depth: u16,
    /// First native SAT model number eligible for advice (for paired runs on a recorded model).
    #[arg(long, default_value_t = 0, requires = "agent")]
    pub agent_start_model: u64,
    #[arg(long, value_enum, default_value = "stall", requires = "agent")]
    pub agent_trigger: AgentTrigger,
    /// Unresolved-depth seconds before advice; resets after yield. Ignored in adaptive mode.
    #[arg(long, default_value_t = AgentOptions::default().agent_stall_secs, requires = "agent")]
    pub agent_stall_secs: u64,
    /// Minimum milliseconds between new snapshot episodes.
    #[arg(long, default_value_t = 1000, requires = "agent")]
    pub agent_interval_ms: u64,
    /// Total inference attempt limit; 0 means unlimited. No automatic retries.
    #[arg(long, default_value_t = 0, requires = "agent")]
    pub agent_max_calls: usize,
    /// Maximum bytes per request, including history; context is never silently truncated.
    #[arg(long, default_value_t = 2097152, requires = "agent")]
    pub agent_max_request_bytes: usize,
    /// Timeout for one provider request; completion never waits for an in-flight worker.
    #[arg(long, default_value_t = 120, requires = "agent")]
    pub agent_timeout_secs: u64,
    /// Read-only trace work when capturing an agent snapshot; 0 disables tracing.
    #[arg(long, default_value_t = 128, requires = "agent")]
    pub agent_trace_work: usize,
    /// Capture/log requests without any provider calls.
    #[arg(long, requires = "agent")]
    pub agent_dry_run: bool,
    /// Fresh JSONL transcript for the active agent mode.
    #[arg(long)]
    pub agent_log: Option<PathBuf>,
}

impl Default for AgentOptions {
    fn default() -> Self {
        Self {
            mode: None,
            agent_config: None,
            agent_start_depth: 0,
            agent_start_model: 0,
            agent_trigger: AgentTrigger::Stall,
            agent_stall_secs: 0,
            agent_interval_ms: 1000,
            agent_max_calls: 0,
            agent_max_request_bytes: 2097152,
            agent_timeout_secs: 120,
            agent_trace_work: 128,
            agent_dry_run: false,
            agent_log: None,
        }
    }
}

impl AgentOptions {
    pub fn validate(&self, run: &crate::YardbirdOptions) -> anyhow::Result<()> {
        anyhow::ensure!(
            self.agent_log.is_none()
                || self.mode.is_some()
                || run.one_shot.replay_instantiations.is_some(),
            "--agent-log requires --agent or --replay-instantiations"
        );
        if self.mode.is_none() {
            return Ok(());
        }
        anyhow::ensure!(
            run.filename.as_deref().is_some_and(|f| f.ends_with(".vmt"))
                && run.theory.legacy_theory().is_none()
                && matches!(run.strategy, crate::Strategy::Abstract)
                && run.solver == crate::SolverBackend::Z3,
            "--agent requires an abstract Z3 VMT strategy with arrays/quantifiers"
        );
        if let Some(path) = &self.agent_log {
            anyhow::ensure!(
                !path.exists(),
                "agent log already exists: {}",
                path.display()
            );
        }
        if self.mode == Some(AgentMode::Bedrock) {
            anyhow::ensure!(
                self.agent_start_depth < run.depth,
                "agent start depth must be less than --depth"
            );
            anyhow::ensure!(
                self.agent_timeout_secs > 0 && self.agent_max_request_bytes > 0,
                "agent timeout and request size must be positive"
            );
            self.provider()?;
            if !self.agent_dry_run {
                anyhow::ensure!(
                    std::env::var("BEDROCK_API_KEY").is_ok_and(|k| !k.trim().is_empty()),
                    "BEDROCK_API_KEY is not configured; use --agent-dry-run for offline capture"
                );
            }
        }
        Ok(())
    }

    pub(crate) fn provider(&self) -> anyhow::Result<LlmOptions> {
        let text = match &self.agent_config {
            Some(path) => std::fs::read_to_string(path)?,
            None => include_str!("bedrock-config.json").into(),
        };
        let value: serde_json::Value = serde_json::from_str(&text)?;
        let mut provider: LlmOptions =
            serde_json::from_value(value.get("llm").unwrap_or(&value).clone())?;
        anyhow::ensure!(
            provider.llm_provider == LlmProvider::Bedrock,
            "agent config must use llm_provider=bedrock"
        );
        anyhow::ensure!(
            provider
                .llm_model
                .as_ref()
                .is_some_and(|m| !m.trim().is_empty())
                && provider.llm_max_output_tokens > 0,
            "agent config requires a model and positive output-token limit"
        );
        provider.llm_timeout_secs = self.agent_timeout_secs;
        Ok(provider)
    }

    pub(crate) fn resolve_log(
        &mut self,
        input: &str,
        root: &std::path::Path,
    ) -> anyhow::Result<()> {
        if self.mode != Some(AgentMode::Bedrock) || self.agent_log.is_some() {
            return Ok(());
        }
        std::fs::create_dir_all(root)?;
        let stem = std::path::Path::new(input)
            .file_stem()
            .unwrap_or_default()
            .to_string_lossy();
        let stem: String = stem
            .chars()
            .take(80)
            .map(|c| {
                if c.is_ascii_alphanumeric() || c == '-' {
                    c
                } else {
                    '_'
                }
            })
            .collect();
        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)?
            .as_secs();
        let directory = tempfile::Builder::new()
            .prefix(&format!("{stem}-{timestamp}-"))
            .tempdir_in(root)?
            .keep();
        self.agent_log = Some(directory.join("agent.jsonl"));
        Ok(())
    }
}
