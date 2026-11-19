use crate::policy::llm::{LlmOptions, LlmProvider};
use clap::Args;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;

/// Older Garden runs stored stdio options and native agent options separately.
pub(crate) fn migrate_saved_options(options: &mut serde_json::Value) -> anyhow::Result<()> {
    use serde_json::Value;

    let Some(legacy) = options.as_object_mut().and_then(|o| o.remove("advisor")) else {
        return Ok(());
    };
    let Value::Object(legacy) = legacy else {
        anyhow::bail!("expected an object for saved native agent options");
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
    #[arg(long, value_enum, default_value = "stall", requires = "agent")]
    pub agent_trigger: AgentTrigger,
    /// Unresolved-depth seconds before advice; resets after yield. Ignored in adaptive mode.
    #[arg(long, default_value_t = 5, requires = "agent")]
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
    /// Serve the typed refinement protocol over stdin/stdout (no LLM calls).
    #[arg(long, conflicts_with_all = ["repl", "json_output", "policy"])]
    pub agent_stdio: bool,
    /// First zero-based depth at which to pause on an abstract SAT model.
    #[arg(long, default_value_t = 0, requires = "agent_stdio")]
    pub agent_pause_depth: u16,
    /// Interaction control mode. Explicit tools alone or tools with bounded search.
    #[arg(long, default_value = "explicit", requires = "agent_stdio", value_parser = ["explicit", "assisted"])]
    pub agent_control: String,
    /// Fresh JSONL transcript for the active agent mode.
    #[arg(long)]
    pub agent_log: Option<PathBuf>,
    /// Maximum protocol commands in one session (including retries).
    #[arg(long, default_value_t = 64, requires = "agent_stdio")]
    pub agent_max_commands: usize,
    /// Maximum pending candidates across explicit proposals and search.
    #[arg(long, default_value_t = 64, requires = "agent_stdio")]
    pub agent_max_pending: usize,
    /// Maximum solver timeout per advance and prelude check, in milliseconds.
    #[arg(long, default_value_t = 5000, requires = "agent_stdio")]
    pub agent_solver_timeout_ms: u32,
    /// Maximum ordinary search operations per tool call.
    #[arg(long, default_value_t = 8, requires = "agent_stdio")]
    pub agent_search_operations: usize,
    /// Maximum action-expansion work per tool call.
    #[arg(long, default_value_t = 200, requires = "agent_stdio")]
    pub agent_expand_action_work: usize,
    /// Cumulative action-expansion budget for the session.
    #[arg(long, default_value_t = 2000, requires = "agent_stdio")]
    pub agent_expansion_work: usize,
}

impl Default for AgentOptions {
    fn default() -> Self {
        Self {
            mode: None,
            agent_config: None,
            agent_start_depth: 0,
            agent_trigger: AgentTrigger::Stall,
            agent_stall_secs: 5,
            agent_interval_ms: 1000,
            agent_max_calls: 0,
            agent_max_request_bytes: 2097152,
            agent_timeout_secs: 120,
            agent_trace_work: 128,
            agent_dry_run: false,
            agent_stdio: false,
            agent_pause_depth: 0,
            agent_control: "explicit".into(),
            agent_log: None,
            agent_max_commands: 64,
            agent_max_pending: 64,
            agent_solver_timeout_ms: 5000,
            agent_search_operations: 8,
            agent_expand_action_work: 200,
            agent_expansion_work: 2000,
        }
    }
}

impl AgentOptions {
    fn validate_stdio(&self, run: &crate::YardbirdOptions) -> anyhow::Result<()> {
        if !self.agent_stdio {
            return Ok(());
        }
        anyhow::ensure!(
            self.agent_max_commands > 0
                && self.agent_max_pending > 0
                && self.agent_solver_timeout_ms > 0
                && self.agent_search_operations > 0
                && self.agent_expand_action_work > 0
                && self.agent_expansion_work > 0,
            "agent work limits must be positive"
        );
        anyhow::ensure!(
            run.solver == crate::SolverBackend::Z3,
            "agent protocol requires Z3"
        );
        anyhow::ensure!(
            matches!(run.strategy, crate::Strategy::Abstract) && run.policy.is_none(),
            "agent protocol requires the abstract strategy without a named policy"
        );
        anyhow::ensure!(
            run.require_filename()?.ends_with(".vmt"),
            "agent protocol requires VMT"
        );
        anyhow::ensure!(
            run.theory.legacy_theory().is_none(),
            "agent protocol does not support list theory"
        );
        anyhow::ensure!(
            self.agent_pause_depth < run.depth,
            "agent pause depth must be less than --depth"
        );
        anyhow::ensure!(!run.repl && !run.json_output && !run.run_ic3ia && !run.interpolate && !run.eager && !run.guarded_read_updates && !run.preprocess_exact_read_after_write && !run.abstract_recurrent_products && !run.split_property_checks && !run.reuse_proved_properties && run.proved_property_instance_limit == 0 && run.solver_capture_dir.is_none(), "agent protocol does not support REPL, output JSON, proof extensions, eager/guarded refinements, alternate preprocessing, property reuse/splitting, or solver capture");
        anyhow::ensure!(
            self.agent_control.is_empty()
                || ["explicit", "assisted"].contains(&self.agent_control.as_str()),
            "unknown agent control mode"
        );
        Ok(())
    }
}

impl AgentOptions {
    pub fn validate(&self, run: &crate::YardbirdOptions) -> anyhow::Result<()> {
        self.validate_stdio(run)?;
        anyhow::ensure!(
            self.agent_log.is_none()
                || self.agent_stdio
                || self.mode.is_some()
                || run.one_shot.replay_instantiations.is_some(),
            "--agent-log requires --agent, --agent-stdio or --replay-instantiations"
        );
        if self.mode.is_none() {
            return Ok(());
        }
        anyhow::ensure!(
            !run.agent.agent_stdio,
            "--agent uses the native driver, not --agent-stdio"
        );
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
            None => include_str!("native/bedrock-config.json").into(),
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
