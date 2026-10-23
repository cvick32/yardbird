//! Full-model array-instantiation experiment. Provider I/O, retries and episode
//! logs live here; the abstract strategy only sees symbolic instance discovery.
//!
//! `one-shot` selects an axiom, then asks for all bindings together and searches
//! their independent distributions. `conditional-binding` selects an axiom,
//! then requests one binding per retained prefix in a fixed argument order.
//! Its beam is approximate: completed tuples are ranked within the retained
//! beam, not globally over all possible conditional paths. Both policies use
//! the complete model/vocabulary and the same trusted validator/installer.
//! With k slots and beam width B, conditional search makes at most
//! 2 + (k - 1) * B API calls per attempt, including axiom selection.
//! Both modes stop at the first verified violation by default. `--jev-batch`
//! checks the full retained candidate budget and sends every distinct verified
//! violation to shared installation, without additional inference requests.
mod client;
mod conditional;
mod feedback;
mod ranked_bindings;
mod snapshot;
#[cfg(test)]
mod tests;

use std::{
    fs::{File, OpenOptions},
    io::Write,
    path::PathBuf,
    time::Instant,
};

use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use smt2parser::concrete::Term;

use crate::{
    instance_installation::{
        assertion_tracker::canonical_instantiation_key, full_unroll::FullUnrollStrategy,
    },
    policy::{
        discovery::{DiscoveryContext, DiscoveryFirst, InstanceDiscovery},
        instance_selection::TermCostInstantiationRanker,
        term_selection::array::ArrayBMCCost,
        YardbirdPolicy,
    },
    rule_matching::candidate::SymbolicInstance,
    solver::{api::ModelEvaluation, PropertyCheckMode},
    strategies::Abstract,
    ArrayProofPlan, SolverBackend, Theory, TheorySelection, YardbirdOptions,
};
use client::{DecisionClient, JevClient};
use feedback::FailureSummary;
use snapshot::Snapshot;

#[derive(clap::ValueEnum, Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum JevPrompt {
    #[default]
    Baseline,
    PropertyDirected,
}

const PROPERTY_DIRECTED_PROMPT: &str = include_str!("prompts/property-directed.txt");

#[derive(clap::Args, Clone, Debug, Serialize, Deserialize)]
#[serde(default)]
pub struct DecisionModelOptions {
    /// Model name sent to TypeSafe (the resolved response name is logged).
    #[arg(long, default_value = "jev-latest")]
    pub jev_model: String,
    /// Task prompt; property-directed uses the original VMT to prefer relevant terms.
    #[arg(long, value_enum, default_value_t = JevPrompt::Baseline)]
    pub jev_prompt: JevPrompt,
    /// New JSONL file for full requests, responses, feedback and episode outcomes.
    #[arg(long)]
    pub jev_log: Option<PathBuf>,
    /// Write complete initial requests and use ordinary refinement without calling Jev.
    #[arg(long)]
    pub jev_dry_run: bool,
    /// Maximum axiom-and-binding attempts per countermodel.
    #[arg(long, default_value_t = 3)]
    pub jev_attempts: usize,
    /// Maximum completed tuples checked per attempt (one-shot: 1 uses the original choice).
    #[arg(long, default_value_t = 10)]
    pub jev_candidates: usize,
    /// Check the entire candidate budget and install every new verified violation.
    /// Without this flag, stop at the first violation.
    #[arg(long)]
    pub jev_batch: bool,
    /// Partial substitutions retained per step by conditional-binding.
    #[arg(long, default_value_t = 3)]
    pub jev_beam_width: usize,
    /// Per-request timeout. Solver wall timeouts remain cooperative.
    #[arg(long, default_value_t = 30)]
    pub jev_timeout_secs: u64,
    /// Skip and log oversized requests; never truncate or shortlist their contents.
    #[arg(long, default_value_t = 2_097_152)]
    pub jev_max_request_bytes: usize,
    /// USD per million input tokens, used only for logged cost estimates.
    #[arg(long, default_value_t = 0.042)]
    pub jev_input_usd_per_million: f64,
    /// USD per million output tokens, used only for logged cost estimates.
    #[arg(long, default_value_t = 0.0)]
    pub jev_output_usd_per_million: f64,
}

impl Default for DecisionModelOptions {
    fn default() -> Self {
        Self {
            jev_model: "jev-latest".into(),
            jev_prompt: JevPrompt::Baseline,
            jev_log: None,
            jev_dry_run: false,
            jev_attempts: 3,
            jev_candidates: 10,
            jev_batch: false,
            jev_beam_width: 3,
            jev_timeout_secs: 30,
            jev_max_request_bytes: 2_097_152,
            jev_input_usd_per_million: 0.042,
            jev_output_usd_per_million: 0.0,
        }
    }
}

impl DecisionModelOptions {
    pub fn validate(&self, run: &YardbirdOptions) -> anyhow::Result<()> {
        if !run
            .policy
            .is_some_and(super::NamedPolicy::uses_decision_model)
        {
            anyhow::ensure!(
                self.jev_log.is_none()
                    && !self.jev_dry_run
                    && self.jev_model == "jev-latest"
                    && self.jev_prompt == JevPrompt::Baseline
                    && self.jev_attempts == 3
                    && self.jev_candidates == 10
                    && !self.jev_batch
                    && self.jev_beam_width == 3
                    && self.jev_timeout_secs == 30
                    && self.jev_max_request_bytes == 2_097_152
                    && self.jev_input_usd_per_million == 0.042
                    && self.jev_output_usd_per_million == 0.0,
                "--jev-* options require --policy one-shot or conditional-binding"
            );
            return Ok(());
        }
        anyhow::ensure!(
            run.policy == Some(super::NamedPolicy::ConditionalBinding) || self.jev_beam_width == 3,
            "--jev-beam-width requires --policy conditional-binding"
        );
        anyhow::ensure!(
            run.filename.as_deref().is_some_and(|f| f.ends_with(".vmt")),
            "Jev policies require a VMT input"
        );
        anyhow::ensure!(
            run.solver == SolverBackend::Z3
                && run.theory.includes(Theory::Array)
                && run.theory.legacy_theory() != Some(Theory::List),
            "Jev policies require Z3 and array ownership"
        );
        anyhow::ensure!(
            matches!(run.theory, TheorySelection::Auto)
                || run.theory == TheorySelection::Explicit(vec![Theory::Array]),
            "Jev policies support --theory auto or --theory array only"
        );
        anyhow::ensure!(!run.eager && run.countermodel_trace_work == 0
            && run.synthesis_trigger == crate::SynthesisTrigger::Off && !run.prefer_axioms,
            "Jev experiments do not support eager seeding, countermodel tracing, auxiliary synthesis, or prefer-axioms");
        anyhow::ensure!(
            self.jev_attempts > 0
                && self.jev_candidates > 0
                && self.jev_beam_width > 0
                && self.jev_timeout_secs > 0
                && self.jev_max_request_bytes > 0,
            "Jev limits must be positive"
        );
        anyhow::ensure!(
            [
                self.jev_input_usd_per_million,
                self.jev_output_usd_per_million
            ]
            .iter()
            .all(|rate| rate.is_finite() && *rate >= 0.0),
            "Jev prices must be finite and nonnegative"
        );
        anyhow::ensure!(
            !self.jev_model.trim().is_empty(),
            "Jev model name must not be empty"
        );
        let log = self
            .jev_log
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("Jev policies require --jev-log <NEW_JSONL_FILE>"))?;
        anyhow::ensure!(
            !log.exists(),
            "Jev log already exists: {}; choose a new path",
            log.display()
        );
        if !self.jev_dry_run {
            anyhow::ensure!(
                std::env::var("JEV_API_KEY").is_ok_and(|v| !v.trim().is_empty()),
                "set JEV_API_KEY, or use --jev-dry-run to inspect requests without inference"
            );
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub(crate) enum BindingMode {
    #[serde(rename = "one-shot")]
    OneShot,
    #[serde(rename = "conditional-binding")]
    Conditional,
}

pub(crate) fn build_plan(run: &YardbirdOptions, mode: BindingMode) -> ArrayProofPlan {
    let options = run.decision_model.clone();
    let winners = if options.jev_batch {
        options.jev_candidates
    } else {
        1
    };
    let experiment = Experiment {
        mode,
        query_id: 0,
        client: Box::new(JevClient::new(options.jev_timeout_secs)),
        options,
        log: None,
        input: run.filename.clone(),
        problem_source: None,
    };
    let policy = YardbirdPolicy::<ArrayBMCCost>::new(())
        .with_instantiation_ranker(Box::new(TermCostInstantiationRanker))
        .with_effort(DiscoveryFirst::default().with_discovery_winners(winners))
        .with_discovery(experiment);
    ArrayProofPlan {
        solver: SolverBackend::Z3,
        instantiation_strategy: Box::new(FullUnrollStrategy::new()),
        strategy: Box::new(
            Abstract::new(run.depth, run.run_ic3ia, policy, true)
                .with_artifact_capture(run.build_array_artifact_capture())
                .with_theory_selection(TheorySelection::Explicit(vec![Theory::Array]))
                .with_property_check_mode(PropertyCheckMode::Assumptions),
        ),
        conditional_history: None,
    }
}

struct Experiment {
    mode: BindingMode,
    query_id: u64,
    options: DecisionModelOptions,
    client: Box<dyn DecisionClient>,
    log: Option<File>,
    input: Option<String>,
    problem_source: Option<String>,
}

impl Experiment {
    fn record(&mut self, context: &DiscoveryContext<'_>, mut record: Value) -> anyhow::Result<()> {
        if self.log.is_none() {
            let path = self
                .options
                .jev_log
                .as_ref()
                .ok_or_else(|| anyhow::anyhow!("missing episode log path"))?;
            self.log = Some(OpenOptions::new().write(true).create_new(true).open(path)?);
        }
        record["schema_version"] = json!(3);
        record["policy"] = json!(self.mode);
        record["query_id"] = json!(self.query_id);
        record["input"] = json!(self.input);
        record["depth"] = json!(context.depth);
        record["refinement_step"] = json!(context.refinement_step);
        record["model_version"] = json!(context.model_version);
        record["configuration"] = json!(self.options);
        let log = self.log.as_mut().unwrap();
        serde_json::to_writer(&mut *log, &record)?;
        writeln!(log)?;
        log.flush()?;
        Ok(())
    }

    fn query(
        &mut self,
        context: &DiscoveryContext<'_>,
        attempt: usize,
        stage: &str,
        request: &Value,
    ) -> anyhow::Result<Option<(Value, f64)>> {
        self.query_id += 1;
        let bytes = serde_json::to_vec(request)?.len();
        self.record(context, json!({"event":"request","attempt":attempt,"stage":stage,"request_bytes":bytes,"request":request}))?;
        let skip = if bytes > self.options.jev_max_request_bytes {
            Some("request_too_large")
        } else if self.options.jev_dry_run {
            Some("dry_run")
        } else {
            None
        };
        if let Some(outcome) = skip {
            self.record(context, json!({"event":"request_skipped","attempt":attempt,"stage":stage,"outcome":outcome}))?;
            self.finish(
                context,
                outcome,
                if stage != "quantifier_selection" {
                    attempt
                } else {
                    attempt - 1
                },
            )?;
            return Ok(None);
        }
        let start = Instant::now();
        match self.client.decide(request) {
            Ok(response) => Ok(Some((response, start.elapsed().as_secs_f64()))),
            Err(error) => {
                self.record(context, json!({"event":"transport_error","attempt":attempt,"stage":stage,"error":error.to_string(),"elapsed_secs":start.elapsed().as_secs_f64(),"cost":query_cost(&Value::Null, &self.options)}))?;
                self.finish(context, "transport_error", attempt)?;
                Ok(None)
            }
        }
    }

    fn finish(
        &mut self,
        context: &DiscoveryContext<'_>,
        outcome: &str,
        attempts: usize,
    ) -> anyhow::Result<()> {
        self.record(
            context,
            json!({"event":"episode_end","outcome":outcome,"attempts":attempts,
            "ordinary_fallback":outcome != "violated", "installation_status":"not_observed_by_discovery"}),
        )
    }
}

impl InstanceDiscovery for Experiment {
    fn discover(
        &mut self,
        context: &DiscoveryContext<'_>,
    ) -> anyhow::Result<Vec<SymbolicInstance>> {
        let mut snapshot = match Snapshot::capture(context) {
            Ok(snapshot) => snapshot,
            Err(error) => {
                self.record(
                    context,
                    json!({"event":"snapshot_error","error":error.to_string()}),
                )?;
                self.finish(context, "snapshot_error", 0)?;
                return Ok(vec![]);
            }
        };
        // Preserve the complete original problem, before abstraction/lowering.
        // Cache it so every model in this experiment sees the same source text.
        if self.problem_source.is_none() {
            let path = self
                .input
                .as_ref()
                .ok_or_else(|| anyhow::anyhow!("missing original VMT path"))?;
            self.problem_source = Some(std::fs::read_to_string(path)?);
        }
        snapshot.state["problem"] = json!({
            "format":"VMT", "source":self.problem_source,
            "notation":"The complete original verification problem. :init marks initialization, :trans the transition relation, :invar-property the property, and :next the current/next variable mapping. For Int arrays, select/store correspond to abstract Read_Int_Int/Write_Int_Int. x@N denotes absolute frame N; next variables denote the following frame. The original problem uses array semantics; the abstract function tables may violate them."
        });
        snapshot.state["prompt_variant"] = json!(self.options.jev_prompt);
        if self.options.jev_prompt == JevPrompt::PropertyDirected {
            snapshot.state["task"] = json!(PROPERTY_DIRECTED_PROMPT.trim());
        }
        let mut failures = FailureSummary::default();
        for attempt in 1..=self.options.jev_attempts {
            let axiom_request = match snapshot.axiom_request(&self.options.jev_model, &failures) {
                Ok(request) => request,
                Err(error) => {
                    self.record(context, json!({"event":"unexpressible","snapshot":snapshot.state,"error":error.to_string()}))?;
                    self.finish(context, "unexpressible", attempt - 1)?;
                    return Ok(vec![]);
                }
            };
            let Some((axiom_response, elapsed)) =
                self.query(context, attempt, "quantifier_selection", &axiom_request)?
            else {
                return Ok(vec![]);
            };
            let schema = match snapshot.selected_axiom(&axiom_request, &axiom_response) {
                Ok(schema) => schema,
                Err(error) => {
                    let feedback = json!({"outcome":"invalid","stage":"quantifier_selection","error":error.to_string()});
                    self.record(context, json!({"event":"attempt_result","attempt":attempt,"stage":"quantifier_selection","response":axiom_response,"feedback":feedback,"elapsed_secs":elapsed,"cost":query_cost(&axiom_response, &self.options)}))?;
                    failures.record(&axiom_request, &axiom_response, &feedback);
                    continue;
                }
            };
            self.record(
                context,
                json!({"event":"axiom_result","attempt":attempt,"stage":"quantifier_selection",
                "selected_axiom":{"id":schema.id,"name":schema.name()},"response":axiom_response,
                "elapsed_secs":elapsed,"cost":query_cost(&axiom_response, &self.options)}),
            )?;
            let request =
                snapshot.binding_request(&self.options.jev_model, &failures, &schema.id)?;
            let (ranked, response, elapsed, ranking_error) = match self.mode {
                BindingMode::OneShot => {
                    let Some((response, elapsed)) =
                        self.query(context, attempt, "instantiation", &request)?
                    else {
                        return Ok(vec![]);
                    };
                    let (ranked, error) = match ranked_bindings::top_bindings(
                        &request,
                        &response,
                        self.options.jev_candidates,
                    ) {
                        Ok(ranked) => (ranked, None),
                        Err(error) => (
                            vec![ranked_bindings::RankedBindings::chosen(&response)],
                            Some(error.to_string()),
                        ),
                    };
                    (ranked, response, elapsed, error)
                }
                BindingMode::Conditional => {
                    match self.conditional_bindings(context, attempt, &snapshot, &request)? {
                        conditional::Outcome::Complete(ranked) => (ranked, Value::Null, 0.0, None),
                        conditional::Outcome::Stopped => return Ok(vec![]),
                        conditional::Outcome::Invalid {
                            request: failed_request,
                            response,
                            error,
                        } => {
                            let feedback = json!({"outcome":"invalid", "stage":"instantiation", "rule":schema.name(), "error":error,
                                "fixed_bindings":failed_request["state"]["fixed_bindings"],"binding_slot":failed_request["state"]["binding_slot"]});
                            failures.record(&failed_request, &response, &feedback);
                            self.record(context, json!({"event":"attempt_result", "attempt":attempt, "stage":"instantiation", "api_call":false, "feedback":feedback, "elapsed_secs":0.0}))?;
                            continue;
                        }
                    }
                }
            };
            let mut feedback = Value::Null;
            let mut instances = Vec::new();
            let mut pending = context.pending.clone();
            let mut successful_feedback = None;
            let mut candidates_checked = 0;
            let mut successful_ranks = Vec::new();
            let validation_start = Instant::now();
            for (index, candidate) in ranked.iter().enumerate() {
                let (mut result, proposed) = match snapshot.proposal(&request, &candidate.response)
                {
                    Ok(instance) => validate(
                        &DiscoveryContext {
                            pending: &pending,
                            ..*context
                        },
                        instance,
                    ),
                    Err(error) => (json!({"outcome":"invalid","error":error.to_string()}), None),
                };
                result["stage"] = json!("instantiation");
                result["rule"] = json!(schema.name());
                candidates_checked += 1;
                self.record(context, json!({"event":"candidate_result","attempt":attempt,"stage":"instantiation",
                    "rank":index + 1,"probability_product":candidate.probability_product,
                    "matches_model_choice":candidate.matches_model_choice,"choices":candidate.response["answers"],"feedback":result}))?;
                if proposed.is_none() {
                    failures.record(&request, &candidate.response, &result);
                }
                feedback = result;
                if let Some(instance) = proposed {
                    // Validation used this same normalization. Reserve the key so
                    // equivalent tuples cannot consume multiple batch slots.
                    if let Some(normalized) = context
                        .smt
                        .make_unquantified_instance(instance.term.clone())
                    {
                        pending.insert(canonical_instantiation_key(normalized.get_term()));
                    }
                    successful_ranks.push(index + 1);
                    successful_feedback.get_or_insert_with(|| feedback.clone());
                    instances.push(instance);
                    if !self.options.jev_batch {
                        break;
                    }
                }
            }
            if let Some(success) = successful_feedback {
                feedback = success;
            }
            self.record(
                context,
                json!({"event":"attempt_result","attempt":attempt,"stage":"instantiation","selected_axiom":schema.id,"response":response,
                "feedback":feedback,"elapsed_secs":elapsed,
                "api_call":self.mode == BindingMode::OneShot,
                "cost":if self.mode == BindingMode::OneShot { query_cost(&response, &self.options) } else { Value::Null },
                "candidates_checked":candidates_checked,"successful_rank":successful_ranks.first(),
                "successful_ranks":successful_ranks,"accepted_instances":instances.len(),"ranking_error":ranking_error,
                "validation_elapsed_secs":validation_start.elapsed().as_secs_f64()}),
            )?;
            if !instances.is_empty() {
                self.finish(context, "violated", attempt)?;
                return Ok(instances);
            }
        }
        self.finish(context, "attempts_exhausted", self.options.jev_attempts)?;
        Ok(vec![])
    }
}

fn query_cost(response: &Value, options: &DecisionModelOptions) -> Value {
    let input = response["usage"]["input_tokens"].as_u64();
    let output = response["usage"]["output_tokens"].as_u64();
    // Missing output usage does not affect the estimate when output is free.
    let estimate = input
        .zip(output.or((options.jev_output_usd_per_million == 0.0).then_some(0)))
        .map(|(input, output)| {
            input as f64 / 1_000_000.0 * options.jev_input_usd_per_million
                + output as f64 / 1_000_000.0 * options.jev_output_usd_per_million
        })
        .filter(|cost| cost.is_finite());
    json!({
        "status": if estimate.is_some() { "estimated" } else { "unknown" },
        "estimated_usd": estimate,
        "input_tokens": input,
        "output_tokens": output,
        "input_usd_per_million": options.jev_input_usd_per_million,
        "output_usd_per_million": options.jev_output_usd_per_million,
        "basis": "response_usage_at_configured_rates",
    })
}

fn validate(
    context: &DiscoveryContext<'_>,
    instance: SymbolicInstance,
) -> (Value, Option<SymbolicInstance>) {
    let mut feedback = json!({"rule":instance.rule.name(),"instance":instance.term.to_string(),
        "bindings":instance.bindings.iter().map(|(v,t)| (v.clone(), t.to_string())).collect::<std::collections::BTreeMap<_,_>>()});
    let Some(normalized) = context
        .smt
        .make_unquantified_instance(instance.term.clone())
    else {
        feedback["outcome"] = json!("uninstallable");
        return (feedback, None);
    };
    let key = canonical_instantiation_key(normalized.get_term());
    if context.pending.contains(&key)
        || context
            .smt
            .get_instantiations()
            .iter()
            .any(|t| canonical_instantiation_key(t) == key)
    {
        feedback["outcome"] = json!("already_present");
        return (feedback, None);
    }
    let evaluation = context.smt.eval_partial(&instance.term);
    match evaluation {
        Ok(ModelEvaluation::Known(value)) if value.trim() == "false" => {
            feedback["outcome"] = json!("violated");
            feedback["model_value"] = json!(false);
            (feedback, Some(instance))
        }
        result => {
            let outcome = match &result {
                Ok(ModelEvaluation::Known(v)) if v.trim() == "true" => "instance_true",
                Ok(_) => "undetermined",
                Err(_) => "evaluation_error",
            };
            feedback["outcome"] = json!(outcome);
            if let Err(error) = result {
                feedback["error"] = json!(error.to_string());
            }
            let mut observations = std::collections::BTreeMap::new();
            observe_subterms(context, &instance.term, &mut observations);
            let mut reason = outcome;
            if outcome == "instance_true" {
                if let Term::Application {
                    qual_identifier,
                    arguments,
                } = &instance.term
                {
                    if qual_identifier.to_string() == "=>" && arguments.len() == 2 {
                        let value = |term: &Term| {
                            observations
                                .get(&term.to_string())
                                .and_then(|v| v["value"].as_str())
                        };
                        if value(&arguments[0]) == Some("false") {
                            reason = "false_antecedent";
                        } else if value(&arguments[1]) == Some("true") {
                            reason = "true_consequent";
                        }
                    }
                }
            }
            feedback["reason"] = json!(reason);
            feedback["observations"] = json!(observations);
            feedback["explanation"] = json!("Only a new, installable instance whose COMPLETE formula evaluates to false excludes this model. A false antecedent makes an implication true. Unknown evaluations are not false. Try a different complete substitution using the original model and this feedback.");
            (feedback, None)
        }
    }
}

fn observe_subterms(
    context: &DiscoveryContext<'_>,
    term: &Term,
    observations: &mut std::collections::BTreeMap<String, Value>,
) {
    let key = term.to_string();
    if observations.contains_key(&key) {
        return;
    }
    let value = match context.smt.eval_partial(term) {
        Ok(ModelEvaluation::Known(value)) => json!({"status":"known","value":value}),
        Ok(ModelEvaluation::Undetermined) => json!({"status":"undetermined"}),
        Err(error) => json!({"status":"error","error":error.to_string()}),
    };
    observations.insert(key, value);
    if let Term::Application { arguments, .. } = term {
        for argument in arguments {
            observe_subterms(context, argument, observations);
        }
    }
}
