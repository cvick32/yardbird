//! One joint LLM proposal per call, using the same frozen context and validator
//! as JEV. Optional feedback attempts reuse that model. Failure always yields
//! to ordinary refinement; providers cannot report proofs or counterexamples.
mod client;
mod cost;
mod options;
mod protocol;
#[cfg(test)]
mod tests;

use crate::{
    instance_installation::full_unroll::FullUnrollStrategy,
    policy::{
        discovery::{DiscoveryContext, DiscoveryFirst, InstanceDiscovery},
        instance_selection::TermCostInstantiationRanker,
        instantiation::{validate, InstantiationSession},
        term_selection::array::ArrayBMCCost,
        YardbirdPolicy,
    },
    rule_matching::candidate::SymbolicInstance,
    solver::PropertyCheckMode,
    strategies::Abstract,
    ArrayProofPlan, SolverBackend, Theory, TheorySelection, YardbirdOptions,
};
use client::{HttpClient, LlmClient};
pub use cost::LlmPricing;
pub use options::{LlmOptions, LlmProvider};
use serde_json::{json, Value};
use std::{
    fs::{File, OpenOptions},
    io::Write,
    path::PathBuf,
    time::Instant,
};

pub(crate) fn build_plan(run: &YardbirdOptions) -> ArrayProofPlan {
    let options = run.llm.clone();
    let experiment = Experiment {
        no_fallback: run.no_guided_fallback,
        client: Box::new(HttpClient::new(
            options.llm_provider,
            options.llm_timeout_secs,
        )),
        options,
        query_id: 0,
        session: Default::default(),
        spend: Default::default(),
        log: None,
        input: run.filename.clone(),
        problem_source: None,
    };
    let policy = YardbirdPolicy::<ArrayBMCCost>::new(())
        .with_instantiation_ranker(Box::new(TermCostInstantiationRanker))
        .with_effort(DiscoveryFirst::default().with_no_fallback(run.no_guided_fallback))
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
    no_fallback: bool,
    options: LlmOptions,
    client: Box<dyn LlmClient>,
    query_id: u64,
    session: InstantiationSession,
    spend: cost::Spend,
    log: Option<File>,
    input: Option<String>,
    problem_source: Option<String>,
}

impl Experiment {
    fn record(&mut self, context: &DiscoveryContext<'_>, mut record: Value) -> anyhow::Result<()> {
        if self.log.is_none() {
            let path: &PathBuf = self
                .options
                .llm_log
                .as_ref()
                .ok_or_else(|| anyhow::anyhow!("missing LLM episode log path"))?;
            self.log = Some(OpenOptions::new().write(true).create_new(true).open(path)?);
        }
        record["no_guided_fallback"] = json!(self.no_fallback);
        record["schema_version"] = json!(3);
        record["run_cost"] = self.spend.summary();
        record["policy"] = json!("llm-one-shot");
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

    fn finish(
        &mut self,
        context: &DiscoveryContext<'_>,
        outcome: &str,
        calls: usize,
    ) -> anyhow::Result<()> {
        self.spend.report();
        self.record(
            context,
            json!({"event":"episode_end", "outcome":outcome,
            "api_calls":calls, "ordinary_fallback":!self.no_fallback && outcome != "violated",
            "installation_status":"not_observed_by_discovery"}),
        )
    }
}

impl InstanceDiscovery for Experiment {
    fn discover(
        &mut self,
        context: &DiscoveryContext<'_>,
    ) -> anyhow::Result<Vec<SymbolicInstance>> {
        if self.problem_source.is_none() {
            let path = self
                .input
                .as_ref()
                .ok_or_else(|| anyhow::anyhow!("missing original VMT path"))?;
            self.problem_source = Some(std::fs::read_to_string(path)?);
        }
        let snapshot = match self
            .session
            .capture(context, self.problem_source.as_deref().unwrap())
        {
            Ok(snapshot) => snapshot,
            Err(error) => {
                self.record(
                    context,
                    json!({"event":"snapshot_error", "error":format!("{error:#}")}),
                )?;
                self.finish(context, "snapshot_error", 0)?;
                return Ok(vec![]);
            }
        };
        let mut failures = Vec::new();
        for attempt in 1..=self.options.llm_attempts {
            let request = protocol::request(&self.options, &snapshot, &failures)?;
            self.query_id += 1;
            let bytes = serde_json::to_vec(&request)?.len();
            self.record(context, json!({"event":"request", "attempt":attempt,
                "endpoint":self.options.llm_provider.endpoint(), "request_bytes":bytes, "request":request}))?;
            let skip = if bytes > self.options.llm_max_request_bytes {
                Some("request_too_large")
            } else if self.options.llm_dry_run {
                Some("dry_run")
            } else {
                None
            };
            if let Some(outcome) = skip {
                self.record(
                    context,
                    json!({"event":"request_skipped", "attempt":attempt, "outcome":outcome}),
                )?;
                self.finish(context, outcome, attempt - 1)?;
                return Ok(vec![]);
            }
            let started = Instant::now();
            let response = match self.client.infer(&request) {
                Ok(response) => response,
                Err(error) => {
                    let cost = cost::unknown("transport failure; billed usage unavailable");
                    self.spend.observe(&cost);
                    self.record(context, json!({"event":"transport_error", "attempt":attempt,
                        "error":format!("{error:#}"), "elapsed_secs":started.elapsed().as_secs_f64(), "usage":null, "cost":cost}))?;
                    self.finish(context, "transport_error", attempt)?;
                    return Ok(vec![]);
                }
            };
            let cost = cost::estimate(&self.options, &response);
            self.spend.observe(&cost);
            log::info!("LLM call {} cost: {}", self.query_id, cost["estimated_usd"]);
            self.spend.report();
            self.record(
                context,
                json!({"event":"response", "attempt":attempt,
                "elapsed_secs":started.elapsed().as_secs_f64(), "resolved_model":response["model"],
                "usage":response["usage"], "response":response, "cost":cost}),
            )?;
            let text = match protocol::response_text(self.options.llm_provider, &response) {
                Ok(text) => text,
                Err(error) => {
                    self.record(
                        context,
                        json!({"event":"attempt_result", "attempt":attempt,
                        "feedback":{"outcome":"response_rejected", "error":format!("{error:#}")}}),
                    )?;
                    self.finish(context, "response_rejected", attempt)?;
                    return Ok(vec![]);
                }
            };
            let validation_started = Instant::now();
            let (feedback, instance) = match protocol::proposal(text) {
                Ok(None) => {
                    self.record(context, json!({"event":"attempt_result", "attempt":attempt, "feedback":{"outcome":"abstained"}}))?;
                    self.finish(context, "abstained", attempt)?;
                    return Ok(vec![]);
                }
                Ok(Some(proposal)) => match snapshot.resolve(&proposal) {
                    Ok(instance) => validate(context, instance),
                    Err(error) => (
                        json!({"outcome":"invalid", "proposal":proposal, "error":format!("{error:#}")}),
                        None,
                    ),
                },
                Err(error) => (
                    json!({"outcome":"invalid", "error":format!("{error:#}")}),
                    None,
                ),
            };
            self.record(context, json!({"event":"attempt_result", "attempt":attempt,
                "feedback":feedback, "validation_elapsed_secs":validation_started.elapsed().as_secs_f64(),
                "accepted_instances":usize::from(instance.is_some())}))?;
            if let Some(instance) = instance {
                self.finish(context, "violated", attempt)?;
                return Ok(vec![instance]);
            }
            // Keep the same model and only compact rejection details in retries.
            // Full observations remain in the log, as in the JEV experiment.
            let mut compact = feedback;
            compact.as_object_mut().unwrap().remove("observations");
            failures.push(compact);
        }
        self.finish(context, "attempts_exhausted", self.options.llm_attempts)?;
        Ok(vec![])
    }
}
