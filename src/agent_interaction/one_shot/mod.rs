//! Complete-batch experiments. This path never invokes symbolic search, strategy
//! SAT hooks, eager seeding, or concrete fallback. The only asserted advice is
//! reconstructed from the prepared program's trusted, typed schemas.
mod bundle;
mod options;
#[cfg(test)]
mod tests;
pub use bundle::Recorder;
pub use options::{BatchPlacement, OneShotOptions};

use crate::{
    agent_interaction::AgentMode,
    instance_installation::request::InstantiationRequest,
    policy::{
        instantiation::InstantiationSnapshot,
        llm::{
            client::{HttpClient, LlmClient},
            LlmOptions,
        },
    },
    problem_context::ProblemContext,
    solver::SolverCheckResult,
    vmt_bmc_session::VmtBmcSession,
    YardbirdOptions,
};
use serde::Serialize;
use serde_json::{json, Value};
use smt2parser::{concrete::Term, vmt::quantified_instantiator::Instance};
use std::{
    collections::{BTreeMap, HashSet},
    fs::File,
    io::Write,
    path::PathBuf,
    time::{Duration, Instant},
};

#[derive(Debug, Serialize)]
struct Report {
    mode: String,
    placement: BatchPlacement,
    status: String,
    target_depth: u16,
    closed_depths: Vec<u16>,
    unresolved_depths: Vec<u16>,
    calls: usize,
    proposed_instances: usize,
    unique_instances: usize,
    installed_instances: u64,
    duplicates: usize,
    rejected_batches: usize,
    rejected_proposals: usize,
    replayed_assertions: u64,
    stop_reason: Option<String>,
    symbolic_refinements: usize,
    usage: Value,
    usage_unknown_calls: usize,
    timings_seconds: BTreeMap<String, f64>,
    total_seconds: f64,
    error: Option<String>,
    log: PathBuf,
}

#[derive(Debug, thiserror::Error)]
#[error("experiment wall deadline reached")]
struct Expired;

struct Experiment {
    start: Instant,
    wall: Duration,
    log: File,
    report: Report,
}
impl Experiment {
    fn remaining(&self) -> anyhow::Result<Duration> {
        self.wall
            .checked_sub(self.start.elapsed())
            .filter(|d| !d.is_zero())
            .ok_or_else(|| Expired.into())
    }
    fn event(&mut self, mut value: Value) -> anyhow::Result<()> {
        value["elapsed_seconds"] = json!(self.start.elapsed().as_secs_f64());
        serde_json::to_writer(&mut self.log, &value)?;
        writeln!(self.log)?;
        self.log.flush()?;
        Ok(())
    }
    fn timing(&mut self, phase: &str, start: Instant) {
        *self.report.timings_seconds.entry(phase.into()).or_default() +=
            start.elapsed().as_secs_f64();
    }
}

pub fn run(options: &YardbirdOptions) -> anyhow::Result<()> {
    let report = execute(options, None)?;
    if options.json_output {
        let mut stdout = std::io::stdout().lock();
        serde_json::to_writer(&mut stdout, &report)?;
        writeln!(stdout)?;
    }
    anyhow::ensure!(
        report.status == "bounded_complete" || report.status == "dry_run",
        "{}: {}; see {}",
        report.mode,
        report.status,
        report.log.display()
    );
    Ok(())
}

fn execute(
    options: &YardbirdOptions,
    client: Option<Box<dyn LlmClient>>,
) -> anyhow::Result<Report> {
    let start = Instant::now();
    options.one_shot.validate(options)?;
    let mode = if options.one_shot.one_shot {
        "one_shot"
    } else {
        "replay"
    };
    let mut log_options = options.agent.clone();
    log_options.mode = Some(AgentMode::Bedrock);
    log_options.resolve_log(
        options.require_filename()?,
        std::path::Path::new(".yardbird/runs"),
    )?;
    let path = log_options.agent_log.unwrap();
    let log = File::options().create_new(true).write(true).open(&path)?;
    let mut experiment = Experiment {
        start,
        wall: Duration::from_secs(options.wall_timeout_secs.unwrap_or(500)),
        log,
        report: Report {
            mode: mode.into(),
            placement: options.one_shot.placement(),
            status: "preparing".into(),
            target_depth: options.depth,
            closed_depths: vec![],
            unresolved_depths: (0..options.depth).collect(),
            calls: 0,
            proposed_instances: 0,
            unique_instances: 0,
            installed_instances: 0,
            duplicates: 0,
            rejected_batches: 0,
            rejected_proposals: 0,
            replayed_assertions: 0,
            stop_reason: None,
            symbolic_refinements: 0,
            usage: Value::Null,
            usage_unknown_calls: 0,
            timings_seconds: BTreeMap::new(),
            total_seconds: 0.0,
            error: None,
            log: path,
        },
    };
    log::info!(
        "BATCH {} bounds=0..{} log={}; no symbolic refinement or fallback",
        mode,
        options.depth - 1,
        experiment.report.log.display()
    );
    experiment.event(json!({"event":"starting","mode":mode,"input":options.filename,
        "target_depth":options.depth,"wall_seconds":experiment.wall.as_secs(),"symbolic_refinement":false}))?;
    if let Err(error) = execute_inner(options, client, &mut experiment) {
        experiment.report.status = if error.is::<Expired>() {
            "timeout"
        } else {
            "error"
        }
        .into();
        experiment.report.error = Some(format!("{error:#}"));
        experiment.report.stop_reason = Some(experiment.report.status.clone());
    }
    experiment.report.total_seconds = experiment.start.elapsed().as_secs_f64();
    experiment.event(json!({"event":"finished","result":experiment.report}))?;
    let summary = experiment.report.log.with_extension("result.json");
    serde_json::to_writer_pretty(
        File::options()
            .create_new(true)
            .write(true)
            .open(&summary)?,
        &experiment.report,
    )?;
    log::info!("BATCH {}: closed {}/{} bounds, proposed={}, installed={}, calls={}, total={:.3}s; summary={}",
        experiment.report.status, experiment.report.closed_depths.len(), options.depth,
        experiment.report.proposed_instances, experiment.report.installed_instances,
        experiment.report.calls,experiment.report.total_seconds,summary.display());
    Ok(experiment.report)
}

fn execute_inner(
    options: &YardbirdOptions,
    mut client: Option<Box<dyn LlmClient>>,
    experiment: &mut Experiment,
) -> anyhow::Result<()> {
    let prepare = Instant::now();
    experiment.remaining()?;
    let source = std::fs::read_to_string(options.require_filename()?)?;
    let mut plan = options.build_array_proof_plan();
    plan.strategy.enable_instantiation_catalogue()?;
    let model = plan
        .strategy
        .configure_model(crate::model_from_options(options));
    if let Some(error) = plan.strategy.configuration_error() {
        anyhow::bail!("{error}");
    }
    let mut vocabulary = VmtBmcSession::new(
        &model,
        &plan.strategy,
        plan.solver,
        false,
        plan.instantiation_strategy.clone_box(),
        false,
        None,
    )?;
    for depth in 0..options.depth {
        experiment.remaining()?;
        vocabulary.unroll(depth);
    }
    let snapshot = plan
        .strategy
        .instantiation_catalogue(&vocabulary, &source, options.depth - 1)?
        .snapshot;
    experiment.timing("preparation", prepare);
    experiment.remaining()?;

    let mut accepted = AcceptedInstances::new(options.one_shot.placement());
    anyhow::ensure!(
        accepted.placement == BatchPlacement::Exact || vocabulary.supports_eager_instantiation(),
        "schema batch placement requires an installation policy that supports eager instantiation"
    );
    if let Some(path) = &options.one_shot.replay_instantiations {
        let start = Instant::now();
        anyhow::ensure!(
            std::fs::metadata(path)?.len() <= 64 * 1024 * 1024,
            "replay artifact exceeds 64 MiB"
        );
        let replay: bundle::Replay = serde_json::from_reader(File::open(path)?)?;
        anyhow::ensure!(
            replay.version == 1 && replay.source == source && replay.target_depth == options.depth,
            "replay artifact source/version/target does not match this experiment"
        );
        experiment.report.proposed_instances = replay.formulas.len();
        let mut validated = Vec::new();
        for formula in replay.formulas {
            experiment.remaining()?;
            validated.push(accepted.prepare(
                bundle::validate_replay(&snapshot, &formula)?,
                options.depth,
                &vocabulary,
            )?);
        }
        accepted.install_prepared(validated, experiment)?;
        experiment.event(json!({"event":"replay_validated","native_progress":replay.native_progress,"count":accepted.unique.len()}))?;
        experiment.timing("validation", start);
        check_batch(&model, &plan, &mut accepted, experiment)?;
        experiment.report.stop_reason = Some("replay_finished".into());
        return Ok(());
    }

    let mut provider = options.agent.provider()?;
    provider.llm_max_output_tokens = options.one_shot.one_shot_output_tokens;
    let prompt = match &options.one_shot.one_shot_prompt {
        Some(path) => std::fs::read_to_string(path)?,
        None => include_str!("prompt.md").into(),
    };
    anyhow::ensure!(
        !prompt.trim().is_empty(),
        "one-shot prompt must not be empty"
    );
    let prepared = model.as_vmt_string();
    let mut previous_attempt = Value::Null;
    let mut countermodel = Value::Null;
    let mut checked = false;
    loop {
        experiment.remaining()?;
        if options.agent.agent_max_calls > 0
            && experiment.report.calls >= options.agent.agent_max_calls
        {
            experiment.report.stop_reason = Some("call_limit".into());
            return Ok(());
        }
        let prepare_request = Instant::now();
        let mut request = request(&provider, &snapshot, &prepared, options.depth, &prompt);
        let mut context: Value =
            serde_json::from_str(request["input"][1]["content"].as_str().unwrap())?;
        context["batch_mode"] = json!({
            "placement":accepted.placement,
            "round":experiment.report.calls + 1,
            "max_calls":options.agent.agent_max_calls,
            "remaining_seconds":experiment.remaining()?.as_secs_f64(),
            "meaning":"Each call submits one batch. Accepted instances accumulate; incomplete results receive solver feedback and another call while budget remains. max_calls=0 means no call cap."
        });
        context["binding_notation"] = json!(match accepted.placement {
            BatchPlacement::Schema => "Supply concrete, well-typed ground SMT-LIB bindings using declared absolute frame names. Yardbird normalizes the entire resulting theory instance to a shared frame origin, preserving relative offsets, and reuses its native installation policy to place/replay it. Do not enumerate shifted copies. For example A@4 with i@5 becomes A+0 with i+1, not two independent +0 terms. Immutable symbols and definition dependencies follow native BMC rules. This shifts the whole instance, not each index independently.",
            BatchPlacement::Exact => "Supply concrete ground SMT-LIB bindings at every required absolute frame. Exact placement does not normalize, shift, or replay instances."
        });
        if experiment.report.calls > 0 {
            context["feedback"] = json!({
                "closed_depths":experiment.report.closed_depths,
                "unresolved_depths":experiment.report.unresolved_depths,
                "accepted_instances":accepted.formulas(),
                "accepted_instance_notation":match accepted.placement {
                    BatchPlacement::Schema => "Normalized temporal schemas: x+N is relative to the shared frame origin. These are installed through the selected native policy. Submit new proposals using concrete declared x@N symbols.",
                    BatchPlacement::Exact => "Exact ground formulas; no temporal replay."
                },
                "remaining_countermodel":countermodel,
                "previous_attempt":previous_attempt,
                "instruction":"Supply additional instances to close the remaining bounds. Already accepted instances are retained; do not repeat them. Model interpretations are observations, not trusted lemmas or permitted new constants."
            });
        }
        request["input"][1]["content"] = json!(context.to_string());
        let bytes = serde_json::to_vec(&request)?.len();
        anyhow::ensure!(bytes <= options.agent.agent_max_request_bytes,
            "one-shot request is {bytes} bytes, above --agent-max-request-bytes; context was not truncated");
        experiment.timing("context", prepare_request);
        experiment.remaining()?;
        if options.agent.agent_dry_run {
            experiment.event(json!({"event":"dry_request","bytes":bytes,"request":request}))?;
            experiment.report.status = "dry_run".into();
            experiment.report.stop_reason = Some("dry_run".into());
            return Ok(());
        }
        let round = experiment.report.calls + 1;
        log::info!(
            "BATCH REQUEST round={} closed={}/{} bytes={} output_tokens={} remaining={:.1}s",
            round,
            experiment.report.closed_depths.len(),
            options.depth,
            bytes,
            provider.llm_max_output_tokens,
            experiment.remaining()?.as_secs_f64()
        );
        experiment
            .event(json!({"event":"request","round":round,"bytes":bytes,"request":request}))?;
        let remaining = experiment.remaining()?;
        experiment.report.calls += 1;
        experiment.report.usage_unknown_calls += 1;
        let inference = Instant::now();
        let response = match client.as_mut() {
            Some(fake) => fake.infer(&request),
            None => HttpClient::new(&provider)
                .with_timeout(remaining)
                .infer(&request),
        };
        experiment.timing("inference", inference);
        if let Ok(response) = &response {
            add_usage(&mut experiment.report.usage, &response["usage"]);
            if response["usage"]["input_tokens"].is_u64()
                && response["usage"]["output_tokens"].is_u64()
            {
                experiment.report.usage_unknown_calls -= 1;
            }
            experiment.event(json!({"event":"response","round":round,"response":response}))?;
        }
        // A timed-out provider call must not start another request or install a late reply.
        experiment.remaining()?;
        let response = response?;
        let start = Instant::now();
        // Only public tool output is fed back, never provider reasoning blocks.
        previous_attempt = json!({"round":round,"tool_calls":response["output"].as_array()
            .into_iter().flatten().filter(|v| v["type"] == "function_call").cloned().collect::<Vec<_>>()});
        let batch = match decode(&response) {
            Ok(batch) => batch,
            Err(error) => {
                let message = format!("{error:#}");
                experiment.report.rejected_batches += 1;
                experiment.report.status = "error".into();
                experiment.report.error = Some(message.clone());
                previous_attempt["validation_error"] = json!(message);
                previous_attempt["accepted"] = json!(false);
                log::warn!(
                    "BATCH REJECT round={} {}; retaining previous instances",
                    round,
                    message
                );
                experiment
                    .event(json!({"event":"batch_rejected","round":round,"error":message}))?;
                continue;
            }
        };
        log::info!(
            "BATCH WHY round={} {}",
            round,
            batch.rationale.escape_debug()
        );
        experiment.report.proposed_instances += batch.instantiations.len();
        let mut terms = Vec::new();
        let mut errors = Vec::new();
        for (index, raw) in batch.instantiations.into_iter().enumerate() {
            experiment.remaining()?;
            let proposal = serde_json::from_value::<bundle::Proposal>(raw)
                .map_err(anyhow::Error::from)
                .and_then(|item| snapshot.resolve_text(&item.schema_id, &item.bindings))
                .and_then(|instance| accepted.prepare(instance.term, options.depth, &vocabulary));
            match proposal {
                Ok(term) => terms.push(term),
                Err(error) => {
                    let rejection = json!({"index":index,"error":format!("{error:#}")});
                    experiment.event(
                        json!({"event":"proposal_rejected","round":round,"rejection":rejection}),
                    )?;
                    errors.push(rejection);
                }
            }
        }
        experiment.report.rejected_proposals += errors.len();
        previous_attempt["rejections"] = json!(errors);
        let added = accepted.install_prepared(terms, experiment)?;
        experiment.timing("validation", start);
        experiment.report.error = None;
        previous_attempt["accepted"] = json!(true);
        previous_attempt["new_instances"] = json!(added);
        // A duplicate/empty batch cannot change the solver result. Keep its existing
        // countermodel for the next call rather than repeat identical solver work.
        if !checked || added > 0 {
            countermodel = check_batch(&model, &plan, &mut accepted, experiment)?;
            checked = true;
        } else {
            experiment.report.status = "incomplete".into();
        }
        log::info!(
            "BATCH ROUND {} closed={}/{} new={} total={} remaining={:.1}s",
            round,
            experiment.report.closed_depths.len(),
            options.depth,
            added,
            accepted.unique.len(),
            experiment.remaining()?.as_secs_f64()
        );
        experiment.event(json!({"event":"round_finished","round":round,"new_instances":added,
            "closed_depths":experiment.report.closed_depths,"unresolved_depths":experiment.report.unresolved_depths}))?;
        if experiment.report.status == "bounded_complete" || experiment.report.status == "unknown" {
            experiment.report.stop_reason = Some(experiment.report.status.clone());
            return Ok(());
        }
    }
}

struct PreparedInstance {
    depth: u16,
    key: Term,
    term: Term,
    instance: Option<Instance>,
}

struct AcceptedInstances {
    placement: BatchPlacement,
    unique: HashSet<Term>,
    at_depth: BTreeMap<u16, Vec<Term>>,
    schemas: BTreeMap<u16, Vec<Instance>>,
    installed: HashSet<Term>,
}
impl AcceptedInstances {
    fn new(placement: BatchPlacement) -> Self {
        Self {
            placement,
            unique: HashSet::new(),
            at_depth: BTreeMap::new(),
            schemas: BTreeMap::new(),
            installed: HashSet::new(),
        }
    }

    fn formulas(&self) -> Vec<String> {
        if self.placement == BatchPlacement::Schema {
            return self
                .schemas
                .values()
                .flatten()
                .map(ToString::to_string)
                .collect();
        }
        self.at_depth
            .values()
            .flatten()
            .map(ToString::to_string)
            .collect()
    }

    fn prepare(
        &self,
        term: Term,
        depth_limit: u16,
        vocabulary: &VmtBmcSession,
    ) -> anyhow::Result<PreparedInstance> {
        let depth = bundle::last_frame(&term)?;
        anyhow::ensure!(
            depth < depth_limit,
            "instance references an out-of-target frame"
        );
        let instance = if self.placement == BatchPlacement::Schema {
            let instance = vocabulary
                .make_unquantified_instance(term.clone())
                .ok_or_else(|| anyhow::anyhow!("could not normalize theory instance"))?;
            anyhow::ensure!(
                instance.width() < depth_limit,
                "schema width exceeds target"
            );
            Some(instance)
        } else {
            None
        };
        let key = crate::instance_installation::assertion_tracker::canonical_instantiation_key(
            instance.as_ref().map_or(&term, Instance::get_term),
        );
        Ok(PreparedInstance {
            depth,
            key,
            term,
            instance,
        })
    }

    fn install_prepared(
        &mut self,
        prepared: Vec<PreparedInstance>,
        experiment: &mut Experiment,
    ) -> anyhow::Result<usize> {
        let before = self.unique.len();
        let mut added = Vec::new();
        for PreparedInstance {
            depth,
            key,
            term,
            instance,
        } in prepared
        {
            if self.unique.insert(key) {
                if let Some(instance) = instance {
                    added.push(instance.to_string());
                    self.schemas
                        .entry(instance.width())
                        .or_default()
                        .push(instance);
                } else {
                    added.push(term.to_string());
                    self.at_depth.entry(depth).or_default().push(term);
                }
            } else {
                experiment.report.duplicates += 1;
            }
        }
        experiment.report.unique_instances = self.unique.len();
        experiment.event(json!({"event":"validated","round":experiment.report.calls,
            "placement":self.placement,"unique_instances":self.unique.len(),"duplicates":experiment.report.duplicates,"instances":added}))?;
        Ok(self.unique.len() - before)
    }
}

/// Each round gets a fresh session; never check an earlier property against later
/// transitions. Closed bounds stay closed because subsequent advice only adds facts.
fn check_batch(
    model: &smt2parser::vmt::VMTModel,
    plan: &crate::ArrayProofPlan,
    accepted: &mut AcceptedInstances,
    experiment: &mut Experiment,
) -> anyhow::Result<Value> {
    experiment.remaining()?;
    let start = Instant::now();
    let mut verifier = VmtBmcSession::new(
        model,
        &plan.strategy,
        plan.solver,
        false,
        plan.instantiation_strategy.clone_box(),
        false,
        None,
    )?;
    experiment.timing("preparation", start);
    let mut countermodel = Value::Null;
    let mut recorded_assertions = 0;
    for depth in 0..experiment.report.target_depth {
        experiment.remaining()?;
        let start = Instant::now();
        verifier.unroll(depth);
        experiment.timing("unrolling", start);
        let start = Instant::now();
        for term in accepted.at_depth.get(&depth).into_iter().flatten() {
            experiment.remaining()?;
            verifier.install_ground_instance(term.clone());
        }
        for instance in accepted.schemas.get(&depth).into_iter().flatten() {
            experiment.remaining()?;
            verifier.add_instantiation(InstantiationRequest::untracked(instance.clone()));
        }
        // Count solver-visible assertions, including native on_loop replay during
        // unroll, rather than confusing a retained schema with a ground placement.
        let assertions = verifier.get_asserted_instantiation_terms();
        if assertions.len() > recorded_assertions {
            experiment.event(json!({"event":"installed","round":experiment.report.calls,"depth":depth,
                "instances":assertions.iter().skip(recorded_assertions).map(ToString::to_string).collect::<Vec<_>>()}))?;
        }
        for term in assertions.iter().skip(recorded_assertions) {
            let key =
                crate::instance_installation::assertion_tracker::canonical_instantiation_key(term);
            if accepted.installed.insert(key) {
                experiment.report.installed_instances += 1;
            } else {
                experiment.report.replayed_assertions += 1;
            }
        }
        recorded_assertions = assertions.len();
        experiment.timing("installation", start);
        if experiment.report.closed_depths.contains(&depth) {
            continue;
        }
        verifier.set_timeout_millis(
            experiment
                .remaining()?
                .as_millis()
                .clamp(1, u32::MAX as u128) as u32,
        )?;
        let start = Instant::now();
        let result = verifier.check_property();
        experiment.timing("solver_checks", start);
        let status = match result {
            SolverCheckResult::Unsat => {
                experiment.report.closed_depths.push(depth);
                experiment.report.closed_depths.sort_unstable();
                experiment.report.unresolved_depths.retain(|d| *d != depth);
                "unsat"
            }
            SolverCheckResult::Sat => "sat",
            SolverCheckResult::Unknown => "unknown",
        };
        log::info!(
            "BATCH CHECK round={} depth={} result={} elapsed={:.3}s",
            experiment.report.calls,
            depth,
            status,
            experiment.start.elapsed().as_secs_f64()
        );
        experiment.event(json!({"event":"check","round":experiment.report.calls,"depth":depth,"result":status,
            "solver_seconds":start.elapsed().as_secs_f64(),"reason_unknown":verifier.get_reason_unknown()}))?;
        if result == SolverCheckResult::Sat && countermodel.is_null() {
            countermodel = json!({"depth":depth,"model":verifier.native_model_to_string()?});
            experiment.event(
                json!({"event":"remaining_countermodel","round":experiment.report.calls,
                "depth":depth,"model":countermodel["model"]}),
            )?;
        }
        experiment.remaining()?;
        if result == SolverCheckResult::Unknown {
            experiment.report.status = "unknown".into();
            return Ok(countermodel);
        }
    }
    experiment.report.status = if experiment.report.unresolved_depths.is_empty() {
        "bounded_complete"
    } else {
        "incomplete"
    }
    .into();
    Ok(countermodel)
}

/// Sum numeric provider usage fields, including nested cached/reasoning counts.
fn add_usage(total: &mut Value, usage: &Value) {
    if let Some(fields) = usage.as_object() {
        if !total.is_object() {
            *total = json!({});
        }
        for (key, value) in fields {
            add_usage(&mut total[key], value);
        }
    } else if let Some(n) = usage.as_u64() {
        *total = json!(total.as_u64().unwrap_or(0).saturating_add(n));
    }
}

fn request(
    provider: &LlmOptions,
    snapshot: &InstantiationSnapshot,
    prepared: &str,
    depth: u16,
    prompt: &str,
) -> Value {
    let mut context = snapshot.state();
    // Inline substitutions do not require catalogue IDs. Source, lowered program,
    // signatures, and complete schemas define the available vocabulary exactly.
    for name in [
        "terms",
        "model",
        "model_format",
        "successful_instantiations",
        "catalogue_scope",
    ] {
        context.as_object_mut().unwrap().remove(name);
    }
    context["prepared_program"] = json!(prepared);
    context["schema_semantics"] = json!({
        "schemas_are_asserted_axioms":false,
        "meaning":"The axioms list is a catalogue of trusted schema constructors. Each proposed substitution is reconstructed from one of these schemas. Temporal placement/replay follows batch_mode.placement; there is no symbolic search for new instantiation patterns.",
        "herbrand_witnesses":"Arbitrary constants used to expose a possible property violation; they do not assert the property or supply theory facts."
    });
    context["target"] = json!({"depths":(0..depth).collect::<Vec<_>>(),"meaning":"Each depth is checked independently against its transition prefix; no later transitions are assumed. All bounds must be UNSAT. This is bounded verification, not an inductive proof."});
    let mut request = json!({"model":provider.llm_model,"input":[
        {"role":"developer","content":prompt},
        {"role":"user","content":context.to_string()}],
        "tools":[{"type":"function","name":"submit_instantiations","description":"Submit concrete trusted theory instances; the host uses the configured schema or exact placement mode.","strict":false,
            "parameters":{"type":"object","additionalProperties":false,"required":["rationale","instantiations"],"properties":{
                "rationale":{"type":"string","maxLength":8000},
                "instantiations":{"type":"array","items":{"type":"object","required":["schema_id","bindings"],"additionalProperties":false,"properties":{
                    "schema_id":{"type":"string"},"bindings":{"type":"object","additionalProperties":{"type":"string"}}}}}}}}],
        "tool_choice":{"type":"function","name":"submit_instantiations"},"parallel_tool_calls":false,
        "max_output_tokens":provider.llm_max_output_tokens,"store":false,"truncation":"disabled"});
    if let Some(effort) = &provider.llm_reasoning_effort {
        request["reasoning"] = json!({"effort":effort});
    }
    request
}

fn decode(response: &Value) -> anyhow::Result<bundle::Batch> {
    anyhow::ensure!(
        response["status"] == "completed",
        "one-shot response incomplete; partial batches are not installed"
    );
    let output = response["output"]
        .as_array()
        .ok_or_else(|| anyhow::anyhow!("missing output"))?;
    let calls = output
        .iter()
        .filter(|v| v["type"] == "function_call")
        .collect::<Vec<_>>();
    anyhow::ensure!(
        calls.len() == 1 && calls[0]["name"] == "submit_instantiations",
        "expected one submit_instantiations call"
    );
    let batch: bundle::Batch = serde_json::from_str(
        calls[0]["arguments"]
            .as_str()
            .ok_or_else(|| anyhow::anyhow!("missing batch arguments"))?,
    )?;
    anyhow::ensure!(
        batch.rationale.chars().count() <= 8000,
        "rationale too long"
    );
    Ok(batch)
}
