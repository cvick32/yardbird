//! The solver thread captures owned syntax and model observations and validates
//! hints against the current SAT model. The agent worker builds the catalogue,
//! renders requests, and calls the provider.
mod assessment;
mod binders;
mod observations;
pub mod one_shot;
mod options;
mod records;
#[cfg(test)]
mod tests;
mod wire;

pub(crate) use options::migrate_saved_options;
pub use options::{AgentMode, AgentOptions, AgentTrigger};

use observations::{Observations, TraceInput};

use crate::{
    policy::{
        discovery::DiscoveryContext,
        instantiation::{validate, InstantiationSession, InstantiationSnapshot, SnapshotInput},
        llm::{
            client::{HttpClient, LlmClient},
            LlmOptions,
        },
    },
    rule_matching::candidate::SymbolicInstance,
    transition_index::TransitionIndex,
    YardbirdOptions,
};
use serde_json::{json, Value};
use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fs::File,
    io::Write,
    sync::{
        atomic::{AtomicBool, AtomicUsize, Ordering},
        mpsc::{self, Receiver, TryRecvError},
        Arc, Mutex,
    },
    time::{Duration, Instant},
};

struct Pinned {
    snapshot: InstantiationSnapshot,
    observations: Option<Observations>,
    records: BTreeMap<String, Value>,
    epoch: String,
}
impl Pinned {
    fn section(&self, section: &str) -> anyhow::Result<Value> {
        if section == "records" {
            return Ok(json!(self.records));
        }
        let state = self.snapshot.state();
        if section == "source" {
            return Ok(state["problem"]["source"].clone());
        }
        state
            .get(section)
            .cloned()
            .ok_or_else(|| anyhow::anyhow!("unknown context section {section}"))
    }
    fn view(&self, binders: Option<binders::BinderContext>) -> Value {
        let mut state = self.snapshot.state();
        let directory: Vec<_> = state
            .as_object()
            .unwrap()
            .iter()
            .map(|(k, v)| {
                json!({"section":k,
            "count":v.as_array().map(Vec::len),"bytes":v.to_string().len()})
            })
            .collect();
        state.as_object_mut().unwrap().remove("terms");
        state.as_object_mut().unwrap().remove("binder_sources");
        state["axioms"] = json!(self
            .snapshot
            .schemas
            .iter()
            .map(|s| json!({"id":s.id,"name":s.name(),"slots":s.slots}))
            .collect::<Vec<_>>());
        if let Some(binders) = binders {
            binders.annotate(&self.snapshot, &mut state["axioms"]);
            state["binder_context_format"] = json!("capture_slot_names and variable_slot_names follow numeric slot order. Each ground_capture_tuples row gives the capture arguments of one observed helper application in SMT-LIB. Each installed_relative_tuples row gives the captures followed by the bound variables of an already installed ordinary instance, in relative frames (+K); null means the formula omits the variable. installed_witness_relative_tuples gives the same columns for installed witness instances, including the constructed witness terms. A witness entry shares its instance entry's source context and accepts only its listed slots.");
        }
        let records: Vec<_> = self
            .records
            .values()
            .filter(|r| r["kind"] == "trace" || r["kind"] == "action")
            .collect();
        json!({"epoch":self.epoch,"snapshot":state,"records":records,"sections":directory,
            "retrieval":"read_context retrieves exact omitted terms and sections; inspect retrieves an exact record ID"})
    }
}

#[derive(Default)]
struct Episode {
    catalogue: InstantiationSession,
    pin: Option<Pinned>,
    history: Vec<Value>,
}

struct Capture {
    binder_actions: Option<binders::BinderActions>,
    input: SnapshotInput,
    trace: Option<TraceInput>,
    source: Arc<str>,
    depth: u16,
    model: u64,
    elapsed: f64,
}
impl Capture {
    fn render(self, episode: &mut Episode, log: &EventLog) -> anyhow::Result<Value> {
        let epoch = format!("e{}", self.model);
        let binders = self
            .binder_actions
            .map(|actions| binders::BinderContext::new(&self.input, actions))
            .transpose()?;
        let mut snapshot = episode
            .catalogue
            .restore_terms(InstantiationSnapshot::from_input(self.input, &self.source)?)?;
        let observations = self
            .trace
            .map(|trace| {
                Observations::from_trace(trace, &epoch, &mut episode.catalogue, &mut snapshot)
            })
            .transpose()?;
        let mut records = records::catalogue(&snapshot);
        if let Some(obs) = &observations {
            records.extend(obs.records.clone());
        }
        let pin = Pinned {
            snapshot,
            observations,
            records,
            epoch,
        };
        let view = pin.view(binders);
        log.emit(json!({"event":"snapshot","model":self.model,"depth":self.depth,"capture_seconds":self.elapsed,"context":view}));
        episode.pin = Some(pin);
        Ok(view)
    }
}

#[derive(Clone)]
struct EventLog {
    sender: Option<mpsc::Sender<Option<Value>>>,
    started: Instant,
}
impl EventLog {
    fn emit(&self, mut event: Value) {
        if let Some(sender) = &self.sender {
            event["elapsed_ms"] = json!(self.started.elapsed().as_millis());
            let _ = sender.send(Some(event));
        }
    }
}

type PrepareRequest =
    Box<dyn FnOnce(&mut Episode, &LlmOptions, &EventLog) -> anyhow::Result<Value> + Send>;
type PrepareReply = Box<dyn FnOnce(&mut Episode, &EventLog) -> anyhow::Result<Value> + Send>;
enum Reply {
    Ready(Value),
    Deferred(PrepareReply),
}
struct Flight {
    receiver: Receiver<anyhow::Result<(Episode, Option<Value>)>>,
    sent_at: Arc<std::sync::OnceLock<Instant>>,
    assessment: Option<(u16, String)>,
}

/// Attached through ProofStrategy; configuration does not alter the proof plan.
pub struct Agent {
    options: AgentOptions,
    provider: Option<LlmOptions>,
    transport: Option<Arc<Mutex<Box<dyn LlmClient + Send>>>>,
    source: Arc<str>,
    episode: Episode,
    continuation: Option<PrepareRequest>,
    flight: Option<Flight>,
    last_capture: Option<Instant>,
    yielded_model: Option<u64>,
    depth: Option<(u16, Instant)>,
    episode_depth: Option<u16>,
    wait_since: Option<Instant>,
    next_assess_step: u32,
    adaptive_ready: bool,
    recent_models: std::collections::VecDeque<assessment::Sample>,
    assessment_statistics: crate::utils::SolverStatistics,
    last_assessment: Value,
    disabled: bool,
    log: EventLog,
    log_writer: Option<std::thread::JoinHandle<()>>,
    calls: Arc<AtomicUsize>,
    replies: usize,
    snapshots: usize,
    polls: usize,
    capture_seconds: f64,
    expansion_work: usize,
    hints: HashMap<String, Vec<String>>,
    feedback: Vec<Value>,
    canceled: Arc<AtomicBool>,
}

impl Agent {
    pub fn from_options(run: &YardbirdOptions) -> anyhow::Result<Option<Self>> {
        let Some(mode) = run.agent.mode else {
            return Ok(None);
        };
        let provider = if mode == AgentMode::Bedrock {
            Some(run.agent.provider()?)
        } else {
            None
        };
        let transport = provider
            .as_ref()
            .map(|p| Box::new(HttpClient::new(p)) as Box<dyn LlmClient + Send>);
        let source = if provider.is_some() {
            std::fs::read_to_string(run.require_filename()?)?
        } else {
            String::new()
        };
        let mut options = run.agent.clone();
        options.resolve_log(
            run.require_filename()?,
            std::path::Path::new(".yardbird/runs"),
        )?;
        let agent = Self::new(options, provider, transport, source)?;
        if let Some(provider) = &agent.provider {
            let trigger = match agent.options.agent_trigger {
                AgentTrigger::Stall => format!(
                    "stall ({}s unresolved at one depth)",
                    agent.options.agent_stall_secs
                ),
                AgentTrigger::Adaptive => "adaptive (LLM assessment at SAT boundaries)".into(),
            };
            log::info!(
                "AGENT model={} trigger={} call_limit={} log={}",
                provider.llm_model.as_deref().unwrap_or_default(),
                trigger,
                if agent.options.agent_max_calls == 0 {
                    "unlimited".into()
                } else {
                    agent.options.agent_max_calls.to_string()
                },
                agent.options.agent_log.as_ref().unwrap().display()
            );
        }
        agent.emit(json!({"event":"starting","mode":mode,"driver":"native",
            "policy":run.policy,"cost_function":run.cost_function,"depth":run.depth,
            "input":run.filename,"options":agent.options}));
        Ok(Some(agent))
    }

    fn new(
        options: AgentOptions,
        provider: Option<LlmOptions>,
        transport: Option<Box<dyn LlmClient + Send>>,
        source: String,
    ) -> anyhow::Result<Self> {
        let log = options
            .agent_log
            .as_ref()
            .map(|p| File::options().write(true).create_new(true).open(p))
            .transpose()?;
        let started = Instant::now();
        let (sender, log_writer) = if let Some(mut file) = log {
            let (tx, rx) = mpsc::channel::<Option<Value>>();
            let writer = std::thread::Builder::new()
                .name("yardbird-agent-log".into())
                .spawn(move || {
                    while let Ok(Some(event)) = rx.recv() {
                        if let Err(e) = serde_json::to_writer(&mut file, &event)
                            .map_err(std::io::Error::other)
                            .and_then(|_| writeln!(file))
                            .and_then(|_| file.flush())
                        {
                            log::warn!("Agent logging failed: {e}");
                            break;
                        }
                    }
                })?;
            (Some(tx), Some(writer))
        } else {
            (None, None)
        };
        Ok(Self {
            options,
            provider,
            transport: transport.map(|t| Arc::new(Mutex::new(t))),
            source: source.into(),
            episode: Default::default(),
            continuation: None,
            flight: None,
            last_capture: None,
            yielded_model: None,
            depth: None,
            episode_depth: None,
            wait_since: None,
            next_assess_step: 0,
            adaptive_ready: false,
            recent_models: Default::default(),
            assessment_statistics: Default::default(),
            last_assessment: Value::Null,
            disabled: false,
            log: EventLog { sender, started },
            log_writer,
            calls: Default::default(),
            replies: 0,
            snapshots: 0,
            polls: 0,
            capture_seconds: 0.0,
            expansion_work: 0,
            hints: HashMap::new(),
            feedback: Vec::new(),
            canceled: Arc::new(AtomicBool::new(false)),
        })
    }

    /// Called before the native solver check. Repeated setup at one depth does not reset age.
    pub(crate) fn enter_depth(&mut self, depth: u16) {
        if self.depth.is_none_or(|(old, _)| old != depth) {
            self.depth = Some((depth, Instant::now()));
            self.wait_since = None;
            self.next_assess_step = 0;
            self.adaptive_ready = false;
            self.recent_models.clear();
            self.assessment_statistics = Default::default();
            self.last_assessment = Value::Null;
        }
    }

    fn stall_elapsed(&self) -> bool {
        self.wait_since
            .or(self.depth.map(|(_, start)| start))
            .is_some_and(|start| {
                start.elapsed() >= Duration::from_secs(self.options.agent_stall_secs)
            })
    }

    fn emit(&self, event: Value) {
        self.log.emit(event);
    }
    fn disable(&mut self, reason: &str) {
        self.disabled = true;
        self.emit(json!({"event":"disabled","reason":reason}));
        log::warn!("Agent disabled: {reason}; native verification continues");
    }

    fn capture(
        &mut self,
        context: &DiscoveryContext<'_>,
        index: Option<&TransitionIndex>,
    ) -> anyhow::Result<Capture> {
        let start = Instant::now();
        let input = SnapshotInput::collect(context, true)?;
        let trace = index
            .filter(|_| self.options.agent_trace_work > 0)
            .map(|index| {
                TraceInput::collect(index.clone(), context, self.options.agent_trace_work)
            });
        let binder_actions = self
            .options
            .agent_binder_context
            .then(|| binders::action_names(index));
        let elapsed = start.elapsed().as_secs_f64();
        self.last_capture = Some(Instant::now());
        self.snapshots += 1;
        self.capture_seconds += elapsed;
        Ok(Capture {
            binder_actions,
            input,
            trace,
            source: self.source.clone(),
            depth: context.depth,
            model: context.model_version,
            elapsed,
        })
    }

    /// Cheap when disabled, no-advice, or inference is still pending. No wait.
    pub(crate) fn poll(
        &mut self,
        context: &DiscoveryContext<'_>,
        index: Option<&TransitionIndex>,
    ) -> Vec<SymbolicInstance> {
        self.polls += 1;
        self.enter_depth(context.depth);
        if self.provider.is_none()
            || self.disabled
            || context.depth < self.options.agent_start_depth
            || context.model_version < self.options.agent_start_model
        {
            return vec![];
        }
        if self.options.agent_trigger == AgentTrigger::Adaptive {
            if self.recent_models.len() == 8 {
                self.recent_models.pop_front();
            }
            self.recent_models
                .push_back(assessment::sample(context, index));
        }
        match self.poll_inner(context, index) {
            Ok(instances) => instances,
            Err(error) => {
                self.disable(&format!("{error:#}"));
                vec![]
            }
        }
    }

    fn poll_inner(
        &mut self,
        context: &DiscoveryContext<'_>,
        index: Option<&TransitionIndex>,
    ) -> anyhow::Result<Vec<SymbolicInstance>> {
        let mut instances = Vec::new();
        if let Some(flight) = &self.flight {
            match flight.receiver.try_recv() {
                Ok(response) => {
                    let assessment = flight.assessment.clone();
                    self.flight = None;
                    let (episode, response) = response?;
                    self.episode = episode;
                    let Some(response) = response else {
                        self.disable("dry_run");
                        return Ok(instances);
                    };
                    self.replies += 1;
                    self.emit(json!({"event":"response","call":self.calls.load(Ordering::Acquire),"live_model":context.model_version,
                        "usage":response["usage"],"response":response}));
                    let (call_id, name, tool) = wire::decode(&response)?;
                    log::info!(
                        "AGENT RESPONSE #{} tool={} usage={}",
                        self.calls.load(Ordering::Acquire),
                        clean(&name),
                        response["usage"]
                    );
                    if let Some((depth, ref epoch)) = assessment {
                        let result = self.assess(tool, context, depth, epoch)?;
                        self.emit(json!({"event":"tool_result","name":name,"live_model":context.model_version,"reply":{"ok":true,"result":result}}));
                    } else {
                        self.episode
                            .history
                            .extend(response["output"].as_array().unwrap().iter().cloned());
                        let reply = self.execute(tool, context, index, &mut instances);
                        let model = context.model_version;
                        let log_reply = |reply: &Value| {
                            self.emit(json!({"event":"tool_result","name":name,"live_model":model,"reply":reply}))
                        };
                        let reply: PrepareReply = match reply {
                            Ok(Reply::Deferred(render)) => Box::new(move |episode, log| {
                                let reply = tool_reply(render(episode, log));
                                log.emit(json!({"event":"tool_result","name":name,"live_model":model,"reply":reply}));
                                Ok(reply)
                            }),
                            result => {
                                let reply = tool_reply(result.map(|r| match r {
                                    Reply::Ready(v) => v,
                                    _ => unreachable!(),
                                }));
                                log_reply(&reply);
                                Box::new(move |_, _| Ok(reply))
                            }
                        };
                        self.continuation = Some(Box::new(move |episode, provider, log| {
                            let value = reply(episode, log)?;
                            episode.history.push(json!({"type":"function_call_output","call_id":call_id,"output":value.to_string()}));
                            Ok(wire::request(provider, &episode.history))
                        }));
                    }
                }
                Err(TryRecvError::Empty) => {
                    if flight.sent_at.get().is_some_and(|start| {
                        start.elapsed() >= Duration::from_secs(self.options.agent_timeout_secs)
                    }) {
                        // Keep the outstanding receiver for final unknown-usage accounting.
                        self.disable("request_timeout; outstanding usage unknown");
                    }
                    return Ok(instances);
                }
                Err(TryRecvError::Disconnected) => anyhow::bail!("agent worker disconnected"),
            }
        }
        // Scheduling another request must never discard a successfully validated hint.
        if let Err(error) = self.schedule(context, index) {
            self.disable(&format!("{error:#}"));
        }
        Ok(instances)
    }

    fn assess(
        &mut self,
        tool: wire::Tool,
        context: &DiscoveryContext<'_>,
        depth: u16,
        epoch: &str,
    ) -> anyhow::Result<Value> {
        let wire::Tool::Assess {
            epoch: received,
            decision,
            reason,
            next_refinements,
        } = tool
        else {
            anyhow::bail!("assessment requires the assess tool");
        };
        anyhow::ensure!(received == epoch, "stale assessment epoch");
        check_rationale(Some(&reason), 2000)?;
        anyhow::ensure!(
            (1..=1024).contains(&next_refinements),
            "next_refinements must be 1..1024"
        );
        if depth != context.depth {
            return Ok(
                json!({"ignored":"depth_closed","observed_depth":depth,"live_depth":context.depth}),
            );
        }
        self.adaptive_ready = matches!(decision, wire::Decision::Advise);
        self.next_assess_step = context.refinement_step.saturating_add(next_refinements);
        let choice = if self.adaptive_ready {
            "advise"
        } else {
            "continue_symbolic"
        };
        log::info!(
            "AGENT ASSESS {} (reassess after {} refinements): {}",
            choice,
            next_refinements,
            clean(&reason)
        );
        self.last_assessment = json!({"decision":choice,"reason":reason,"next_refinements":next_refinements,
            "next_assess_step":self.next_assess_step,"observed_epoch":epoch,"live_model":context.model_version});
        Ok(self.last_assessment.clone())
    }

    fn schedule(
        &mut self,
        context: &DiscoveryContext<'_>,
        index: Option<&TransitionIndex>,
    ) -> anyhow::Result<()> {
        if self.options.agent_max_calls > 0
            && self.calls.load(Ordering::Acquire) >= self.options.agent_max_calls
        {
            self.disable("call_limit");
            return Ok(());
        }
        if self
            .episode_depth
            .is_some_and(|depth| depth != context.depth)
        {
            self.episode.pin = None;
            self.episode.history.clear();
            self.continuation = None;
            self.yielded_model = None;
            self.episode_depth = None;
            self.wait_since = None;
        }
        if let Some(model) = self.yielded_model {
            if model == context.model_version
                || (self.options.agent_trigger == AgentTrigger::Stall
                    && self.last_capture.is_some_and(|t| {
                        t.elapsed() < Duration::from_millis(self.options.agent_interval_ms)
                    }))
            {
                return Ok(());
            }
            self.episode.pin = None;
            self.episode.history.clear();
            self.continuation = None;
            self.yielded_model = None;
        }
        if self.episode.pin.is_none() {
            match self.options.agent_trigger {
                AgentTrigger::Stall if !self.stall_elapsed() => return Ok(()),
                AgentTrigger::Adaptive if !self.adaptive_ready => {
                    if context.refinement_step < self.next_assess_step {
                        return Ok(());
                    }
                    let (request, stats) = assessment::request(
                        context,
                        &self.recent_models,
                        &self.assessment_statistics,
                        &self.last_assessment,
                    );
                    self.assessment_statistics = stats;
                    return self.send(
                        request,
                        context.depth,
                        context.model_version,
                        Some((context.depth, format!("e{}", context.model_version))),
                    );
                }
                _ => {}
            }
            self.adaptive_ready = false;
            let capture = self.capture(context, index)?;
            let feedback = std::mem::take(&mut self.feedback);
            let assessment = self.last_assessment.clone();
            self.episode_depth = Some(context.depth);
            self.continuation = Some(Box::new(move |episode, provider, log| {
                let view = capture.render(episode, log)?;
                episode.history = vec![
                    json!({"role":"developer","content":wire::PROMPT}),
                    json!({"role":"user","content":json!({"context":view,"previous_feedback":feedback,"trigger_assessment":assessment}).to_string()}),
                ];
                Ok(wire::request(provider, &episode.history))
            }));
        }
        if let Some(request) = self.continuation.take() {
            self.send(request, context.depth, context.model_version, None)?;
        }
        Ok(())
    }

    fn send(
        &mut self,
        prepare: PrepareRequest,
        depth: u16,
        model: u64,
        assessment: Option<(u16, String)>,
    ) -> anyhow::Result<()> {
        let provider = self.provider.as_ref().unwrap().clone();
        let transport = self.transport.as_ref().unwrap().clone();
        let canceled = self.canceled.clone();
        let (sender, receiver) = mpsc::sync_channel(1);
        let log = self.log.clone();
        let calls = self.calls.clone();
        let dry_run = self.options.agent_dry_run;
        let max_bytes = self.options.agent_max_request_bytes;
        let kind = if assessment.is_some() {
            "assessment"
        } else {
            "advice"
        };
        let mut episode = std::mem::take(&mut self.episode);
        let sent_at = Arc::new(std::sync::OnceLock::new());
        let worker_sent_at = Arc::clone(&sent_at);
        let run = move || -> anyhow::Result<_> {
            let request = prepare(&mut episode, &provider, &log)?;
            let bytes = serde_json::to_vec(&request)?.len();
            anyhow::ensure!(bytes <= max_bytes, "request_size_limit");
            if dry_run {
                log.emit(json!({"event": "dry_request", "kind": kind, "request": request}));
                return Ok((episode, None));
            }

            let mut transport = transport
                .lock()
                .map_err(|_| anyhow::anyhow!("agent transport lock poisoned"))?;
            anyhow::ensure!(!canceled.load(Ordering::Acquire), "verification finished");
            let _ = worker_sent_at.set(Instant::now());
            let call = calls.fetch_add(1, Ordering::AcqRel) + 1;
            let epoch = episode
                .pin
                .as_ref()
                .map(|pin| pin.epoch.clone())
                .unwrap_or_else(|| format!("e{model}"));
            log::info!("AGENT REQUEST #{call} {kind} at depth {depth} model e{model}");
            log.emit(json!({
                "event":"request", "kind":kind, "call":call,
                "observed_epoch":epoch, "live_model":model, "request":request,
            }));
            let response = transport.infer(&request)?;
            Ok((episode, Some(response)))
        };
        std::thread::Builder::new()
            .name("yardbird-agent".into())
            .spawn(move || {
                let _ = sender.send(run());
            })?;
        self.flight = Some(Flight {
            receiver,
            sent_at,
            assessment,
        });
        Ok(())
    }

    fn execute(
        &mut self,
        tool: wire::Tool,
        context: &DiscoveryContext<'_>,
        index: Option<&TransitionIndex>,
        instances: &mut Vec<SymbolicInstance>,
    ) -> anyhow::Result<Reply> {
        let pin = self
            .episode
            .pin
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("no pinned snapshot"))?;
        anyhow::ensure!(
            tool.epoch() == pin.epoch,
            "stale_snapshot: use pinned epoch {}",
            pin.epoch
        );
        if matches!(tool, wire::Tool::Snapshot { .. }) {
            let capture = self.capture(context, index)?;
            return Ok(Reply::Deferred(Box::new(move |episode, log| {
                capture.render(episode, log)
            })));
        }
        match tool {
            wire::Tool::ReadContext { .. }
            | wire::Tool::Inspect { .. }
            | wire::Tool::MakeTerm { .. } => Ok(Reply::Deferred(Box::new(move |episode, _| {
                let pin = episode.pin.as_mut().unwrap();
                match tool {
                    wire::Tool::ReadContext {
                        section,
                        r#ref,
                        query,
                        offset,
                        limit,
                        ..
                    } => wire::retrieve(
                        &pin.section(&section)?,
                        r#ref.as_deref(),
                        query.as_deref(),
                        offset,
                        limit,
                    ),
                    wire::Tool::Inspect { r#ref, .. } => Ok(
                        json!({"record":pin.records.get(&r#ref).ok_or_else(||anyhow::anyhow!("unknown_ref"))?}),
                    ),
                    wire::Tool::MakeTerm { smt2, .. } => {
                        anyhow::ensure!(smt2.len() <= 16000, "term too large");
                        let term = crate::policy::instantiation::terms::parse(&smt2)?;
                        let ids = episode.catalogue.admit(
                            &mut pin.snapshot,
                            std::slice::from_ref(&term),
                            256,
                        )?;
                        pin.records.extend(records::catalogue(&pin.snapshot));
                        let id = pin
                            .snapshot
                            .terms
                            .iter()
                            .find(|t| t.term == term)
                            .map(|t| t.id.clone());
                        Ok(
                            json!({"term_ref":id,"admitted_refs":ids,"evaluation":"not_evaluated","asserted":false}),
                        )
                    }
                    _ => unreachable!(),
                }
            }))),
            wire::Tool::ExpandAction { r#ref, work, .. } => {
                anyhow::ensure!(
                    pin.epoch == format!("e{}", context.model_version),
                    "snapshot_expired: refresh before live action expansion"
                );
                anyhow::ensure!(
                    work > 0 && work <= 200 && self.expansion_work + work <= 20000,
                    "expansion_limit"
                );
                let (values, used) = pin
                    .observations
                    .as_ref()
                    .ok_or_else(|| anyhow::anyhow!("tracing disabled"))?
                    .expansion_values(&r#ref, work, context)?;
                self.expansion_work += used;
                Ok(Reply::Deferred(Box::new(move |episode, _| {
                    let pin = episode.pin.as_mut().unwrap();
                    let (new, refs, used, cutoff) =
                        pin.observations.as_mut().unwrap().expand_with(
                            &r#ref,
                            work,
                            |term| values[term].clone(),
                            &mut episode.catalogue,
                            &mut pin.snapshot,
                        )?;
                    pin.records.extend(records::catalogue(&pin.snapshot));
                    for r in &new {
                        if let Some(id) = r["id"].as_str() {
                            pin.records.insert(id.into(), r.clone());
                        }
                    }
                    Ok(
                        json!({"records":new,"discovered_refs":refs,"work_used":used,"cutoff":cutoff}),
                    )
                })))
            }
            wire::Tool::Instantiate {
                items, rationale, ..
            } => {
                check_rationale(rationale.as_deref(), 2000)?;
                anyhow::ensure!(
                    !items.is_empty() && items.len() <= 16,
                    "expected 1..16 proposals"
                );
                let mut ids = HashSet::new();
                if let Some(reason) = &rationale {
                    log::info!("AGENT WHY {}", clean(reason));
                }
                let mut feedback = Vec::new();
                for (index, raw) in items.into_iter().enumerate() {
                    let id = raw["proposal_id"].as_str().map(str::to_owned);
                    let resolved = (|| -> anyhow::Result<_> {
                        let item: wire::Item = serde_json::from_value(raw)?;
                        anyhow::ensure!(
                            !item.proposal_id.is_empty() && !ids.contains(&item.proposal_id),
                            "proposal IDs must be nonempty and unique"
                        );
                        check_rationale(item.rationale.as_deref(), 1000)?;
                        let instance = pin.snapshot.resolve_async(&item.proposal)?;
                        ids.insert(item.proposal_id.clone());
                        Ok((item, instance))
                    })();
                    let (item, instance) = match resolved {
                        Ok(pair) => pair,
                        Err(error) => {
                            feedback.push(json!({"index":index,"proposal_id":id,"outcome":"invalid_proposal","error":error.to_string()}));
                            continue;
                        }
                    };
                    let expression = instance.term.to_string();
                    let (mut outcome, accepted) = validate(context, instance);
                    outcome["proposal_id"] = json!(item.proposal_id);
                    outcome["rationale"] = json!(item.rationale);
                    outcome["source_epoch"] = json!(pin.epoch);
                    outcome["evaluated_epoch"] = json!(format!("e{}", context.model_version));
                    if let Some(reason) = &item.rationale {
                        log::info!("AGENT WHY {}: {}", clean(&item.proposal_id), clean(reason));
                    }
                    log::info!(
                        "AGENT REFINE {} {} -> e{}: {}\n  {}",
                        clean(&item.proposal_id),
                        pin.epoch,
                        context.model_version,
                        outcome["outcome"],
                        clean(&expression)
                    );
                    if let Some(instance) = accepted {
                        self.hints
                            .entry(expression)
                            .or_default()
                            .push(item.proposal_id);
                        instances.push(instance);
                    }
                    feedback.push(outcome);
                }
                self.feedback = feedback.clone();
                Ok(Reply::Ready(
                    json!({"source_epoch":pin.epoch,"evaluated_epoch":format!("e{}",context.model_version),"candidates":feedback}),
                ))
            }
            wire::Tool::Yield { reason, .. } => {
                log::info!("AGENT YIELD {}", clean(&reason));
                self.yielded_model = Some(context.model_version);
                self.wait_since = Some(Instant::now());
                self.next_assess_step = context.refinement_step.saturating_add(1);
                Ok(Reply::Ready(
                    json!({"yielded":true,"verification_continues":true}),
                ))
            }
            wire::Tool::Snapshot { .. } => unreachable!(),
            wire::Tool::Assess { .. } => {
                anyhow::bail!("assess is only available during adaptive assessment")
            }
        }
    }

    pub(crate) fn installed(
        &mut self,
        expression: &str,
        result: &crate::instance_installation::request::InstantiationInstallResult,
    ) {
        if let Some(ids) = self.hints.remove(expression) {
            log::info!(
                "AGENT APPLIED {}: new instance={}, assertions={}\n  {}",
                ids.iter().map(|s| clean(s)).collect::<Vec<_>>().join(", "),
                result.abstract_instance_added,
                result.solver_assertions_added(),
                clean(expression)
            );
            self.emit(json!({"event":"installed","proposal_ids":ids,"expression":expression,"installation":result}));
        }
    }

    pub(crate) fn has_pending_hints(&self) -> bool {
        !self.hints.is_empty()
    }
    pub(crate) fn selected(&mut self, expressions: HashSet<String>) {
        let mut dropped = Vec::new();
        self.hints.retain(|expression, ids| {
            if expressions.contains(expression) {
                true
            } else {
                dropped.push(json!({"expression":expression,"proposal_ids":ids}));
                false
            }
        });
        self.emit(json!({"event":"selection","selected":expressions,"not_selected":dropped}));
    }
    pub(crate) fn needs_context(&self) -> bool {
        self.provider.is_some()
    }
}

impl Drop for Agent {
    fn drop(&mut self) {
        self.canceled.store(true, Ordering::Release);
        let mut unknown_usage = false;
        // Never join an in-flight HTTP request or wait for advice to finish.
        if let Some(flight) = self.flight.take() {
            let result = if self.options.agent_dry_run {
                flight
                    .receiver
                    .recv()
                    .map_err(|_| TryRecvError::Disconnected)
            } else {
                flight.receiver.try_recv()
            };
            match result {
                Ok(Ok((_, None))) => {}
                Ok(Ok((_, Some(response)))) => {
                    self.replies += 1;
                    self.emit(json!({"event":"unused_response","usage":response["usage"],"response":response}));
                }
                Ok(Err(error)) if flight.sent_at.get().is_none() => {
                    self.disable(&format!("{error:#}"));
                }
                Err(_) if flight.sent_at.get().is_none() => {
                    self.emit(json!({"event":"canceled_preparation"}));
                }
                other => {
                    unknown_usage = true;
                    self.emit(json!({"event":"outstanding_call","usage":"unknown","completed_error":matches!(other,Ok(Err(_)))}));
                }
            }
        }
        self.emit(
            json!({"event":"finished","calls":self.calls.load(Ordering::Acquire),"replies":self.replies,
            "snapshots":self.snapshots,"polls":self.polls,"capture_seconds":self.capture_seconds,
            "pending_hints":self.hints.len(),"driver":"native"}),
        );
        log::info!(
            "AGENT FINISHED calls={} replies={} snapshots={}{}",
            self.calls.load(Ordering::Acquire),
            self.replies,
            self.snapshots,
            if unknown_usage {
                "; outstanding request usage unknown"
            } else {
                ""
            }
        );
        if let Some(sender) = &self.log.sender {
            let _ = sender.send(None);
        }
        if let Some(writer) = self.log_writer.take() {
            let _ = writer.join();
        }
    }
}
fn tool_reply(result: anyhow::Result<Value>) -> Value {
    match result {
        Ok(result) => json!({"ok":true,"result":result}),
        Err(error) => json!({"ok":false,"error":format!("{error:#}")}),
    }
}
fn clean(s: &str) -> String {
    s.chars()
        .map(|c| if c.is_control() { ' ' } else { c })
        .collect()
}
fn check_rationale(s: Option<&str>, max: usize) -> anyhow::Result<()> {
    anyhow::ensure!(
        s.is_none_or(|s| !s.trim().is_empty() && s.chars().count() <= max),
        "invalid rationale length"
    );
    Ok(())
}
