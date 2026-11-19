use super::records;
use crate::{
    instance_installation::{
        assertion_tracker::canonical_instantiation_key, request::InstantiationInstallResult,
    },
    policy::{
        discovery::DiscoveryContext,
        instantiation::{validate, InstantiationProposal, InstantiationSession},
    },
    problem_context::ProblemContext,
    rule_matching::candidate::SymbolicInstance,
    YardbirdOptions,
};
use anyhow::Context;
use serde::Deserialize;
use serde_json::{json, Value};
use std::{
    collections::{HashMap, HashSet},
    fs::{File, OpenOptions},
    io::{BufRead, BufReader, Read, Write},
    sync::mpsc::{self, Receiver},
    time::{Duration, Instant},
};

const CAPABILITIES: &[&str] = &[
    "snapshot",
    "inspect",
    "expand_action",
    "make_term",
    "instantiate",
    "advance",
    "stop",
];
const MAX_LINE: usize = 65536;
const MAX_RESPONSE: usize = 16 * 1024 * 1024;

#[derive(Deserialize)]
#[serde(tag = "op", rename_all = "snake_case", deny_unknown_fields)]
enum Tool {
    Snapshot {},
    MakeTerm { smt2: String },
    ExpandAction { r#ref: String, work: usize },
    Search { operations: usize },
    Inspect { r#ref: String },
    Instantiate { items: Vec<Value> },
    Advance { solver_timeout_ms: u32 },
    Stop {},
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Item {
    proposal_id: String,
    proposal: InstantiationProposal,
}

struct Queued {
    key: String,
    instance: SymbolicInstance,
    report: Value,
}

struct SearchTurn {
    command: Value,
    remaining: usize,
    operations: Vec<Value>,
    reason: String,
}

pub(super) struct Session {
    pub(super) index: Option<crate::transition_index::TransitionIndex>,
    pub(super) admitted: Vec<smt2parser::concrete::Term>,
    observations: Option<super::observations::Observations>,
    searching: Option<SearchTurn>,
    searched: Vec<(String, Value)>,
    capabilities: Vec<String>,
    limits: super::AgentOptions,
    expansion_work: usize,
    search_work: usize,
    input: Receiver<std::io::Result<String>>,
    output: Box<dyn Write + Send>,
    log: Option<File>,
    source: String,
    catalogue: InstantiationSession,
    cache: HashMap<String, (Value, Value)>,
    epoch: String,
    paused: Value,
    queued: Vec<Queued>,
    proposal_ids: HashSet<String>,
    reports: Vec<(String, Value)>,
    advancing: Option<Value>,
    events: Vec<Value>,
    checks: u64,
    advance_checks: u64,
    commands: usize,
    started: Instant,
    command_started: Instant,
    configuration: Value,
    wall: Duration,
    stats: Value,
    advance_stats: Value,
    advance_stats_before: Option<crate::utils::SolverStatistics>,
    pub(super) solver_timeout_ms: u32,
    pub(super) terminated: bool,
    pub(super) ever_paused: bool,
}

impl Session {
    pub(super) fn record_assertions(&mut self, smt2: &str) {
        self.configuration["assertions_hash"] = json!(digest(smt2.as_bytes()));
    }
    pub(super) fn stdio(options: &YardbirdOptions) -> anyhow::Result<Self> {
        let source = std::fs::read_to_string(options.require_filename()?)?;
        let log = options
            .agent
            .agent_log
            .as_ref()
            .map(|p| OpenOptions::new().write(true).create_new(true).open(p))
            .transpose()?;
        let (tx, input) = mpsc::sync_channel(1);
        std::thread::spawn(move || {
            let mut reader = BufReader::new(std::io::stdin());
            loop {
                let mut bytes = Vec::new();
                let result = reader
                    .by_ref()
                    .take((MAX_LINE + 1) as u64)
                    .read_until(b'\n', &mut bytes);
                let line = match result {
                    Ok(0) => break,
                    Ok(_) if bytes.len() > MAX_LINE => Err(std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        "command exceeds 64 KiB",
                    )),
                    Ok(_) => String::from_utf8(bytes)
                        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e)),
                    Err(e) => Err(e),
                };
                let failed = line.is_err();
                if tx.send(line).is_err() || failed {
                    break;
                }
            }
        });
        let mut capabilities = CAPABILITIES
            .iter()
            .map(|s| s.to_string())
            .collect::<Vec<_>>();
        if options.agent.agent_control == "assisted" {
            capabilities.push("search".into());
        }
        let mut s = Self {
            index: None,
            admitted: vec![],
            observations: None,
            searching: None,
            searched: vec![],
            capabilities,
            limits: options.agent.clone(),
            expansion_work: 0,
            search_work: 0,
            input,
            output: Box::new(std::io::stdout()),
            log,
            source,
            catalogue: Default::default(),
            cache: HashMap::new(),
            epoch: String::new(),
            paused: Value::Null,
            queued: vec![],
            proposal_ids: HashSet::new(),
            reports: vec![],
            advancing: None,
            events: vec![],
            checks: 0,
            advance_checks: 0,
            commands: 0,
            started: Instant::now(),
            command_started: Instant::now(),
            configuration: json!({"requested":options,"effective":{"term_cost":"bmc-cost","ranker":"term-cost","installation":"full-unroll","property_check":"assumptions","candidate_winners":64,"control":options.agent.agent_control}}),
            wall: Duration::from_secs(options.wall_timeout_secs.unwrap_or(120)),
            stats: Value::Null,
            advance_stats: Value::Null,
            advance_stats_before: None,
            solver_timeout_ms: options.agent.agent_solver_timeout_ms,
            terminated: false,
            ever_paused: false,
        };
        let config = serde_json::to_vec(&s.configuration)?;
        s.emit(json!({"v":0,"event":"ready","run_id":format!("agent-{}",std::process::id()),"capabilities":s.capabilities,"limits":{"commands":s.limits.agent_max_commands,"wall_ms":s.wall.as_millis(),"batch":16,"pending":s.limits.agent_max_pending,"command_bytes":MAX_LINE,"response_bytes":MAX_RESPONSE,"solver_timeout_ms":s.limits.agent_solver_timeout_ms,"expand_action_work":s.limits.agent_expand_action_work,"expansion_work":s.limits.agent_expansion_work,"search_operations":s.limits.agent_search_operations,"term_nodes":256},"input_hash":digest(s.source.as_bytes()),"build_id":digest_file(std::env::current_exe()?)?,"config_hash":digest(&config)}))?;
        Ok(s)
    }
    pub(super) fn expired(&self) -> bool {
        self.started.elapsed() >= self.wall
    }
    pub(super) fn check_timeout_ms(&self) -> u32 {
        let remaining = self.wall.saturating_sub(self.started.elapsed());
        remaining
            .as_millis()
            .clamp(1, u128::from(self.solver_timeout_ms)) as u32
    }
    fn emit(&mut self, message: Value) -> anyhow::Result<()> {
        let bytes = serde_json::to_vec(&message)?;
        anyhow::ensure!(
            bytes.len() <= MAX_RESPONSE,
            "protocol response exceeds limit"
        );
        self.output.write_all(&bytes)?;
        self.output.write_all(b"\n")?;
        self.output.flush()?;
        self.log_message("server", &message)
    }
    fn log_message(&mut self, direction: &str, message: &Value) -> anyhow::Result<()> {
        if let Some(log) = &mut self.log {
            serde_json::to_writer(
                &mut *log,
                &json!({"direction":direction,"message":message,"elapsed_ms":self.started.elapsed().as_millis()}),
            )?;
            writeln!(log)?;
            log.flush()?;
        }
        Ok(())
    }
    fn respond(&mut self, command: &Value, mut result: Value) -> anyhow::Result<()> {
        if command["op"] != "snapshot" {
            result["usage"]["elapsed_ms"] = json!(self.command_started.elapsed().as_millis());
        }
        let epoch = if self.terminated {
            Value::Null
        } else {
            json!(self.epoch)
        };
        let mut response = json!({"v":0,"id":command["id"],"op":command["op"],"ok":true,"epoch":epoch,"result":result});
        if serde_json::to_vec(&response)?.len() > MAX_RESPONSE {
            response = self.error_message(
                command,
                "response_too_large",
                "response exceeds configured limit",
            );
        }
        self.cache.insert(
            command["id"].as_str().unwrap().into(),
            (command.clone(), response.clone()),
        );
        self.emit(response)
    }
    fn error_message(&self, c: &Value, code: &str, message: &str) -> Value {
        json!({"v":0,"id":c["id"].as_str(),"op":c["op"].as_str(),"ok":false,"epoch":if self.epoch.is_empty() || self.terminated {Value::Null} else {json!(self.epoch)},"error":{"code":code,"message":message,"details":{}}})
    }
    fn error(&mut self, c: &Value, code: &str, message: &str) -> anyhow::Result<()> {
        let response = self.error_message(c, code, message);
        if let Some(id) = c["id"].as_str() {
            self.cache
                .entry(id.into())
                .or_insert((c.clone(), response.clone()));
        }
        self.emit(response)
    }
    pub(super) fn checked(&mut self, smt: &dyn ProblemContext) {
        self.checks += 1;
        let statistics = smt.get_solver_statistics();
        self.stats = statistics.to_json_value();
        if let Some(before) = &self.advance_stats_before {
            self.advance_stats = statistics.delta_since(before);
        }
        if self.advancing.is_some() {
            self.advance_checks += 1;
        }
    }
    pub(super) fn depth_closed(&mut self, depth: u16) {
        if self.advancing.is_some() {
            self.events
                .push(json!({"event":"depth_closed","depth":depth}));
        }
    }
    pub(super) fn installed(&mut self, key: &str, result: InstantiationInstallResult) {
        for (i, (candidate_key, report)) in self.reports.iter_mut().enumerate() {
            if candidate_key == key {
                report["selection"] = json!("selected");
                report["installation_id"] = json!(format!("{}:install:{i}", self.epoch));
                report["installation"] = serde_json::to_value(result).unwrap();
            }
        }
    }
    fn advance_result(&mut self, outcome: &str, paused: Value) -> Value {
        let reports = std::mem::take(&mut self.reports)
            .into_iter()
            .map(|(_, mut r)| {
                if r["selection"] == "pending" {
                    r["selection"] = json!("not_selected");
                }
                r
            })
            .collect::<Vec<_>>();
        let mut usage = records::usage(self.advance_checks);
        usage["solver_statistics"] = self.advance_stats.clone();
        json!({"outcome":outcome,"events":std::mem::take(&mut self.events),"paused":paused,"candidates":reports,"usage":usage})
    }
    pub(super) fn no_progress(&mut self) -> anyhow::Result<()> {
        if let Some(command) = self.advancing.take() {
            let result = self.advance_result("no_progress", self.paused.clone());
            self.respond(&command, result)?;
        }
        Ok(())
    }
    pub(super) fn terminate(&mut self, reason: &str) -> anyhow::Result<()> {
        if self.terminated {
            return Ok(());
        }
        self.terminated = true;
        if let Some(turn) = self.searching.take() {
            self.error(&turn.command, "internal_error", reason)?;
        }
        if let Some(command) = self.advancing.take() {
            let result = self.advance_result(reason, Value::Null);
            self.respond(&command, result)?;
        }
        let mut usage = records::usage(self.checks);
        usage["elapsed_ms"] = json!(self.started.elapsed().as_millis());
        usage["solver_statistics"] = self.stats.clone();
        self.emit(json!({"v":0,"event":"terminal","reason":reason,"usage":usage}))
    }

    pub(super) fn interact(
        &mut self,
        context: &DiscoveryContext<'_>,
    ) -> anyhow::Result<Vec<SymbolicInstance>> {
        let mut snapshot = self.catalogue.capture(context, &self.source)?;
        let new_epoch = format!("e{}", self.checks);
        let changed = self.epoch != new_epoch;
        self.epoch = new_epoch;
        if changed {
            self.observations = self
                .index
                .clone()
                .map(|index| {
                    super::observations::Observations::new(
                        index,
                        context,
                        &self.epoch,
                        &mut self.catalogue,
                        &mut snapshot,
                    )
                })
                .transpose()?;
        }
        let mut records = records::catalogue(&snapshot);
        if let Some(observations) = &self.observations {
            records.extend(observations.records.clone());
        }
        self.paused = json!({"epoch":self.epoch,"depth":context.depth,"refinement_step":context.refinement_step,"model_version":self.checks,"roots":self.observations.as_ref().map(|o|o.roots.clone()).unwrap_or_default()});
        if changed {
            self.proposal_ids.clear();
        }
        if let Some(command) = self.advancing.take() {
            let result = self.advance_result("sat", self.paused.clone());
            self.respond(&command, result)?;
        } else if !self.ever_paused {
            self.emit(json!({"v":0,"event":"paused","paused":self.paused}))?;
        }
        self.ever_paused = true;
        if let Some(turn) = self.searching.take() {
            let mut usage = records::usage(0);
            usage["search_operations"] = json!(turn.operations.len());
            let result = json!({"candidates":self.searched.iter().map(|(_,r)|r).collect::<Vec<_>>(),"records":records.values().collect::<Vec<_>>(),"pending_ids":self.pending_ids(),"operations":turn.operations,"cutoff":turn.reason=="operation_limit" || turn.reason=="pending_limit","stop_reason":turn.reason,"usage":usage});
            self.respond(&turn.command, result)?;
        }
        loop {
            if self.expired() || self.commands >= self.limits.agent_max_commands {
                self.terminate("timeout")?;
                anyhow::bail!("agent budget exhausted");
            }
            let remaining = self.wall.saturating_sub(self.started.elapsed());
            let line = match self.input.recv_timeout(remaining) {
                Ok(Ok(line)) => line,
                Ok(Err(error)) => {
                    self.error(&Value::Null, "limit_exceeded", &error.to_string())?;
                    self.terminate("internal_error")?;
                    anyhow::bail!("invalid input stream");
                }
                Err(mpsc::RecvTimeoutError::Timeout) => {
                    self.terminate("timeout")?;
                    anyhow::bail!("agent timeout");
                }
                Err(_) => {
                    self.terminate("eof")?;
                    anyhow::bail!("agent disconnected");
                }
            };
            self.commands += 1;
            self.command_started = Instant::now();
            let command: Value = match serde_json::from_str(&line) {
                Ok(v) => v,
                Err(e) => {
                    self.error(&Value::Null, "invalid_json", &e.to_string())?;
                    continue;
                }
            };
            self.log_message("client", &command)?;
            if let Some((old, response)) = command["id"].as_str().and_then(|id| self.cache.get(id))
            {
                if old == &command {
                    let response = response.clone();
                    self.emit(response)?;
                } else {
                    self.error(&command, "id_conflict", "command ID already used")?;
                }
                continue;
            }
            if command["v"] != 0
                || command["id"].as_str().is_none_or(str::is_empty)
                || command["epoch"].as_str().is_none_or(str::is_empty)
            {
                self.error(
                    &command,
                    "invalid_command",
                    "expected v=0, nonempty id and epoch",
                )?;
                continue;
            }
            if command["epoch"] != self.epoch {
                self.error(&command, "stale_epoch", "epoch is no longer active")?;
                continue;
            }
            let mut body = command.clone();
            for key in ["v", "id", "epoch"] {
                body.as_object_mut().unwrap().remove(key);
            }
            let tool: Tool = match serde_json::from_value(body) {
                Ok(t) => t,
                Err(e) => {
                    self.error(&command, "invalid_command", &e.to_string())?;
                    continue;
                }
            };
            match tool {
                Tool::Search { operations } => {
                    if !self.capabilities.iter().any(|c| c == "search") {
                        self.error(
                            &command,
                            "unsupported",
                            "search is disabled in explicit mode",
                        )?;
                        continue;
                    }
                    if operations == 0 || operations > self.limits.agent_search_operations {
                        self.error(
                            &command,
                            "limit_exceeded",
                            "search operations exceed the advertised allowance",
                        )?;
                        continue;
                    }
                    self.admitted
                        .extend(snapshot.terms.iter().map(|t| t.term.clone()));
                    self.searching = Some(SearchTurn {
                        command,
                        remaining: operations,
                        operations: vec![],
                        reason: "operation_limit".into(),
                    });
                    return Ok(vec![]);
                }
                Tool::MakeTerm { smt2 } => {
                    let parsed = crate::policy::instantiation::terms::parse(&smt2);
                    let term = match parsed {
                        Ok(t) => t,
                        Err(e) => {
                            self.error(&command, "invalid_command", &e.to_string())?;
                            continue;
                        }
                    };
                    match self
                        .catalogue
                        .admit(&mut snapshot, std::slice::from_ref(&term), 256)
                    {
                        Ok(ids) => {
                            self.admitted.push(term.clone());
                            records.extend(records::catalogue(&snapshot));
                            let tid = snapshot
                                .terms
                                .iter()
                                .find(|t| t.expression == term.to_string())
                                .unwrap()
                                .id
                                .clone();
                            let mut returned =
                                ids.iter().map(|id| records[id].clone()).collect::<Vec<_>>();
                            if !ids.contains(&tid) {
                                returned.push(records[&tid].clone());
                            }
                            self.respond(&command,json!({"term_ref":tid,"records":returned,"usage":records::usage(0)}))?;
                        }
                        Err(e) => {
                            let code = if e.to_string().contains("budget") {
                                "limit_exceeded"
                            } else {
                                "sort_error"
                            };
                            self.error(&command, code, &e.to_string())?;
                        }
                    }
                }
                Tool::ExpandAction { r#ref, work } => {
                    if work == 0
                        || work > self.limits.agent_expand_action_work
                        || work
                            > self
                                .limits
                                .agent_expansion_work
                                .saturating_sub(self.expansion_work)
                    {
                        self.error(
                            &command,
                            "limit_exceeded",
                            "expansion exceeds work allowance",
                        )?;
                        continue;
                    }
                    let Some(observations) = &mut self.observations else {
                        self.error(&command, "unknown_ref", "no action observations available")?;
                        continue;
                    };
                    match observations.expand(
                        &r#ref,
                        work,
                        context,
                        &mut self.catalogue,
                        &mut snapshot,
                    ) {
                        Ok((mut returned, refs, used, cutoff)) => {
                            self.expansion_work += used;
                            let vocabulary = records::catalogue(&snapshot);
                            returned.extend(vocabulary.values().cloned());
                            records.extend(vocabulary);
                            records.extend(observations.records.clone());
                            let mut usage = records::usage(0);
                            usage["expansion_work"] = json!(used);
                            self.respond(&command,json!({"records":returned,"discovered_refs":refs,"work_used":used,"cutoff":cutoff,"usage":usage}))?;
                        }
                        Err(e) => self.error(&command, "unknown_ref", &e.to_string())?,
                    }
                }
                Tool::Snapshot {} => {
                    let mut usage = records::usage(self.checks);
                    usage["elapsed_ms"] = json!(self.started.elapsed().as_millis());
                    usage["solver_statistics"] = self.stats.clone();
                    usage["search_operations"] = json!(self.search_work);
                    usage["expansion_work"] = json!(self.expansion_work);
                    self.respond(&command,json!({"shared_snapshot":({let mut value=snapshot.state(); value["agent_configuration"]=self.configuration.clone(); value}),"records":records.values().collect::<Vec<_>>(),"paused":self.paused,"capabilities":self.capabilities,"pending_ids":self.pending_ids(),"usage":usage}))?;
                }
                Tool::Inspect { r#ref } => {
                    if let Some(record) = records.get(&r#ref) {
                        self.respond(&command, json!({"record":record,"usage":records::usage(0)}))?;
                    } else {
                        self.error(
                            &command,
                            "unknown_ref",
                            "reference is not in the current catalogue",
                        )?;
                    }
                }
                Tool::Instantiate { items } => {
                    if items.is_empty() || items.len() > 16 {
                        self.error(&command, "limit_exceeded", "expected 1..16 proposals")?;
                        continue;
                    }
                    let mut rejections = Vec::new();
                    let mut added = Vec::new();
                    let mut reports = vec![];
                    let mut pending = context.pending.clone();
                    for q in &self.queued {
                        if let Some(i) = context
                            .smt
                            .make_unquantified_instance(q.instance.term.clone())
                        {
                            pending.insert(canonical_instantiation_key(i.get_term()));
                        }
                    }
                    for (index, raw) in items.into_iter().enumerate() {
                        let id = raw["proposal_id"].as_str().map(str::to_owned);
                        let resolved = (|| -> anyhow::Result<_> {
                            let item: Item = serde_json::from_value(raw)?;
                            anyhow::ensure!(
                                !item.proposal_id.is_empty()
                                    && !self.proposal_ids.contains(&item.proposal_id),
                                "proposal ID must be new and nonempty"
                            );
                            let instance = snapshot.resolve(&item.proposal)?;
                            let ids = self.catalogue.admit(
                                &mut snapshot,
                                std::slice::from_ref(&instance.term),
                                4096,
                            )?;
                            Ok((item, instance, ids))
                        })();
                        let (item, instance, ids) = match resolved {
                            Ok(item) => item,
                            Err(error) => {
                                rejections.push(json!({"index":index,"proposal_id":id,"error":error.to_string()}));
                                continue;
                            }
                        };
                        self.proposal_ids.insert(item.proposal_id.clone());
                        added.extend(ids);
                        self.admitted.push(instance.term.clone());
                        let expression = instance.term.to_string();
                        let ctx = DiscoveryContext {
                            pending: &pending,
                            ..*context
                        };
                        let (feedback, accepted) = validate(&ctx, instance);
                        if accepted.is_some()
                            && self.queued.len() + self.searched.len()
                                >= self.limits.agent_max_pending
                        {
                            rejections.push(json!({"index":index,"proposal_id":item.proposal_id,"error":"pending limit reached"}));
                            continue;
                        }
                        let id = accepted.as_ref().map(|_| {
                            format!("{}:candidate:{}", self.epoch, self.proposal_ids.len())
                        });
                        let report = json!({"candidate_id":id,"proposal_ids":[item.proposal_id],"search_command_ids":[],"expression":expression,"construction":"constructed","validation":feedback["outcome"],"reason":feedback["reason"],"observations":feedback["observations"].as_object().cloned().unwrap_or_default(),"term_refs":item.proposal.bindings.values().collect::<Vec<_>>(),"selection":if accepted.is_some(){"pending"}else{"not_eligible"},"installation_id":null,"installation":null,"installation_error":null});
                        if let Some(instance) = accepted {
                            let normalized = context
                                .smt
                                .make_unquantified_instance(instance.term.clone())
                                .context("validated instance no longer normalizes")?;
                            let key = canonical_instantiation_key(normalized.get_term());
                            pending.insert(key.clone());
                            self.queued.push(Queued {
                                key: key.to_string(),
                                instance,
                                report: report.clone(),
                            });
                        }
                        reports.push(report);
                    }
                    records.extend(records::catalogue(&snapshot));
                    let returned: Vec<_> = added.iter().map(|id| &records[id]).collect();
                    self.respond(&command,json!({"candidates":reports,"rejections":rejections,"records":returned,"pending_ids":self.pending_ids(),"usage":records::usage(0)}))?;
                }
                Tool::Advance { solver_timeout_ms } => {
                    if solver_timeout_ms == 0
                        || solver_timeout_ms > self.limits.agent_solver_timeout_ms
                    {
                        self.error(
                            &command,
                            "limit_exceeded",
                            "solver timeout exceeds the advertised allowance",
                        )?;
                        continue;
                    }
                    self.solver_timeout_ms = solver_timeout_ms;
                    self.advance_checks = 0;
                    self.advance_stats = Value::Null;
                    self.advance_stats_before = Some(context.smt.get_solver_statistics());
                    if self.queued.is_empty() && self.searched.is_empty() {
                        let result = self.advance_result("no_progress", self.paused.clone());
                        self.respond(&command, result)?;
                        continue;
                    }
                    self.admitted
                        .extend(snapshot.terms.iter().map(|t| t.term.clone()));
                    self.advancing = Some(command);
                    self.reports.append(&mut self.searched);
                    let mut instances = vec![];
                    for q in self.queued.drain(..) {
                        self.reports.push((q.key, q.report));
                        instances.push(q.instance);
                    }
                    return Ok(instances);
                }
                Tool::Stop {} => {
                    self.terminated = true;
                    self.respond(&command,json!({"outcome":"stopped","pending_ids":self.pending_ids(),"usage":records::usage(0)}))?;
                    self.terminated = false;
                    self.terminate("stopped")?;
                    anyhow::bail!("agent stopped");
                }
            }
        }
    }
    pub(super) fn is_advancing(&self) -> bool {
        // After the check, re-enter discovery to publish the new model/epoch.
        self.advancing.is_some() && self.advance_checks == 0
    }
    pub(super) fn candidate_capacity(&self) -> usize {
        self.limits
            .agent_max_pending
            .saturating_sub(self.queued.len())
    }
    pub(super) fn search_remaining(&self) -> usize {
        self.searching.as_ref().map(|s| s.remaining).unwrap_or(0)
    }
    pub(super) fn end_search(&mut self, reason: &str) {
        if let Some(s) = &mut self.searching {
            s.remaining = 0;
            s.reason = reason.into();
        }
    }
    pub(super) fn observe_search(
        &mut self,
        kind: crate::policy::effort::OperationKind,
        report: &crate::policy::effort::WorkReport,
        candidates: &[crate::rule_matching::candidate::InstantiationCandidate],
        smt: &dyn ProblemContext,
    ) -> anyhow::Result<()> {
        if kind == crate::policy::effort::OperationKind::PolicyCandidates {
            return Ok(());
        }
        let Some(turn) = &mut self.searching else {
            return Ok(());
        };
        turn.remaining = turn.remaining.saturating_sub(1);
        self.search_work += 1;
        turn.operations.push(json!({"name":format!("{kind:?}"),"work":{"examined_substitutions":report.examined_substitutions,"dependency_work":report.dependency_work,"vocabulary_work":report.vocabulary_work,"candidates_returned":report.candidates_returned,"selected":report.selected}}));
        for candidate in candidates {
            let term = crate::terms::language::expr_to_term(candidate.expression.clone());
            let Some(normalized) = smt.make_unquantified_instance(term.clone()) else {
                continue;
            };
            let key = canonical_instantiation_key(normalized.get_term()).to_string();
            if self.searched.iter().any(|(k, _)| k == &key) {
                continue;
            }
            if let Some(position) = self.queued.iter().position(|q| q.key == key) {
                let mut queued = self.queued.remove(position);
                queued.report["search_command_ids"] = json!([turn.command["id"]]);
                self.searched.push((key, queued.report));
                continue;
            }
            let id = format!("{}:search:{}", self.epoch, self.searched.len());
            self.searched.push((key,json!({"candidate_id":id,"proposal_ids":[],"search_command_ids":[turn.command["id"]],"expression":term.to_string(),"construction":"constructed","validation":"violated","reason":null,"observations":{},"term_refs":[],"selection":"pending","installation_id":null,"installation":null,"installation_error":null})));
        }
        if self.searched.len() + self.queued.len() >= self.limits.agent_max_pending {
            turn.remaining = 0;
            turn.reason = "pending_limit".into();
        }
        Ok(())
    }

    fn pending_ids(&self) -> Vec<Value> {
        self.queued
            .iter()
            .map(|q| q.report["candidate_id"].clone())
            .chain(self.searched.iter().map(|(_, r)| r["candidate_id"].clone()))
            .collect()
    }
}

fn digest(bytes: &[u8]) -> String {
    let mut h = 0xcbf29ce484222325u64;
    for b in bytes {
        h = (h ^ u64::from(*b)).wrapping_mul(0x100000001b3);
    }
    format!("fnv1a64:{h:016x}")
}
fn digest_file(path: std::path::PathBuf) -> anyhow::Result<String> {
    Ok(digest(&std::fs::read(path)?))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn tools_are_closed_and_advance_cannot_hide_search() {
        assert!(
            serde_json::from_value::<Tool>(json!({"op":"advance","solver_timeout_ms":100})).is_ok()
        );
        assert!(serde_json::from_value::<Item>(
            json!({"proposal_id":"x","proposal":{"axiom_id":"q","bindings":{},"formula":"false"}})
        )
        .is_err());
        for value in [
            json!({"op":"advance","solver_timeout_ms":100,"search_ops":1}),
            json!({"op":"resume","solver_timeout_ms":100,"search_ops":0}),
            json!({"op":"advance","solver_timeout_ms":-1}),
            json!({"op":"advance","solver_timeout_ms":true}),
            json!({"op":"snapshot","extra":true}),
        ] {
            assert!(
                serde_json::from_value::<Tool>(value.clone()).is_err(),
                "{value}"
            );
        }
    }
}
