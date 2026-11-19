use super::*;
use crate::{
    strategies::{ProofStrategyExt, RefinementState},
    Driver,
};
use std::sync::atomic::{AtomicUsize, Ordering};

fn response(name: &str, args: Value) -> Value {
    json!({"status":"completed","output":[{"type":"function_call","call_id":"fake-call",
        "name":name,"arguments":args.to_string()}],"usage":{"input_tokens":100,"output_tokens":20}})
}

struct Progress(Arc<AtomicUsize>);
impl ProofStrategyExt<RefinementState> for Progress {
    fn sat(
        &mut self,
        _: &mut RefinementState,
        _: &dyn crate::problem_context::ProblemContext,
        _: u32,
    ) -> anyhow::Result<()> {
        self.0.fetch_add(1, Ordering::SeqCst);
        Ok(())
    }
}

struct DelayedTools {
    progress: Arc<AtomicUsize>,
    calls: usize,
    epoch: String,
    schema: Option<String>,
}
impl LlmClient for DelayedTools {
    fn infer(&mut self, request: &Value) -> anyhow::Result<Value> {
        self.calls += 1;
        if self.calls == 1 {
            let initial: Value =
                serde_json::from_str(request["input"][1]["content"].as_str().unwrap())?;
            self.epoch = initial["context"]["epoch"].as_str().unwrap().into();
            let start = Instant::now();
            while self.progress.load(Ordering::SeqCst) < 4
                && start.elapsed() < Duration::from_secs(3)
            {
                std::thread::sleep(Duration::from_millis(1));
            }
            anyhow::ensure!(
                self.progress.load(Ordering::SeqCst) >= 4,
                "native driver blocked during inference"
            );
            return Ok(response(
                "read_context",
                json!({"epoch":self.epoch,"section":"axioms","query":"(p31 variable_0)"}),
            ));
        }
        let feedback: Value = serde_json::from_str(
            request["input"].as_array().unwrap().last().unwrap()["output"]
                .as_str()
                .unwrap(),
        )?;
        anyhow::ensure!(feedback["ok"] == true, "tool failed: {feedback}");
        if self.calls == 2 {
            self.schema = Some(
                feedback["result"]["items"][0]["id"]
                    .as_str()
                    .unwrap()
                    .into(),
            );
            return Ok(response(
                "read_context",
                json!({"epoch":self.epoch,"section":"terms","query":"\"expression\":\"0\""}),
            ));
        }
        if self.calls == 3 {
            let term = feedback["result"]["items"]
                .as_array()
                .unwrap()
                .iter()
                .find(|t| t["expression"] == "0")
                .unwrap();
            return Ok(response(
                "instantiate",
                json!({"epoch":self.epoch,"rationale":"Supply the missing final universal fact while native search handles the other conjuncts.","items":[{
                "proposal_id":"late-p31","proposal":{"axiom_id":self.schema,"bindings":{"variable_0":term["id"]}}}]}),
            ));
        }
        Ok(response(
            "yield",
            json!({"epoch":self.epoch,"reason":"Native search can finish."}),
        ))
    }
}

fn fixture(root: &std::path::Path, count: usize) -> std::path::PathBuf {
    let path = root.join("facts.vmt");
    let declarations = (0..count)
        .map(|i| format!("(declare-fun p{i} (Int) Bool)\n"))
        .collect::<String>();
    let init = (0..count)
        .map(|i| format!("(forall ((x Int)) (p{i} x))"))
        .collect::<Vec<_>>()
        .join(" ");
    let prop = (0..count)
        .map(|i| format!("(p{i} 0)"))
        .collect::<Vec<_>>()
        .join(" ");
    std::fs::write(&path,format!("{declarations}(define-fun init () Bool (! (and {init}) :init true))\n(define-fun trans () Bool (! true :trans true))\n(define-fun prop () Bool (! (and {prop}) :invar-property 0))\n")).unwrap();
    path
}

fn run_fake(
    root: &std::path::Path,
    transport: Box<dyn LlmClient + Send>,
    count: usize,
    max_calls: usize,
    progress: Arc<AtomicUsize>,
) -> crate::ProofLoopResult {
    run_fake_options(
        root,
        transport,
        count,
        max_calls,
        progress,
        AgentOptions {
            agent_stall_secs: 0,
            ..Default::default()
        },
    )
}

fn run_fake_options(
    root: &std::path::Path,
    transport: Box<dyn LlmClient + Send>,
    count: usize,
    max_calls: usize,
    progress: Arc<AtomicUsize>,
    base: AgentOptions,
) -> crate::ProofLoopResult {
    let path = fixture(root, count);
    let run = YardbirdOptions {
        filename: Some(path.to_str().unwrap().into()),
        depth: 1,
        ..Default::default()
    };
    let options = AgentOptions {
        mode: Some(AgentMode::Bedrock),
        agent_start_depth: 0,
        agent_trace_work: 0,
        agent_interval_ms: 0,
        agent_max_calls: max_calls,
        agent_log: Some(root.join("events.jsonl")),
        ..base
    };
    let provider = LlmOptions {
        llm_model: Some("fake".into()),
        ..Default::default()
    };
    let agent = NativeAgent::new(
        options,
        Some(provider),
        Some(transport),
        std::fs::read_to_string(path).unwrap(),
    )
    .unwrap();
    let mut plan = run.build_array_proof_plan();
    plan.strategy.attach_agent(agent).unwrap();
    let mut driver = Driver::new(
        crate::model_from_options(&run),
        plan.instantiation_strategy,
        plan.solver,
    )
    .with_wall_timeout(Some(Duration::from_secs(20)));
    driver.add_extension(Progress(progress));
    driver.check_strategy(1, plan.strategy).unwrap()
}
fn events(root: &std::path::Path) -> Vec<Value> {
    std::fs::read_to_string(root.join("events.jsonl"))
        .unwrap()
        .lines()
        .map(|l| serde_json::from_str(l).unwrap())
        .collect()
}

#[test]
fn exact_command_defaults_resolve_embedded_config_and_unique_logs() {
    use clap::Parser;
    let mut run = YardbirdOptions::try_parse_from([
        "yardbird",
        "-f",
        "examples/distributed_protocols/german/german.encoding.vmt",
        "--policy",
        "german-fast",
        "-d",
        "20",
        "--wall-timeout-secs",
        "500",
        "--agent",
        "bedrock",
    ])
    .unwrap();
    assert_eq!(run.agent.agent_stall_secs, 5);
    assert_eq!(run.agent.agent_max_calls, 0);
    assert_eq!(run.agent.agent_start_depth, 0);
    assert_eq!(run.agent.agent_trigger, AgentTrigger::Stall);
    assert!(run.agent.agent_config.is_none());
    assert!(run.agent.agent_log.is_none());
    assert_eq!(
        run.agent.provider().unwrap().llm_model.as_deref(),
        Some("openai.gpt-5.5")
    );
    // Exercise all configuration validation without requiring credentials or HTTP.
    run.agent.agent_dry_run = true;
    run.agent.validate(&run).unwrap();
    let root = tempfile::tempdir().unwrap();
    let mut other = run.agent.clone();
    run.agent
        .resolve_log(run.filename.as_deref().unwrap(), root.path())
        .unwrap();
    other
        .resolve_log(run.filename.as_deref().unwrap(), root.path())
        .unwrap();
    assert_ne!(run.agent.agent_log, other.agent_log);
    let log = run.agent.agent_log.clone().unwrap();
    let agent = NativeAgent::new(run.agent.clone(), None, None, String::new()).unwrap();
    assert!(log.exists());
    assert!(NativeAgent::new(run.agent, None, None, String::new()).is_err());
    drop(agent);
}

#[test]
fn stall_timer_survives_same_depth_setup_and_resets_on_depth_change_and_yield() {
    let mut agent = NativeAgent::new(Default::default(), None, None, String::new()).unwrap();
    agent.enter_depth(0);
    assert!(!agent.stall_elapsed());
    agent.depth = Some((0, Instant::now() - Duration::from_secs(6)));
    agent.enter_depth(0);
    assert!(agent.stall_elapsed());
    agent.wait_since = Some(Instant::now());
    assert!(!agent.stall_elapsed());
    agent.wait_since = Some(Instant::now() - Duration::from_secs(6));
    assert!(agent.stall_elapsed());
    agent.enter_depth(1);
    assert!(!agent.stall_elapsed());
}

#[test]
fn fast_native_completion_never_contacts_provider_with_default_threshold() {
    let root = tempfile::tempdir().unwrap();
    let result = run_fake_options(
        root.path(),
        Box::new(Failed),
        8,
        0,
        Arc::new(AtomicUsize::new(0)),
        AgentOptions::default(),
    );
    assert_eq!(
        result.run_progress.unwrap().deepest_completed_depth,
        Some(0)
    );
    let events = events(root.path());
    assert_eq!(events.last().unwrap()["calls"], 0);
    assert_eq!(events.last().unwrap()["snapshots"], 0);
}

#[test]
fn assessment_rejects_invalid_decisions_and_ignores_a_closed_depth() {
    let run = YardbirdOptions {
        filename: Some("tests/fixtures/prerequisite_explicit_action.vmt".into()),
        ..Default::default()
    };
    let mut plan = run.build_array_proof_plan();
    let model = plan
        .strategy
        .configure_model(crate::model_from_options(&run));
    let smt = crate::vmt_bmc_session::VmtBmcSession::new(
        &model,
        &plan.strategy,
        crate::SolverBackend::Z3,
        false,
        plan.instantiation_strategy,
        false,
        None,
    )
    .unwrap();
    let pending = HashSet::new();
    let context = DiscoveryContext {
        smt: &smt,
        depth: 1,
        refinement_step: 5,
        model_version: 9,
        quantifiers: None,
        call_limit: 1,
        symbolic_feedback: &Value::Null,
        pending: &pending,
    };
    let mut agent = NativeAgent::new(Default::default(), None, None, String::new()).unwrap();
    agent.enter_depth(1);
    let decision = |epoch: &str, next_refinements| wire::Tool::Assess {
        epoch: epoch.into(),
        decision: wire::Decision::Advise,
        reason: "Inspect the missing relationship.".into(),
        next_refinements,
    };
    let ignored = agent.assess(decision("e2", 1), &context, 0, "e2").unwrap();
    assert_eq!(ignored["ignored"], "depth_closed");
    assert!(!agent.adaptive_ready);
    assert!(agent
        .assess(decision("wrong", 1), &context, 1, "e2")
        .is_err());
    for count in [0, 1025] {
        assert!(agent
            .assess(decision("e2", count), &context, 1, "e2")
            .is_err());
    }
    assert!(agent
        .assess(
            wire::Tool::Snapshot { epoch: "e2".into() },
            &context,
            1,
            "e2"
        )
        .is_err());
    agent.assess(decision("e2", 1), &context, 1, "e2").unwrap();
    assert!(
        agent.adaptive_ready,
        "older model at the same depth can request inspection"
    );
    agent.enter_depth(2);
    assert!(!agent.adaptive_ready);
    assert_eq!(agent.next_assess_step, 0);
}

struct AdaptiveTools {
    assessments: usize,
    advice: DelayedTools,
}
impl LlmClient for AdaptiveTools {
    fn infer(&mut self, request: &Value) -> anyhow::Result<Value> {
        if request["tools"][0]["name"] != "assess" {
            return self.advice.infer(request);
        }
        self.assessments += 1;
        let evidence: Value =
            serde_json::from_str(request["input"][1]["content"].as_str().unwrap())?;
        assert!(evidence.get("context").is_none());
        assert!(evidence["recent_models"].as_array().unwrap().len() <= 8);
        assert!(evidence["recent_assertions"].as_array().unwrap().len() <= 8);
        if self.assessments == 1 {
            let start = Instant::now();
            while self.advice.progress.load(Ordering::SeqCst) < 4
                && start.elapsed() < Duration::from_secs(3)
            {
                std::thread::sleep(Duration::from_millis(1));
            }
            anyhow::ensure!(
                self.advice.progress.load(Ordering::SeqCst) >= 4,
                "assessment blocked native refinement"
            );
        } else {
            assert!(!evidence["recent_assertions"].as_array().unwrap().is_empty());
            assert_eq!(
                evidence["previous_assessment"]["decision"],
                "continue_symbolic"
            );
        }
        Ok(response(
            "assess",
            json!({"epoch":evidence["epoch"],
            "decision":if self.assessments == 1 {"continue_symbolic"}else{"advise"},
            "reason":"Test assessment: allow more native work, then inspect the missing universal fact.","next_refinements":3}),
        ))
    }
}

#[test]
fn adaptive_assessment_defers_then_opens_an_episode_and_installs_a_late_hint() {
    let root = tempfile::tempdir().unwrap();
    let progress = Arc::new(AtomicUsize::new(0));
    let fake = AdaptiveTools {
        assessments: 0,
        advice: DelayedTools {
            progress: progress.clone(),
            calls: 0,
            epoch: String::new(),
            schema: None,
        },
    };
    run_fake_options(
        root.path(),
        Box::new(fake),
        32,
        5,
        progress,
        AgentOptions {
            agent_trigger: AgentTrigger::Adaptive,
            // Adaptive mode must ignore even an impossibly long stall threshold.
            agent_stall_secs: u64::MAX,
            ..Default::default()
        },
    );
    let events = events(root.path());
    let decisions: Vec<_> = events
        .iter()
        .filter(|e| e["event"] == "tool_result" && e["name"] == "assess")
        .collect();
    assert_eq!(decisions.len(), 2, "{events:?}");
    assert_eq!(
        decisions[0]["reply"]["result"]["decision"],
        "continue_symbolic"
    );
    assert_eq!(decisions[1]["reply"]["result"]["decision"], "advise");
    let requests: Vec<_> = events
        .iter()
        .filter(|e| e["event"] == "request" && e["kind"] == "assessment")
        .collect();
    let second: Value = serde_json::from_str(
        requests[1]["request"]["input"][1]["content"]
            .as_str()
            .unwrap(),
    )
    .unwrap();
    assert!(
        second["recent_models"].as_array().unwrap().last().unwrap()["refinement_step"]
            .as_u64()
            .unwrap()
            >= decisions[0]["reply"]["result"]["next_assess_step"]
                .as_u64()
                .unwrap()
    );
    let first_snapshot = events
        .iter()
        .position(|e| e["event"] == "snapshot")
        .unwrap();
    let last_assessment = events
        .iter()
        .rposition(|e| e["event"] == "tool_result" && e["name"] == "assess")
        .unwrap();
    assert!(first_snapshot > last_assessment);
    assert!(
        events
            .iter()
            .any(|e| e["event"] == "installed" && e["proposal_ids"][0] == "late-p31"),
        "{events:?}"
    );
}

#[test]
fn native_driver_progresses_during_fake_inference_and_installs_late_exact_hint() {
    let root = tempfile::tempdir().unwrap();
    let progress = Arc::new(AtomicUsize::new(0));
    let fake = DelayedTools {
        progress: progress.clone(),
        calls: 0,
        epoch: String::new(),
        schema: None,
    };
    let result = run_fake(root.path(), Box::new(fake), 32, 3, progress);
    assert_eq!(
        result.run_progress.unwrap().deepest_completed_depth,
        Some(0)
    );
    let events = events(root.path());
    let hint = events
        .iter()
        .find(|e| e["event"] == "tool_result" && e["name"] == "instantiate")
        .expect("received hint");
    assert_eq!(hint["reply"]["ok"], true, "{hint}");
    let data = &hint["reply"]["result"];
    assert_ne!(data["source_epoch"], data["evaluated_epoch"]);
    assert_eq!(data["candidates"][0]["outcome"], "violated", "{hint}");
    assert!(events
        .iter()
        .any(|e| e["event"] == "installed" && e["proposal_ids"][0] == "late-p31"));
    assert_eq!(events.last().unwrap()["snapshots"], 1);
}

struct Blocking(Arc<(Mutex<bool>, std::sync::Condvar)>);
impl LlmClient for Blocking {
    fn infer(&mut self, _: &Value) -> anyhow::Result<Value> {
        let (lock, signal) = &*self.0;
        let done = lock.lock().unwrap();
        let _ = signal
            .wait_timeout_while(done, Duration::from_secs(10), |v| !*v)
            .unwrap();
        anyhow::bail!("released fake")
    }
}
#[test]
fn completion_does_not_join_worker() {
    let root = tempfile::tempdir().unwrap();
    let signal = Arc::new((Mutex::new(false), std::sync::Condvar::new()));
    let start = Instant::now();
    run_fake(
        root.path(),
        Box::new(Blocking(signal.clone())),
        8,
        1,
        Arc::new(AtomicUsize::new(0)),
    );
    *signal.0.lock().unwrap() = true;
    signal.1.notify_all();
    assert!(start.elapsed() < Duration::from_secs(5));
    let events = events(root.path());
    assert!(
        events.iter().any(|e| e["event"] == "outstanding_call"),
        "{events:?}"
    );
    assert_eq!(events.last().unwrap()["calls"], 1);
}

struct Failed;
impl LlmClient for Failed {
    fn infer(&mut self, _: &Value) -> anyhow::Result<Value> {
        anyhow::bail!("fake provider failure")
    }
}
#[test]
fn failure_does_not_retry_or_stop_native_verification() {
    let root = tempfile::tempdir().unwrap();
    run_fake(
        root.path(),
        Box::new(Failed),
        32,
        100,
        Arc::new(AtomicUsize::new(0)),
    );
    let es = events(root.path());
    assert_eq!(es.last().unwrap()["calls"], 1, "{es:?}");
    assert!(es.iter().any(|e| e["event"] == "disabled"
        && e["reason"]
            .as_str()
            .unwrap()
            .contains("fake provider failure")));
}

struct LargeContinuation(DelayedTools);
impl LlmClient for LargeContinuation {
    fn infer(&mut self, request: &Value) -> anyhow::Result<Value> {
        let mut response = self.0.infer(request)?;
        if self.0.calls == 3 {
            response["output"].as_array_mut().unwrap().push(json!({
                "type":"reasoning","encrypted_content":"x".repeat(2_100_000)}));
        }
        Ok(response)
    }
}
#[test]
fn next_request_size_limit_does_not_discard_an_accepted_hint() {
    let root = tempfile::tempdir().unwrap();
    let progress = Arc::new(AtomicUsize::new(0));
    let fake = LargeContinuation(DelayedTools {
        progress: progress.clone(),
        calls: 0,
        epoch: String::new(),
        schema: None,
    });
    run_fake(root.path(), Box::new(fake), 32, 4, progress);
    let es = events(root.path());
    assert!(es
        .iter()
        .any(|e| e["event"] == "disabled" && e["reason"] == "request_size_limit"));
    assert!(es
        .iter()
        .any(|e| e["event"] == "installed" && e["proposal_ids"][0] == "late-p31"));
    assert_eq!(es.last().unwrap()["calls"], 3);
}

#[test]
fn indexed_retrieval_is_exact_paged_and_tool_arguments_are_strict() {
    let values = json!([{"id":"t0","expression":"0"},{"id":"t1","expression":"1"}]);
    assert_eq!(
        wire::retrieve(&values, None, None, 0, 1).unwrap()["next_offset"],
        1
    );
    assert_eq!(
        wire::retrieve(&values, Some("t1"), None, 0, 20).unwrap()["items"][0]["expression"],
        "1"
    );
    assert_eq!(
        wire::retrieve(&json!("αβγ"), None, None, 1, 1).unwrap()["text"],
        "β"
    );
    assert!(wire::decode(&response("stop", json!({"epoch":"e1"}))).is_err());
    assert!(wire::decode(&response("snapshot", json!({"epoch":"e1","extra":true}))).is_err());
    assert!(wire::decode(&response("instantiate",json!({"epoch":"e1","items":[{"proposal_id":"p","proposal":{"axiom_id":"q","bindings":{},"formula":"false"}}]}))).is_err());
}

#[test]
fn request_preparation_leaves_the_solver_thread_free() {
    let root = tempfile::tempdir().unwrap();
    let mut agent = NativeAgent::new(
        AgentOptions {
            agent_dry_run: true,
            agent_log: Some(root.path().join("events.jsonl")),
            ..Default::default()
        },
        Some(LlmOptions::default()),
        Some(Box::new(Failed)),
        String::new(),
    )
    .unwrap();
    let solver_thread = std::thread::current().id();
    let (release, wait) = mpsc::channel();
    agent
        .send(
            Box::new(move |_, _, _| {
                assert_ne!(std::thread::current().id(), solver_thread);
                wait.recv_timeout(Duration::from_secs(5))?;
                Ok(json!({"prepared":true}))
            }),
            0,
            1,
            None,
        )
        .unwrap();
    release.send(()).unwrap();
    drop(agent);
    assert!(events(root.path())
        .iter()
        .any(|event| event["event"] == "dry_request" && event["request"]["prepared"] == true));
}
