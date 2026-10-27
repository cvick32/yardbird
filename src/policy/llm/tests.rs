use super::*;
use crate::{
    policy::NamedPolicy,
    problem_context::ProblemContext,
    solver::SolverCheckResult,
    strategies::{ProofStrategy, RefinementState},
    vmt_bmc_session::VmtBmcSession,
};
use clap::Parser;
use smt2parser::{concrete::SyntaxBuilder, vmt::VMTModel, CommandStream};
use std::{
    cell::RefCell,
    collections::{HashSet, VecDeque},
    rc::Rc,
};

const INPUT: &str = r#"
    (declare-fun a () (Array Int Int))
    (declare-fun unused () (Array Int Int))
    (define-fun init () Bool (! (and
        (= (select (store a 1 7) 1) 9)
        (= (select unused 123) 42)) :init true))
    (define-fun trans () Bool (! true :trans true))
    (define-fun prop () Bool (! (= (select (store a 1 7) 1) 7) :invar-property 0))
"#;

fn model() -> VMTModel {
    VMTModel::checked_from(
        CommandStream::new(INPUT.as_bytes(), SyntaxBuilder, None)
            .collect::<Result<Vec<_>, _>>()
            .unwrap(),
    )
    .unwrap()
}

fn fixture() -> VmtBmcSession {
    let mut strategy: Box<dyn ProofStrategy<'_, RefinementState>> =
        Box::new(Abstract::<ArrayBMCCost>::new(
            1,
            false,
            YardbirdPolicy::new(()),
            false,
        ));
    let model = strategy.configure_model(model());
    let mut smt = VmtBmcSession::new(
        &model,
        &strategy,
        SolverBackend::Z3,
        false,
        Box::new(FullUnrollStrategy::new()),
        false,
        None,
    )
    .unwrap();
    assert_eq!(smt.check_property(), SolverCheckResult::Sat);
    smt
}

fn context<'a>(
    smt: &'a VmtBmcSession,
    pending: &'a HashSet<smt2parser::concrete::Term>,
) -> DiscoveryContext<'a> {
    DiscoveryContext {
        smt,
        depth: 0,
        refinement_step: 0,
        model_version: 1,
        pending,
    }
}

fn request_state(request: &Value) -> Value {
    let messages = if request.get("input").is_some() {
        &request["input"]
    } else {
        &request["messages"]
    };
    let blocks = messages
        .as_array()
        .unwrap()
        .iter()
        .find(|message| message["role"] == "user")
        .unwrap()["content"]
        .as_array()
        .unwrap();
    let mut state = json!({"terms":[],"declarations":[]});
    for block in blocks {
        let part: Value = serde_json::from_str(block["text"].as_str().unwrap()).unwrap();
        for (key, value) in part.as_object().unwrap() {
            if matches!(key.as_str(), "terms" | "declarations") {
                state[key]
                    .as_array_mut()
                    .unwrap()
                    .extend(value.as_array().unwrap().iter().cloned());
            } else {
                assert!(state.get(key).is_none(), "duplicate field {key}");
                state[key] = value.clone();
            }
        }
    }
    state
}

fn envelope(provider: LlmProvider, text: &str) -> Value {
    match provider {
        LlmProvider::Openai => {
            json!({"id":"response-1", "model":"resolved-openai-model", "status":"completed",
            "output":[{"type":"reasoning", "summary":[]}, {"type":"message", "role":"assistant", "status":"completed",
                "content":[{"type":"output_text", "text":text}]}],
            "usage":{"input_tokens":100, "input_tokens_details":{"cached_tokens":0}, "output_tokens":20, "output_tokens_details":{"reasoning_tokens":10}}})
        }
        LlmProvider::Anthropic => {
            json!({"id":"message-1", "model":"resolved-anthropic-model", "type":"message", "role":"assistant", "stop_reason":"end_turn",
            "content":[{"type":"thinking", "thinking":"fixture", "signature":"opaque"}, {"type":"text", "text":text}],
            "usage":{"input_tokens":100, "output_tokens":20, "cache_read_input_tokens":12, "cache_creation_input_tokens":0}})
        }
    }
}

#[derive(Clone, Copy)]
enum Reply {
    Valid,
    FalseGuard,
    Invalid,
    BadId,
    Abstain,
    Truncated,
    Refusal,
    TransportError,
}

struct MockClient {
    provider: LlmProvider,
    requests: Rc<RefCell<Vec<Value>>>,
    replies: VecDeque<Reply>,
}

impl LlmClient for MockClient {
    fn infer(&mut self, request: &Value) -> anyhow::Result<Value> {
        self.requests.borrow_mut().push(request.clone());
        let reply = self
            .replies
            .pop_front()
            .expect("unexpected inference request");
        let text = match reply {
            Reply::TransportError => anyhow::bail!("fixture timeout"),
            Reply::Abstain => "{\"proposal\":null}".to_owned(),
            Reply::Invalid => "{\"proposal\":{}}".to_owned(),
            _ => {
                let state = request_state(request);
                let rule = if matches!(reply, Reply::FalseGuard) {
                    "write-does-not-overwrite"
                } else {
                    "read-after-write"
                };
                let schema = state["axioms"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .find(|s| s["name"].as_str().unwrap().starts_with(rule))
                    .unwrap();
                let bindings = schema["slots"]
                    .as_object()
                    .unwrap()
                    .keys()
                    .map(|slot| {
                        let expression = match slot.as_str() {
                            "a" => "a@0",
                            "idx" | "c" => "1",
                            "val" => "7",
                            _ => panic!("unexpected slot"),
                        };
                        let term = state["terms"]
                            .as_array()
                            .unwrap()
                            .iter()
                            .find(|t| t["expression"] == expression)
                            .unwrap();
                        (slot.clone(), term["id"].clone())
                    })
                    .collect::<serde_json::Map<_, _>>();
                let mut result = json!({"proposal":{"axiom_id":schema["id"], "bindings":bindings}});
                if matches!(reply, Reply::BadId) {
                    result["proposal"]["bindings"]["idx"] = json!("t999");
                }
                result.to_string()
            }
        };
        let mut response = envelope(self.provider, &text);
        if matches!(reply, Reply::Truncated) {
            response["status"] = json!("incomplete");
            response["stop_reason"] = json!("max_tokens");
        }
        if matches!(reply, Reply::Refusal) {
            match self.provider {
                LlmProvider::Openai => {
                    response["output"][1]["content"] =
                        json!([{"type":"refusal", "refusal":"fixture"}])
                }
                LlmProvider::Anthropic => response["stop_reason"] = json!("refusal"),
            }
        }
        Ok(response)
    }
}

fn experiment(
    path: PathBuf,
    provider: LlmProvider,
    replies: Vec<Reply>,
) -> (Experiment, Rc<RefCell<Vec<Value>>>) {
    let requests = Rc::new(RefCell::new(Vec::new()));
    (
        Experiment {
            no_fallback: false,
            options: LlmOptions {
                llm_provider: provider,
                llm_model: Some("explicit-model-id".into()),
                llm_log: Some(path),
                pricing: LlmPricing {
                    llm_input_usd_per_million: Some(10.0),
                    llm_output_usd_per_million: Some(50.0),
                    llm_cached_input_usd_per_million: Some(1.0),
                    ..Default::default()
                },
                ..Default::default()
            },
            client: Box::new(MockClient {
                provider,
                requests: requests.clone(),
                replies: replies.into(),
            }),
            query_id: 0,
            session: Default::default(),
            spend: Default::default(),
            log: None,
            input: Some("fixture.vmt".into()),
            problem_source: Some(INPUT.into()),
        },
        requests,
    )
}

fn records(path: &std::path::Path) -> Vec<Value> {
    std::fs::read_to_string(path)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect()
}

#[test]
fn both_providers_receive_identical_full_context_and_joint_response_schema() {
    let smt = fixture();
    let pending = HashSet::new();
    let context = context(&smt, &pending);
    let snapshot = InstantiationSession::default()
        .capture(&context, INPUT)
        .unwrap();
    let options = LlmOptions {
        llm_model: Some("exact-model".into()),
        llm_reasoning_effort: Some("high".into()),
        ..Default::default()
    };
    let openai = protocol::request(&options, &snapshot, &[]).unwrap();
    let anthropic = protocol::request(
        &LlmOptions {
            llm_provider: LlmProvider::Anthropic,
            llm_adaptive_thinking: true,
            ..options
        },
        &snapshot,
        &[],
    )
    .unwrap();
    let mut expected = snapshot.state();
    expected["failure_summary"] = json!([]);
    assert_eq!(request_state(&openai), expected);
    assert_eq!(request_state(&anthropic), expected);
    assert_eq!(openai["input"][0]["content"], anthropic["system"]);
    assert_eq!(openai["reasoning"]["effort"], "high");
    assert_eq!(anthropic["output_config"]["effort"], "high");
    assert_eq!(anthropic["thinking"]["type"], "adaptive");
    assert_eq!(openai["store"], false);
    assert_eq!(openai["truncation"], "disabled");
    assert!(openai.get("tools").is_none() && anthropic.get("tools").is_none());
    assert_eq!(
        openai["text"]["format"]["schema"],
        anthropic["output_config"]["format"]["schema"]
    );
    let alternatives = openai["text"]["format"]["schema"]["properties"]["proposal"]["anyOf"]
        .as_array()
        .unwrap();
    assert_eq!(alternatives.len(), snapshot.schemas.len() + 1);
    for (schema, alternative) in snapshot.schemas.iter().zip(&alternatives[1..]) {
        assert_eq!(
            alternative["properties"]["axiom_id"]["enum"],
            json!([schema.id])
        );
        assert_eq!(
            alternative["properties"]["bindings"]["required"],
            json!(schema.slots.keys().collect::<Vec<_>>())
        );
        assert_eq!(
            alternative["properties"]["bindings"]["additionalProperties"],
            false
        );
    }
}

#[test]
fn default_single_call_accepts_complete_proposal_and_logs_provider_usage() {
    let smt = fixture();
    let pending = HashSet::new();
    let context = context(&smt, &pending);
    for provider in [LlmProvider::Openai, LlmProvider::Anthropic] {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("episode.jsonl");
        let (mut experiment, requests) = experiment(path.clone(), provider, vec![Reply::Valid]);
        let instances = experiment.discover(&context).unwrap();
        assert_eq!(instances.len(), 1);
        assert_eq!(requests.borrow().len(), 1);
        assert_eq!(
            instances[0].term.to_string(),
            "(= (Read_Int_Int (Write_Int_Int a@0 1 7) 1) 7)"
        );
        let log = records(&path);
        let response = log.iter().find(|r| r["event"] == "response").unwrap();
        assert_eq!(response["usage"], response["response"]["usage"]);
        assert_eq!(response["usage"]["input_tokens"], 100);
        assert_eq!(response["cost"]["status"], "estimated");
        assert_eq!(
            log.last().unwrap()["run_cost"]["estimated_total_usd"],
            response["cost"]["estimated_usd"]
        );
        assert!(response["resolved_model"]
            .as_str()
            .unwrap()
            .starts_with("resolved-"));
        assert_eq!(log.last().unwrap()["api_calls"], 1);
        assert_eq!(log.last().unwrap()["outcome"], "violated");
    }
}

#[test]
fn feedback_retries_keep_the_model_and_catalogue_fixed() {
    let smt = fixture();
    let pending = HashSet::new();
    let context = context(&smt, &pending);
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("episode.jsonl");
    let (mut experiment, requests) = experiment(
        path.clone(),
        LlmProvider::Openai,
        vec![Reply::FalseGuard, Reply::BadId, Reply::Valid],
    );
    experiment.options.llm_attempts = 3;
    assert_eq!(experiment.discover(&context).unwrap().len(), 1);
    let requests = requests.borrow();
    assert_eq!(requests.len(), 3);
    let initial = request_state(&requests[0]);
    for request in requests.iter() {
        let state = request_state(request);
        for field in [
            "model",
            "terms",
            "axioms",
            "declarations",
            "problem",
            "model_version",
        ] {
            assert_eq!(state[field], initial[field]);
        }
    }
    let second = request_state(&requests[1]);
    assert_eq!(second["failure_summary"][0]["reason"], "false_antecedent");
    assert!(second["failure_summary"][0].get("observations").is_none());
    let third = request_state(&requests[2]);
    assert_eq!(
        third["failure_summary"][1]["proposal"]["bindings"]["idx"],
        "t999"
    );
    assert_eq!(records(&path).last().unwrap()["api_calls"], 3);
    assert!(
        (records(&path).last().unwrap()["run_cost"]["estimated_total_usd"]
            .as_f64()
            .unwrap()
            - 0.006)
            .abs()
            < 1e-10
    );
}

#[test]
fn malformed_proposals_exhaust_exactly_the_attempt_budget() {
    let smt = fixture();
    let pending = HashSet::new();
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("episode.jsonl");
    let (mut experiment, requests) =
        experiment(path.clone(), LlmProvider::Openai, vec![Reply::Invalid; 3]);
    experiment.options.llm_attempts = 3;
    assert!(experiment
        .discover(&context(&smt, &pending))
        .unwrap()
        .is_empty());
    assert_eq!(requests.borrow().len(), 3);
    assert_eq!(
        records(&path).last().unwrap()["outcome"],
        "attempts_exhausted"
    );
}

#[test]
fn abstention_refusal_truncation_and_transport_errors_stop_without_repair_calls() {
    let smt = fixture();
    let pending = HashSet::new();
    for provider in [LlmProvider::Openai, LlmProvider::Anthropic] {
        for (reply, outcome) in [
            (Reply::Abstain, "abstained"),
            (Reply::Refusal, "response_rejected"),
            (Reply::Truncated, "response_rejected"),
            (Reply::TransportError, "transport_error"),
        ] {
            let directory = tempfile::tempdir().unwrap();
            let path = directory.path().join("episode.jsonl");
            let (mut experiment, requests) = experiment(path.clone(), provider, vec![reply]);
            experiment.options.llm_attempts = 3;
            assert!(experiment
                .discover(&context(&smt, &pending))
                .unwrap()
                .is_empty());
            assert_eq!(requests.borrow().len(), 1);
            let log = records(&path);
            assert_eq!(log.last().unwrap()["outcome"], outcome);
            assert_eq!(log.last().unwrap()["ordinary_fallback"], true);
            let cost = &log.last().unwrap()["run_cost"];
            assert_eq!(cost["api_calls"], 1);
            if matches!(reply, Reply::TransportError) {
                assert_eq!(cost["unknown_cost_calls"], 1);
                assert!(cost["estimated_total_usd"].is_null());
            } else {
                assert_eq!(cost["unknown_cost_calls"], 0);
                assert!(cost["estimated_total_usd"].as_f64().unwrap() > 0.0);
            }
        }
    }
}

#[test]
fn dry_run_and_oversized_requests_log_full_context_without_inference() {
    let smt = fixture();
    let pending = HashSet::new();
    for oversized in [false, true] {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("episode.jsonl");
        let (mut experiment, requests) = experiment(path.clone(), LlmProvider::Openai, vec![]);
        experiment.options.llm_dry_run = !oversized;
        if oversized {
            experiment.options.llm_max_request_bytes = 1;
        }
        assert!(experiment
            .discover(&context(&smt, &pending))
            .unwrap()
            .is_empty());
        assert!(requests.borrow().is_empty());
        let log = records(&path);
        let state = request_state(&log[0]["request"]);
        assert_eq!(state["problem"]["source"], INPUT);
        assert_eq!(state["model"], smt.native_model_to_string().unwrap());
        assert_eq!(log.last().unwrap()["api_calls"], 0);
        assert_eq!(log.last().unwrap()["run_cost"]["estimated_total_usd"], 0.0);
        assert_eq!(
            log.last().unwrap()["outcome"],
            if oversized {
                "request_too_large"
            } else {
                "dry_run"
            }
        );
    }
}

#[test]
fn response_parser_rejects_missing_extra_and_unexpected_content() {
    assert!(protocol::proposal("{\"proposal\":null}").unwrap().is_none());
    for text in [
        "{}",
        "null",
        "[]",
        "{\"proposal\":null,\"proof\":true}",
        "```json\n{\"proposal\":null}\n```",
        "{\"proposal\":{\"axiom_id\":\"q0\",\"bindings\":{},\"formula\":\"false\"}}",
    ] {
        assert!(protocol::proposal(text).is_err(), "accepted {text}");
    }
    let mut response = envelope(LlmProvider::Openai, "{\"proposal\":null}");
    response["output"]
        .as_array_mut()
        .unwrap()
        .push(json!({"type":"function_call"}));
    assert!(protocol::response_text(LlmProvider::Openai, &response).is_err());
    let mut response = envelope(LlmProvider::Anthropic, "{\"proposal\":null}");
    response["content"]
        .as_array_mut()
        .unwrap()
        .push(json!({"type":"text", "text":"{}"}));
    assert!(protocol::response_text(LlmProvider::Anthropic, &response).is_err());
}

#[test]
fn success_installs_through_shared_path_and_failures_use_ordinary_refinement() {
    for succeeds in [false, true] {
        let directory = tempfile::tempdir().unwrap();
        let (experiment, _) = experiment(
            directory.path().join("episode.jsonl"),
            LlmProvider::Openai,
            vec![if succeeds {
                Reply::Valid
            } else {
                Reply::TransportError
            }],
        );
        let policy = YardbirdPolicy::<ArrayBMCCost>::new(())
            .with_instantiation_ranker(Box::new(TermCostInstantiationRanker))
            .with_effort(DiscoveryFirst::default())
            .with_discovery(experiment);
        let options = YardbirdOptions {
            profile: true,
            ..Default::default()
        };
        let mut driver = crate::Driver::new(
            model(),
            Box::new(FullUnrollStrategy::new()),
            SolverBackend::Z3,
        )
        .with_profiler(options.build_profiler())
        .with_wall_timeout(Some(std::time::Duration::from_secs(10)));
        let result = driver
            .check_strategy(1, Box::new(Abstract::new(1, false, policy, true)))
            .unwrap();
        assert!(!result.counterexample);
        assert!(result.total_instantiations_added > 0);
        let operations = result
            .profiling
            .cost_records
            .iter()
            .flat_map(|r| &r.effort)
            .collect::<Vec<_>>();
        assert!(operations.iter().any(
            |r| r.operation == "PolicyCandidates" && r.report.selected == usize::from(succeeds)
        ));
        assert_eq!(
            operations.iter().any(|r| r.operation == "ArrayCandidates"),
            !succeeds
        );
    }
}

#[test]
fn cli_validation_serialization_and_plan_match_experiment_requirements() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("episode.jsonl");
    let options = YardbirdOptions::try_parse_from([
        "yardbird",
        "-f",
        "fixture.vmt",
        "--policy",
        "llm-one-shot",
        "--llm-provider",
        "anthropic",
        "--llm-model",
        "exact-model",
        "--llm-adaptive-thinking",
        "--llm-reasoning-effort",
        "high",
        "--llm-dry-run",
        "--llm-input-usd-per-million",
        "3",
        "--llm-output-usd-per-million",
        "15",
        "--llm-log",
        path.to_str().unwrap(),
    ])
    .unwrap();
    options.llm.validate(&options).unwrap();
    options.decision_model.validate(&options).unwrap();
    assert!(options.profiling_enabled());
    let decoded: YardbirdOptions =
        serde_json::from_value(serde_json::to_value(&options).unwrap()).unwrap();
    assert_eq!(decoded.llm, options.llm);
    let mut old = serde_json::to_value(YardbirdOptions::default()).unwrap();
    old.as_object_mut().unwrap().remove("llm");
    assert_eq!(
        serde_json::from_value::<YardbirdOptions>(old).unwrap().llm,
        LlmOptions::default()
    );
    for invalid in 0..12 {
        let mut run = options.clone();
        match invalid {
            0 => run.policy = Some(NamedPolicy::OneShot),
            1 => run.llm.llm_model = None,
            2 => run.llm.llm_attempts = 0,
            3 => run.llm.llm_max_output_tokens = 0,
            4 => run.llm.llm_max_request_bytes = 0,
            5 => run.llm.llm_timeout_secs = 0,
            6 => run.llm.llm_provider = LlmProvider::Openai,
            7 => run.llm.llm_reasoning_effort = Some(" ".into()),
            8 => run.filename = Some("fixture.smt2".into()),
            9 => run.theory = TheorySelection::Explicit(vec![Theory::Quantifiers]),
            10 => run.llm.pricing.llm_input_usd_per_million = None,
            11 => run.llm.pricing.llm_output_usd_per_million = Some(-1.0),
            _ => unreachable!(),
        }
        assert!(run.llm.validate(&run).is_err(), "accepted case {invalid}");
    }
    let plan = NamedPolicy::LlmOneShot.build_plan(&options);
    assert_eq!(plan.solver, SolverBackend::Z3);
    assert_eq!(
        plan.strategy.property_check_mode(),
        PropertyCheckMode::Assumptions
    );
    assert_eq!(
        format!("{:?}", plan.instantiation_strategy),
        format!("{:?}", FullUnrollStrategy::new())
    );
    std::fs::write(path, "existing log").unwrap();
    assert!(options.llm.validate(&options).is_err());
}

#[test]
fn cached_requests_keep_full_context_and_prior_endpoints_across_models_and_retries() {
    let mut smt = fixture();
    let pending = HashSet::new();
    let mut session = InstantiationSession::default();
    let mut previous_prefix: Vec<Value> = Vec::new();
    let mut previous_terms: Vec<Value> = Vec::new();
    let mut previous_declarations: Vec<Value> = Vec::new();
    for depth in 0..8 {
        smt.unroll(depth);
        assert_eq!(smt.check_property(), SolverCheckResult::Sat);
        let mut context = context(&smt, &pending);
        context.depth = depth;
        context.model_version = u64::from(depth) + 1;
        let snapshot = session.capture(&context, INPUT).unwrap();

        let state = snapshot.state();
        let grows = previous_terms
            .iter()
            .all(|t| state["terms"].as_array().unwrap().contains(t))
            && previous_declarations
                .iter()
                .all(|d| state["declarations"].as_array().unwrap().contains(d));
        if grows {
            assert_eq!(&snapshot.prefix()[..previous_prefix.len()], previous_prefix);
        } else {
            assert_ne!(snapshot.prefix(), previous_prefix);
        }
        for old in &previous_terms {
            if let Some(new) =
                state["terms"].as_array().unwrap().iter().find(|new| {
                    new["expression"] == old["expression"] && new["sort"] == old["sort"]
                })
            {
                assert_eq!(new["id"], old["id"]);
            }
        }
        for provider in [LlmProvider::Openai, LlmProvider::Anthropic] {
            let options = LlmOptions {
                llm_provider: provider,
                llm_model: Some("fixture".into()),
                ..Default::default()
            };
            let request = protocol::request(&options, &snapshot, &[]).unwrap();
            let retry =
                protocol::request(&options, &snapshot, &[json!({"outcome":"invalid"})]).unwrap();
            let (messages, retry_messages, marker) = match provider {
                LlmProvider::Openai => {
                    assert_eq!(
                        request["prompt_cache_options"],
                        json!({"mode":"explicit", "ttl":"30m"})
                    );
                    (
                        &request["input"],
                        &retry["input"],
                        "prompt_cache_breakpoint",
                    )
                }
                LlmProvider::Anthropic => {
                    (&request["messages"], &retry["messages"], "cache_control")
                }
            };
            let blocks = messages.as_array().unwrap().last().unwrap()["content"]
                .as_array()
                .unwrap();
            let retry_blocks = retry_messages.as_array().unwrap().last().unwrap()["content"]
                .as_array()
                .unwrap();
            assert_eq!(
                &blocks[..blocks.len() - 1],
                &retry_blocks[..retry_blocks.len() - 1]
            );
            assert!(blocks.last().unwrap().get(marker).is_none());
            assert!(blocks.iter().filter(|b| b.get(marker).is_some()).count() <= 4);
            assert!(blocks[snapshot.prefix().len() - 1].get(marker).is_some());
            if grows && !previous_prefix.is_empty() {
                assert!(
                    blocks[previous_prefix.len() - 1].get(marker).is_some(),
                    "prior endpoint unavailable for lookup"
                );
            }
            let mut expected = state.clone();
            expected["failure_summary"] = json!([]);
            assert_eq!(request_state(&request), expected);
            expected["failure_summary"] = json!([{"outcome":"invalid"}]);
            assert_eq!(request_state(&retry), expected);
            let disabled = protocol::request(
                &LlmOptions {
                    llm_explicit_cache: false,
                    ..options
                },
                &snapshot,
                &[],
            )
            .unwrap();
            assert!(disabled.get("prompt_cache_options").is_none());
            assert!(!disabled.to_string().contains(marker));
            assert_eq!(request_state(&disabled), request_state(&request));
        }
        previous_prefix = snapshot.prefix().to_vec();
        previous_terms = state["terms"].as_array().unwrap().clone();
        previous_declarations = state["declarations"].as_array().unwrap().clone();
    }
}

#[test]
fn strict_guidance_failure_stops_without_installing_ordinary_instances() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("strict.jsonl");
    let (mut discovery, _) = experiment(
        path.clone(),
        LlmProvider::Openai,
        vec![Reply::TransportError],
    );
    discovery.no_fallback = true;
    let policy = YardbirdPolicy::<ArrayBMCCost>::new(())
        .with_effort(DiscoveryFirst::default().with_no_fallback(true))
        .with_discovery(discovery);
    let mut driver = crate::Driver::new(
        model(),
        Box::new(FullUnrollStrategy::new()),
        SolverBackend::Z3,
    );
    let error = driver
        .check_strategy(1, Box::new(Abstract::new(1, false, policy, true)))
        .unwrap_err();
    assert!(
        matches!(error, crate::driver::Error::NoProgress { ref instantiations, .. }
        if instantiations.is_empty())
    );
    let failed = driver.take_failed_result().unwrap();
    assert!(!failed.counterexample);
    assert!(!failed.found_proof);
    assert_eq!(failed.total_instantiations_added, 0);
    assert_eq!(
        failed
            .solver_statistics
            .get_f64("concrete_validation_checks")
            .unwrap(),
        0.0
    );
    let records = std::fs::read_to_string(path).unwrap();
    let last: Value = serde_json::from_str(records.lines().last().unwrap()).unwrap();
    assert_eq!(last["ordinary_fallback"], false);
    assert_eq!(last["no_guided_fallback"], true);
}
