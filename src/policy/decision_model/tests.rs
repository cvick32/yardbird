use super::*;
use crate::{
    problem_context::ProblemContext,
    solver::SolverCheckResult,
    strategies::{ProofStrategy, RefinementState},
    vmt_bmc_session::VmtBmcSession,
};
use smt2parser::{concrete::SyntaxBuilder, vmt::VMTModel, CommandStream};
use std::{cell::RefCell, collections::HashSet, rc::Rc};

const INPUT: &str = r#"
    (declare-fun a () (Array Int Int))
    (declare-fun unused () (Array Int Int))
    (define-fun init () Bool (! (and
        (= (select (store a 1 7) 1) 9)
        (= (select unused 123) 42)) :init true))
    (define-fun trans () Bool (! true :trans true))
    (define-fun prop () Bool (! (= (select (store a 1 7) 1) 7) :invar-property 0))
"#;

fn model(input: &str) -> VMTModel {
    VMTModel::checked_from(
        CommandStream::new(input.as_bytes(), SyntaxBuilder, None)
            .collect::<Result<Vec<_>, _>>()
            .unwrap(),
    )
    .unwrap()
}

fn fixture() -> VmtBmcSession {
    fixture_from(INPUT)
}

fn fixture_from(input: &str) -> VmtBmcSession {
    let mut strategy: Box<dyn ProofStrategy<'_, RefinementState>> =
        Box::new(Abstract::<ArrayBMCCost>::new(
            1,
            false,
            YardbirdPolicy::new(()),
            false,
        ));
    let model = strategy.configure_model(model(input));
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

fn response(request: &Value, axiom_name: &str) -> Value {
    if request["questions"].get("axiom").is_some() {
        let (id, _) = request["questions"]["axiom"]["criteria"]
            .as_object()
            .unwrap()
            .iter()
            .find(|(_, value)| value["name"].as_str().unwrap().starts_with(axiom_name))
            .unwrap();
        return json!({"model":"fixture-model-v1","answers":{"axiom":{"type":"choice","choice":id}},"usage":{"input_tokens":100}});
    }
    let id = request["state"]["selected_axiom"]["id"].as_str().unwrap();
    let mut answers = serde_json::Map::new();
    for (question, detail) in request["questions"].as_object().unwrap() {
        let Some(slot) = question.strip_prefix(&format!("{id}_")) else {
            continue;
        };
        let expression = match slot {
            "a" => "a@0",
            "idx" | "c" => "1",
            "val" => "7",
            _ => panic!("unexpected slot"),
        };
        let term = request["state"]["terms"]
            .as_array()
            .unwrap()
            .iter()
            .find(|value| value["expression"] == expression)
            .unwrap();
        let term_id = term["id"].as_str().unwrap();
        assert!(detail["criteria"].get(term_id).is_some());
        answers.insert(question.clone(), json!({"type":"choice","choice":term_id}));
    }
    json!({"model":"fixture-model-v1","answers":answers,"usage":{"input_tokens":100}})
}

fn binding_request(snapshot: &Snapshot, name: &str) -> Value {
    let schema = snapshot
        .schemas
        .iter()
        .find(|s| s.name().starts_with(name))
        .unwrap();
    snapshot
        .binding_request("fixture", &FailureSummary::default(), &schema.id)
        .unwrap()
}

struct RetryClient {
    requests: Rc<RefCell<Vec<Value>>>,
}
impl DecisionClient for RetryClient {
    fn decide(&mut self, request: &Value) -> anyhow::Result<Value> {
        let first = self.requests.borrow().len() < 2;
        self.requests.borrow_mut().push(request.clone());
        let mut answer = response(
            request,
            if first {
                "write-does-not-overwrite"
            } else {
                "read-after-write"
            },
        );
        for (name, question) in request["questions"].as_object().unwrap() {
            let criteria = question["criteria"].as_object().unwrap();
            if answer["answers"].get(name).is_none() {
                answer["answers"][name] =
                    json!({"type":"choice","choice":criteria.keys().next().unwrap()});
            }
            answer["answers"][name]["confidence"] = json!(0.8);
            answer["answers"][name]["probabilities"] = json!(criteria
                .keys()
                .map(|id| (id.clone(), 1.0 / criteria.len() as f64))
                .collect::<std::collections::BTreeMap<_, _>>());
        }
        Ok(answer)
    }
}

fn experiment(path: PathBuf, client: impl DecisionClient + 'static) -> Experiment {
    Experiment {
        options: DecisionModelOptions {
            jev_log: Some(path),
            jev_candidates: 1,
            ..Default::default()
        },
        client: Box::new(client),
        log: None,
        input: Some("fixture.vmt".into()),
    }
}

#[test]
fn full_snapshot_preserves_irrelevant_terms_and_native_model_and_rejects_bad_ids() {
    let smt = fixture();
    let pending = HashSet::new();
    let context = DiscoveryContext {
        smt: &smt,
        depth: 0,
        refinement_step: 0,
        model_version: 1,
        pending: &pending,
    };
    let snapshot = Snapshot::capture(&context).unwrap();
    assert_eq!(
        snapshot.state["model"],
        smt.native_model_to_string().unwrap()
    );
    assert!(snapshot.terms.iter().any(|t| t.expression == "123"));
    assert!(snapshot
        .terms
        .iter()
        .any(|t| t.expression == "(Read_Int_Int unused@0 123)"));
    let request = binding_request(&snapshot, "read-after-write");
    for schema in &snapshot.schemas {
        let request = snapshot
            .binding_request("fixture", &FailureSummary::default(), &schema.id)
            .unwrap();
        assert_eq!(
            request["questions"].as_object().unwrap().len(),
            schema.slots.len()
        );
        assert!(request["questions"].get("axiom").is_none());
        for (slot, sort) in &schema.slots {
            let question = &request["questions"][format!("{}_{}", schema.id, slot)];
            let criteria = question["criteria"].as_object().unwrap();
            let expected = snapshot
                .terms
                .iter()
                .filter(|term| &term.sort == sort)
                .map(|term| term.id.as_str())
                .collect::<std::collections::BTreeSet<_>>();
            assert_eq!(
                criteria
                    .keys()
                    .map(String::as_str)
                    .collect::<std::collections::BTreeSet<_>>(),
                expected
            );
            assert!(criteria.values().all(Value::is_null));
            assert!(question["instructions"]
                .as_str()
                .unwrap()
                .contains("state.terms"));
        }
    }
    let answer = response(&request, "read-after-write");
    let instance = snapshot.proposal(&request, &answer).unwrap();
    assert_eq!(
        instance.term.to_string(),
        "(= (Read_Int_Int (Write_Int_Int a@0 1 7) 1) 7)"
    );
    assert!(validate(&context, instance).1.is_some());
    let axiom_request = snapshot
        .axiom_request("fixture", &FailureSummary::default())
        .unwrap();
    assert_eq!(axiom_request["questions"].as_object().unwrap().len(), 1);
    assert!(axiom_request["state"].get("terms").is_none());
    assert!(axiom_request["state"].get("catalogue_scope").is_none());
    assert!(axiom_request["state"].get("axioms").is_none());
    assert_eq!(axiom_request["state"]["model"], snapshot.state["model"]);
    let mut answer = response(&axiom_request, "read-after-write");
    answer["answers"]["axiom"]["choice"] = json!("q999");
    assert!(snapshot.selected_axiom(&axiom_request, &answer).is_err());
    let mut answer = response(&request, "read-after-write");
    let id = request["state"]["selected_axiom"]["id"].as_str().unwrap();
    // A binding response cannot switch axioms, even if it adds an axiom answer.
    answer["answers"]["axiom"] = json!({"type":"choice","choice":"q999"});
    assert!(snapshot.proposal(&request, &answer).is_ok());
    let array_id = snapshot
        .terms
        .iter()
        .find(|t| t.expression == "a@0")
        .unwrap()
        .id
        .clone();
    answer["answers"][format!("{id}_idx")]["choice"] = json!(array_id);
    assert!(snapshot.proposal(&request, &answer).is_err());
}

#[test]
fn retry_feedback_keeps_model_fixed_and_finds_a_verified_violation() {
    let smt = fixture();
    let original = smt.native_model_to_string().unwrap();
    let pending = HashSet::new();
    let context = DiscoveryContext {
        smt: &smt,
        depth: 0,
        refinement_step: 0,
        model_version: 1,
        pending: &pending,
    };
    let directory = tempfile::tempdir().unwrap();
    let requests = Rc::new(RefCell::new(vec![]));
    let mut experiment = experiment(
        directory.path().join("episodes.jsonl"),
        RetryClient {
            requests: requests.clone(),
        },
    );
    let instances = experiment.discover(&context).unwrap();
    assert_eq!(instances.len(), 1);
    let requests = requests.borrow();
    assert_eq!(requests.len(), 4);
    assert_eq!(
        requests[0]["state"]["decision_stage"],
        "quantifier_selection"
    );
    assert_eq!(requests[1]["state"]["decision_stage"], "instantiation");
    assert_eq!(
        requests[2]["state"]["decision_stage"],
        "quantifier_selection"
    );
    assert_eq!(requests[3]["state"]["decision_stage"], "instantiation");
    assert_ne!(
        requests[1]["state"]["selected_axiom"]["id"],
        requests[3]["state"]["selected_axiom"]["id"]
    );
    for request in requests.iter() {
        assert_eq!(request["state"]["model"], requests[0]["state"]["model"]);
        if request["state"]["decision_stage"] == "quantifier_selection" {
            assert!(request["state"].get("terms").is_none());
        } else {
            assert!(request["state"]["terms"].is_array());
            assert_eq!(request["state"]["terms"], requests[1]["state"]["terms"]);
        }
    }
    assert_eq!(requests[0]["state"]["model"], requests[1]["state"]["model"]);
    assert_eq!(
        requests[2]["state"]["failure_summary"]["failure_counts"]["false_antecedent"],
        1
    );
    assert_eq!(smt.native_model_to_string().unwrap(), original);
    let log = std::fs::read_to_string(directory.path().join("episodes.jsonl")).unwrap();
    let records = log
        .lines()
        .map(|line| serde_json::from_str::<Value>(line).unwrap())
        .collect::<Vec<_>>();
    assert_eq!(records.last().unwrap()["outcome"], "violated");
    assert_eq!(records.last().unwrap()["attempts"], 2);
    let first_result = records
        .iter()
        .find(|r| r["event"] == "attempt_result")
        .unwrap();
    let history = &requests[2]["state"]["failure_summary"];
    assert_eq!(history["total_failures"], 1);
    assert_eq!(
        history["latest_failure"]["failure"]["bindings"],
        first_result["feedback"]["bindings"]
    );
    assert!(!history.to_string().contains("probabilities"));
    assert!(!history.to_string().contains("observations"));
    assert!(first_result["feedback"]["observations"].is_object());
    assert!(first_result["response"]["answers"]
        .as_object()
        .unwrap()
        .values()
        .all(|a| a["probabilities"].is_object()));
    assert!(requests[1]["state"].get("attempts").is_none());
    for question in requests[2]["questions"].as_object().unwrap().values() {
        assert!(question["instructions"]
            .as_str()
            .unwrap()
            .contains("false_antecedent"));
    }
    assert_eq!(requests[1]["state"]["terms"], requests[3]["state"]["terms"]);
    let costs = records
        .iter()
        .filter(|r| r["event"] == "attempt_result" || r["event"] == "axiom_result")
        .map(|r| r["cost"]["estimated_usd"].as_f64().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(costs.len(), 4);
    assert!(costs.iter().all(|cost| (*cost - 0.0000042).abs() < 1e-15));
}

#[test]
fn invalid_retry_retains_feedback_without_copying_malformed_answers() {
    let request = json!({"questions":{"axiom":{},"q0_idx":{}}});
    let response = json!({"answers":{"axiom":{"choice":"q0"},"q0_idx":{"choice":42,"probabilities":{"huge":1}}}});
    let feedback = json!({"outcome":"invalid","error":"missing choice for q0_idx"});
    let mut summary = FailureSummary::default();
    summary.record(&request, &response, &feedback);
    let history = serde_json::to_value(summary).unwrap();
    assert_eq!(
        history["latest_failure"]["failure"]["choices"],
        json!({"axiom":"q0"})
    );
    assert_eq!(
        history["latest_failure"]["failure"]["error"],
        feedback["error"]
    );
}

struct FailingClient;

struct AlternativesClient {
    requests: Rc<RefCell<Vec<Value>>>,
}
impl DecisionClient for AlternativesClient {
    fn decide(&mut self, request: &Value) -> anyhow::Result<Value> {
        self.requests.borrow_mut().push(request.clone());
        let mut answer = response(request, "read-after-write");
        if request["state"]["decision_stage"] == "instantiation" {
            for (name, question) in request["questions"].as_object().unwrap() {
                let chosen = answer["answers"][name]["choice"]
                    .as_str()
                    .unwrap()
                    .to_owned();
                let mut probabilities = serde_json::Map::new();
                for id in question["criteria"].as_object().unwrap().keys() {
                    let expression = request["state"]["terms"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .find(|t| t["id"] == *id)
                        .unwrap()["expression"]
                        .as_str()
                        .unwrap();
                    let p = if name.ends_with("_val") {
                        match expression {
                            "7" => 0.6,
                            "8" => 0.4,
                            _ => 0.0,
                        }
                    } else if id == &chosen {
                        1.0
                    } else {
                        0.0
                    };
                    probabilities.insert(id.clone(), json!(p));
                }
                answer["answers"][name]["probabilities"] = json!(probabilities);
            }
        }
        Ok(answer)
    }
}

#[test]
fn second_ranked_binding_finds_violation_without_another_api_call() {
    let smt = fixture_from(
        r#"
        (declare-fun a () (Array Int Int))
        (define-fun init () Bool (! (and
            (= (select (store a 1 7) 1) 7)
            (= (select (store a 1 8) 1) 9)) :init true))
        (define-fun trans () Bool (! true :trans true))
        (define-fun prop () Bool (! (= (select (store a 1 8) 1) 8) :invar-property 0))
    "#,
    );
    let pending = HashSet::new();
    let context = DiscoveryContext {
        smt: &smt,
        depth: 0,
        refinement_step: 0,
        model_version: 1,
        pending: &pending,
    };
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("episodes.jsonl");
    let requests = Rc::new(RefCell::new(vec![]));
    let mut experiment = experiment(
        path.clone(),
        AlternativesClient {
            requests: requests.clone(),
        },
    );
    experiment.options.jev_candidates = 10;
    let instances = experiment.discover(&context).unwrap();
    assert_eq!(instances.len(), 1);
    assert_eq!(
        instances[0].term.to_string(),
        "(= (Read_Int_Int (Write_Int_Int a@0 1 8) 1) 8)"
    );
    assert_eq!(requests.borrow().len(), 2);
    let records = std::fs::read_to_string(path)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str::<Value>(line).unwrap())
        .collect::<Vec<_>>();
    let candidates = records
        .iter()
        .filter(|r| r["event"] == "candidate_result")
        .collect::<Vec<_>>();
    assert_eq!(candidates.len(), 2);
    assert_eq!(candidates[0]["feedback"]["outcome"], "instance_true");
    assert_eq!(candidates[1]["feedback"]["outcome"], "violated");
    assert_eq!(candidates[1]["matches_model_choice"], false);
    let result = records
        .iter()
        .find(|r| r["event"] == "attempt_result")
        .unwrap();
    assert_eq!(result["successful_rank"], 2);
    assert_eq!(result["candidates_checked"], 2);
    assert_eq!(
        records.iter().filter(|r| r.get("cost").is_some()).count(),
        2
    );
    assert_eq!(records.last().unwrap()["attempts"], 1);
}

#[test]
fn repeated_failures_are_counted_once_without_observation_history() {
    let mut summary = FailureSummary::default();
    let failure = json!({"outcome":"instance_true","reason":"false_antecedent",
        "rule":"write-does-not-overwrite","instance":"same instance",
        "bindings":{"?idx":"i@0","?c":"i@0"},
        "observations":{"large":"retained only in the log"}});
    for _ in 0..73 {
        summary.record(&json!({}), &json!({}), &failure);
    }
    let compact = serde_json::to_value(&summary).unwrap();
    assert_eq!(compact["total_failures"], 73);
    assert_eq!(compact["failure_counts"]["false_antecedent"], 73);
    assert_eq!(compact["failed_substitutions"].as_array().unwrap().len(), 1);
    assert_eq!(compact["failed_substitutions"][0]["count"], 73);
    assert!(!compact.to_string().contains("observations"));
    summary.record(
        &json!({}),
        &json!({}),
        &json!({"outcome":"already_present","instance":"another instance"}),
    );
    let compact = serde_json::to_value(&summary).unwrap();
    assert_eq!(compact["total_failures"], 74);
    assert_eq!(compact["failure_counts"]["already_present"], 1);
    assert_eq!(compact["failed_substitutions"].as_array().unwrap().len(), 2);
    assert_eq!(
        compact["latest_failure"]["failure"]["reason"],
        "already_present"
    );
}

#[test]
fn snapshot_reports_only_installed_successes_in_normalized_notation() {
    let mut smt = fixture();
    let pending = HashSet::new();
    let context = DiscoveryContext {
        smt: &smt,
        depth: 0,
        refinement_step: 0,
        model_version: 1,
        pending: &pending,
    };
    let snapshot = Snapshot::capture(&context).unwrap();
    assert_eq!(
        snapshot.state["successful_instantiations"]["instances"],
        json!([])
    );
    let request = binding_request(&snapshot, "write-does-not-overwrite");
    let instance = snapshot
        .proposal(&request, &response(&request, "write-does-not-overwrite"))
        .unwrap();
    let normalized = smt.make_unquantified_instance(instance.term).unwrap();
    let installed = normalized.get_term().to_string();
    let result = smt.add_instantiation(
        crate::instance_installation::request::InstantiationRequest::untracked(normalized),
    );
    assert!(result.abstract_instance_added);
    assert_eq!(smt.check_property(), SolverCheckResult::Sat);
    let context = DiscoveryContext {
        smt: &smt,
        depth: 0,
        refinement_step: 1,
        model_version: 2,
        pending: &pending,
    };
    let snapshot = Snapshot::capture(&context).unwrap();
    assert_eq!(
        snapshot.state["successful_instantiations"]["instances"],
        json!([installed])
    );
    let request = binding_request(&snapshot, "write-does-not-overwrite");
    assert_eq!(request["state"]["failure_summary"]["total_failures"], 0);
}

impl DecisionClient for FailingClient {
    fn decide(&mut self, _: &Value) -> anyhow::Result<Value> {
        anyhow::bail!("simulated timeout")
    }
}

struct BindingFailureClient;
impl DecisionClient for BindingFailureClient {
    fn decide(&mut self, request: &Value) -> anyhow::Result<Value> {
        if request["state"]["decision_stage"] == "quantifier_selection" {
            Ok(response(request, "read-after-write"))
        } else {
            anyhow::bail!("simulated binding timeout")
        }
    }
}

#[test]
fn binding_transport_failure_keeps_selection_cost_and_stops_the_episode() {
    let smt = fixture();
    let pending = HashSet::new();
    let context = DiscoveryContext {
        smt: &smt,
        depth: 0,
        refinement_step: 0,
        model_version: 1,
        pending: &pending,
    };
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("episodes.jsonl");
    let mut experiment = experiment(path.clone(), BindingFailureClient);
    assert!(experiment.discover(&context).unwrap().is_empty());
    let records = std::fs::read_to_string(path)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str::<Value>(line).unwrap())
        .collect::<Vec<_>>();
    assert_eq!(
        records.iter().filter(|r| r["event"] == "request").count(),
        2
    );
    let selection = records
        .iter()
        .find(|r| r["event"] == "axiom_result")
        .unwrap();
    assert_eq!(selection["cost"]["status"], "estimated");
    let error = records
        .iter()
        .find(|r| r["event"] == "transport_error")
        .unwrap();
    assert_eq!(error["stage"], "instantiation");
    assert_eq!(error["cost"]["status"], "unknown");
    assert!(!records.iter().any(|r| r["event"] == "attempt_result"));
    assert_eq!(records.last().unwrap()["ordinary_fallback"], true);
    assert_eq!(records.last().unwrap()["attempts"], 1);
}

#[test]
fn transport_failure_falls_back_and_shared_installation_still_proves_the_input() {
    let directory = tempfile::tempdir().unwrap();
    let policy = YardbirdPolicy::<ArrayBMCCost>::new(())
        .with_effort(DiscoveryFirst::default())
        .with_discovery(experiment(
            directory.path().join("episodes.jsonl"),
            FailingClient,
        ));
    let strategy = Abstract::new(1, false, policy, true);
    let mut options = YardbirdOptions::from_filename("fixture.vmt".into());
    options.profile = true;
    let mut driver = crate::Driver::new(
        model(INPUT),
        Box::new(FullUnrollStrategy::new()),
        SolverBackend::Z3,
    )
    .with_profiler(options.build_profiler())
    .with_wall_timeout(Some(std::time::Duration::from_secs(10)));
    let result = driver.check_strategy(1, Box::new(strategy)).unwrap();
    assert!(!result.counterexample);
    assert!(result.total_instantiations_added > 0);
    let operations = result
        .profiling
        .cost_records
        .iter()
        .flat_map(|r| &r.effort)
        .collect::<Vec<_>>();
    assert!(operations
        .iter()
        .any(|r| r.operation == "PolicyCandidates" && r.report.selected == 0));
    assert!(operations
        .iter()
        .any(|r| r.operation == "ArrayCandidates" && r.report.selected > 0));
}

#[test]
fn oversized_and_dry_run_requests_never_call_the_client_or_truncate_the_log() {
    let smt = fixture();
    let pending = HashSet::new();
    let context = DiscoveryContext {
        smt: &smt,
        depth: 0,
        refinement_step: 0,
        model_version: 1,
        pending: &pending,
    };
    for oversized in [false, true] {
        let directory = tempfile::tempdir().unwrap();
        let requests = Rc::new(RefCell::new(vec![]));
        let path = directory.path().join("episodes.jsonl");
        let mut experiment = experiment(
            path.clone(),
            RetryClient {
                requests: requests.clone(),
            },
        );
        if oversized {
            experiment.options.jev_max_request_bytes = 1;
        } else {
            experiment.options.jev_dry_run = true;
        }
        assert!(experiment.discover(&context).unwrap().is_empty());
        assert!(requests.borrow().is_empty());
        let log = std::fs::read_to_string(path).unwrap();
        let records = log
            .lines()
            .map(|l| serde_json::from_str::<Value>(l).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(
            records[0]["request"]["state"]["model"],
            smt.native_model_to_string().unwrap()
        );
        assert_eq!(
            records.last().unwrap()["outcome"],
            if oversized {
                "request_too_large"
            } else {
                "dry_run"
            }
        );
    }
}

#[test]
fn successful_proposal_reaches_shared_installation_without_ordinary_matching() {
    let directory = tempfile::tempdir().unwrap();
    let requests = Rc::new(RefCell::new(vec![]));
    let policy = YardbirdPolicy::<ArrayBMCCost>::new(())
        .with_instantiation_ranker(Box::new(TermCostInstantiationRanker))
        .with_effort(DiscoveryFirst::default())
        .with_discovery(experiment(
            directory.path().join("episodes.jsonl"),
            RetryClient { requests },
        ));
    let mut options = YardbirdOptions::from_filename("fixture.vmt".into());
    options.profile = true;
    let mut driver = crate::Driver::new(
        model(INPUT),
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
    assert!(operations
        .iter()
        .any(|r| r.operation == "PolicyCandidates" && r.report.selected == 1));
    assert!(!operations.iter().any(|r| r.operation == "ArrayCandidates"));
}

struct InvalidClient;
impl DecisionClient for InvalidClient {
    fn decide(&mut self, _: &Value) -> anyhow::Result<Value> {
        Ok(json!({"answers":{}}))
    }
}

#[test]
fn invalid_answers_exhaust_exactly_the_retry_budget_and_never_become_instances() {
    let smt = fixture();
    let pending = HashSet::new();
    let context = DiscoveryContext {
        smt: &smt,
        depth: 0,
        refinement_step: 0,
        model_version: 1,
        pending: &pending,
    };
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("episodes.jsonl");
    let mut experiment = experiment(path.clone(), InvalidClient);
    assert!(experiment.discover(&context).unwrap().is_empty());
    let log = std::fs::read_to_string(path).unwrap();
    let records = log
        .lines()
        .map(|l| serde_json::from_str::<Value>(l).unwrap())
        .collect::<Vec<_>>();
    assert_eq!(
        records
            .iter()
            .filter(|r| r["event"] == "attempt_result")
            .count(),
        3
    );
    assert_eq!(records.last().unwrap()["outcome"], "attempts_exhausted");
    assert_eq!(records.last().unwrap()["ordinary_fallback"], true);
}

#[test]
fn constant_axiom_uses_shared_schema_and_unknown_evaluation_is_not_a_violation() {
    let smt = fixture();
    let pending = HashSet::new();
    let context = DiscoveryContext {
        smt: &smt,
        depth: 0,
        refinement_step: 0,
        model_version: 1,
        pending: &pending,
    };
    let snapshot = Snapshot::capture(&context).unwrap();
    let schema = snapshot
        .schemas
        .iter()
        .find(|s| s.name().starts_with("constant-array"))
        .unwrap();
    let bindings = std::collections::BTreeMap::from([
        ("a".into(), "7".parse().unwrap()),
        ("b".into(), "1".parse().unwrap()),
    ]);
    let instance = schema.instantiate(&bindings).unwrap();
    assert_eq!(
        instance.term.to_string(),
        "(= (Read_Int_Int (ConstArr_Int_Int 7) 1) 7)"
    );
    let unknown_smt = fixture_from(
        r#"
        (declare-fun a () (Array Int Int))
        (define-fun init () Bool (! true :init true))
        (define-fun trans () Bool (! true :trans true))
        (define-fun prop () Bool (! false :invar-property 0))
    "#,
    );
    let unknown_context = DiscoveryContext {
        smt: &unknown_smt,
        ..context
    };
    let (feedback, accepted) = validate(&unknown_context, instance);
    assert!(accepted.is_none());
    assert_eq!(feedback["outcome"], "undetermined");

    let request = binding_request(&snapshot, "read-after-write");
    let instance = snapshot
        .proposal(&request, &response(&request, "read-after-write"))
        .unwrap();
    let normalized = smt
        .make_unquantified_instance(instance.term.clone())
        .unwrap();
    let pending = HashSet::from([canonical_instantiation_key(normalized.get_term())]);
    let context = DiscoveryContext {
        pending: &pending,
        ..context
    };
    let (feedback, accepted) = validate(&context, instance);
    assert!(accepted.is_none());
    assert_eq!(feedback["outcome"], "already_present");
}

#[test]
fn cli_dry_run_needs_no_key_and_options_survive_serialization() {
    use clap::Parser;
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("episodes.jsonl");
    let options = YardbirdOptions::try_parse_from([
        "yardbird",
        "-f",
        "examples/array/array_copy.vmt",
        "--policy",
        "decision-model",
        "--jev-dry-run",
        "--jev-log",
        path.to_str().unwrap(),
    ])
    .unwrap();
    options.decision_model.validate(&options).unwrap();
    assert!(options.profiling_enabled());
    let decoded: YardbirdOptions =
        serde_json::from_value(serde_json::to_value(&options).unwrap()).unwrap();
    assert_eq!(decoded.decision_model.jev_log, Some(path));
    let mut invalid = options.clone();
    invalid.decision_model.jev_attempts = 0;
    assert!(invalid.decision_model.validate(&invalid).is_err());
    for rate in [-1.0, f64::NAN, f64::INFINITY] {
        invalid = options.clone();
        invalid.decision_model.jev_input_usd_per_million = rate;
        assert!(invalid.decision_model.validate(&invalid).is_err());
    }
    invalid = options;
    invalid.policy = None;
    assert!(invalid.decision_model.validate(&invalid).is_err());
}

#[test]
fn query_cost_uses_reported_usage_and_preserves_unknowns() {
    let mut options = DecisionModelOptions::default();
    let response = json!({"usage":{"input_tokens":1_000_000,"output_tokens":200}});
    assert_eq!(query_cost(&response, &options)["estimated_usd"], 0.042);
    assert_eq!(
        query_cost(&json!({"usage":{"input_tokens":0}}), &options)["estimated_usd"],
        0.0
    );
    assert_eq!(query_cost(&Value::Null, &options)["status"], "unknown");
    assert!(query_cost(&json!({"usage":{"input_tokens":-1}}), &options)["estimated_usd"].is_null());
    options.jev_output_usd_per_million = 2.0;
    assert_eq!(query_cost(&response, &options)["estimated_usd"], 0.0424);
    assert!(
        query_cost(&json!({"usage":{"input_tokens":100}}), &options)["estimated_usd"].is_null()
    );
}
