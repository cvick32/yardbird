use super::*;
use crate::{agent_interaction::AgentOptions, Driver};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};

fn options(root: &std::path::Path, source: &str, depth: u16) -> YardbirdOptions {
    let path = root.join("input.vmt");
    std::fs::write(&path, source).unwrap();
    YardbirdOptions {
        filename: Some(path.to_str().unwrap().into()),
        depth,
        wall_timeout_secs: Some(30),
        one_shot: OneShotOptions {
            one_shot: true,
            one_shot_placement: Some(BatchPlacement::Exact),
            ..Default::default()
        },
        agent: AgentOptions {
            mode: Some(AgentMode::Bedrock),
            agent_log: Some(root.join("events.jsonl")),
            agent_max_calls: 1,
            ..Default::default()
        },
        ..Default::default()
    }
}

struct Fake {
    calls: Arc<AtomicUsize>,
    batch: Box<dyn Fn(&Value) -> Value>,
}
impl LlmClient for Fake {
    fn infer(&mut self, request: &Value) -> anyhow::Result<Value> {
        assert_eq!(
            self.calls.fetch_add(1, Ordering::SeqCst),
            0,
            "only one inference allowed"
        );
        assert_eq!(request["tool_choice"]["name"], "submit_instantiations");
        assert_eq!(request["tools"].as_array().unwrap().len(), 1);
        let context: Value =
            serde_json::from_str(request["input"][1]["content"].as_str().unwrap())?;
        assert!(context.get("model").is_none());
        assert!(context.get("successful_instantiations").is_none());
        let batch = (self.batch)(&context);
        Ok(
            json!({"status":"completed","output":[{"type":"function_call","name":"submit_instantiations","arguments":batch.to_string()}],"usage":{"input_tokens":100,"output_tokens":200}}),
        )
    }
}

fn run_fake(options: &YardbirdOptions, batch: impl Fn(&Value) -> Value + 'static) -> Report {
    let calls = Arc::new(AtomicUsize::new(0));
    let report = execute(
        options,
        Some(Box::new(Fake {
            calls: calls.clone(),
            batch: Box::new(batch),
        })),
    )
    .unwrap();
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(report.calls, 1);
    assert_eq!(report.symbolic_refinements, 0);
    report
}

fn facts(count: usize) -> String {
    let prop = (0..count)
        .map(|n| format!("(marked {n})"))
        .collect::<Vec<_>>()
        .join(" ");
    format!("(declare-fun marked (Int) Bool)\n(define-fun init () Bool (! (forall ((n Int)) (marked n)) :init true))\n(define-fun trans () Bool (! true :trans true))\n(define-fun prop () Bool (! (and {prop}) :invar-property 0))\n")
}

#[test]
fn one_call_installs_more_than_sixteen_typed_instances_without_a_model_or_search() {
    let root = tempfile::tempdir().unwrap();
    let options = options(root.path(), &facts(24), 1);
    let report = run_fake(&options, |context| {
        let schema = context["axioms"]
            .as_array()
            .unwrap()
            .iter()
            .find(|s| s["provenance"]["direction"] == "instance")
            .unwrap();
        let mut proposals = (0..24)
            .map(|n| json!({"schema_id":schema["id"],"bindings":{"variable_0":n.to_string()}}))
            .collect::<Vec<_>>();
        proposals.push(proposals[0].clone());
        json!({"rationale":"Instantiate the universal fact at every property argument.","instantiations":proposals})
    });
    assert_eq!(report.status, "bounded_complete", "{report:?}");
    assert_eq!(report.closed_depths, vec![0]);
    assert_eq!(report.proposed_instances, 25);
    assert_eq!(report.installed_instances, 24);
    assert_eq!(report.duplicates, 1);
}

#[test]
fn incomplete_batch_returns_countermodel_without_native_completion() {
    let root = tempfile::tempdir().unwrap();
    let options = options(root.path(), &facts(2), 1);
    let report = run_fake(
        &options,
        |_| json!({"rationale":"Intentionally incomplete test batch.","instantiations":[]}),
    );
    assert_eq!(report.status, "incomplete");
    assert_eq!(report.unresolved_depths, vec![0]);
    assert_eq!(report.installed_instances, 0);
    let log = std::fs::read_to_string(&report.log).unwrap();
    assert!(log.contains("remaining_countermodel"));
}

#[test]
fn bundled_prompt_example_closes_a_real_query_that_empty_advice_does_not() {
    let source = r#"
(declare-fun flags () (Array Int Bool))
(declare-fun flags_next () (Array Int Bool))
(declare-fun probe () Int)
(declare-fun probe_next () Int)
(define-fun .flags () (Array Int Bool) (! flags :next flags_next))
(define-fun .probe () Int (! probe :next probe_next))
(define-fun init () Bool (! (= flags ((as const (Array Int Bool)) false)) :init true))
(define-fun trans () Bool (! (and (= flags_next flags) (= probe_next probe)) :trans true))
(define-fun prop () Bool (! (not (select flags probe)) :invar-property 0))
"#;
    let empty_root = tempfile::tempdir().unwrap();
    let empty = run_fake(
        &options(empty_root.path(), source, 1),
        |_| json!({"rationale":"Control with no array semantics.","instantiations":[]}),
    );
    assert_eq!(empty.unresolved_depths, vec![0]);

    let example_root = tempfile::tempdir().unwrap();
    let report = run_fake(&options(example_root.path(), source, 1), |context| {
        // Exercise the exact JSON printed in the prompt, changing only its
        // illustrative schema ID to the ID offered by this actual catalogue.
        let example = include_str!("prompt.md")
            .split_once("```json\n")
            .unwrap()
            .1
            .split_once("```")
            .unwrap()
            .0;
        let mut batch: Value = serde_json::from_str(example).unwrap();
        let schema = context["axioms"]
            .as_array()
            .unwrap()
            .iter()
            .find(|s| s["body"].as_str().unwrap().contains("ConstArr_Int_Bool"))
            .unwrap();
        batch["instantiations"][0]["schema_id"] = schema["id"].clone();
        batch
    });
    assert_eq!(report.status, "bounded_complete", "{report:?}");
    assert_eq!(report.closed_depths, vec![0]);
    assert_eq!(report.installed_instances, 1);
}

#[test]
fn inline_constructed_term_needs_no_retrieval_or_term_creation_call() {
    let root = tempfile::tempdir().unwrap();
    let options = options(root.path(), &facts(2), 1);
    let report = run_fake(&options, |context| {
        let schema = context["axioms"]
            .as_array()
            .unwrap()
            .iter()
            .find(|s| s["provenance"]["direction"] == "instance")
            .unwrap();
        json!({"rationale":"Construct arithmetic arguments inline.","instantiations":[
            {"schema_id":schema["id"],"bindings":{"variable_0":"(- 1 1)"}},
            {"schema_id":schema["id"],"bindings":{"variable_0":"(+ 0 1)"}}]})
    });
    assert_eq!(report.status, "bounded_complete", "{report:?}");
    assert_eq!(report.installed_instances, 2);
}

#[test]
fn expired_budget_and_oversized_context_make_no_provider_calls() {
    struct Never;
    impl LlmClient for Never {
        fn infer(&mut self, _: &Value) -> anyhow::Result<Value> {
            panic!("provider must not run")
        }
    }
    for expired in [true, false] {
        let root = tempfile::tempdir().unwrap();
        let mut options = options(root.path(), &facts(2), 1);
        if expired {
            options.wall_timeout_secs = Some(0);
        } else {
            options.agent.agent_max_request_bytes = 1;
        }
        let report = execute(&options, Some(Box::new(Never))).unwrap();
        assert_eq!(report.status, if expired { "timeout" } else { "error" });
        assert_eq!(report.calls, 0);
        assert_eq!(report.installed_instances, 0);
    }
}

#[test]
fn invalid_late_proposal_rejects_the_entire_batch_before_installation() {
    let root = tempfile::tempdir().unwrap();
    let options = options(root.path(), &facts(2), 1);
    let report = run_fake(&options, |context| {
        let schema = context["axioms"]
            .as_array()
            .unwrap()
            .iter()
            .find(|s| s["provenance"]["direction"] == "instance")
            .unwrap();
        json!({"rationale":"Test atomic validation.","instantiations":[
            {"schema_id":schema["id"],"bindings":{"variable_0":"0"}},
            {"schema_id":schema["id"],"bindings":{"variable_0":"true"}}]})
    });
    assert_eq!(report.status, "error");
    assert!(report.error.unwrap().contains("wrong sort"));
    assert_eq!(report.installed_instances, 0);
    assert!(report.closed_depths.is_empty());
}

#[test]
fn future_transition_unsat_cannot_hide_an_earlier_counterexample() {
    let root = tempfile::tempdir().unwrap();
    let options = options(root.path(),"(declare-fun bad () Bool)\n(declare-fun bad_next () Bool)\n(define-fun .bad () Bool (! bad :next bad_next))\n(define-fun init () Bool (! (not bad) :init true))\n(define-fun trans () Bool (! false :trans true))\n(define-fun prop () Bool (! bad :invar-property 0))",2);
    let report = run_fake(
        &options,
        |_| json!({"rationale":"Test each prefix independently.","instantiations":[]}),
    );
    assert_eq!(report.status, "incomplete", "{report:?}");
    assert_eq!(report.unresolved_depths, vec![0]);
    assert_eq!(report.closed_depths, vec![1]);
}

#[test]
fn german_native_export_replays_exact_ground_instances_and_rejects_tampering() {
    let root = tempfile::tempdir().unwrap();
    let artifact = root.path().join("native.json");
    let mut options = YardbirdOptions {
        filename: Some("examples/distributed_protocols/german/german.encoding.vmt".into()),
        depth: 4,
        policy: Some(crate::policy::NamedPolicy::GermanFast),
        wall_timeout_secs: Some(30),
        one_shot: OneShotOptions {
            export_instantiations: Some(artifact.clone()),
            ..Default::default()
        },
        ..Default::default()
    };
    let recorder = Recorder::default();
    let plan = options.build_array_proof_plan();
    let mut driver = Driver::new(
        crate::model_from_options(&options),
        plan.instantiation_strategy,
        plan.solver,
    );
    driver.add_extension(recorder.clone());
    let native = driver.check_strategy(options.depth, plan.strategy).unwrap();
    recorder.save(&options, &native).unwrap();
    options.one_shot.export_instantiations = None;
    options.one_shot.replay_instantiations = Some(artifact.clone());
    options.agent.agent_log = Some(root.path().join("replay.jsonl"));
    let replay = execute(&options, None).unwrap();
    assert_eq!(replay.status, "bounded_complete", "{replay:?}");
    assert_eq!(replay.closed_depths, vec![0, 1, 2, 3]);
    assert_eq!(replay.calls, 0);
    assert_eq!(replay.proposed_instances as u64, replay.installed_instances);
    let mut data: Value = serde_json::from_reader(File::open(&artifact).unwrap()).unwrap();
    data["formulas"]
        .as_array_mut()
        .unwrap()
        .push(json!("false"));
    std::fs::write(&artifact, serde_json::to_vec(&data).unwrap()).unwrap();
    options.agent.agent_log = Some(root.path().join("tampered.jsonl"));
    let invalid = execute(&options, None).unwrap();
    assert_eq!(invalid.status, "error");
    assert_eq!(invalid.installed_instances, 0);
    assert!(invalid.error.unwrap().contains("trusted schema"));
}

#[test]
fn truncation_extra_fields_and_other_tools_are_not_partial_solutions() {
    assert!(decode(&json!({"status":"incomplete","output":[]})).is_err());
    let response = |name: &str, arguments: Value| json!({"status":"completed","output":[{"type":"function_call","name":name,"arguments":arguments.to_string()}]});
    assert!(decode(&response("inspect", json!({}))).is_err());
    assert!(decode(&response(
        "submit_instantiations",
        json!({"rationale":"","instantiations":[],"assert":"false"})
    ))
    .is_err());
}

type Respond = dyn FnMut(usize, &Value) -> Value;

struct Sequence {
    calls: Arc<AtomicUsize>,
    respond: Box<Respond>,
}
impl LlmClient for Sequence {
    fn infer(&mut self, request: &Value) -> anyhow::Result<Value> {
        let call = self.calls.fetch_add(1, Ordering::SeqCst);
        let context: Value =
            serde_json::from_str(request["input"][1]["content"].as_str().unwrap())?;
        assert_eq!(context["batch_mode"]["round"], call + 1);
        Ok((self.respond)(call, &context))
    }
}

fn run_sequence(
    options: &YardbirdOptions,
    respond: impl FnMut(usize, &Value) -> Value + 'static,
) -> Report {
    let calls = Arc::new(AtomicUsize::new(0));
    let report = execute(
        options,
        Some(Box::new(Sequence {
            calls: calls.clone(),
            respond: Box::new(respond),
        })),
    )
    .unwrap();
    assert_eq!(report.calls, calls.load(Ordering::SeqCst));
    assert_eq!(report.symbolic_refinements, 0);
    report
}

fn response(proposals: Value) -> Value {
    json!({"status":"completed","output":[{"type":"function_call","name":"submit_instantiations",
        "arguments":json!({"rationale":"Explain reads at the supplied probe frames.","instantiations":proposals}).to_string()}],
        "usage":{"input_tokens":100,"output_tokens":200,"input_tokens_details":{"cached_tokens":50},
            "output_tokens_details":{"reasoning_tokens":10}}})
}

const FRAMED_FLAGS: &str = r#"
(declare-fun flags () (Array Int Bool))
(declare-fun flags_next () (Array Int Bool))
(declare-fun probe () Int)
(declare-fun probe_next () Int)
(define-fun .flags () (Array Int Bool) (! flags :next flags_next))
(define-fun .probe () Int (! probe :next probe_next))
(define-fun init () Bool (! (= flags ((as const (Array Int Bool)) false)) :init true))
(define-fun trans () Bool (! (= flags_next flags) :trans true))
(define-fun prop () Bool (! (not (select flags probe)) :invar-property 0))
"#;

fn constant_at(context: &Value, frame: u16) -> Value {
    let schema = context["axioms"]
        .as_array()
        .unwrap()
        .iter()
        .find(|s| s["body"].as_str().unwrap().contains("ConstArr_Int_Bool"))
        .unwrap();
    json!({"schema_id":schema["id"],"bindings":{"a":"false","b":format!("probe@{frame}")}})
}

fn events(report: &Report) -> Vec<Value> {
    std::fs::read_to_string(&report.log)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect()
}

#[test]
fn retries_accumulate_instances_with_model_feedback_and_skip_proved_bounds() {
    let root = tempfile::tempdir().unwrap();
    let mut options = options(root.path(), FRAMED_FLAGS, 2);
    options.agent.agent_max_calls = 0;
    let report = run_sequence(&options, |call, context| match call {
        0 => {
            assert!(context.get("feedback").is_none());
            response(json!([constant_at(context, 0)]))
        }
        1 => {
            let feedback = &context["feedback"];
            assert_eq!(feedback["closed_depths"], json!([0]));
            assert_eq!(feedback["unresolved_depths"], json!([1]));
            assert_eq!(feedback["remaining_countermodel"]["depth"], 1);
            assert!(!feedback["remaining_countermodel"]["model"]
                .as_str()
                .unwrap()
                .is_empty());
            assert_eq!(feedback["accepted_instances"].as_array().unwrap().len(), 1);
            // Repeated proposals are deduplicated across responses.
            response(json!([constant_at(context, 0), constant_at(context, 1)]))
        }
        _ => panic!("must stop once both bounds are proved"),
    });
    assert_eq!(report.status, "bounded_complete", "{report:?}");
    assert_eq!(report.stop_reason.as_deref(), Some("bounded_complete"));
    assert_eq!(report.closed_depths, vec![0, 1]);
    assert!(report.unresolved_depths.is_empty());
    assert_eq!(report.calls, 2);
    assert_eq!(report.proposed_instances, 3);
    assert_eq!(report.unique_instances, 2);
    assert_eq!(report.installed_instances, 2);
    assert_eq!(report.replayed_assertions, 1);
    assert_eq!(report.duplicates, 1);
    assert_eq!(report.usage["input_tokens"], 200);
    assert_eq!(report.usage["input_tokens_details"]["cached_tokens"], 100);
    assert_eq!(
        report.usage["output_tokens_details"]["reasoning_tokens"],
        20
    );
    let checks: Vec<_> = events(&report)
        .into_iter()
        .filter(|e| e["event"] == "check")
        .map(|e| (e["round"].as_u64().unwrap(), e["depth"].as_u64().unwrap()))
        .collect();
    assert_eq!(checks, vec![(1, 0), (1, 1), (2, 1)]);
}

#[test]
fn invalid_batch_can_be_repaired_without_losing_previous_instances() {
    let root = tempfile::tempdir().unwrap();
    let mut options = options(root.path(), FRAMED_FLAGS, 2);
    options.agent.agent_max_calls = 0;
    let report = run_sequence(&options, |call, context| match call {
        0 => response(json!([constant_at(context, 0)])),
        1 => {
            let mut invalid = constant_at(context, 1);
            invalid["bindings"]["b"] = json!("true");
            response(json!([constant_at(context, 1), invalid]))
        }
        2 => {
            let feedback = &context["feedback"];
            assert_eq!(feedback["accepted_instances"].as_array().unwrap().len(), 1);
            assert_eq!(feedback["closed_depths"], json!([0]));
            assert_eq!(feedback["previous_attempt"]["accepted"], false);
            assert!(feedback["previous_attempt"]["validation_error"]
                .as_str()
                .unwrap()
                .contains("wrong sort"));
            response(json!([constant_at(context, 1)]))
        }
        _ => panic!("repair should close the target"),
    });
    assert_eq!(report.status, "bounded_complete", "{report:?}");
    assert_eq!(report.rejected_batches, 1);
    assert_eq!(report.installed_instances, 2);
    assert_eq!(report.unique_instances, 2);
    assert!(report.error.is_none());
}

#[test]
fn empty_and_duplicate_batches_keep_trying_until_the_call_cap() {
    let root = tempfile::tempdir().unwrap();
    let mut options = options(root.path(), FRAMED_FLAGS, 2);
    options.agent.agent_max_calls = 3;
    let report = run_sequence(&options, |call, context| match call {
        0 | 1 => response(json!([constant_at(context, 0)])),
        2 => {
            assert_eq!(context["feedback"]["previous_attempt"]["new_instances"], 0);
            assert_eq!(context["feedback"]["remaining_countermodel"]["depth"], 1);
            response(json!([]))
        }
        _ => panic!("call cap exceeded"),
    });
    assert_eq!(report.status, "incomplete");
    assert_eq!(report.stop_reason.as_deref(), Some("call_limit"));
    assert_eq!(report.calls, 3);
    assert_eq!(report.closed_depths, vec![0]);
    assert_eq!(report.unresolved_depths, vec![1]);
    assert_eq!(report.installed_instances, 1);
    assert_eq!(report.duplicates, 1);
    assert_eq!(
        events(&report)
            .iter()
            .filter(|e| e["event"] == "check")
            .count(),
        2
    );
}

#[test]
fn wall_deadline_preserves_progress_and_does_not_install_a_late_reply() {
    let root = tempfile::tempdir().unwrap();
    let mut options = options(root.path(), FRAMED_FLAGS, 2);
    options.agent.agent_max_calls = 0;
    options.wall_timeout_secs = Some(1);
    let report = run_sequence(&options, |call, context| match call {
        0 => response(json!([constant_at(context, 0)])),
        1 => {
            let remaining = context["batch_mode"]["remaining_seconds"].as_f64().unwrap();
            std::thread::sleep(Duration::from_secs_f64(remaining + 0.05));
            response(json!([constant_at(context, 1)]))
        }
        _ => panic!("must not call after deadline"),
    });
    assert_eq!(report.status, "timeout", "{report:?}");
    assert_eq!(report.stop_reason.as_deref(), Some("timeout"));
    assert_eq!(report.calls, 2);
    assert_eq!(report.closed_depths, vec![0]);
    assert_eq!(report.unresolved_depths, vec![1]);
    assert_eq!(report.installed_instances, 1);
    assert_eq!(report.usage["input_tokens"], 200);
}

#[test]
fn truncated_batch_gets_repair_feedback_without_installing_partial_output() {
    let root = tempfile::tempdir().unwrap();
    let mut options = options(root.path(), FRAMED_FLAGS, 1);
    options.agent.agent_max_calls = 0;
    let report = run_sequence(&options, |call, context| match call {
        0 => {
            let mut truncated = response(json!([constant_at(context, 0)]));
            truncated["status"] = json!("incomplete");
            truncated
        }
        1 => {
            assert!(context["feedback"]["accepted_instances"]
                .as_array()
                .unwrap()
                .is_empty());
            assert!(context["feedback"]["previous_attempt"]["validation_error"]
                .as_str()
                .unwrap()
                .contains("response incomplete"));
            response(json!([constant_at(context, 0)]))
        }
        _ => panic!("one repair is enough"),
    });
    assert_eq!(report.status, "bounded_complete", "{report:?}");
    assert_eq!(report.installed_instances, 1);
    assert_eq!(report.rejected_batches, 1);
    assert_eq!(report.calls, 2);
}

#[test]
fn retry_does_not_reuse_later_transitions_to_close_an_earlier_bound() {
    let root = tempfile::tempdir().unwrap();
    let source = r#"
(declare-fun bad () Bool)
(declare-fun bad_next () Bool)
(define-fun .bad () Bool (! bad :next bad_next))
(define-fun init () Bool (! (not bad) :init true))
(define-fun trans () Bool (! false :trans true))
(define-fun prop () Bool (! (and bad (= (select ((as const (Array Int Int)) 0) 0) 0)) :invar-property 0))
"#;
    let mut options = options(root.path(), source, 2);
    options.agent.agent_max_calls = 2;
    let report = run_sequence(&options, |call, context| match call {
        0 => response(json!([])),
        1 => {
            assert_eq!(context["feedback"]["closed_depths"], json!([1]));
            assert_eq!(context["feedback"]["unresolved_depths"], json!([0]));
            let schema = context["axioms"]
                .as_array()
                .unwrap()
                .iter()
                .find(|s| s["body"].as_str().unwrap().contains("ConstArr_Int_Int"))
                .unwrap();
            response(json!([{"schema_id":schema["id"],"bindings":{"a":"0","b":"0"}}]))
        }
        _ => panic!("call limit exceeded"),
    });
    assert_eq!(report.status, "incomplete", "{report:?}");
    assert_eq!(report.closed_depths, vec![1]);
    assert_eq!(report.unresolved_depths, vec![0]);
    assert_eq!(report.installed_instances, 1);
    assert_eq!(report.stop_reason.as_deref(), Some("call_limit"));
    assert!(events(&report).iter().any(|e| e["event"] == "check"
        && e["round"] == 2
        && e["depth"] == 0
        && e["result"] == "sat"));
}

#[test]
fn provider_failure_retains_proof_progress_and_marks_missing_usage() {
    struct FailsOnRetry(usize);
    impl LlmClient for FailsOnRetry {
        fn infer(&mut self, request: &Value) -> anyhow::Result<Value> {
            self.0 += 1;
            if self.0 > 1 {
                anyhow::bail!("fake transport failure");
            }
            let context: Value =
                serde_json::from_str(request["input"][1]["content"].as_str().unwrap())?;
            Ok(response(json!([constant_at(&context, 0)])))
        }
    }
    let root = tempfile::tempdir().unwrap();
    let mut options = options(root.path(), FRAMED_FLAGS, 2);
    options.agent.agent_max_calls = 0;
    let report = execute(&options, Some(Box::new(FailsOnRetry(0)))).unwrap();
    assert_eq!(report.status, "error");
    assert_eq!(report.calls, 2);
    assert_eq!(report.usage_unknown_calls, 1);
    assert_eq!(report.usage["input_tokens"], 100);
    assert_eq!(report.closed_depths, vec![0]);
    assert_eq!(report.unresolved_depths, vec![1]);
    assert_eq!(report.installed_instances, 1);
    assert!(report.error.unwrap().contains("fake transport failure"));
}

#[test]
fn native_schema_replay_closes_all_frames_from_one_shifted_example() {
    let schema_root = tempfile::tempdir().unwrap();
    let mut schema_options = options(schema_root.path(), FRAMED_FLAGS, 6);
    schema_options.one_shot.one_shot_placement = None;
    let schema = run_fake(&schema_options, |context| {
        assert_eq!(context["batch_mode"]["placement"], "schema");
        json!({"rationale":"Reuse the constant-array fact at every probe frame.",
            "instantiations":[constant_at(context, 3), constant_at(context, 5)]})
    });
    assert_eq!(schema.status, "bounded_complete", "{schema:?}");
    assert_eq!(schema.closed_depths, vec![0, 1, 2, 3, 4, 5]);
    assert_eq!(schema.unique_instances, 1);
    assert_eq!(schema.duplicates, 1);
    assert_eq!(schema.installed_instances, 6);
    assert_eq!(schema.calls, 1);
    let exact_root = tempfile::tempdir().unwrap();
    let exact = run_fake(
        &options(exact_root.path(), FRAMED_FLAGS, 6),
        |context| json!({"rationale":"Exact-frame control.","instantiations":[constant_at(context, 3)]}),
    );
    assert_eq!(exact.status, "incomplete");
    assert_eq!(exact.closed_depths, vec![3]);
    assert_eq!(exact.installed_instances, 1);
}

#[test]
fn native_schema_replay_preserves_shared_offsets_and_distinguishes_widths() {
    let root = tempfile::tempdir().unwrap();
    let mut options = options(root.path(), FRAMED_FLAGS, 7);
    options.one_shot.one_shot_placement = None;
    let report = run_fake(&options, |context| {
        let schema = context["axioms"]
            .as_array()
            .unwrap()
            .iter()
            .find(|s| s["name"].as_str().unwrap().contains("read-after-write"))
            .unwrap();
        let at = |a, i| {
            json!({"schema_id":schema["id"],"bindings":{
            "a":format!("flags@{a}"),"idx":format!("probe@{i}"),"val":"false"}})
        };
        json!({"rationale":"Two relative distances, with a shifted duplicate of the first.",
            "instantiations":[at(3,4),at(5,6),at(1,4)]})
    });
    assert_eq!(report.unique_instances, 2);
    assert_eq!(report.duplicates, 1);
    assert_eq!(report.installed_instances, 10);
    let installed: Vec<_> = events(&report)
        .into_iter()
        .filter(|e| e["event"] == "installed")
        .collect();
    assert_eq!(installed.first().unwrap()["depth"], 1);
    for event in installed {
        let depth = event["depth"].as_u64().unwrap();
        let formulas = event["instances"].as_array().unwrap();
        assert_eq!(formulas.len(), if depth >= 3 { 2 } else { 1 });
        for formula in formulas {
            assert!(formula
                .as_str()
                .unwrap()
                .contains(&format!("probe@{depth}")));
            assert!(
                formula
                    .as_str()
                    .unwrap()
                    .contains(&format!("flags@{}", depth - 1))
                    || (depth >= 3
                        && formula
                            .as_str()
                            .unwrap()
                            .contains(&format!("flags@{}", depth - 3)))
            );
        }
    }
}

#[test]
fn schema_mode_retains_binder_guards_when_replaying() {
    let root = tempfile::tempdir().unwrap();
    let source = r#"
(declare-fun marked (Int) Bool)
(declare-fun enabled () Bool)
(declare-fun enabled_next () Bool)
(define-fun .enabled () Bool (! enabled :next enabled_next))
(define-fun init () Bool (! (and (not enabled) (=> enabled (forall ((n Int)) (marked n)))) :init true))
(define-fun trans () Bool (! true :trans true))
(define-fun prop () Bool (! (marked 0) :invar-property 0))
"#;
    let mut options = options(root.path(), source, 3);
    options.one_shot.one_shot_placement = None;
    let report = run_fake(&options, |context| {
        let schema = context["axioms"]
            .as_array()
            .unwrap()
            .iter()
            .find(|s| s["provenance"]["direction"] == "instance")
            .unwrap();
        json!({"rationale":"Instantiate a guarded universal; its guard is not asserted.",
            "instantiations":[{"schema_id":schema["id"],"bindings":{"variable_0":"0"}}]})
    });
    assert_eq!(report.status, "incomplete", "{report:?}");
    assert!(report.closed_depths.is_empty());
    let installed: Vec<_> = events(&report)
        .into_iter()
        .filter(|e| e["event"] == "installed")
        .collect();
    assert!(installed
        .iter()
        .flat_map(|e| e["instances"].as_array().unwrap())
        .all(|formula| formula.as_str().unwrap().starts_with("(=>")));
}

#[test]
fn schema_replay_respects_the_selected_native_installation_policy() {
    let root = tempfile::tempdir().unwrap();
    let mut options = options(root.path(), FRAMED_FLAGS, 3);
    options.one_shot.one_shot_placement = None;
    options.instantiation_strategy = crate::InstantiationStrategyType::NoUnrollOnLoop;
    let report = run_fake(&options, |context| {
        json!({"rationale":"The selected native policy disables later replay.",
            "instantiations":[constant_at(context, 0)]})
    });
    assert_eq!(report.status, "incomplete", "{report:?}");
    assert_eq!(report.closed_depths, vec![0]);
    assert_eq!(report.installed_instances, 1);
}
