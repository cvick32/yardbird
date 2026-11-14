use serde_json::Value;
use std::process::Command;

fn run_frontier_options(source: &str, work: u32, depth: u16) -> (Value, String) {
    let temp = tempfile::tempdir().unwrap();
    let path = temp.path().join("model.vmt");
    std::fs::write(&path, source).unwrap();
    let capture = temp.path().join("capture");
    let mut command = Command::new(env!("CARGO_BIN_EXE_yardbird"));
    command
        .arg("-f")
        .arg(&path)
        .args([
            "--policy",
            "countermodel-guided",
            "--theory",
            "array,quantifiers",
            "--guidance-schedule",
            "supplement",
            "--guidance-transition-order",
            "predecessor-first",
            "--guidance-action-requirements",
            "when-unproductive",
            "--wall-timeout-secs",
            "5",
            "--json-output",
            "--profile",
            "--solver-capture-dir",
        ])
        .arg(&capture)
        .arg("--guidance-work")
        .arg(work.to_string())
        .arg("-d")
        .arg(depth.to_string());
    command.arg("--guided-read-frontiers");
    let output = command.output().unwrap();
    let result: Value = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|e| panic!("{e}: {}", String::from_utf8_lossy(&output.stderr)));
    assert!(
        output.status.success() || result["counterexample"] == true,
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let transcript = std::fs::read_to_string(capture.join("solver-session.smt2")).unwrap();
    (result, transcript)
}

fn schedule(result: &Value) -> usize {
    let mut guided_batches = 0;
    for record in result["profiling"]["cost_records"].as_array().unwrap() {
        let events = record["effort"].as_array().unwrap();
        let operations: Vec<_> = events
            .iter()
            .filter(|e| e["kind"] == "operation" || e["operation"] == "ReturnToDriver")
            .collect();
        if let Some(first) = operations.first() {
            assert_eq!(first["operation"], "CountermodelCandidates");
            if first["report"]["selected"].as_u64().unwrap_or(0) > 0 {
                guided_batches += 1;
                assert_eq!(operations[1]["operation"], "DiscoverDependencies");
                assert_eq!(operations[2]["operation"], "ReturnToDriver");
                assert_eq!(operations[1]["allowance"]["dependency_work"], 128);
            }
        }
    }
    guided_batches
}

fn owns_both(transcript: &str) {
    for forbidden in ["(forall ", "(exists ", "(select ", "(store ", "(Array "] {
        assert!(
            !transcript.contains(forbidden),
            "native theory escaped: {forbidden}"
        );
    }
}

#[test]
fn traced_read_requests_use_reserved_work_and_keep_theory_ownership() {
    let source = r#"
        (declare-fun a () (Array Int Int))
        (declare-fun an () (Array Int Int))
        (define-fun .a () (Array Int Int) (! a :next an))
        (define-fun init () Bool (! (forall ((i Int)) (= (select a i) 0)) :init true))
        (define-fun trans () Bool (! (= an a) :trans true))
        (define-fun prop () Bool (! (= (select a 5) 0) :invar-property 0))
    "#;
    // Stop tracing on the demanded read itself, so its equation needs the
    // reserved continuation instead of being solved inside the trace.
    let (result, transcript) = run_frontier_options(source, 4, 3);
    assert_eq!(result["run_progress"]["termination_reason"], "depth_limit");
    owns_both(&transcript);
    schedule(&result);
    let records = result["profiling"]["cost_records"].as_array().unwrap();
    for name in [
        "traced_frontier_work",
        "traced_frontier_requests_attempted",
        "traced_frontier_instances_selected",
    ] {
        assert!(
            records
                .iter()
                .any(|r| r["counters"][name].as_u64().unwrap_or(0) > 0),
            "missing {name}"
        );
    }
    for event in records.iter().flat_map(|r| r["effort"].as_array().unwrap()) {
        if event["operation"] == "DiscoverDependencies" && event["kind"] == "operation" {
            assert!(
                event["report"]["dependency_work"].as_u64().unwrap()
                    <= event["allowance"]["dependency_work"].as_u64().unwrap()
            );
            assert!(
                event["report"]["examined_substitutions"].as_u64().unwrap()
                    <= event["allowance"]["binder_page_size"].as_u64().unwrap()
            );
        }
    }
}

#[test]
fn traced_read_requests_do_not_verify_an_unsafe_update() {
    let source = r#"
        (declare-fun a () (Array Bool Int))
        (declare-fun an () (Array Bool Int))
        (define-fun .a () (Array Bool Int) (! a :next an))
        (define-fun init () Bool (! (forall ((i Bool)) (= (select a i) 0)) :init true))
        (define-fun trans () Bool (! (= an (store a true 1)) :trans true))
        (define-fun prop () Bool (! (= (select a true) 0) :invar-property 0))
    "#;
    let (result, transcript) = run_frontier_options(source, 2, 2);
    assert_eq!(result["found_proof"], false);
    assert_eq!(result["run_progress"]["deepest_completed_depth"], 0);
    assert!(
        result["counterexample"] == true
            || result["run_progress"]["termination_reason"] == "timeout"
    );
    owns_both(&transcript);
}

#[test]
fn demanded_indices_are_preferred_when_frontier_equations_cannot_match() {
    let source = r#"
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (define-fun init () Bool (! (and (= (select a 5) 1)
            (forall ((i Int)) (=> (= (select a i) 1) (= (select b i) 0)))) :init true))
        (define-fun trans () Bool (! true :trans true))
        (define-fun prop () Bool (! (= (select b 5) 0) :invar-property 0))
    "#;
    let (result, transcript) = run_frontier_options(source, 4, 1);
    assert_eq!(result["run_progress"]["termination_reason"], "depth_limit");
    owns_both(&transcript);
    schedule(&result);
    let records = result["profiling"]["cost_records"].as_array().unwrap();
    assert!(records
        .iter()
        .any(|r| r["counters"]["demanded_index_instances_selected"]
            .as_u64()
            .unwrap_or(0)
            > 0));
}
