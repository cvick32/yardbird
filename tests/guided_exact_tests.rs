use serde_json::Value;
use std::process::Command;

fn run(source: &str, exact: bool, work: u32, depth: u16) -> (Value, String) {
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
    if exact {
        command.arg("--guided-exact-grounding");
    }
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
        assert!(
            events.iter().all(|e| e["operation"] != "GroundBinders"),
            "exact grounding must not introduce a preemptive operation"
        );
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
fn guided_exact_runs_only_inside_scheduled_binder_work() {
    let source = r#"
        (declare-fun a () (Array Int Int))
        (declare-fun mark (Int) Bool)
        (assert (forall ((i Int)) (mark i)))
        (define-fun init () Bool (! true :init true))
        (define-fun trans () Bool (! true :trans true))
        (define-fun prop () Bool (! (and (mark 7)
            (= (select (store a 3 9) 3) 9)) :invar-property 0))
    "#;
    let (result, transcript) = run(source, true, 1, 2);
    assert_eq!(result["run_progress"]["termination_reason"], "depth_limit");
    let selected: u64 = result["profiling"]["cost_records"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| {
            r["counters"]["input_binder_scheduled_exact_candidates"]
                .as_u64()
                .unwrap_or(0)
        })
        .sum();
    assert!(
        selected > 0,
        "fixture must propose scheduled exact candidates"
    );
    let preferred: u64 = result["profiling"]["cost_records"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| {
            r["counters"]["input_binder_scheduled_ordinary_preferred"]
                .as_u64()
                .unwrap_or(0)
        })
        .sum();
    assert!(
        preferred > 0,
        "ordinary candidates must not be displaced by exact tuples"
    );
    let fallbacks: u64 = result["profiling"]["cost_records"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| {
            r["counters"]["input_binder_scheduled_exact_fallbacks"]
                .as_u64()
                .unwrap_or(0)
        })
        .sum();
    assert!(
        fallbacks > 0,
        "fixture must exercise ordinary fallback as well"
    );
    assert!(result["profiling"]["cost_records"]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|r| r["effort"].as_array().unwrap())
        .any(|e| e["operation"] == "ArrayCandidates"
            && e["report"]["selected"].as_u64().unwrap_or(0) > 0));
    schedule(&result);
    owns_both(&transcript);
}

#[test]
fn guided_exact_preserves_productive_guidance_and_supplement_order() {
    let source = r#"
        (declare-fun a () (Array Int Int))
        (declare-fun an () (Array Int Int))
        (define-fun .a () (Array Int Int) (! a :next an))
        (declare-fun tick () Bool)
        (define-fun .tick () Bool (! tick :action 0))
        (define-fun init () Bool (! (forall ((i Int)) (= (select a i) 0)) :init true))
        (define-fun trans () Bool (! (and tick (= an a)) :trans true))
        (define-fun prop () Bool (! (and (= (select a 5) 0)
            (= (select (store a 5 7) 5) 7)) :invar-property 0))
    "#;
    for exact in [false, true] {
        let (result, transcript) = run(source, exact, 4096, 3);
        assert_eq!(result["run_progress"]["termination_reason"], "depth_limit");
        assert!(schedule(&result) > 0);
        owns_both(&transcript);
    }
}

#[test]
fn guided_exact_keeps_existential_and_negative_universal_directions() {
    let source = r#"
        (declare-fun a () (Array Bool Int))
        (define-fun init () Bool (! (exists ((i Bool)) (= (select a i) 1)) :init true))
        (define-fun trans () Bool (! true :trans true))
        (define-fun prop () Bool (! (not (forall ((j Bool))
            (not (= (select a j) 1)))) :invar-property 0))
    "#;
    let (result, transcript) = run(source, true, 1, 1);
    assert_eq!(result["run_progress"]["termination_reason"], "depth_limit");
    assert_eq!(result["counterexample"], false);
    schedule(&result);
    owns_both(&transcript);
}

#[test]
fn guided_exact_does_not_verify_an_unsafe_array_update() {
    let source = r#"
        (declare-fun a () (Array Bool Int))
        (declare-fun an () (Array Bool Int))
        (define-fun .a () (Array Bool Int) (! a :next an))
        (define-fun init () Bool (! (forall ((i Bool)) (= (select a i) 0)) :init true))
        (define-fun trans () Bool (! (= an (store a true 1)) :trans true))
        (define-fun prop () Bool (! (= (select a true) 0) :invar-property 0))
    "#;
    let (result, _) = run(source, true, 1, 2);
    assert_eq!(result["found_proof"], false);
    assert_eq!(result["run_progress"]["deepest_completed_depth"], 0);
    assert!(
        result["counterexample"] == true
            || result["run_progress"]["termination_reason"] == "timeout"
    );
}
