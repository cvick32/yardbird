use serde_json::Value;
use std::process::Command;

fn run(source: &str, depth: usize) -> (Value, String) {
    let dir = tempfile::tempdir().unwrap();
    let input = dir.path().join("input.vmt");
    std::fs::write(&input, source).unwrap();
    let capture = dir.path().join("capture");
    let mut command = Command::new(env!("CARGO_BIN_EXE_yardbird"));
    let out = command
        .arg("-f")
        .arg(input)
        .args([
            "--policy",
            "countermodel-guided",
            "--theory",
            "array,quantifiers",
            "--guided-read-support",
            "--guidance-schedule",
            "supplement",
            "--guidance-work",
            "4096",
            "--wall-timeout-secs",
            "5",
            "--json-output",
            "--profile",
            "--solver-capture-dir",
        ])
        .arg(&capture)
        .arg("-d")
        .arg(depth.to_string())
        .output()
        .unwrap();
    let result: Value = serde_json::from_slice(&out.stdout)
        .unwrap_or_else(|e| panic!("{e}: {}", String::from_utf8_lossy(&out.stderr)));
    let transcript = std::fs::read_to_string(capture.join("solver-session.smt2")).unwrap();
    for native in ["(forall ", "(exists ", "(select ", "(store ", "(Array "] {
        assert!(
            !transcript.contains(native),
            "native theory escaped: {native}"
        );
    }
    (result, transcript)
}
#[test]
fn support_closes_reads_exposed_only_by_a_quantified_body() {
    let (result, transcript) = run(
        r#"
        (declare-fun a () (Array Int Int))
        (declare-fun b () (Array Int Int))
        (define-fun init () Bool (! (forall ((i Int))
            (= (select a i) (select (store b 5 9) i))) :init true))
        (define-fun trans () Bool (! true :trans true))
        (define-fun prop () Bool (! (= (select a 5) 9) :invar-property 0))
    "#,
        1,
    );
    assert_eq!(result["run_progress"]["termination_reason"], "depth_limit");
    let records = result["profiling"]["cost_records"].as_array().unwrap();
    for key in [
        "read_support_quantifier_instances_generated",
        "read_support_array_instances_generated",
        "read_support_instances_selected",
    ] {
        assert!(
            records
                .iter()
                .any(|r| r["counters"][key].as_u64().unwrap_or(0) > 0),
            "missing {key}"
        );
    }
    let events = records
        .iter()
        .flat_map(|r| r["effort"].as_array().unwrap())
        .filter(|e| e["kind"] == "operation" && e["operation"] == "ReadSupport")
        .collect::<Vec<_>>();
    assert!(!events.is_empty());
    for event in events {
        assert!(event["report"]["dependency_work"].as_u64().unwrap() <= 2048);
    }
    assert!(
        transcript.contains("(Write_Int_Int b@0 5 9)")
            || transcript.contains("(Write_Int_Int b 5 9)")
    );
}
#[test]
fn support_does_not_verify_an_unsafe_update() {
    let (result, _) = run(
        r#"
        (declare-fun a () (Array Bool Int))
        (declare-fun an () (Array Bool Int))
        (define-fun .a () (Array Bool Int) (! a :next an))
        (define-fun init () Bool (! (forall ((i Bool)) (= (select a i) 0)) :init true))
        (define-fun trans () Bool (! (= an (store a true 1)) :trans true))
        (define-fun prop () Bool (! (= (select a true) 0) :invar-property 0))
    "#,
        2,
    );
    assert_eq!(result["found_proof"], false);
    assert_eq!(result["run_progress"]["deepest_completed_depth"], 0);
    assert!(
        result["counterexample"] == true
            || result["run_progress"]["termination_reason"] == "timeout"
    );
}
#[test]
fn multi_variable_binders_keep_guided_fallback() {
    let (result, _) = run(
        r#"
        (declare-fun p (Int Int) Bool)
        (define-fun init () Bool (! (forall ((i Int) (j Int)) (p i j)) :init true))
        (define-fun trans () Bool (! true :trans true))
        (define-fun prop () Bool (! (p 3 4) :invar-property 0))
    "#,
        1,
    );
    assert_eq!(result["run_progress"]["termination_reason"], "depth_limit");
}

#[test]
fn scalar_domain_axioms_remain_available_to_guided_fallback() {
    let (result, _) = run(
        r#"
        (declare-sort Opcode 0)
        (declare-fun a () Opcode)
        (declare-fun b () Opcode)
        (declare-fun k () Opcode)
        (define-fun init () Bool (! (forall ((i Opcode)) (or (= i a) (= i b))) :init true))
        (define-fun trans () Bool (! true :trans true))
        (define-fun prop () Bool (! (or (= k a) (= k b)) :invar-property 0))
    "#,
        1,
    );
    assert_eq!(result["run_progress"]["termination_reason"], "depth_limit");
    assert!(result["profiling"]["cost_records"]
        .as_array()
        .unwrap()
        .iter()
        .all(
            |r| r["counters"]["read_support_quantifier_instances_generated"]
                .as_u64()
                .unwrap_or(0)
                == 0
        ));
}

#[test]
fn complete_read_equation_handles_symbolic_index_aliases() {
    let (result, transcript) = run(
        r#"
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)
        (declare-fun v () Int)
        (define-fun init () Bool (! (forall ((k Int)) (= (select a k) 0)) :init true))
        (define-fun trans () Bool (! true :trans true))
        (define-fun prop () Bool (! (= (select (store a i v) j)
            (ite (= i j) v (select a j))) :invar-property 0))
    "#,
        1,
    );
    assert_eq!(result["run_progress"]["termination_reason"], "depth_limit");
    assert!(result["profiling"]["cost_records"]
        .as_array()
        .unwrap()
        .iter()
        .any(|r| r["installations"].as_array().unwrap().iter().any(|i| i
            ["abstract_instantiation_id"]
            .as_str()
            .unwrap()
            .contains("read-over-write-Int-Int"))));
    assert!(transcript.contains("(ite (= i@0 j@0) v@0 (Read_Int_Int a@0 j@0))"));
}

#[test]
fn support_keeps_progress_across_reused_boolean_array_schemas() {
    let (result, _) = run(
        r#"
        (declare-fun a () (Array Bool Bool))
        (declare-fun an () (Array Bool Bool))
        (declare-fun flag () Bool)
        (declare-fun flagn () Bool)
        (define-fun .a () (Array Bool Bool) (! a :next an))
        (define-fun .flag () Bool (! flag :next flagn))
        (define-fun init () Bool (! (and (not flag) (forall ((i Bool)) (not (select a i)))) :init true))
        (define-fun trans () Bool (! (and (= an (store a true (not flag))) (= flagn (not flag))) :trans true))
        (define-fun prop () Bool (! (= (select a true) flag) :invar-property 0))
    "#,
        5,
    );
    assert_eq!(
        result["run_progress"]["termination_reason"], "depth_limit",
        "{result}"
    );
}
