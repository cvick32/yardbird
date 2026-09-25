use std::{fs, process::Command};

const MIXED: &str = "
(declare-fun a () (Array Int Int))
(declare-fun a_next () (Array Int Int))
(define-fun .a () (Array Int Int) (! a :next a_next))
(define-fun init () Bool (! (forall ((i Int)) (= (select a i) 0)) :init true))
(define-fun trans () Bool (! (= a_next (store a 1 1)) :trans true))
(define-fun prop () Bool (! (= (select a 0) 0) :invar-property 0))
";

fn run(source: &str, selection: Option<&str>) -> (std::process::Output, String) {
    let dir = tempfile::tempdir().unwrap();
    let file = dir.path().join("input.vmt");
    let capture = dir.path().join("capture");
    fs::write(&file, source).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_yardbird"));
    command
        .arg("--filename")
        .arg(file)
        .args(["--depth", "2", "--wall-timeout-secs", "10", "--json-output"])
        .arg("--solver-capture-dir")
        .arg(&capture)
        .env("RUST_LOG", "info");
    if let Some(selection) = selection {
        command.args(["--theory", selection]);
    }
    let output = command.output().unwrap();
    let transcript = fs::read_to_string(capture.join("solver-session.smt2")).unwrap_or_default();
    (output, transcript)
}

#[test]
fn ownership_matrix_preserves_the_result_and_solver_vocabulary() {
    for (selection, arrays, quantifiers) in [
        (None, true, true),
        (Some("auto"), true, true),
        (Some("array,quantifiers"), true, true),
        (Some("quantifiers,array"), true, true),
        (Some("array"), true, false),
        (Some("quantifiers"), false, true),
        (Some("none"), false, false),
    ] {
        let (output, transcript) = run(MIXED, selection);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "{selection:?}: {stderr}");
        let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(
            result["run_progress"]["termination_reason"], "depth_limit",
            "{selection:?}: {stderr}"
        );
        assert_eq!(result["unsat_events"].as_array().unwrap().len(), 2);
        assert_eq!(
            transcript.contains("Read_Int_Int"),
            arrays,
            "{selection:?}: {transcript}"
        );
        assert_eq!(
            transcript.contains("(Array Int Int)"),
            !arrays,
            "{selection:?}: {transcript}"
        );
        assert_eq!(
            transcript.contains("(forall "),
            !quantifiers,
            "{selection:?}: {transcript}"
        );
        if !arrays {
            for name in ["Read_", "Write_", "ConstArr_", "Array_Int_Int"] {
                assert!(!transcript.contains(name), "{selection:?} leaked {name}");
            }
        }
    }
}

#[test]
fn auto_handles_array_free_vmt_and_none_reports_a_real_counterexample() {
    let source = "(declare-fun x () Int) (declare-fun xn () Int)
        (define-fun .x () Int (! x :next xn))
        (define-fun init () Bool (! (= x 0) :init true))
        (define-fun trans () Bool (! (= xn (+ x 1)) :trans true))
        (define-fun prop () Bool (! (= x 0) :invar-property 0))";
    for selection in [None, Some("none")] {
        let (output, transcript) = run(source, selection);
        assert!(!output.status.success());
        let result: serde_json::Value = serde_json::from_slice(&output.stdout)
            .unwrap_or_else(|_| panic!("{}", String::from_utf8_lossy(&output.stderr)));
        assert_eq!(result["counterexample"], true);
        assert!(!transcript.contains("Read_"));
    }
}

#[test]
fn native_array_values_remain_typed_quantifier_domains() {
    let source = "(declare-fun a () (Array Int Int))
        (declare-fun p ((Array Int Int)) Bool)
        (define-fun init () Bool (! (forall ((b (Array Int Int))) (p b)) :init true))
        (define-fun trans () Bool (! true :trans true))
        (define-fun prop () Bool (! (p (store a 0 1)) :invar-property 0))";
    let (output, transcript) = run(source, Some("quantifiers"));
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(!transcript.contains("Read_"));
    assert!(!transcript.contains("(forall "));
    assert!(transcript.contains("(Array Int Int)"));
}

#[test]
fn array_only_ownership_preserves_quantifiers_over_abstract_array_sorts() {
    let source = "(declare-fun a () (Array Bool Bool))
        (declare-fun p ((Array Bool Bool)) Bool)
        (define-fun init () Bool (! (forall ((b (Array Bool Bool))) (p b)) :init true))
        (define-fun trans () Bool (! true :trans true))
        (define-fun prop () Bool (! (p a) :invar-property 0))";
    let (output, transcript) = run(source, Some("array"));
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(transcript.contains("(forall "));
    assert!(transcript.contains("Array_Bool_Bool"));
    assert!(!transcript.contains("(Array Bool Bool)"));
}

#[test]
fn cli_rejects_conflicting_or_unknown_selections() {
    for args in [
        vec!["--theory", "auto,array"],
        vec!["--theory", "quantifiers,list"],
        vec!["--theory", "quantifiers", "--strategy", "concrete"],
        vec!["--native-arrays"],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_yardbird"))
            .args(args)
            .output()
            .unwrap();
        assert!(!output.status.success());
    }
}
