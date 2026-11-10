use serde_json::Value;
use std::process::Command;

fn run(transition: &str, depth: usize, split: bool) -> (Value, String) {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("case.vmt");
    std::fs::write(
        &path,
        format!(
            r#"
        (declare-fun a () (Array Bool Int))
        (declare-fun an () (Array Bool Int))
        (declare-fun phase () Bool) (declare-fun pn () Bool)
        (define-fun .a () (Array Bool Int) (! a :next an))
        (define-fun .phase () Bool (! phase :next pn))
        (define-fun init () Bool (! (and (not phase)
            (forall ((i Bool)) (= (select a i) 0))) :init true))
        (define-fun trans () Bool (! (and (= pn (not phase)) {transition}) :trans true))
        (define-fun prop () Bool (! (and (not (= phase (not phase))) (forall ((i Bool)) (= (select a i) 0))) :invar-property 0))
    "#
        ),
    )
    .unwrap();
    let capture = dir.path().join("capture");
    let mut command = Command::new(env!("CARGO_BIN_EXE_yardbird"));
    if split {
        command.arg("--split-property-checks");
    }
    let output = command
        .arg("-f")
        .arg(path)
        .arg("-d")
        .arg(depth.to_string())
        .args([
            "--policy",
            "countermodel-guided",
            "--theory",
            "array,quantifiers",
            "--guided-read-support",
            "--reuse-proved-properties",
            "--proved-property-instance-limit",
            "512",
            "--json-output",
            "--wall-timeout-secs",
            "5",
            "--solver-capture-dir",
        ])
        .arg(&capture)
        .output()
        .unwrap();
    let result: Value = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|e| panic!("{e}: {}", String::from_utf8_lossy(&output.stderr)));
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
fn reuses_bounded_quantified_properties_with_both_theories_abstract() {
    for split in [false, true] {
        let (result, transcript) = run("(= an (store a phase 0))", 5, split);
        assert!(
            transcript.lines().any(|line| line.starts_with("(assert ")
                && line.contains("(= (Read_Bool_Int a@0 true) 0)")),
            "proved universal property was not instantiated at a different index"
        );
        assert_eq!(result["run_progress"]["termination_reason"], "depth_limit");
        assert_eq!(result["run_progress"]["deepest_completed_depth"], 4);
    }
}

#[test]
fn bounded_property_reuse_does_not_hide_a_later_unsafe_store() {
    for split in [false, true] {
        let (result, _) = run("(= an (ite phase (store a true 1) a))", 3, split);
        assert_eq!(result["found_proof"], false);
        assert_eq!(result["run_progress"]["deepest_completed_depth"], 1);
        assert_ne!(result["run_progress"]["termination_reason"], "depth_limit");
    }
}
