use std::process::Command;

#[test]
fn guided_clause_matching_rejects_cross_sort_existing_bindings() {
    check_guidance("tests/fixtures/quantified_equality_sorts.vmt".as_ref());
}

#[test]
fn guided_clause_matching_rejects_cross_sort_ground_captures() {
    let directory = tempfile::tempdir().unwrap();
    let file = directory.path().join("ground-capture.vmt");
    let input = std::fs::read_to_string("tests/fixtures/quantified_equality_sorts.vmt")
        .unwrap()
        .replace("(= x y)", "(= chosen y)");
    std::fs::write(&file, input).unwrap();
    check_guidance(&file);
}

fn check_guidance(file: &std::path::Path) {
    let output = Command::new(env!("CARGO_BIN_EXE_yardbird"))
        .arg("--filename")
        .arg(file)
        .args([
            "--policy",
            "countermodel-guided",
            "--guidance-schedule",
            "supplement",
            "--depth",
            "2",
            "--wall-timeout-secs",
            "5",
            "--json-output",
        ])
        .env("RUST_LOG", "off")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(result["run_progress"]["deepest_completed_depth"], 1);
    assert_eq!(result["counterexample"], false);
}
