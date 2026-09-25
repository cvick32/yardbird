//! Executable support claims: small VMT examples, checked in the actual CLI.
use std::{fs, process::Command};

const OWNERS: &[&str] = &["auto", "array", "quantifiers", "array,quantifiers", "none"];

fn example(name: &str) -> String {
    fs::read_to_string(format!(
        "{}/examples/theories/{name}.vmt",
        env!("CARGO_MANIFEST_DIR")
    ))
    .unwrap()
}

fn run(source: &str, theory: &str) -> std::process::Output {
    let dir = tempfile::tempdir().unwrap();
    let input = dir.path().join("input.vmt");
    fs::write(&input, source).unwrap();
    Command::new(env!("CARGO_BIN_EXE_yardbird"))
        .arg("-f")
        .arg(input)
        .args([
            "--theory",
            theory,
            "-d",
            "2",
            "--wall-timeout-secs",
            "10",
            "--json-output",
        ])
        .output()
        .unwrap()
}

fn assert_result(source: &str, theory: &str, counterexample: bool) {
    let output = run(source, theory);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let result: serde_json::Value =
        serde_json::from_slice(&output.stdout).unwrap_or_else(|_| panic!("{theory}: {stderr}"));
    assert_eq!(
        output.status.success(),
        !counterexample,
        "{theory}: {stderr}\n{result}"
    );
    assert_eq!(
        result["counterexample"], counterexample,
        "{theory}: {stderr}"
    );
    assert_eq!(
        result["run_progress"]["deepest_completed_depth"],
        if counterexample { 0 } else { 1 },
        "{theory}: {result}"
    );
    if !counterexample {
        assert_eq!(result["run_progress"]["termination_reason"], "depth_limit");
        assert_eq!(result["unsat_events"].as_array().unwrap().len(), 2);
    }
}

#[test]
fn scalar_bitvectors_have_modular_arithmetic_and_wide_literals() {
    for theory in ["auto", "none"] {
        for name in [
            "bitvector_counter",
            "bitvector_wide_literals",
            "bitvector_operations",
        ] {
            assert_result(&example(name), theory, false);
        }
        assert_result(&example("bitvector_overflow"), theory, true);
    }
}

#[test]
fn bitvector_arrays_and_quantifiers_agree_across_ownership_choices() {
    let safe = example("bitvector_array");
    let unsafe_source = example("bitvector_array_counterexample");
    for theory in OWNERS {
        assert_result(&safe, theory, false);
        assert_result(&unsafe_source, theory, true);
    }
}

#[test]
fn mixed_integer_bitvector_arrays_preserve_their_sorts() {
    for theory in OWNERS {
        assert_result(&example("mixed_integer_bitvector_array"), theory, false);
    }
}

#[test]
fn quantified_bitvector_counterexample_with_native_quantifiers() {
    for theory in ["none", "array"] {
        assert_result(
            &example("quantified_bitvector_counterexample"),
            theory,
            true,
        );
    }
}

#[test]
#[ignore = "known quantifier-refinement convergence limitation; see examples/theories/README.md"]
fn quantified_bitvector_counterexample_with_yardbird_quantifiers() {
    for theory in ["auto", "quantifiers"] {
        assert_result(
            &example("quantified_bitvector_counterexample"),
            theory,
            true,
        );
    }
}
