//! Golden instance traces captured BEFORE the policy facade, using the binary
//! and source identity documented in fixtures/policy_parity/README.md.

use std::{
    fs::{self, File},
    process::{Command, Stdio},
    thread,
    time::{Duration, Instant},
};

use serde::Deserialize;
use serde_json::{Map, Value};

#[derive(Deserialize)]
struct Case {
    name: String,
    args: Vec<String>,
}

fn fields(value: &Value, keys: &[&str]) -> Value {
    Value::Object(
        keys.iter()
            .map(|key| ((*key).to_owned(), value[*key].clone()))
            .collect::<Map<_, _>>(),
    )
}

fn instance_trace(result: &Value) -> Value {
    let mut trace = fields(
        result,
        &[
            "used_instances",
            "total_instantiations_added",
            "total_refinement_steps",
            "counterexample",
            "found_proof",
        ],
    );
    trace["selected_instances"] = result["abstract_instantiations"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|record| record["was_selected"] == true)
        .map(|record| {
            fields(
                record,
                &[
                    "axiom_name",
                    "term",
                    "bmc_depth",
                    "refinement_step",
                    "substitution",
                ],
            )
        })
        .collect();
    trace["solver_checks"] = result["profiling"]["solver_checks"]
        .as_array()
        .unwrap()
        .iter()
        .map(|record| {
            fields(
                record,
                &[
                    "depth",
                    "refinement_step",
                    "result",
                    "instances_total",
                    "assertion_count",
                ],
            )
        })
        .collect();
    trace["progress"] = fields(
        &result["run_progress"],
        &[
            "termination_reason",
            "deepest_completed_depth",
            "current_depth",
        ],
    );
    trace
}

#[test]
fn policy_facade_preserves_baseline_instance_selection() {
    let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let fixtures = repo.join("tests/fixtures/policy_parity");
    let cases: Vec<Case> =
        serde_json::from_slice(&fs::read(fixtures.join("cases.json")).unwrap()).unwrap();
    for case in cases {
        let temp = tempfile::tempdir().unwrap();
        let stdout = temp.path().join("stdout.json");
        let stderr = temp.path().join("stderr.log");
        let mut child = Command::new(env!("CARGO_BIN_EXE_yardbird"))
            .args(&case.args)
            .args([
                "--json-output",
                "--record-decisions",
                "--profile",
                "--wall-timeout-secs",
                "30",
            ])
            .env("RUST_LOG", "off")
            .current_dir(repo)
            .stdout(Stdio::from(File::create(&stdout).unwrap()))
            .stderr(Stdio::from(File::create(&stderr).unwrap()))
            .spawn()
            .unwrap();
        let start = Instant::now();
        let status = loop {
            if let Some(status) = child.try_wait().unwrap() {
                break status;
            }
            if start.elapsed() > Duration::from_secs(90) {
                child.kill().unwrap();
                child.wait().unwrap();
                panic!("{} exceeded the external test timeout", case.name);
            }
            thread::sleep(Duration::from_millis(20));
        };
        assert!(
            status.success(),
            "{} failed: {}",
            case.name,
            fs::read_to_string(&stderr).unwrap()
        );
        let result: Value = serde_json::from_slice(&fs::read(stdout).unwrap()).unwrap();
        let expected: Value = serde_json::from_slice(
            &fs::read(fixtures.join(format!("{}.json", case.name))).unwrap(),
        )
        .unwrap();
        assert_eq!(instance_trace(&result), expected, "{} parity", case.name);
    }
}
