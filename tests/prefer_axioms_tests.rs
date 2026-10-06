use serde_json::Value;
use std::{collections::HashSet, process::Command};

fn run(prefer: bool, profile: bool) -> Value {
    let mut command = Command::new(env!("CARGO_BIN_EXE_yardbird"));
    command.args([
        "-f",
        "tests/fixtures/prefer_axioms.vmt",
        "-d",
        "1",
        "--policy",
        "countermodel-guided",
        "--guidance-schedule",
        "supplement",
        "--json-output",
        "--wall-timeout-secs",
        "10",
    ]);
    if prefer {
        command.arg("--prefer-axioms");
    }
    if profile {
        command.arg("--profile");
    }
    let output = command.env("RUST_LOG", "off").output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let value: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(
        value["run_progress"]["deepest_completed_depth"], 0,
        "{value}"
    );
    value
}

#[test]
fn prefer_axioms_precedes_guidance_including_nested_background_and_preserves_baseline() {
    let baseline = run(false, true);
    let enabled = run(true, true);
    let unprofiled = run(true, false);
    for key in [
        "total_instantiations_added",
        "total_refinement_steps",
        "counterexample",
    ] {
        assert_eq!(enabled[key], unprofiled[key], "{key}");
    }
    let provenance = &enabled["profiling"]["quantifier_provenance"];
    let background = provenance["rules"]
        .as_object()
        .unwrap()
        .iter()
        .filter(|(_, meta)| {
            provenance["sources"][meta["source_id"].as_str().unwrap()]["command"] == "assert"
        })
        .map(|(name, _)| name.as_str())
        .collect::<HashSet<_>>();
    assert_eq!(
        background.len(),
        3,
        "the nested existential is a background rule too"
    );
    let mut background_selected = 0;
    let mut arrays_selected = 0;
    for record in enabled["profiling"]["cost_records"].as_array().unwrap() {
        let efforts = record["effort"].as_array().unwrap();
        let Some(guidance) = efforts
            .iter()
            .position(|e| e["operation"] == "CountermodelCandidates")
        else {
            continue;
        };
        assert!(guidance > 0);
        for effort in &efforts[..guidance] {
            if effort["kind"] == "binder_page" && effort["chosen"] != "ReturnToCoordinator" {
                let operation = effort["operation"].as_str().unwrap();
                let rule = operation.split_once(':').unwrap().1;
                assert!(
                    background.contains(rule),
                    "non-background binder visited early: {rule}"
                );
            }
            if effort["kind"] != "operation" {
                continue;
            }
            for candidate in effort["candidates"].as_array().unwrap() {
                if candidate["selected"] != true {
                    continue;
                }
                if background.contains(candidate["rule"].as_str().unwrap()) {
                    background_selected += 1;
                }
                if effort["operation"] == "ArrayCandidates" {
                    arrays_selected += 1;
                }
            }
        }
    }
    assert!(background_selected > 0);
    assert!(arrays_selected > 0);
    for record in baseline["profiling"]["cost_records"].as_array().unwrap() {
        let efforts = record["effort"].as_array().unwrap();
        if !efforts.is_empty() {
            assert_eq!(efforts[0]["operation"], "CountermodelCandidates");
        }
    }
}

#[test]
fn prefer_axioms_reaches_standard_and_german_plans() {
    for policy in [None, Some("german-fast")] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_yardbird"));
        command.args([
            "-f",
            "tests/fixtures/prefer_axioms.vmt",
            "-d",
            "1",
            "--prefer-axioms",
            "--profile",
            "--json-output",
            "--wall-timeout-secs",
            "10",
        ]);
        if let Some(policy) = policy {
            command.args(["--policy", policy]);
        }
        let output = command.env("RUST_LOG", "off").output().unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let value: Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(value["run_progress"]["deepest_completed_depth"], 0);
        let records = value["profiling"]["cost_records"].as_array().unwrap();
        let effort = records
            .iter()
            .flat_map(|r| r["effort"].as_array().unwrap())
            .next()
            .unwrap();
        assert_eq!(effort["operation"], "GuardedReads");
    }
}
