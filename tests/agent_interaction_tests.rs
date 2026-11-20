//! Agent CLI regressions. None/dry-run modes never contact a provider.
use serde_json::Value;
use std::process::Command;

fn run(flags: &[&str]) -> Value {
    let output = Command::new(env!("CARGO_BIN_EXE_yardbird"))
        .args([
            "-f",
            "examples/distributed_protocols/german/german.encoding.vmt",
            "-d",
            "4",
            "--json-output",
            "--wall-timeout-secs",
            "30",
        ])
        .args(flags)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).unwrap()
}

#[test]
fn no_advice_preserves_selected_policy_and_exact_native_refinements() {
    let root = tempfile::tempdir().unwrap();
    for policy in ["german-fast", "countermodel-guided"] {
        let native = run(&["--policy", policy]);
        let log = root.path().join(format!("{policy}.jsonl"));
        let advised = run(&[
            "--policy",
            policy,
            "--agent",
            "none",
            "--agent-log",
            log.to_str().unwrap(),
        ]);
        for field in [
            "used_instances",
            "total_instantiations_added",
            "total_refinement_steps",
            "counterexample",
            "found_proof",
        ] {
            assert_eq!(native[field], advised[field], "{policy}: {field}");
        }
        assert_eq!(advised["run_progress"]["deepest_completed_depth"], 3);
        let events: Vec<Value> = std::fs::read_to_string(log)
            .unwrap()
            .lines()
            .map(|l| serde_json::from_str(l).unwrap())
            .collect();
        let end = events.last().unwrap();
        assert_eq!(end["calls"], 0);
        assert_eq!(end["snapshots"], 0);
        assert_eq!(end["capture_seconds"], 0.0);
        assert!(end["polls"].as_u64().unwrap() > 0);
    }
    // The configured (non-named) policy still owns its term-cost/ranker choices.
    let native = run(&["-c", "ast-size"]);
    let advised = run(&["-c", "ast-size", "--agent", "none"]);
    assert_eq!(native["used_instances"], advised["used_instances"]);
}

#[test]
fn dry_run_captures_one_indexed_context_without_network_or_vocabulary_admission() {
    let root = tempfile::tempdir().unwrap();
    let log = root.path().join("dry.jsonl");
    let result = run(&[
        "--policy",
        "german-fast",
        "--agent",
        "bedrock",
        "--agent-stall-secs",
        "0",
        "--agent-log",
        log.to_str().unwrap(),
        "--agent-dry-run",
    ]);
    assert_eq!(result["run_progress"]["deepest_completed_depth"], 3);
    let events: Vec<Value> = std::fs::read_to_string(log)
        .unwrap()
        .lines()
        .map(|l| serde_json::from_str(l).unwrap())
        .collect();
    assert!(events.iter().any(|e| e["event"] == "dry_request"));
    let end = events.last().unwrap();
    assert_eq!(end["snapshots"], 1);
    assert_eq!(end["calls"], 0);
    let native = run(&["--policy", "german-fast"]);
    assert_eq!(native["used_instances"], result["used_instances"]);
}

#[test]
fn removed_stdio_flag_is_rejected_by_the_cli() {
    let output = Command::new(env!("CARGO_BIN_EXE_yardbird"))
        .args([
            "-f",
            "tests/fixtures/prerequisite_explicit_action.vmt",
            "--agent-stdio",
            "--agent",
            "none",
        ])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("unexpected argument '--agent-stdio'"));
}

#[test]
fn defaults_work_outside_the_repo_and_adaptive_dry_run_needs_no_credentials() {
    let root = tempfile::tempdir().unwrap();
    let input = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples/distributed_protocols/german/german.encoding.vmt");
    for adaptive in [false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_yardbird"));
        command
            .current_dir(root.path())
            .env_remove("BEDROCK_API_KEY")
            .args([
                "-f",
                input.to_str().unwrap(),
                "--policy",
                "german-fast",
                "-d",
                "4",
                "--wall-timeout-secs",
                "30",
                "--agent",
                "bedrock",
                "--agent-dry-run",
                "--json-output",
            ]);
        if adaptive {
            command.args(["--agent-trigger", "adaptive"]);
        }
        let output = command.output().unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let result: Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(result["run_progress"]["deepest_completed_depth"], 3);
    }
    let paths: Vec<_> = std::fs::read_dir(root.path().join(".yardbird/runs"))
        .unwrap()
        .map(|e| e.unwrap().path().join("agent.jsonl"))
        .collect();
    assert_eq!(paths.len(), 2);
    let mut assessments = 0;
    for path in paths {
        let events: Vec<Value> = std::fs::read_to_string(path)
            .unwrap()
            .lines()
            .map(|l| serde_json::from_str(l).unwrap())
            .collect();
        assert_eq!(events.last().unwrap()["calls"], 0);
        assert_eq!(events.last().unwrap()["snapshots"], 0);
        for event in &events {
            if event["event"] == "dry_request" {
                assert_eq!(event["kind"], "assessment");
                assert_eq!(event["request"]["tools"][0]["name"], "assess");
                assessments += 1;
            }
        }
    }
    assert_eq!(assessments, 1);
}

#[test]
fn binder_context_keeps_source_names_and_correlated_terms_on_the_wire() {
    let root = tempfile::tempdir().unwrap();
    let log = root.path().join("agent.jsonl");
    let result = Command::new(env!("CARGO_BIN_EXE_yardbird"))
        .args([
            "-f",
            "tests/fixtures/quantified_quorum_vote_update.vmt",
            "-d",
            "4",
            "--policy",
            "countermodel-guided",
            "--agent",
            "bedrock",
            "--agent-start-model",
            "5",
            "--agent-stall-secs",
            "0",
            "--agent-binder-context",
            "--agent-dry-run",
            "--agent-log",
        ])
        .arg(&log)
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let request = std::fs::read_to_string(log)
        .unwrap()
        .lines()
        .map(|l| serde_json::from_str::<Value>(l).unwrap())
        .find(|e| e["event"] == "dry_request")
        .unwrap();
    let input: Value =
        serde_json::from_str(request["request"]["input"][1]["content"].as_str().unwrap()).unwrap();
    assert_eq!(input["context"]["epoch"], "e5");
    let axioms = input["context"]["snapshot"]["axioms"].as_array().unwrap();
    let rule = axioms
        .iter()
        .find(|a| {
            a["binder_context"]["formula"]
                == "(forall ((n node)) (=> (member n chosen) (select votes n)))"
        })
        .unwrap();
    let data = &rule["binder_context"];
    assert_eq!(data["variable_slot_names"], serde_json::json!(["n"]));
    assert_eq!(
        data["capture_slot_names"],
        serde_json::json!(["chosen", "votes"])
    );
    assert!(data["ground_capture_tuples"]
        .as_array()
        .unwrap()
        .contains(&serde_json::json!(["chosen@0", "votes@0"])));
    assert!(data["installed_relative_tuples"]
        .as_array()
        .unwrap()
        .contains(&serde_json::json!(["chosen+0", "votes+0", "newcomer+0"])));
    assert!(axioms
        .iter()
        .any(|a| a["binder_context_ref"] == rule["id"] && a["slots"].get("variable_0").is_none()));
    // The inner binder captures the outer existential variable under its original name.
    assert!(axioms
        .iter()
        .any(|a| a["binder_context"]["capture_slot_names"] == serde_json::json!(["q", "votes"])));
}
