//! Entire CLI paths, with no credentials or provider calls.
use serde_json::Value;
use std::{
    path::Path,
    process::{Command, Output},
};

fn command(root: &Path, flags: &[&str]) -> Output {
    let input = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples/distributed_protocols/german/german.encoding.vmt");
    Command::new(env!("CARGO_BIN_EXE_yardbird"))
        .current_dir(root)
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
            "--json-output",
        ])
        .args(flags)
        .output()
        .unwrap()
}

fn success(output: Output) -> Value {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).unwrap()
}

#[test]
fn native_export_and_checked_replay_work_through_the_cli_without_an_agent() {
    let root = tempfile::tempdir().unwrap();
    let file = root.path().join("german-native.json");
    let native = success(command(
        root.path(),
        &["--export-instantiations", file.to_str().unwrap()],
    ));
    assert_eq!(native["run_progress"]["deepest_completed_depth"], 3);
    let replay = success(command(
        root.path(),
        &["--replay-instantiations", file.to_str().unwrap()],
    ));
    assert_eq!(replay["status"], "bounded_complete");
    assert_eq!(replay["closed_depths"], serde_json::json!([0, 1, 2, 3]));
    assert_eq!(replay["calls"], 0);
    assert_eq!(replay["symbolic_refinements"], 0);
    assert_eq!(replay["proposed_instances"], replay["installed_instances"]);
    assert_eq!(replay["placement"], "exact");
    let schema = success(command(
        root.path(),
        &[
            "--replay-instantiations",
            file.to_str().unwrap(),
            "--one-shot-placement",
            "schema",
        ],
    ));
    assert_eq!(schema["placement"], "schema");
    assert_eq!(schema["status"], "bounded_complete");
    assert_eq!(schema["closed_depths"], serde_json::json!([0, 1, 2, 3]));
    assert_eq!(schema["calls"], 0);
    assert!(
        schema["unique_instances"].as_u64().unwrap()
            <= schema["proposed_instances"].as_u64().unwrap()
    );
    assert!(!command(
        root.path(),
        &["--export-instantiations", file.to_str().unwrap()]
    )
    .status
    .success());
}

#[test]
fn one_shot_dry_run_uses_bundled_config_and_a_complete_single_response_interface() {
    let root = tempfile::tempdir().unwrap();
    let report = success(command(
        root.path(),
        &["--agent", "bedrock", "--one-shot", "--agent-dry-run"],
    ));
    assert_eq!(report["status"], "dry_run");
    assert_eq!(report["calls"], 0);
    let path = root.path().join(report["log"].as_str().unwrap());
    let events: Vec<Value> = std::fs::read_to_string(path)
        .unwrap()
        .lines()
        .map(|l| serde_json::from_str(l).unwrap())
        .collect();
    let request = &events.iter().find(|e| e["event"] == "dry_request").unwrap()["request"];
    assert_eq!(request["tools"].as_array().unwrap().len(), 1);
    assert_eq!(request["tools"][0]["name"], "submit_instantiations");
    assert!(
        request["tools"][0]["parameters"]["properties"]["instantiations"]
            .get("maxItems")
            .is_none()
    );
    assert_eq!(request["max_output_tokens"], 32768);
    assert_eq!(
        request["input"][0]["content"],
        include_str!("../src/agent_interaction/one_shot/prompt.md")
    );
    let context: Value =
        serde_json::from_str(request["input"][1]["content"].as_str().unwrap()).unwrap();
    assert_eq!(context["target"]["depths"], serde_json::json!([0, 1, 2, 3]));
    assert_eq!(context["batch_mode"]["round"], 1);
    assert_eq!(context["batch_mode"]["max_calls"], 0);
    assert_eq!(context["batch_mode"]["placement"], "schema");
    assert!(context.get("model").is_none());
    assert_eq!(
        context["schema_semantics"]["schemas_are_asserted_axioms"],
        false
    );
    assert!(context.get("successful_instantiations").is_none());
    assert!(context["prepared_program"]
        .as_str()
        .unwrap()
        .contains("Read_client_Bool"));
}

#[test]
fn custom_prompt_is_logged_verbatim_and_empty_prompt_fails_without_calls() {
    let root = tempfile::tempdir().unwrap();
    let prompt = root.path().join("instructions.md");
    let text = "Custom experiment instructions.\nPreserve this exact prompt.\n";
    std::fs::write(&prompt, text).unwrap();
    let flags = [
        "--agent",
        "bedrock",
        "--one-shot",
        "--agent-dry-run",
        "--one-shot-prompt",
        prompt.to_str().unwrap(),
    ];
    let report = success(command(root.path(), &flags));
    assert_eq!(report["calls"], 0);
    let events =
        std::fs::read_to_string(root.path().join(report["log"].as_str().unwrap())).unwrap();
    let request = events
        .lines()
        .map(|line| serde_json::from_str::<Value>(line).unwrap())
        .find(|event| event["event"] == "dry_request")
        .unwrap();
    assert_eq!(request["request"]["input"][0]["content"], text);

    std::fs::write(&prompt, " \n").unwrap();
    let output = command(root.path(), &flags);
    assert!(!output.status.success());
    let report: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["calls"], 0);
    assert!(report["error"]
        .as_str()
        .unwrap()
        .contains("prompt must not be empty"));
}

#[test]
fn one_shot_rejects_adaptive_assessments_and_non_bedrock_modes() {
    let root = tempfile::tempdir().unwrap();
    for flags in [
        vec!["--agent", "none", "--one-shot"],
        vec![
            "--agent",
            "bedrock",
            "--one-shot",
            "--agent-dry-run",
            "--agent-trigger",
            "adaptive",
        ],
    ] {
        assert!(!command(root.path(), &flags).status.success());
    }
}

#[test]
fn quantified_transition_with_framed_helpers_round_trips() {
    let root = tempfile::tempdir().unwrap();
    let input = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/quantified_guarded_transition.vmt");
    for flag in ["--export-instantiations", "--replay-instantiations"] {
        let report = success(
            Command::new(env!("CARGO_BIN_EXE_yardbird"))
                .current_dir(root.path())
                .arg("-f")
                .arg(&input)
                .args(["-d", "2", "--json-output", flag, "bundle.json"])
                .output()
                .unwrap(),
        );
        if flag == "--replay-instantiations" {
            assert_eq!(report["closed_depths"], serde_json::json!([0, 1]));
        }
    }
}
