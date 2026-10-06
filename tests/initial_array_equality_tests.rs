use serde_json::Value;
use std::process::Command;

fn run_fixture(profile: bool) -> Value {
    let mut command = Command::new(env!("CARGO_BIN_EXE_yardbird"));
    command.args([
        "-f",
        "tests/fixtures/initial_array_equality.vmt",
        "--policy",
        "countermodel-guided",
        "--guidance-schedule",
        "supplement",
        "-d",
        "3",
        "--json-output",
        "--wall-timeout-secs",
        "10",
    ]);
    if profile {
        command.arg("--profile");
    }
    let output = command.env("RUST_LOG", "off").output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let result: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(result["run_progress"]["deepest_completed_depth"], 2);
    assert_eq!(result["counterexample"], false);
    result
}

#[test]
fn guidance_installs_a_nested_constant_axiom_through_the_initial_equality() {
    let result = run_fixture(true);
    let mut found = false;
    for record in result["profiling"]["cost_records"].as_array().unwrap() {
        let Some(nodes) = record["countermodel_trace"]["nodes"].as_array() else {
            continue;
        };
        assert!(record["countermodel_trace"]["work"].as_u64().unwrap() <= 1024);
        for effort in record["effort"].as_array().unwrap() {
            if effort["operation"] != "CountermodelCandidates" {
                continue;
            }
            for candidate in effort["candidates"].as_array().unwrap() {
                if candidate["selected"] != true
                    || !candidate["rule"]
                        .as_str()
                        .unwrap()
                        .starts_with("constant-array-node-")
                {
                    continue;
                }
                let id = candidate["countermodel_origin"]["node"].as_u64().unwrap() as usize;
                let node = &nodes[id];
                let formula = node["lemma"]["formula"].as_str().unwrap();
                if !formula.contains("__yardbird_witness_") {
                    continue;
                }
                assert_eq!(node["status"]["kind"], "violated_array_axiom");
                assert_eq!(node["lemma"]["model_value"], "false");
                let mut parent = node["parent"].as_u64();
                let (mut initial, mut body, mut action) = (false, false, false);
                while let Some(id) = parent {
                    let ancestor = &nodes[id as usize];
                    match ancestor["reason"]["kind"].as_str().unwrap() {
                        "initialization" => {
                            assert!(
                                ancestor["lemma"].is_null(),
                                "source equalities are observations"
                            );
                            initial |= ancestor["conditions"].as_array().unwrap().iter().any(|c| {
                                c["expression"].as_str().unwrap().contains("votes@0")
                                    && c["value"] == "true"
                            });
                        }
                        "asserted_quantifier_body" => body = true,
                        "action_requirement" => action |= ancestor["reason"]["action"] == "decide",
                        _ => {}
                    }
                    parent = ancestor["parent"].as_u64();
                }
                let installed = record["installations"].as_array().unwrap().iter().any(|i| {
                    i["abstract_instantiation_id"] == candidate["abstract_instantiation_id"]
                        && i["result"]["abstract_instance_added"] == true
                });
                found |= initial && body && action && installed;
            }
        }
    }
    assert!(found, "guidance must follow decide -> quorum witness -> initial equality -> installed constant-array axiom");
    let unprofiled = run_fixture(false);
    assert_eq!(
        result["total_refinement_steps"],
        unprofiled["total_refinement_steps"]
    );
    assert_eq!(
        result["total_instantiations_added"],
        unprofiled["total_instantiations_added"]
    );
}
