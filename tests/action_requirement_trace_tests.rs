use std::process::Command;

#[test]
fn guided_instances_follow_the_enabling_requirement_into_another_array() {
    let output = Command::new(env!("CARGO_BIN_EXE_yardbird"))
        .args([
            "-f",
            "tests/fixtures/action_requirement_trace.vmt",
            "--policy",
            "countermodel-guided",
            "-d",
            "3",
            "--profile",
            "--json-output",
            "--wall-timeout-secs",
            "10",
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
    assert_eq!(result["run_progress"]["deepest_completed_depth"], 2);
    let records = result["profiling"]["cost_records"].as_array().unwrap();
    assert!(
        records.iter().any(|record| {
            let Some(nodes) = record["countermodel_trace"]["nodes"].as_array() else {
                return false;
            };
            record["effort"].as_array().unwrap().iter().any(|effort| {
                effort["operation"] == "CountermodelCandidates"
                    && effort["candidates"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .any(|candidate| {
                            let Some(id) = candidate["countermodel_origin"]["node"].as_u64() else {
                                return false;
                            };
                            let node = &nodes[id as usize];
                            if candidate["selected"] != true
                                || !node["lemma"]["formula"]
                                    .as_str()
                                    .is_some_and(|s| s.contains("votes@0"))
                            {
                                return false;
                            }
                            let mut parent = node["parent"].as_u64();
                            while let Some(id) = parent {
                                let node = &nodes[id as usize];
                                if node["reason"]["kind"] == "action_requirement"
                                    && node["reason"]["action"] == "decide"
                                    && node["reason"]["frame"] == 0
                                {
                                    return true;
                                }
                                parent = node["parent"].as_u64();
                            }
                            false
                        })
            })
        }),
        "the vote initializer must be selected by guidance through the decide requirement"
    );
}

#[test]
fn quantified_action_requirement_follows_asserted_quorum_tuple_to_initializer() {
    let output = Command::new(env!("CARGO_BIN_EXE_yardbird"))
        .args([
            "-f",
            "tests/fixtures/action_requirement_quorum.vmt",
            "--policy",
            "countermodel-guided",
            "-d",
            "3",
            "--profile",
            "--json-output",
            "--wall-timeout-secs",
            "10",
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
    assert_eq!(result["run_progress"]["deepest_completed_depth"], 2);
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
                if candidate["selected"] != true {
                    continue;
                }
                let id = candidate["countermodel_origin"]["node"].as_u64().unwrap() as usize;
                let formula = nodes[id]["lemma"]["formula"].as_str().unwrap();
                if !formula.contains("votes@0") || !formula.contains("__yardbird_witness_") {
                    continue;
                }
                let mut parent = nodes[id]["parent"].as_u64();
                let mut asserted_body = false;
                while let Some(id) = parent {
                    let node = &nodes[id as usize];
                    if node["reason"]["kind"] == "asserted_quantifier_body" {
                        assert!(node["lemma"].is_null(), "observed bodies are not axioms");
                        asserted_body = true;
                    }
                    if node["reason"]["kind"] == "action_requirement"
                        && node["reason"]["action"] == "decide"
                    {
                        found |= asserted_body;
                    }
                    parent = node["parent"].as_u64();
                }
            }
        }
    }
    assert!(
        found,
        "guidance must connect decide, an asserted quorum tuple, and the vote initializer"
    );
}
