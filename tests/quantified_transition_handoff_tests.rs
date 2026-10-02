use std::process::Command;

#[test]
fn ordinary_search_supplies_the_missing_index_of_a_transition_request() {
    let output = Command::new(env!("CARGO_BIN_EXE_yardbird"))
        .args([
            "--filename",
            "tests/fixtures/quantified_partial_transition.vmt",
            "--policy",
            "countermodel-guided",
            "--depth",
            "2",
            "--wall-timeout-secs",
            "10",
            "--profile",
            "--json-output",
        ])
        .env("RUST_LOG", "off")
        .output()
        .unwrap();
    let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(result["run_progress"]["deepest_completed_depth"], 1);
    let provenance = &result["profiling"]["quantifier_provenance"];
    assert!(
        result["profiling"]["cost_records"]
            .as_array()
            .unwrap()
            .iter()
            .any(|record| {
                record["effort"].as_array().unwrap().iter().any(|effort| {
                    effort["operation"]
                        .as_str()
                        .is_some_and(|op| op.starts_with("DependencyRequest"))
                        && effort["candidates"]
                            .as_array()
                            .unwrap()
                            .iter()
                            .any(|candidate| {
                                let Some(node) = candidate["countermodel_origin"]["node"].as_u64()
                                else {
                                    return false;
                                };
                                let Some(rule) = candidate["rule"]
                                    .as_str()
                                    .and_then(|name| provenance["rules"].get(name))
                                else {
                                    return false;
                                };
                                candidate["selected"] == true
                                    && provenance["sources"][rule["source_id"].as_str().unwrap()]
                                        ["command"]
                                        == "define-fun trans"
                                    && rule["lowered_body"]
                                        .as_str()
                                        .is_some_and(|body| body.contains("Write_"))
                                    && record["countermodel_trace"]["nodes"][node as usize]
                                        ["expression"]
                                        .as_str()
                                        .is_some_and(|term| term.contains("table@1"))
                            })
                })
            }),
        "a row match fixes the node, and ordinary search must supply the store index"
    );
}
