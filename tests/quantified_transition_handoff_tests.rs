use std::process::Command;

#[test]
fn direct_updates_follow_active_guards_across_models_and_do_not_hide_bad_updates() {
    let source = include_str!("fixtures/quantified_guarded_transition.vmt");
    for broken in [false, true] {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("guarded.vmt");
        std::fs::write(
            &file,
            if broken {
                source.replace("(= (select cells_next i) 1)", "(= (select cells_next i) 0)")
            } else {
                source.into()
            },
        )
        .unwrap();
        for concrete in [false, true] {
            let mut command = Command::new(env!("CARGO_BIN_EXE_yardbird"));
            command.arg("--filename").arg(&file).args([
                "--depth",
                "3",
                "--wall-timeout-secs",
                if broken { "1" } else { "10" },
                "--json-output",
            ]);
            if concrete {
                command.args(["--strategy", "concrete"]);
            } else {
                command.args(["--policy", "countermodel-guided", "--profile"]);
            }
            let output = command.env("RUST_LOG", "off").output().unwrap();
            let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
            assert_eq!(
                result["run_progress"]["deepest_completed_depth"],
                if broken { 0 } else { 2 }
            );
            if concrete {
                assert_eq!(result["counterexample"], broken);
            }
            if concrete || broken {
                continue;
            }
            let provenance = &result["profiling"]["quantifier_provenance"];
            for (frame, expected) in [(0, "define-fun fill_one"), (1, "define-fun fill_zero")] {
                let mut found = false;
                for record in result["profiling"]["cost_records"].as_array().unwrap() {
                    let Some(nodes) = record["countermodel_trace"]["nodes"].as_array() else {
                        continue;
                    };
                    for node in nodes {
                        if node["reason"]["kind"] != "quantified_transition"
                            || node["reason"]["frame"] != frame
                        {
                            continue;
                        }
                        for lemma in node["reason"]["path"]
                            .as_array()
                            .unwrap()
                            .iter()
                            .chain(node.get("lemma").filter(|lemma| !lemma.is_null()))
                        {
                            let rule = &provenance["rules"][lemma["rule"].as_str().unwrap()];
                            assert_eq!(
                                provenance["sources"][rule["source_id"].as_str().unwrap()]
                                    ["command"],
                                expected
                            );
                            found = true;
                        }
                    }
                }
                assert!(found, "must trace the active update at frame {frame}");
            }
        }
    }
}

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

#[test]
fn guidance_follows_a_pointwise_update_before_ordinary_search() {
    let output = Command::new(env!("CARGO_BIN_EXE_yardbird"))
        .args([
            "--filename",
            "tests/fixtures/quantified_pointwise_transition.vmt",
            "--policy",
            "countermodel-guided",
            "--guidance-schedule",
            "supplement",
            "--depth",
            "3",
            "--wall-timeout-secs",
            "10",
            "--profile",
            "--json-output",
        ])
        .env("RUST_LOG", "off")
        .output()
        .unwrap();
    let result: serde_json::Value = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|e| panic!("{e}: {}", String::from_utf8_lossy(&output.stderr)));
    assert_eq!(result["run_progress"]["deepest_completed_depth"], 2);
    let provenance = &result["profiling"]["quantifier_provenance"];
    assert!(
        result["profiling"]["cost_records"]
            .as_array()
            .unwrap()
            .iter()
            .any(|record| {
                record["effort"].as_array().unwrap().iter().any(|effort| {
                    effort["operation"] == "CountermodelCandidates"
                        && effort["candidates"]
                            .as_array()
                            .unwrap()
                            .iter()
                            .any(|candidate| {
                                let Some(node) = candidate["countermodel_origin"]["node"].as_u64()
                                else {
                                    return false;
                                };
                                let frontier =
                                    &record["countermodel_trace"]["nodes"][node as usize];
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
                                        .is_some_and(|body| body.contains("Read_"))
                                    && candidate["countermodel_origin"]["model_version"]
                                        == record["countermodel_trace"]["model_version"]
                                    && frontier["status"]["kind"] == "violated_quantifier_instance"
                                    && frontier["reason"]["kind"] == "quantified_transition"
                                    && candidate["substitution"]
                                        .as_array()
                                        .unwrap()
                                        .iter()
                                        .any(|s| s["term"] == "left+0")
                                    && candidate["substitution"]
                                        .as_array()
                                        .unwrap()
                                        .iter()
                                        .any(|s| s["term"] == "left+1")
                            })
                })
            }),
        "guidance must directly select the pointwise transition instance"
    );
    assert!(
        result["profiling"]["cost_records"]
            .as_array()
            .unwrap()
            .iter()
            .any(|record| {
                let Some(nodes) = record["countermodel_trace"]["nodes"].as_array() else {
                    return false;
                };
                nodes.iter().any(|node| {
                    if node["reason"]["kind"] != "quantified_transition"
                        || node["reason"]["frame"] != 0
                        || node["status"]["kind"] != "expanded"
                    {
                        return false;
                    }
                    let mut parent = node["parent"].as_u64();
                    while let Some(id) = parent {
                        let ancestor = &nodes[id as usize];
                        if ancestor["reason"]["kind"] == "quantified_transition"
                            && ancestor["reason"]["frame"] == 1
                        {
                            return true;
                        }
                        parent = ancestor["parent"].as_u64();
                    }
                    false
                })
            }),
        "a satisfied update must continue through its body into the previous quantified update"
    );
}
