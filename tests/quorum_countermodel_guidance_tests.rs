use std::process::Command;

#[test]
fn quorum_guidance_does_not_verify_erased_votes_and_does_not_require_profiling() {
    for (file, counterexample) in [
        ("tests/fixtures/quantified_quorum_transition.vmt", false),
        ("tests/fixtures/quantified_quorum_lost_votes.vmt", true),
    ] {
        for strategy in ["countermodel-guided", "concrete"] {
            let mut command = Command::new(env!("CARGO_BIN_EXE_yardbird"));
            command.args([
                "--filename",
                file,
                "--depth",
                "2",
                "--wall-timeout-secs",
                if counterexample && strategy != "concrete" {
                    "1"
                } else {
                    "10"
                },
                "--json-output",
            ]);
            if strategy == "concrete" {
                command.args(["--strategy", strategy]);
            } else {
                command.args(["--policy", strategy]);
            }
            let output = command.env("RUST_LOG", "off").output().unwrap();
            let result: serde_json::Value =
                serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
                    panic!(
                        "{file} ({strategy}): {error}: {}",
                        String::from_utf8_lossy(&output.stderr)
                    )
                });
            // General quantifier abstraction currently does not validate real
            // counterexamples with concrete Z3. It may time out on the unsafe
            // case, but must never complete that depth. Concrete is the oracle.
            if strategy == "concrete" || !counterexample {
                assert_eq!(
                    result["counterexample"], counterexample,
                    "{file} ({strategy})"
                );
            }
            assert_eq!(result["found_proof"], false, "{file} ({strategy})");
            assert_eq!(
                result["run_progress"]["deepest_completed_depth"],
                if counterexample { 0 } else { 1 },
                "{file} ({strategy})"
            );
        }
    }
}

#[test]
fn guidance_keeps_the_property_frame_when_matching_an_earlier_quorum_guard() {
    let output = Command::new(env!("CARGO_BIN_EXE_yardbird"))
        .args([
            "--filename",
            "tests/fixtures/quantified_quorum_transition.vmt",
            "--policy",
            "countermodel-guided",
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
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(result["run_progress"]["deepest_completed_depth"], 2);
    assert!(result["profiling"]["cost_records"].as_array().unwrap().iter().any(|record| {
        record["countermodel_trace"]["nodes"].as_array().is_some_and(|nodes| nodes.iter().any(|node| {
            node["reason"]["kind"] == "quantifier_match"
                && node["lemma"]["formula"].as_str().is_some_and(|term| {
                    term.contains("chosen@0") && term.contains("votes@1") && !term.contains("votes@0")
                })
        }))
    }), "the proposed existential must use the earlier action quorum with the property's current vote array");
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
                                let Some(id) = candidate["countermodel_origin"]["node"].as_u64()
                                else {
                                    return false;
                                };
                                candidate["selected"] == true
                                    && record["countermodel_trace"]["nodes"][id as usize]["lemma"]
                                        ["formula"]
                                        .as_str()
                                        .is_some_and(|term| {
                                            term.contains("__yardbird_witness_")
                                                && term.contains("chosen@0")
                                        })
                            })
                })
            }),
        "the nested quorum obligation must produce a selected guided refinement"
    );
}

#[test]
fn guidance_connects_a_quorum_guard_to_a_nested_existential_property() {
    let output = Command::new(env!("CARGO_BIN_EXE_yardbird"))
        .args([
            "--filename",
            "tests/fixtures/quantified_quorum_witness.vmt",
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
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(result["run_progress"]["deepest_completed_depth"], 1);
    let rules = result["profiling"]["quantifier_provenance"]["rules"]
        .as_object()
        .unwrap();
    assert!(result["profiling"]["cost_records"].as_array().unwrap().iter().any(|record| {
        record["effort"].as_array().unwrap().iter().any(|effort| {
            effort["operation"] == "CountermodelCandidates"
                && effort["candidates"].as_array().unwrap().iter().any(|candidate| {
                    let Some(id) = candidate["countermodel_origin"]["node"].as_u64() else { return false; };
                    let lemma = &record["countermodel_trace"]["nodes"][id as usize]["lemma"];
                    let Some(rule) = lemma["rule"].as_str().and_then(|name| rules.get(name)) else { return false; };
                    let source = &result["profiling"]["quantifier_provenance"]["sources"][rule["source_id"].as_str().unwrap()];
                    candidate["selected"] == true && source["command"] == "define-fun init"
                        && lemma["formula"].as_str().is_some_and(|term| {
                            term.contains("chosen@") && term.contains("__yardbird_witness_")
                        })
                })
        })
    }), "guided search must instantiate the source quorum guard at the inner property's counterexample witness");
}
