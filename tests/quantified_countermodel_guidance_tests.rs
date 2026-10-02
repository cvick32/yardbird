use std::process::Command;

#[test]
fn guidance_keeps_property_captures_when_source_terms_are_model_equal() {
    for compound in [false, true] {
        let directory = tempfile::tempdir().unwrap();
        let file = directory.path().join("capture.vmt");
        let mut input =
            std::fs::read_to_string("tests/fixtures/quantified_response_capture.vmt").unwrap();
        if compound {
            input = input
                .replace(
                    "(declare-fun chosen () request)",
                    "(declare-fun chosen () request)\n(declare-fun response_alias (response) response)",
                )
                .replace(
                    "(! (matches chosen reply) :init true)",
                    "(! (and (= (response_alias reply) reply) (matches chosen (response_alias reply))) :init true)",
                );
        }
        std::fs::write(&file, input).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_yardbird"))
            .arg("--filename")
            .arg(&file)
            .args([
                "--policy",
                "countermodel-guided",
                "--depth",
                "1",
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
        assert_eq!(result["run_progress"]["deepest_completed_depth"], 0);
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
                                let node = &record["countermodel_trace"]["nodes"][id as usize];
                                candidate["selected"] == true
                                    && node["status"]["kind"] == "violated_quantifier_instance"
                                    && node["lemma"]["formula"].as_str().is_some_and(|formula| {
                                        formula.starts_with(
                                            "(=> (matches chosen@0 (__yardbird_witness_",
                                        )
                                    })
                            })
                })
            }),
        "the useful source request must be instantiated with the property's actual witness capture (compound={compound})"
    );
    }
}

#[test]
fn guidance_binds_a_false_existential_from_a_known_response_pair() {
    let output = Command::new(env!("CARGO_BIN_EXE_yardbird"))
        .args([
            "--filename",
            "tests/fixtures/quantified_response_witness.vmt",
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
    assert!(
        result["profiling"]["cost_records"]
            .as_array()
            .unwrap()
            .iter()
            .any(|record| {
                let trace = &record["countermodel_trace"];
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
                                let node = &trace["nodes"][id as usize];
                                candidate["selected"] == true
                                    && node["status"]["kind"] == "violated_quantifier_instance"
                                    && node["lemma"]["formula"].as_str().is_some_and(|formula| {
                                        formula.starts_with("(=> (matches chosen@0 reply@0) ")
                                    })
                            })
                })
            }),
        "guidance must instantiate the existential using the known request/response pair"
    );
}

#[test]
fn guidance_reaches_array_refinement_inside_a_quantified_property() {
    let output = Command::new(env!("CARGO_BIN_EXE_yardbird"))
        .args([
            "--filename",
            "tests/fixtures/quantified_read_after_write.vmt",
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
    let records = result["profiling"]["cost_records"].as_array().unwrap();
    assert!(
        records.iter().any(|record| {
            let trace = &record["countermodel_trace"];
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
                            candidate["selected"] == true
                                && trace["nodes"][node as usize]["status"]["kind"]
                                    == "violated_array_axiom"
                        })
            })
        }),
        "guidance must enter the quantified property and select its array refinement; traces: {}",
        serde_json::Value::Array(
            records
                .iter()
                .map(|r| r["countermodel_trace"].clone())
                .collect()
        )
    );
}
