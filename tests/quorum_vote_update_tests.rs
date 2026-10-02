use std::process::Command;

const PRESERVE: &str = "tests/fixtures/quantified_quorum_vote_update.vmt";
const ERASE: &str = "tests/fixtures/quantified_quorum_vote_erasure.vmt";

fn run_fixture(file: &str, concrete: bool, profile: bool) -> serde_json::Value {
    let mut command = Command::new(env!("CARGO_BIN_EXE_yardbird"));
    command.args([
        "--filename",
        file,
        "--depth",
        "3",
        "--wall-timeout-secs",
        "5",
        "--json-output",
    ]);
    if concrete {
        command.args(["--strategy", "concrete"]);
    } else {
        command.args([
            "--policy",
            "countermodel-guided",
            "--guidance-schedule",
            "supplement",
        ]);
    }
    if profile {
        command.arg("--profile");
    }
    let output = command.env("RUST_LOG", "off").output().unwrap();
    let result: serde_json::Value =
        serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
            panic!(
                "{file}: {error}: {}",
                String::from_utf8_lossy(&output.stderr)
            )
        });
    assert!(
        output.status.success() || result["counterexample"] == true,
        "{file}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    result
}

#[test]
fn concrete_distinguishes_adding_a_vote_from_erasing_a_required_vote() {
    let safe = run_fixture(PRESERVE, true, false);
    assert_eq!(safe["counterexample"], false);
    assert_eq!(safe["run_progress"]["deepest_completed_depth"], 2);

    let unsafe_result = run_fixture(ERASE, true, false);
    assert_eq!(unsafe_result["counterexample"], true);
    assert_eq!(unsafe_result["run_progress"]["deepest_completed_depth"], 1);
    assert_eq!(unsafe_result["run_progress"]["current_depth"], 2);
}

#[test]
fn guidance_does_not_use_an_old_quorum_to_verify_erased_votes() {
    let result = run_fixture(ERASE, false, false);
    // Quantifier abstraction may time out instead of reporting the real
    // counterexample, but it must not verify the state after the erasure.
    assert_eq!(result["found_proof"], false);
    assert_eq!(result["run_progress"]["deepest_completed_depth"], 1);
}

#[test]
fn guidance_reuses_an_earlier_quorum_after_a_vote_preserving_update() {
    let result = run_fixture(PRESERVE, false, true);
    assert_eq!(result["counterexample"], false);
    assert_eq!(result["run_progress"]["deepest_completed_depth"], 2);

    let profiling = &result["profiling"];
    let rules = &profiling["quantifier_provenance"]["rules"];
    let sources = &profiling["quantifier_provenance"]["sources"];
    assert!(
        profiling["cost_records"]
            .as_array()
            .unwrap()
            .iter()
            .any(|record| {
                record["bmc_depth"] == 2
                    && record["countermodel_trace"]["nodes"]
                        .as_array()
                        .is_some_and(|nodes| {
                            nodes.iter().any(|node| {
                                let Some(rule) = node["lemma"]["rule"]
                                    .as_str()
                                    .and_then(|name| rules.get(name))
                                else {
                                    return false;
                                };
                                let Some(source) =
                                    rule["source_id"].as_str().and_then(|id| sources.get(id))
                                else {
                                    return false;
                                };
                                node["reason"]["kind"] == "quantifier_match"
                                    && source["command"] == "define-fun prop"
                                    && source["kind"] == "exists"
                                    && node["lemma"]["formula"].as_str().is_some_and(|term| {
                                        term.contains("chosen@0")
                                            && term.contains("votes@2")
                                            && !term.contains("votes@0")
                                            && !term.contains("votes@1")
                                    })
                            })
                        })
            }),
        "guidance must retain the earlier quorum as an existential candidate with the \
         property's post-update vote array; ordinary-search completion alone is insufficient"
    );

    let mut traced_guard = false;
    let mut traced_update = false;
    for record in profiling["cost_records"].as_array().unwrap() {
        if record["bmc_depth"] != 2 {
            continue;
        }
        for effort in record["effort"].as_array().unwrap() {
            if effort["operation"] != "CountermodelCandidates" {
                continue;
            }
            for candidate in effort["candidates"].as_array().unwrap() {
                if candidate["selected"] != true {
                    continue;
                }
                let Some(id) = candidate["countermodel_origin"]["node"].as_u64() else {
                    continue;
                };
                let node = &record["countermodel_trace"]["nodes"][id as usize];
                let Some(formula) = node["lemma"]["formula"].as_str() else {
                    continue;
                };
                if !formula.contains("chosen@0") || !formula.contains("votes@2") {
                    continue;
                }
                traced_update |= node["reason"]["kind"] == "array_axiom"
                    && formula.contains("Write_node_Bool votes@1 newcomer@1 true");
                if let Some(source) = node["lemma"]["rule"]
                    .as_str()
                    .and_then(|name| rules.get(name))
                    .and_then(|rule| rule["source_id"].as_str())
                    .and_then(|id| sources.get(id))
                {
                    traced_guard |= source["command"] == "define-fun trans"
                        && formula.contains("votes@0")
                        && formula.contains("__yardbird_witness_");
                }
            }
        }
    }
    assert!(
        traced_guard && traced_update,
        "guidance must follow the current property's node witness through the vote update \
         and select an instance of the earlier quorum guard"
    );
}
