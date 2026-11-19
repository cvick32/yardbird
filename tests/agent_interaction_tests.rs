use std::process::{Command, Stdio};

mod support;
use serde_json::{json, Value};
use support::{term_id, Session};

#[test]
fn scripted_pause_instantiate_advance_for_arrays_and_binders() {
    for (fixture, array) in [
        ("prerequisite_explicit_action", true),
        ("quantified_response_witness", false),
    ] {
        let mut s = Session::new(fixture, 1, 0, false);
        assert_eq!(s.ready["capabilities"].as_array().unwrap().len(), 7);
        let snapshot = s.call("snapshot", json!({}));
        assert_eq!(snapshot["pending_ids"], json!([]));
        let shared = &snapshot["shared_snapshot"];
        let schema = shared["axioms"]
            .as_array()
            .unwrap()
            .iter()
            .find(|q| {
                if array {
                    q["name"] == "constant-array-Int-Int"
                } else {
                    q["provenance"]["direction"] == "instance"
                }
            })
            .unwrap();
        let bindings = if array {
            let zero = term_id(shared, "0");
            json!({"a": zero, "b": zero})
        } else {
            json!({"capture_0": term_id(shared, "reply@0"), "variable_0": term_id(shared, "chosen@0")})
        };
        assert_eq!(
            s.call("inspect", json!({"ref":schema["id"]}))["record"]["data"]["slots"],
            schema["slots"]
        );
        assert_eq!(
            s.invoke("inspect", json!({"epoch":"stale","ref":schema["id"]}))["error"]["code"],
            "stale_epoch"
        );
        assert_eq!(
            s.invoke("search", json!({"operations":1}))["error"]["code"],
            "unsupported"
        );
        let epoch = s.epoch.clone();
        let empty = s.call("advance", json!({"solver_timeout_ms":5000}));
        assert_eq!(empty["outcome"], "no_progress");
        assert_eq!(s.epoch, epoch);
        assert_eq!(empty["usage"]["solver_checks"], 0);
        let item = json!({"proposal_id":"test-instance","proposal":{"axiom_id":schema["id"],"bindings":bindings}});
        let mut bad = item.clone();
        let wrong = shared["terms"]
            .as_array()
            .unwrap()
            .iter()
            .find(|t| t["sort"] == if array { "Array_Int_Int" } else { "Bool" })
            .unwrap();
        let slot = schema["slots"].as_object().unwrap().keys().next().unwrap();
        bad["proposal"]["bindings"][slot] = wrong["id"].clone();
        assert_eq!(s.invoke("instantiate", json!({"items":[bad]}))["ok"], false);
        assert_eq!(s.call("snapshot", json!({}))["pending_ids"], json!([]));
        let accepted = s.invoke("instantiate", json!({"items":[item]}));
        let command = s.last_command.clone();
        assert_eq!(s.send(&command), accepted);
        let mut collision = command;
        collision["items"][0]["proposal_id"] = json!("collision");
        assert_eq!(s.send(&collision)["error"]["code"], "id_conflict");
        let candidate = &accepted["result"]["candidates"][0];
        assert_eq!(candidate["validation"], "violated");
        assert!(candidate["installation"].is_null());
        assert_eq!(candidate["selection"], "pending");
        assert_eq!(
            accepted["result"]["pending_ids"].as_array().unwrap().len(),
            1
        );
        let mut duplicate = item;
        duplicate["proposal_id"] = json!("duplicate");
        assert_eq!(
            s.call("instantiate", json!({"items":[duplicate]}))["candidates"][0]["validation"],
            "already_present"
        );
        let advanced = s.call("advance", json!({"solver_timeout_ms":5000}));
        assert_eq!(advanced["outcome"], "bounded_complete");
        assert!(s.epoch.is_null());
        assert_eq!(
            advanced["events"],
            json!([{"event":"depth_closed","depth":0}])
        );
        assert_eq!(advanced["candidates"][0]["selection"], "selected");
        assert!(
            advanced["candidates"][0]["installation"]["indexed_assertions_added"]
                .as_u64()
                .unwrap()
                > 0
        );
        assert_eq!(advanced["usage"]["solver_checks"], 1);
        assert_eq!(advanced["usage"]["search_operations"], 0);
        s.terminal("bounded_complete");
    }
}

#[test]
fn successive_countermodels_require_new_epochs() {
    let mut s = Session::new("prerequisite_explicit_action", 2, 0, false);
    let snapshot = s.call("snapshot", json!({}));
    let shared = &snapshot["shared_snapshot"];
    let schema = shared["axioms"]
        .as_array()
        .unwrap()
        .iter()
        .find(|q| q["name"] == "constant-array-Int-Int")
        .unwrap();
    let zero = term_id(shared, "0");
    let item = json!({"proposal_id":"init","proposal":{"axiom_id":schema["id"],"bindings":{"a":zero,"b":zero}}});
    assert_eq!(
        s.call("instantiate", json!({"items":[item]}))["candidates"][0]["validation"],
        "violated"
    );
    let old = s.epoch.clone();
    assert_eq!(
        s.call("advance", json!({"solver_timeout_ms":5000}))["outcome"],
        "sat"
    );
    assert_ne!(s.epoch, old);
    assert_eq!(
        s.invoke("snapshot", json!({"epoch":old}))["error"]["code"],
        "stale_epoch"
    );
    s.stop();
}

#[test]
fn term_construction_is_typed_and_does_not_complete_the_model() {
    let mut s = Session::new("array_dataflow_actions", 1, 0, false);
    let original = s.call("snapshot", json!({}))["shared_snapshot"]["model"].clone();
    let constructed = s.call("make_term", json!({"smt2":"(+ 0 1)"}));
    assert!(constructed["records"]
        .as_array()
        .unwrap()
        .iter()
        .any(|r| r["id"] == constructed["term_ref"] && r["sort"] == "Int"));
    for bad in [
        "(witness true)",
        "(not 1)",
        "(= 0 0 1)",
        "(xor true false)",
        "unregistered",
        "(forall ((x Int)) (witness x))",
        "0) (assert false) (assert 0",
        "witness",
        "1.25",
    ] {
        assert_eq!(
            s.invoke("make_term", json!({"smt2":bad}))["ok"],
            false,
            "{bad}"
        );
    }
    s.call("make_term", json!({"smt2":"(witness b@0)"}));
    let current = s.call("snapshot", json!({}));
    assert_eq!(current["shared_snapshot"]["model"], original);
    assert_eq!(current["pending_ids"], json!([]));
    s.stop();
}

#[test]
fn dependent_witnesses_preserve_distinct_and_nested_captures() {
    let mut s = Session::new("quantified_response_capture", 1, 0, false);
    let snapshot = s.call("snapshot", json!({}));
    let schema = snapshot["shared_snapshot"]["axioms"]
        .as_array()
        .unwrap()
        .iter()
        .find(|q| {
            q["provenance"]["direction"] == "witness"
                && q["provenance"]["lowered"]["kind"] == "forall"
        })
        .unwrap();
    let slot = schema["slots"].as_object().unwrap().keys().next().unwrap();
    let witness = schema["provenance"]["lowered"]["witnesses"][0]
        .as_str()
        .unwrap();
    let mut witnesses = Vec::new();
    for (i, capture) in ["(ite true reply@0 reply@0)", "(ite false reply@0 reply@0)"]
        .iter()
        .enumerate()
    {
        let term = s.call("make_term", json!({"smt2":capture}))["term_ref"].clone();
        let result = s.call(
            "instantiate",
            json!({"items":[{
                "proposal_id": format!("witness-{i}"),
                "proposal": {"axiom_id":schema["id"], "bindings":{slot:term}}
            }]}),
        );
        let expected = format!("({witness} {capture})");
        witnesses.push(
            result["records"]
                .as_array()
                .unwrap()
                .iter()
                .find(|record| {
                    record["kind"] == "term"
                        && record["sort"] == "response"
                        && record["expression"] == expected
                })
                .unwrap()
                .clone(),
        );
    }
    assert_ne!(witnesses[0]["id"], witnesses[1]["id"]);
    let nested = s.call(
        "instantiate",
        json!({"items":[{
            "proposal_id": "nested",
            "proposal": {"axiom_id": schema["id"], "bindings":{slot:witnesses[0]["id"]}}
        }]}),
    );
    let expected = format!(
        "({witness} {})",
        witnesses[0]["expression"].as_str().unwrap()
    );
    assert!(nested["records"]
        .as_array()
        .unwrap()
        .iter()
        .any(|record| record["expression"] == expected));
    assert_eq!(
        s.call("snapshot", json!({}))["shared_snapshot"]["model"],
        snapshot["shared_snapshot"]["model"]
    );
    s.stop();
}

#[test]
fn assisted_search_only_queues_and_advance_only_installs_and_checks() {
    let mut s = Session::new("prerequisite_explicit_action", 1, 0, true);
    let epoch = s.epoch.clone();
    let mut found = false;
    for _ in 0..8 {
        let result = s.call("search", json!({"operations":8}));
        assert_eq!(s.epoch, epoch);
        assert_eq!(result["usage"]["solver_checks"], 0);
        assert!(result["operations"].as_array().unwrap().len() <= 8);
        assert!(result["candidates"]
            .as_array()
            .unwrap()
            .iter()
            .all(|c| c["installation"].is_null()));
        if !result["pending_ids"].as_array().unwrap().is_empty() {
            assert!(result["candidates"].as_array().unwrap().iter().any(|c| !c
                ["search_command_ids"]
                .as_array()
                .unwrap()
                .is_empty()
                && c["proposal_ids"].as_array().unwrap().is_empty()));
            found = true;
            break;
        }
    }
    assert!(found);
    let advanced = s.call("advance", json!({"solver_timeout_ms":5000}));
    assert_eq!(advanced["outcome"], "bounded_complete");
    assert_eq!(advanced["usage"]["search_operations"], 0);
    s.terminal("bounded_complete");
}

#[test]
fn targeted_action_expansion_supplies_exact_captures_for_refinement() {
    use std::collections::BTreeMap;
    let mut s = Session::new("action_requirement_quorum", 2, 1, false);
    let snapshot = s.call("snapshot", json!({}));
    let mut records: BTreeMap<String, Value> = snapshot["records"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| (r["id"].as_str().unwrap().into(), r.clone()))
        .collect();
    let action = records
        .values()
        .find(|r| r["kind"] == "action" && r["expression"].as_str().unwrap().contains("decide"))
        .unwrap()["id"]
        .clone();
    assert_eq!(
        s.invoke(
            "expand_action",
            json!({"ref":format!("{}:unseen",action.as_str().unwrap()),"work":200})
        )["ok"],
        false
    );
    let action_args = records[action.as_str().unwrap()]["data"]["arguments"]
        .as_object()
        .unwrap();
    for term in ["decisions@0", "decisions@1", "0", "true"] {
        assert!(
            action_args
                .values()
                .any(|id| records[id.as_str().unwrap()]["expression"] == term),
            "{term}"
        );
    }
    let limited = s.call("expand_action", json!({"ref":action,"work":1}));
    assert!(limited["work_used"].as_u64().unwrap() <= 1);
    let expanded = s.call("expand_action", json!({"ref":action,"work":200}));
    let repeat = s.call("expand_action", json!({"ref":action,"work":200}));
    assert_eq!(repeat["work_used"], 0);
    assert_eq!(repeat["cutoff"], false);
    assert_eq!(expanded["usage"]["search_operations"], 0);
    let current = s.call("snapshot", json!({}));
    assert_eq!(current["pending_ids"], json!([]));
    assert_eq!(
        current["shared_snapshot"]["model"],
        snapshot["shared_snapshot"]["model"]
    );
    for result in [&limited, &expanded] {
        for r in result["records"].as_array().unwrap() {
            records.insert(r["id"].as_str().unwrap().into(), r.clone());
        }
    }
    let requirement = [&limited, &expanded]
        .into_iter()
        .flat_map(|r| r["discovered_refs"].as_array().unwrap())
        .flat_map(|id| {
            records[id.as_str().unwrap()]["links"]["binders"]
                .as_array()
                .into_iter()
                .flatten()
        })
        .map(|id| &records[id.as_str().unwrap()])
        .find(|r| {
            r["links"]["schemas"]
                .as_array()
                .is_some_and(|s| !s.is_empty())
        })
        .unwrap();
    let schema = requirement["links"]["schemas"]
        .as_array()
        .unwrap()
        .iter()
        .map(|id| &records[id.as_str().unwrap()])
        .find(|r| r["data"]["direction"] == "instance")
        .unwrap();
    let captures = &requirement["links"]["captures"];
    let node = records
        .values()
        .find(|r| r["kind"] == "term" && r["sort"] == "node")
        .unwrap()["id"]
        .clone();
    let bindings: serde_json::Map<String, Value> = schema["data"]["slots"]
        .as_object()
        .unwrap()
        .keys()
        .map(|slot| {
            let value = slot
                .strip_prefix("capture_")
                .map(|n| captures[n.parse::<usize>().unwrap()].clone())
                .unwrap_or_else(|| node.clone());
            (slot.clone(), value)
        })
        .collect();
    let result = s.call(
        "instantiate",
        json!({"items":[{
            "proposal_id": "decide-at-target",
            "proposal": {"axiom_id":schema["id"], "bindings":bindings}
        }]}),
    );
    let candidate = &result["candidates"][0];
    assert_eq!(candidate["construction"], "constructed");
    let expression = candidate["expression"].as_str().unwrap();
    assert!(!captures.as_array().unwrap().is_empty());
    for id in captures.as_array().unwrap() {
        let capture = &records[id.as_str().unwrap()];
        assert!(
            expression.contains(capture["expression"].as_str().unwrap()),
            "{expression}"
        );
    }
    s.stop();
}

#[test]
fn disconnected_controller_is_inconclusive() {
    let result = Command::new(env!("CARGO_BIN_EXE_yardbird"))
        .args([
            "-f",
            "tests/fixtures/prerequisite_explicit_action.vmt",
            "-d",
            "1",
            "--agent-stdio",
        ])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let messages: Vec<serde_json::Value> = String::from_utf8(result.stdout)
        .unwrap()
        .lines()
        .map(|s| serde_json::from_str(s).unwrap())
        .collect();
    assert_eq!(messages.last().unwrap()["reason"], "eof");
    assert!(!messages.iter().any(|v| v["reason"] == "bounded_complete"));
}

#[test]
fn unsupported_configuration_fails_before_protocol_start() {
    let result = Command::new(env!("CARGO_BIN_EXE_yardbird"))
        .args([
            "-f",
            "tests/fixtures/prerequisite_explicit_action.vmt",
            "--agent-stdio",
            "--solver",
            "cvc5",
        ])
        .output()
        .unwrap();
    assert!(!result.status.success());
    assert!(result.stdout.is_empty());
    assert!(String::from_utf8_lossy(&result.stderr).contains("requires Z3"));
}

#[test]
fn explicit_stop_is_acknowledged_without_a_proof() {
    use std::io::Write;
    let mut child = Command::new(env!("CARGO_BIN_EXE_yardbird"))
        .args([
            "-f",
            "tests/fixtures/prerequisite_explicit_action.vmt",
            "-d",
            "1",
            "--agent-stdio",
        ])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(b"{\"v\":0,\"id\":\"stop\",\"epoch\":\"e1\",\"op\":\"stop\"}\n")
        .unwrap();
    let result = child.wait_with_output().unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let messages: Vec<serde_json::Value> = String::from_utf8(result.stdout)
        .unwrap()
        .lines()
        .map(|s| serde_json::from_str(s).unwrap())
        .collect();
    assert_eq!(messages[2]["result"]["outcome"], "stopped");
    assert_eq!(messages[2]["epoch"], serde_json::Value::Null);
    assert_eq!(messages.last().unwrap()["reason"], "stopped");
}

#[test]
fn oversized_command_is_rejected_without_a_solver_advance() {
    use std::io::Write;
    let mut child = Command::new(env!("CARGO_BIN_EXE_yardbird"))
        .args([
            "-f",
            "tests/fixtures/prerequisite_explicit_action.vmt",
            "-d",
            "1",
            "--agent-stdio",
        ])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let bytes = vec![b'x'; 65_537];
    child.stdin.take().unwrap().write_all(&bytes).unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success());
    let messages: Vec<serde_json::Value> = String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    assert!(messages
        .iter()
        .any(|m| m["error"]["code"] == "limit_exceeded"));
    let last = messages.last().unwrap();
    assert_eq!(last["reason"], "internal_error");
    assert_eq!(last["usage"]["solver_checks"], 1);
}

#[test]
fn idle_controller_expires_inconclusively() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_yardbird"))
        .args([
            "-f",
            "tests/fixtures/prerequisite_explicit_action.vmt",
            "-d",
            "1",
            "--agent-stdio",
            "--wall-timeout-secs",
            "1",
        ])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let input = child.stdin.take().unwrap();
    let output = child.wait_with_output().unwrap();
    drop(input);
    assert!(output.status.success());
    let messages: Vec<serde_json::Value> = String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    assert_eq!(messages.last().unwrap()["reason"], "timeout");
    assert!(!messages.iter().any(|m| m["reason"] == "bounded_complete"));
}
