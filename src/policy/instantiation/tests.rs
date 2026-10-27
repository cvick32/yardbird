use super::*;
use crate::{
    instance_installation::full_unroll::FullUnrollStrategy,
    policy::{discovery::DiscoveryContext, term_selection::array::ArrayBMCCost, YardbirdPolicy},
    problem_context::ProblemContext,
    solver::SolverCheckResult,
    strategies::{Abstract, ProofStrategy, RefinementState},
    vmt_bmc_session::VmtBmcSession,
    SolverBackend,
};
use serde_json::{json, Value};
use smt2parser::{concrete::SyntaxBuilder, vmt::VMTModel, CommandStream};
use std::collections::HashSet;

const INPUT: &str = r#"
    (declare-fun a () (Array Int Int))
    (declare-fun unused () (Array Int Int))
    (define-fun init () Bool (! (and
        (= (select (store a 1 7) 1) 9)
        (= (select unused 123) 42)) :init true))
    (define-fun trans () Bool (! true :trans true))
    (define-fun prop () Bool (! (= (select (store a 1 7) 1) 7) :invar-property 0))
"#;

pub(super) fn fixture() -> VmtBmcSession {
    let model = VMTModel::checked_from(
        CommandStream::new(INPUT.as_bytes(), SyntaxBuilder, None)
            .collect::<Result<Vec<_>, _>>()
            .unwrap(),
    )
    .unwrap();
    let mut strategy: Box<dyn ProofStrategy<'_, RefinementState>> =
        Box::new(Abstract::<ArrayBMCCost>::new(
            1,
            false,
            YardbirdPolicy::new(()),
            false,
        ));
    let model = strategy.configure_model(model);
    let mut smt = VmtBmcSession::new(
        &model,
        &strategy,
        SolverBackend::Z3,
        false,
        Box::new(FullUnrollStrategy::new()),
        false,
        None,
    )
    .unwrap();
    assert_eq!(smt.check_property(), SolverCheckResult::Sat);
    smt
}

fn proposal(snapshot: &InstantiationSnapshot, rule: &str) -> InstantiationProposal {
    let schema = snapshot
        .schemas
        .iter()
        .find(|s| s.name().starts_with(rule))
        .unwrap();
    let bindings: std::collections::BTreeMap<String, String> = schema
        .slots
        .keys()
        .map(|slot| {
            let expression = match slot.as_str() {
                "a" => "a@0",
                "idx" | "c" => "1",
                "val" => "7",
                _ => panic!("unexpected slot"),
            };
            let term = snapshot
                .terms
                .iter()
                .find(|t| t.expression == expression)
                .unwrap();
            (slot.clone(), term.id.clone())
        })
        .collect();
    // A joint response needs no JEV questions, choices, or probability tables.
    serde_json::from_value(json!({"axiom_id": schema.id, "bindings": bindings})).unwrap()
}

#[test]
fn context_is_complete_owned_and_independent_of_provider_request_edits() {
    let smt = fixture();
    let pending = HashSet::new();
    let context = DiscoveryContext {
        smt: &smt,
        depth: 0,
        refinement_step: 2,
        model_version: 3,
        pending: &pending,
    };
    let mut source = INPUT.to_owned();
    let snapshot = InstantiationSession::default()
        .capture(&context, &source)
        .unwrap();
    source.clear();
    let state = snapshot.state();
    assert_eq!(state["problem"]["source"], INPUT);
    assert_eq!(state["model"], smt.native_model_to_string().unwrap());
    assert_eq!(state["refinement_step"], 2);
    assert_eq!(state["model_version"], 3);
    assert!(state["terms"]
        .as_array()
        .unwrap()
        .iter()
        .any(|t| t["expression"] == "123"));
    for field in [
        "task",
        "questions",
        "decision_stage",
        "selected_axiom",
        "failure_summary",
    ] {
        assert!(
            state.get(field).is_none(),
            "provider field {field} in shared context"
        );
    }
    assert!(!state.to_string().contains("Jev"));
    let mut request = snapshot.state();
    request["terms"] = json!([]);
    request["model"] = Value::Null;
    assert_eq!(snapshot.state(), state);
}

#[test]
fn joint_proposals_use_exact_schemas_and_shared_whole_formula_validation() {
    let smt = fixture();
    let pending = HashSet::new();
    let context = DiscoveryContext {
        smt: &smt,
        depth: 0,
        refinement_step: 0,
        model_version: 1,
        pending: &pending,
    };
    let snapshot = InstantiationSession::default()
        .capture(&context, INPUT)
        .unwrap();
    let instance = snapshot
        .resolve(&proposal(&snapshot, "read-after-write"))
        .unwrap();
    assert_eq!(
        instance.term.to_string(),
        "(= (Read_Int_Int (Write_Int_Int a@0 1 7) 1) 7)"
    );
    let (feedback, accepted) = validate(&context, instance);
    assert_eq!(feedback["outcome"], "violated");
    assert!(accepted.is_some());

    let instance = snapshot
        .resolve(&proposal(&snapshot, "write-does-not-overwrite"))
        .unwrap();
    let (feedback, accepted) = validate(&context, instance);
    assert_eq!(feedback["reason"], "false_antecedent");
    assert!(accepted.is_none());
}

#[test]
fn joint_proposals_reject_unknown_ids_wrong_sorts_and_inexact_slots() {
    let smt = fixture();
    let pending = HashSet::new();
    let context = DiscoveryContext {
        smt: &smt,
        depth: 0,
        refinement_step: 0,
        model_version: 1,
        pending: &pending,
    };
    let snapshot = InstantiationSession::default()
        .capture(&context, INPUT)
        .unwrap();
    let valid = proposal(&snapshot, "read-after-write");
    let mut unknown_axiom = valid.clone();
    unknown_axiom.axiom_id = "q999".into();
    let mut unknown_term = valid.clone();
    unknown_term.bindings.insert("idx".into(), "t999".into());
    let mut model_value = valid.clone();
    model_value
        .bindings
        .insert("a".into(), "Array_Int_Int!val!0".into());
    let mut wrong_sort = valid.clone();
    wrong_sort
        .bindings
        .insert("idx".into(), valid.bindings["a"].clone());
    let mut missing = valid.clone();
    missing.bindings.remove("idx");
    let mut extra = valid.clone();
    extra
        .bindings
        .insert("c".into(), valid.bindings["idx"].clone());
    for invalid in [
        unknown_axiom,
        unknown_term,
        model_value,
        wrong_sort,
        missing,
        extra,
    ] {
        assert!(snapshot.resolve(&invalid).is_err(), "accepted {invalid:?}");
    }
    let mut raw = serde_json::to_value(valid).unwrap();
    raw["formula"] = json!("false");
    assert!(serde_json::from_value::<InstantiationProposal>(raw).is_err());
}
