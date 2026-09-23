use super::*;
use crate::theories::array::array_dataflow::{DataflowRole, StaticArrayProvenance};
use smt2parser::{concrete::SyntaxBuilder, CommandStream};
use std::sync::Arc;

fn parse(input: &str) -> VMTModel {
    VMTModel::checked_from(
        CommandStream::new(input.as_bytes(), SyntaxBuilder, None)
            .collect::<Result<Vec<_>, _>>()
            .unwrap(),
    )
    .unwrap()
}

fn example() -> VMTModel {
    parse(
        r#"
        (declare-fun a () (Array Int Int))
        (declare-fun a_next () (Array Int Int))
        (define-fun .a () (Array Int Int) (! a :next a_next))
        (declare-fun send () Bool)
        (define-fun .send () Bool (! send :action 0))
        (declare-fun idle () Bool)
        (define-fun .idle () Bool (! idle :action 0))
        (declare-fun choose () Bool)
        (declare-fun guard ((Array Int Int)) Bool)
        (define-fun action_body () Bool
          (and (= a_next (ite choose (store a 1 10) (store a 2 20)))
               (or (guard a) (not choose))))
        (define-fun init () Bool (! true :init true))
        (define-fun trans () Bool (! (and (=> send action_body)
               (=> idle (= a_next a)) (or send idle)
               (or (not send) (not idle))) :trans true))
        (define-fun prop () Bool (! (= (select a 0) 0) :invar-property 0))
    "#,
    )
}

#[test]
fn keeps_action_body_branches_binder_links_and_array_sites_together() {
    let model = example();
    let index = Arc::new(TransitionIndex::from_model(
        &model,
        &HashSet::from(["guard".into()]),
    ));
    let action = &index.actions()["send"];
    // The requirement resolves the zero-argument helper and retains the full
    // Boolean structure, including the alternative to the quantified guard.
    assert!(action
        .requirements
        .iter()
        .any(|r| r.body.to_string().contains("(or (guard a) (not choose))")));
    let uses = action
        .requirements
        .iter()
        .flat_map(|r| &r.binders)
        .collect::<Vec<_>>();
    assert_eq!(uses.len(), 1);
    assert_eq!(uses[0].application.to_string(), "(guard a)");
    assert_eq!(uses[0].expression_path, vec![1, 0]);
    let writes = index.action_updates("send").collect::<Vec<_>>();
    assert_eq!(writes.len(), 2);
    assert!(writes.iter().any(|u| u
        .guards
        .iter()
        .any(|g| g.expression.to_string() == "choose" && !g.required_value)));
    assert_eq!(index.action_updates("idle").count(), 1);
    let arrays = StaticArrayProvenance::with_transition_index(&model, index);
    assert!(arrays
        .action_sites("send")
        .iter()
        .any(|s| s.role == DataflowRole::WriteIndex && s.expression.to_string() == "2"));
}

#[test]
fn selects_one_action_at_the_exact_frame_and_rejects_a_broken_exclusivity_contract() {
    let index = TransitionIndex::from_model(&example(), &HashSet::new());
    assert_eq!(
        index
            .selected_action(4, |t| Ok(if t.to_string() == "send@4" {
                "true"
            } else {
                "false"
            }
            .into()))
            .unwrap(),
        Some("send")
    );
    assert_eq!(
        index
            .selected_action(5, |t| Ok(if t.to_string() == "idle@5" {
                "true"
            } else {
                "false"
            }
            .into()))
            .unwrap(),
        Some("idle")
    );
    assert_eq!(
        index.selected_action(0, |_| Ok("false".into())).unwrap(),
        None
    );
    assert!(index
        .selected_action(0, |_| Ok("true".into()))
        .unwrap_err()
        .to_string()
        .contains("mutually exclusive"));
}

#[test]
fn indexes_actionless_paths_without_treating_negated_equalities_as_updates() {
    let model = parse(
        r#"
        (declare-fun x () Int) (declare-fun x_next () Int)
        (define-fun .x () Int (! x :next x_next))
        (define-fun init () Bool (! true :init true))
        (define-fun trans () Bool (! (and (= x_next (+ x 1)) (not (= x_next 0))) :trans true))
        (define-fun prop () Bool (! (>= x 0) :invar-property 0))
    "#,
    );
    let index = TransitionIndex::from_model(&model, &HashSet::new());
    assert!(index.actions().is_empty());
    assert_eq!(index.update_paths("x").len(), 1);
    assert_eq!(index.update_paths("x")[0].value.to_string(), "(+ x 1)");
    assert_eq!(
        index
            .selected_action(3, |_| panic!("no action flags to evaluate"))
            .unwrap(),
        None
    );
}

#[test]
fn protocol_action_indexes_link_lowered_quantifiers_without_protocol_specific_names() {
    for protocol in [
        "paxos",
        "distributed_lock",
        "two_phase_commit",
        "ring_leader_election",
    ] {
        let model = VMTModel::from_path(format!(
            "examples/distributed_protocols/{protocol}/{protocol}.encoding.vmt"
        ))
        .unwrap();
        let mut provenance = Default::default();
        let (lowered, plan) =
            crate::theories::quantifiers::lower_model_with_provenance(model, &mut provenance)
                .unwrap();
        let helpers = plan.rules.iter().map(|r| r.name.clone()).collect();
        let (lowered, _) = lowered.abstract_array_theory_with_preprocessing(false);
        let index = TransitionIndex::from_model(&lowered, &helpers);
        assert!(!index.actions().is_empty(), "{protocol}");
        for (name, action) in index.actions() {
            assert!(!action.requirements.is_empty(), "{protocol}: {name}");
            assert!(
                index.action_updates(name).next().is_some(),
                "{protocol}: {name}"
            );
            for binder in action.requirements.iter().flat_map(|r| &r.binders) {
                assert!(plan.rules.iter().any(|r| r.name == binder.helper));
            }
        }
        assert_eq!(
            index
                .actions()
                .values()
                .any(|a| a.requirements.iter().any(|r| !r.binders.is_empty())),
            protocol != "distributed_lock", // This protocol's action guards are quantifier-free.
            "{protocol}"
        );
        if protocol == "paxos" {
            let decide = &index.actions()["decide"];
            let occurrences = decide
                .requirements
                .iter()
                .flat_map(|r| &r.binders)
                .collect::<Vec<_>>();
            assert_eq!(occurrences.len(), 1);
            let rule = plan
                .rules
                .iter()
                .find(|r| r.name == occurrences[0].helper)
                .unwrap();
            assert!(rule.body.to_string().contains("member"));
            assert!(rule.body.to_string().contains("vote"));
            assert!(index
                .action_updates("decide")
                .any(|u| u.target == "decision" && u.value.to_string().contains("Write_")));
        }
    }
}
