use super::*;
use crate::policy::instantiation::{
    snapshot::CatalogueTerm, tests::fixture, InstantiationProposal,
};
use std::collections::HashSet;

fn snapshot() -> InstantiationSnapshot {
    let smt = fixture();
    InstantiationSnapshot::capture(
        &DiscoveryContext {
            smt: &smt,
            depth: 0,
            refinement_step: 0,
            model_version: 1,
            pending: &HashSet::new(),
        },
        "fixture source",
    )
    .unwrap()
}

fn reconstruct(snapshot: &InstantiationSnapshot) -> Value {
    let mut state = snapshot.current_state();
    state["terms"] = json!([]);
    state["declarations"] = json!([]);
    for block in snapshot.prefix() {
        for (key, value) in block.as_object().unwrap() {
            if matches!(key.as_str(), "terms" | "declarations") {
                state[key]
                    .as_array_mut()
                    .unwrap()
                    .extend(value.as_array().unwrap().iter().cloned());
            } else {
                assert!(state.get(key).is_none());
                state[key] = value.clone();
            }
        }
    }
    state
}

#[test]
fn growth_preserves_ids_and_bytes_and_reconstructs_full_current_context() {
    let mut session = InstantiationSession::default();
    let mut first = snapshot();
    session.prepare(&mut first);
    assert_eq!(reconstruct(&first), first.state());
    let mut second = snapshot();
    second.terms.push(CatalogueTerm {
        id: "discarded".into(),
        expression: "(- 999)".into(),
        sort: "Int".into(),
        term: "(- 999)".parse().unwrap(),
    });
    second
        .declarations
        .push("(declare-fun extra () Int)".into());
    session.prepare(&mut second);
    assert_eq!(&second.prefix()[..first.prefix().len()], first.prefix());
    for old in &first.terms {
        assert!(second
            .terms
            .iter()
            .any(|new| new.expression == old.expression && new.id == old.id));
    }
    assert_eq!(reconstruct(&second), second.state());
    let prefix = second.prefix().to_vec();
    session.prepare(&mut second);
    assert_eq!(second.prefix(), prefix);
    assert_eq!(reconstruct(&second), second.state());
}

#[test]
fn shrinking_rebuilds_prefix_without_reusing_removed_ids() {
    let mut session = InstantiationSession::default();
    let mut full = snapshot();
    session.prepare(&mut full);
    let removed_id = full.terms[0].id.clone();
    let mut smaller = snapshot();
    smaller.terms.remove(0);
    smaller.declarations.remove(0);
    session.prepare(&mut smaller);
    assert!(!smaller.terms.iter().any(|t| t.id == removed_id));
    let rule = smaller
        .schemas
        .iter()
        .find(|s| s.name().starts_with("read-after-write"))
        .unwrap();
    let mut bindings: BTreeMap<_, _> = rule
        .slots
        .iter()
        .map(|(slot, sort)| {
            (
                slot.clone(),
                smaller
                    .terms
                    .iter()
                    .find(|t| &t.sort == sort)
                    .unwrap()
                    .id
                    .clone(),
            )
        })
        .collect();
    bindings.insert("idx".into(), removed_id.clone());
    assert!(smaller
        .resolve(&InstantiationProposal {
            axiom_id: rule.id.clone(),
            bindings
        })
        .unwrap_err()
        .to_string()
        .contains("unknown term"));
    assert_eq!(reconstruct(&smaller), smaller.state());
    assert_ne!(smaller.prefix(), full.prefix());
    let smaller_prefix = smaller.prefix().to_vec();
    let mut restored = snapshot();
    session.prepare(&mut restored);
    assert_eq!(&restored.prefix()[..smaller_prefix.len()], smaller_prefix);
    assert_eq!(
        restored
            .terms
            .iter()
            .find(|t| t.expression == full.terms[0].expression)
            .unwrap()
            .id,
        removed_id
    );
    assert_eq!(reconstruct(&restored), restored.state());
}

#[test]
fn changed_source_rebuilds_static_context_without_renumbering_terms() {
    let mut session = InstantiationSession::default();
    let mut first = snapshot();
    session.prepare(&mut first);
    let smt = fixture();
    let next = session
        .capture(
            &DiscoveryContext {
                smt: &smt,
                depth: 0,
                refinement_step: 1,
                model_version: 2,
                pending: &HashSet::new(),
            },
            "changed source",
        )
        .unwrap();
    assert_ne!(first.prefix()[0], next.prefix()[0]);
    assert_eq!(next.state()["terms"], first.state()["terms"]);
    assert_eq!(next.state()["problem"]["source"], "changed source");
    assert_eq!(reconstruct(&next), next.state());
}
