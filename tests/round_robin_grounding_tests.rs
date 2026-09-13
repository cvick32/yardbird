use std::collections::HashSet;

use smt2parser::{concrete::Term, vmt::ReadsAndWrites};
use yardbird::{
    cost_functions::array::ArrayBMCCost,
    problem_context::{ArrayCandidateCatalog, ArrayCandidatePool},
    theories::array::{
        array_axioms::{
            generate_array_instantiation_candidates_with_budget, translate_term,
            ArrayInstantiationInstrumentation, ArrayInstantiationOptions, ArrayLanguage,
        },
        array_rule_instantiator::ArrayArtifactCapture,
        candidate_scope::CandidateScope,
        instantiation_candidate::InstantiationCandidate,
    },
};

fn array_binding(candidate: &InstantiationCandidate) -> String {
    candidate
        .provenance
        .relative_substitution()
        .into_iter()
        .find(|binding| binding.variable == "?a")
        .unwrap()
        .term
}

// Two distinct e-matches, each with three intact source sites. All source
// values are false, but each read of the written index is model-true.
fn explore(
    budget: usize,
    mut accept: impl FnMut(&InstantiationCandidate) -> anyhow::Result<bool>,
) -> anyhow::Result<Vec<String>> {
    let mut egraph = egg::EGraph::<ArrayLanguage, ()>::default();
    let mut terms = vec![
        "false".to_string(),
        "true".to_string(),
        "|idx:0|".to_string(),
    ];
    let false_id = egraph.add_expr(&translate_term("false".parse().unwrap()).unwrap());
    let true_id = egraph.add_expr(&translate_term("true".parse().unwrap()).unwrap());
    let mut reads_and_writes = ReadsAndWrites::default();
    for family in ["a", "b"] {
        let mut base = None;
        for ordinal in 0..3 {
            let array = format!("{family}{ordinal}@0");
            let id = egraph.add_expr(&translate_term(array.parse().unwrap()).unwrap());
            if let Some(base) = base {
                egraph.union(base, id);
            } else {
                base = Some(id);
            }
            let write = format!("(Write_Int_Bool {array} |idx:0| false)");
            let read = format!("(Read_Int_Bool {write} |idx:0|)");
            let write_term: Term = write.parse().unwrap();
            write_term
                .accept_term_visitor(&mut reads_and_writes)
                .unwrap();
            let read_id = egraph.add_expr(&translate_term(read.parse().unwrap()).unwrap());
            egraph.union(read_id, true_id);
            terms.extend([array, write, read]);
        }
    }
    egraph.rebuild();
    assert_ne!(egraph.find(false_id), egraph.find(true_id));
    let cost = ArrayBMCCost::new(
        1,
        terms.iter().map(|term| term.as_str().into()).collect(),
        Default::default(),
        reads_and_writes.clone(),
    );
    let batch = generate_array_instantiation_candidates_with_budget(
        &egraph,
        cost,
        &[("Int".into(), "Bool".into())],
        ArrayInstantiationOptions {
            additional_terms: vec![],
            candidate_catalog: ArrayCandidateCatalog {
                source_grounded: ArrayCandidatePool {
                    terms,
                    reads_and_writes,
                },
                derived: ArrayCandidatePool::default(),
            },
            candidate_scope: CandidateScope::SourceGroundedOnly,
            refinement_step: 0,
            selection_counts: Default::default(),
            depth: 1,
            instrumentation: ArrayInstantiationInstrumentation {
                artifact_capture: ArrayArtifactCapture::default(),
                profiling: None,
            },
        },
        budget,
        |candidate| {
            assert!(candidate.rule.name().starts_with("read-after-write"));
            let bindings = candidate.provenance.relative_substitution();
            assert_eq!(
                bindings.iter().find(|b| b.variable == "?val").unwrap().term,
                "false"
            );
            // The repeated write/read index is a single coherent binding.
            assert_eq!(bindings.iter().filter(|b| b.variable == "?idx").count(), 1);
            accept(candidate)
        },
    )?;
    Ok(batch.candidates.iter().map(array_binding).collect())
}

#[test]
fn advances_each_match_before_requesting_its_next_source_site() {
    let generated = explore(4, |_| Ok(true)).unwrap();
    assert_eq!(generated.len(), 4);
    let families = generated
        .iter()
        .map(|term| term.chars().next().unwrap())
        .collect::<Vec<_>>();
    assert_ne!(families[0], families[1]);
    assert_eq!(&families[..2], &families[2..]);
    assert_eq!(generated.iter().collect::<HashSet<_>>().len(), 4);
}

#[test]
fn a_filled_first_pass_does_not_explore_alternatives() {
    let generated = explore(1, |_| Ok(true)).unwrap();
    // Both initial matches remain available to the downstream whole-candidate
    // ranker, exactly as before. The additional source sites stay unexplored.
    assert_eq!(generated.len(), 2);
    assert!(generated
        .iter()
        .all(|term| term.starts_with("a0+") || term.starts_with("b0+")));
}

#[test]
fn rejected_candidates_do_not_spend_the_winner_budget() {
    let mut accepted = 0;
    let generated = explore(3, |candidate| {
        let usable = !array_binding(candidate).starts_with("a0")
            && !array_binding(candidate).starts_with("b0");
        accepted += usize::from(usable);
        Ok(usable)
    })
    .unwrap();
    assert_eq!(accepted, 3);
    assert_eq!(generated.len(), 5);
}

#[test]
fn exhausted_matches_stop_without_duplicate_groundings() {
    let generated = explore(16, |_| Ok(false)).unwrap();
    assert_eq!(generated.len(), 6);
    assert_eq!(generated.iter().collect::<HashSet<_>>().len(), 6);
}

#[test]
fn candidate_validation_errors_are_propagated() {
    let error = explore(4, |_| anyhow::bail!("model evaluation failed")).unwrap_err();
    assert_eq!(error.to_string(), "model evaluation failed");
}
