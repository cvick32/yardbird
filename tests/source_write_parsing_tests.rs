use smt2parser::{concrete::Term, vmt::ReadsAndWrites};
use yardbird::{
    cost_functions::array::ArrayBMCCost,
    problem_context::{ArrayCandidateCatalog, ArrayCandidatePool},
    theories::array::{
        array_axioms::{
            expr_to_term, generate_array_instantiation_candidates, translate_term,
            ArrayInstantiationInstrumentation, ArrayInstantiationOptions, ArrayLanguage,
        },
        array_rule_instantiator::ArrayArtifactCapture,
        candidate_scope::CandidateScope,
    },
};

fn assert_source_write_is_preserved(array: &str, index: &str, value: &str) {
    let write = format!("(Write_Int_Bool {array} {index} {value})");
    let read = format!("(Read_Int_Bool next@1 {index})");
    let terms = [
        array, index, value, "alias@1", "next@1", "guard@0", "false", "true", &write, &read,
    ]
    .map(str::to_owned);
    let mut egraph = egg::EGraph::<ArrayLanguage, ()>::default();
    let ids = terms
        .iter()
        .map(|raw| egraph.add_expr(&translate_term(raw.parse().unwrap()).unwrap()))
        .collect::<Vec<_>>();
    // Reproduce a spurious model: the next-state read is true despite writing
    // false. Cheaper source terms coincide with the write's array and value.
    egraph.union(ids[0], ids[3]);
    egraph.union(ids[4], ids[8]);
    egraph.union(ids[2], ids[6]);
    egraph.union(ids[5], ids[6]);
    egraph.union(ids[7], ids[9]);
    egraph.rebuild();

    let mut reads_and_writes = ReadsAndWrites::default();
    let write_term: Term = write.parse().unwrap();
    write_term
        .accept_term_visitor(&mut reads_and_writes)
        .unwrap();
    let cost = ArrayBMCCost::new(
        1,
        terms.iter().map(|s| s.as_str().into()).collect(),
        ["alias@1".into()].into_iter().collect(),
        reads_and_writes.clone(),
    );
    let batch = generate_array_instantiation_candidates(
        &egraph,
        cost,
        &[("Int".into(), "Bool".into())],
        ArrayInstantiationOptions {
            additional_terms: vec![],
            candidate_catalog: ArrayCandidateCatalog {
                source_grounded: ArrayCandidatePool {
                    terms: terms.into(),
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
    );
    let actual = batch
        .candidates
        .iter()
        .filter(|candidate| candidate.rule.name().starts_with("read-after-write"))
        .map(|candidate| expr_to_term(candidate.expression.clone()))
        .collect::<Vec<_>>();
    let expected: Term = format!("(= (Read_Int_Bool {write} {index}) {value})")
        .parse()
        .unwrap();
    assert_eq!(actual, vec![expected]);
}

#[test]
fn source_grounding_preserves_write_with_quoted_index() {
    assert_source_write_is_preserved("source@0", "|idx:client@0|", "false");
}

#[test]
fn source_grounding_preserves_quoted_array_and_value() {
    assert_source_write_is_preserved("|source:array@0|", "i@0", "|stored:value@0|");
}

#[test]
fn source_grounding_preserves_symbols_containing_spaces() {
    assert_source_write_is_preserved("|source array@0|", "|write index@0|", "|stored value@0|");
}
