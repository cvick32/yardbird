//! Built-in array axioms, using the shared instantiation engine.
use crate::instantiation::engine::{
    generate_quantified_candidates, CompiledQuantifiedRule, InstantiationOptions,
};
use crate::instantiation::{
    instantiator::CandidateDemand,
    language::*,
    rule::{ArrayAxiomKind, QuantifiedRule},
    scope::CandidateScope,
};
use crate::{cost_functions::YardbirdCostFunction, instantiation::candidate::InstantiationBatch};
use egg::*;

pub fn generate_array_instantiation_candidates<CF, N>(
    egraph: &EGraph<TermLanguage, N>,
    cost_fn: CF,
    array_types: &[(String, String)],
    options: InstantiationOptions,
) -> InstantiationBatch
where
    N: Analysis<TermLanguage> + 'static,
    CF: YardbirdCostFunction<TermLanguage> + 'static,
{
    generate_array_candidates(egraph, cost_fn, array_types, options, None)
        .expect("unfiltered array generation cannot fail")
}

/// Refill an underfilled source batch by exploring source-write alternatives.
/// `accept` must admit only novel, installable, model-violated candidates that
/// satisfy the ranker's eligibility and rule limits. Full search stays unchanged.
pub fn generate_array_instantiation_candidates_with_budget<CF, N>(
    egraph: &EGraph<TermLanguage, N>,
    cost_fn: CF,
    array_types: &[(String, String)],
    options: InstantiationOptions,
    budget: usize,
    mut accept: impl FnMut(
        &crate::instantiation::candidate::InstantiationCandidate,
    ) -> anyhow::Result<bool>,
) -> anyhow::Result<InstantiationBatch>
where
    N: Analysis<TermLanguage> + 'static,
    CF: YardbirdCostFunction<TermLanguage> + 'static,
{
    assert!(budget > 0, "candidate groups need a winner");
    if options.candidate_scope != CandidateScope::SourceGroundedOnly {
        return Ok(generate_array_instantiation_candidates(
            egraph,
            cost_fn,
            array_types,
            options,
        ));
    }
    let mut accept = |candidate: &mut crate::instantiation::candidate::InstantiationCandidate| {
        let accepted = accept(candidate)?;
        candidate.model_violation_verified = accepted;
        Ok(accepted)
    };
    generate_array_candidates(
        egraph,
        cost_fn,
        array_types,
        options,
        Some(CandidateDemand {
            budget,
            accept: &mut accept,
        }),
    )
}

fn generate_array_candidates<CF, N>(
    egraph: &EGraph<TermLanguage, N>,
    cost_fn: CF,
    array_types: &[(String, String)],
    options: InstantiationOptions,
    demand: Option<CandidateDemand<'_>>,
) -> anyhow::Result<InstantiationBatch>
where
    N: Analysis<TermLanguage> + 'static,
    CF: YardbirdCostFunction<TermLanguage> + 'static,
{
    generate_quantified_candidates(
        egraph,
        cost_fn,
        &array_rules_with_types(array_types),
        options,
        demand,
    )
}

/// Generate array rules for a specific type pair (index_sort, value_sort).
/// This creates type-specific versions of the three core array axioms.
fn array_rules_for_type<N>(index_sort: &str, value_sort: &str) -> Vec<CompiledQuantifiedRule<N>>
where
    N: Analysis<TermLanguage> + 'static,
{
    // Axiom 1: write-does-not-overwrite
    // (Read (Write a idx val) c) => (Read a c) when idx != c
    let rule_1 = QuantifiedRule::array_axiom(
        ArrayAxiomKind::WriteDoesNotOverwrite,
        index_sort,
        value_sort,
    );
    let pattern_1 = format!(
        "(Read {} {} (Write {} {} ?a ?idx ?val) ?c)",
        index_sort, value_sort, index_sort, value_sort
    );
    let replacement_1 = format!("(Read {} {} ?a ?c)", index_sort, value_sort);
    let parsed_pattern: egg::Pattern<TermLanguage> = pattern_1.parse().unwrap();
    let formula_1 = format!("(=> (not (= ?c ?idx)) (= {pattern_1} {replacement_1}))");
    let axiom_1 = CompiledQuantifiedRule::new(
        rule_1,
        ConditionalSearcher::new(parsed_pattern, not_equal("?idx", "?c")),
        replacement_1.parse().unwrap(),
        formula_1.parse().unwrap(),
    )
    .unwrap();

    // Axiom 2: read-after-write
    // (Read (Write a idx val) idx) => val
    let rule_2 =
        QuantifiedRule::array_axiom(ArrayAxiomKind::ReadAfterWrite, index_sort, value_sort);
    let pattern_2 = format!(
        "(Read {} {} (Write {} {} ?a ?idx ?val) ?idx)",
        index_sort, value_sort, index_sort, value_sort
    );
    let pat2 = pattern_2.parse::<egg::Pattern<TermLanguage>>().unwrap();
    let replacement_2 = "?val";
    let formula_2 = format!("(= {pattern_2} {replacement_2})");
    let axiom_2 = CompiledQuantifiedRule::new(
        rule_2,
        pat2,
        replacement_2.parse().unwrap(),
        formula_2.parse().unwrap(),
    )
    .unwrap();

    let rule_3 = QuantifiedRule::array_axiom(ArrayAxiomKind::ConstantArray, index_sort, value_sort);
    let pattern_3 = format!(
        "(Read {} {} (ConstArr {} {} ?a) ?b)",
        index_sort, value_sort, index_sort, value_sort
    );
    let pat3 = pattern_3.parse::<egg::Pattern<TermLanguage>>().unwrap();
    let replacement_3 = "?a";
    let formula_3 = format!("(= {pattern_3} {replacement_3})");
    let axiom_3 = CompiledQuantifiedRule::new(
        rule_3,
        pat3,
        replacement_3.parse().unwrap(),
        formula_3.parse().unwrap(),
    )
    .unwrap();

    vec![axiom_1, axiom_2, axiom_3]
}

/// Generate executable quantified rules for all discovered array types.
fn array_rules_with_types<N>(array_types: &[(String, String)]) -> Vec<CompiledQuantifiedRule<N>>
where
    N: Analysis<TermLanguage> + 'static,
{
    let mut rules = Vec::new();
    for (index_sort, value_sort) in array_types {
        rules.extend(array_rules_for_type(index_sort, value_sort));
    }
    rules
}

fn not_equal<N>(
    index_0: &'static str,
    index_1: &'static str,
) -> impl Fn(&EGraph<TermLanguage, N>, Id, &Subst) -> bool
where
    N: Analysis<TermLanguage>,
{
    let var_0 = index_0.parse().unwrap();
    let var_1 = index_1.parse().unwrap();
    move |egraph, _, subst| egraph.find(subst[var_0]) != egraph.find(subst[var_1])
}

/// An `egg::Searcher` that only returns search results that pass a provided condition
struct ConditionalSearcher<S, C> {
    searcher: S,
    condition: C,
}

impl<S, C> ConditionalSearcher<S, C> {
    fn new(searcher: S, condition: C) -> Self {
        Self {
            searcher,
            condition,
        }
    }
}

impl<L, N, S, C> egg::Searcher<L, N> for ConditionalSearcher<S, C>
where
    L: egg::Language,
    N: egg::Analysis<L>,
    S: egg::Searcher<L, N>,
    C: Fn(&egg::EGraph<L, N>, egg::Id, &egg::Subst) -> bool,
{
    fn search_with_limit(&self, egraph: &EGraph<L, N>, limit: usize) -> Vec<SearchMatches<'_, L>> {
        self.searcher
            .search_with_limit(egraph, limit)
            .into_iter()
            .filter_map(|matches| {
                // only return substs that pass the provided condition
                let substs: Vec<_> = matches
                    .substs
                    .into_iter()
                    .filter(|subst| (self.condition)(egraph, matches.eclass, subst))
                    .collect();
                if substs.is_empty() {
                    None
                } else {
                    Some(SearchMatches {
                        eclass: matches.eclass,
                        substs,
                        ast: matches.ast,
                    })
                }
            })
            .collect()
    }

    fn search_eclass_with_limit(
        &self,
        egraph: &EGraph<L, N>,
        eclass: Id,
        limit: usize,
    ) -> Option<SearchMatches<'_, L>> {
        self.searcher
            .search_eclass_with_limit(egraph, eclass, limit)
            .map(|matches| SearchMatches {
                eclass: matches.eclass,
                substs: matches
                    .substs
                    .into_iter()
                    .filter(|subst| (self.condition)(egraph, matches.eclass, subst))
                    .collect(),
                ast: matches.ast,
            })
    }

    fn vars(&self) -> Vec<Var> {
        self.searcher.vars()
    }

    fn get_pattern_ast(&self) -> Option<&PatternAst<L>> {
        self.searcher.get_pattern_ast()
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashSet;

    use super::*;
    use crate::{
        instantiation::{engine::InstantiationInstrumentation, instantiator::ArtifactCapture},
        problem_context::ArrayCandidateCatalog,
    };
    use smt2parser::concrete::{Constant, QualIdentifier, Symbol as SmtSymbol, Term};

    #[test]
    fn declared_array_sorts_disambiguate_underscores() {
        let term: Term = "(Read_tag_t_Bool (ConstArr_tag_t_Bool false) i)"
            .parse()
            .unwrap();
        let expression =
            translate_term_with_array_types(term.clone(), &[("tag_t".into(), "Bool".into())])
                .unwrap();
        assert_eq!(
            expression.to_string(),
            "(Read tag_t Bool (ConstArr tag_t Bool false) i)"
        );
        assert_eq!(expr_to_term(expression), term);
    }

    #[test]
    fn opaque_reserved_function_applications_round_trip() {
        let term: Term = "(=> enabled (|match| request response))".parse().unwrap();
        assert_eq!(expr_to_term(translate_term(term.clone()).unwrap()), term);
    }
    use crate::{
        cost_functions::YardbirdCostFunction,
        instantiation::ranker::PreferSourceInstantiationRanker,
    };
    use rustc_hash::FxHashMap;
    use smt2parser::vmt::ReadsAndWrites;

    #[derive(Clone)]
    struct ZeroCost;

    #[derive(Clone)]
    struct PreferB;

    #[derive(Clone)]
    struct HighCostA;

    const LEGACY_HIGH_COST_THRESHOLD: u32 = 100;

    fn prepare_violations(batch: &mut InstantiationBatch, scope: CandidateScope) {
        batch
            .prepare(
                scope,
                &HashSet::new(),
                1,
                |term| Ok(term.to_string().starts_with("(not ").to_string()),
                |candidate| Some(candidate.expression.clone()),
            )
            .unwrap();
    }

    impl egg::CostFunction<TermLanguage> for ZeroCost {
        type Cost = u32;

        fn cost<C>(&mut self, _enode: &TermLanguage, _costs: C) -> Self::Cost
        where
            C: FnMut(egg::Id) -> Self::Cost,
        {
            0
        }
    }

    impl YardbirdCostFunction<TermLanguage> for ZeroCost {
        fn get_string_terms(&self) -> Vec<String> {
            vec![]
        }

        fn get_reads_and_writes(&self) -> ReadsAndWrites {
            ReadsAndWrites::default()
        }
    }

    impl egg::CostFunction<TermLanguage> for PreferB {
        type Cost = u32;

        fn cost<C>(&mut self, enode: &TermLanguage, mut costs: C) -> Self::Cost
        where
            C: FnMut(egg::Id) -> Self::Cost,
        {
            let own = match enode {
                TermLanguage::Symbol(symbol) if symbol.as_str() == "A" => 10,
                _ => 0,
            };
            enode.fold(own, |sum, child| sum.saturating_add(costs(child)))
        }
    }

    impl YardbirdCostFunction<TermLanguage> for PreferB {
        fn get_string_terms(&self) -> Vec<String> {
            vec![]
        }

        fn get_reads_and_writes(&self) -> ReadsAndWrites {
            ReadsAndWrites::default()
        }
    }

    impl egg::CostFunction<TermLanguage> for HighCostA {
        type Cost = u32;

        fn cost<C>(&mut self, enode: &TermLanguage, mut costs: C) -> Self::Cost
        where
            C: FnMut(egg::Id) -> Self::Cost,
        {
            let own = match enode {
                TermLanguage::Symbol(symbol) if symbol.as_str() == "A" => {
                    LEGACY_HIGH_COST_THRESHOLD + 1
                }
                _ => 0,
            };
            enode.fold(own, |sum, child| sum.saturating_add(costs(child)))
        }
    }

    impl YardbirdCostFunction<TermLanguage> for HighCostA {
        fn get_string_terms(&self) -> Vec<String> {
            vec![]
        }

        fn get_reads_and_writes(&self) -> ReadsAndWrites {
            ReadsAndWrites::default()
        }
    }

    fn init() {
        let _ = env_logger::builder()
            .is_test(true)
            .filter_level(log::LevelFilter::Debug)
            .filter_module("egg", log::LevelFilter::Off)
            .filter_module("z3", log::LevelFilter::Off)
            .try_init();
    }

    fn two_write_candidate_catalog() -> ArrayCandidateCatalog {
        let terms = [
            "A",
            "i",
            "v",
            "j",
            "B",
            "p",
            "w",
            "q",
            "(Write_Int_Int A i v)",
            "(Read_Int_Int (Write_Int_Int A i v) j)",
            "(Write_Int_Int B p w)",
            "(Read_Int_Int (Write_Int_Int B p w) q)",
        ]
        .into_iter()
        .map(str::to_string)
        .collect();

        ArrayCandidateCatalog {
            source_grounded: crate::problem_context::ArrayCandidatePool {
                terms,
                reads_and_writes: ReadsAndWrites::from(
                    std::collections::HashSet::new(),
                    std::collections::HashSet::from([
                        ("A".to_string(), "i".to_string(), "v".to_string()),
                        ("B".to_string(), "p".to_string(), "w".to_string()),
                    ]),
                ),
            },
            derived: crate::problem_context::ArrayCandidatePool::default(),
        }
    }

    #[test]
    fn write_does_not_overwrite_searcher_matches_distinct_indices() {
        init();
        let expr: RecExpr<TermLanguage> = "(Read Int Int (Write Int Int A 0 0) 1)".parse().unwrap();
        let mut egraph = EGraph::<TermLanguage, ()>::default();
        egraph.add_expr(&expr);
        egraph.rebuild();
        let rules = array_rules_with_types::<()>(&[("Int".into(), "Int".into())]);
        let rule = rules
            .iter()
            .find(|rule| {
                rule.metadata().kind()
                    == crate::instantiation::rule::QuantifiedRuleKind::ArrayAxiom(
                        ArrayAxiomKind::WriteDoesNotOverwrite,
                    )
            })
            .unwrap();

        assert_eq!(rule.search_with_limit(&egraph, usize::MAX).len(), 1);
    }

    #[test]
    fn write_does_not_overwrite_searcher_rejects_equal_indices() {
        init();
        let expr: RecExpr<TermLanguage> = "(Read Int Int (Write Int Int A 0 0) 0)".parse().unwrap();
        let mut egraph = EGraph::<TermLanguage, ()>::default();
        egraph.add_expr(&expr);
        egraph.rebuild();
        let rules = array_rules_with_types::<()>(&[("Int".into(), "Int".into())]);
        let rule = rules
            .iter()
            .find(|rule| {
                rule.metadata().kind()
                    == crate::instantiation::rule::QuantifiedRuleKind::ArrayAxiom(
                        ArrayAxiomKind::WriteDoesNotOverwrite,
                    )
            })
            .unwrap();

        assert!(rule.search_with_limit(&egraph, usize::MAX).is_empty());
    }

    #[test]
    fn translate_term_uses_same_numeric_encoding_as_parser() {
        let translated = translate_term(Term::Constant(Constant::Numeral(10u64.into()))).unwrap();
        let parsed: RecExpr<TermLanguage> = "10".parse().unwrap();

        let mut egraph = EGraph::<TermLanguage, ()>::default();
        let translated_id = egraph.add_expr(&translated);
        let parsed_id = egraph.add_expr(&parsed);
        egraph.rebuild();

        assert_eq!(egraph.find(translated_id), egraph.find(parsed_id));
    }

    #[test]
    fn translate_term_supports_ite() {
        let term = "(ite true x y)".parse().unwrap();
        let translated = translate_term(term).unwrap();
        let parsed: RecExpr<TermLanguage> = "(ite true x y)".parse().unwrap();

        let mut egraph = EGraph::<TermLanguage, ()>::default();
        let translated_id = egraph.add_expr(&translated);
        let parsed_id = egraph.add_expr(&parsed);
        egraph.rebuild();

        assert_eq!(egraph.find(translated_id), egraph.find(parsed_id));
        assert_eq!(expr_to_term(translated).to_string(), "(ite true x y)");
    }

    #[test]
    fn expr_to_term_preserves_atomic_and_opaque_symbol_terms() {
        for rendered in [
            "simple@7",
            "true",
            "|fml:cl+0|",
            "Array_Int_Int!val!8",
            "#b1",
            "123",
            "(opaque x)",
        ] {
            let expr = TermExpr::from(vec![TermLanguage::Symbol(rendered.into())]);
            let expected: Term = rendered
                .parse()
                .unwrap_or_else(|_| SmtSymbol(rendered.to_string()).to_string().parse().unwrap());

            assert_eq!(expr_to_term(expr), expected, "symbol {rendered}");
        }
    }

    #[test]
    fn translate_term_lowers_bvcomp_without_adding_array_theory_semantics() {
        let term = "(bvcomp #b0011 #b0101)".parse().unwrap();
        let translated = translate_term(term).unwrap();

        assert_eq!(
            expr_to_term(translated).to_string(),
            "(ite (= #b0011 #b0101) #b1 #b0)"
        );
    }

    #[test]
    fn translate_term_strips_solver_metadata_attributes() {
        let term = "(! (<= x 1) :predicate true)".parse().unwrap();
        let translated = translate_term(term).unwrap();

        assert_eq!(expr_to_term(translated).to_string(), "(<= x 1)");
    }

    #[test]
    fn translate_term_preserves_to_real_coercions() {
        let term = "(to_real (- 1))".parse().unwrap();
        let translated = translate_term(term).unwrap();

        assert_eq!(expr_to_term(translated).to_string(), "(to_real (- 1))");
    }

    #[test]
    fn egraph_round_trip_does_not_embed_smt_symbol_quotes() {
        let term = Term::QualIdentifier(QualIdentifier::simple(".x{78}@1"));

        let translated = translate_term(term).unwrap();
        let round_tripped = expr_to_term(translated);

        assert_eq!(
            round_tripped,
            Term::QualIdentifier(QualIdentifier::simple(".x{78}@1"))
        );
    }

    #[test]
    fn unsupported_scalar_applications_round_trip_as_opaque_terms() {
        let term: Term = "(bvadd #b0001 #b0010)".parse().unwrap();

        let translated = translate_term(term.clone()).unwrap();

        assert_eq!(expr_to_term(translated), term);
    }

    #[test]
    fn typed_write_does_not_overwrite_instantiation_keeps_disequality_guard() {
        init();
        let expr: RecExpr<TermLanguage> = "(Read Int Int (Write Int Int A 0 0) 1)".parse().unwrap();
        let mut egraph = EGraph::<TermLanguage, ()>::default();
        egraph.add_expr(&expr);
        egraph.rebuild();

        let mut result = generate_array_instantiation_candidates(
            &egraph,
            ZeroCost,
            &[("Int".into(), "Int".into())],
            InstantiationOptions {
                search_allowance: crate::policy::effort::WorkAllowance::default(),
                additional_terms: vec![],
                candidate_catalog: ArrayCandidateCatalog::default(),
                candidate_scope: CandidateScope::AllCandidates,
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                instrumentation: InstantiationInstrumentation {
                    artifact_capture: ArtifactCapture::default(),
                    profiling: None,
                },
            },
        );

        assert_eq!(result.selected().count(), 0);
        prepare_violations(&mut result, CandidateScope::AllCandidates);
        assert_eq!(result.selected().count(), 1);
        let instantiation = result.selected().next().unwrap();
        assert!(instantiation.expression.to_string().starts_with("(=> "));

        let term = expr_to_term(instantiation.expression.clone()).to_string();
        assert_eq!(
            term,
            "(=> (not (= 1 0)) (= (Read_Int_Int (Write_Int_Int A 0 0) 1) (Read_Int_Int A 1)))"
        );
    }

    #[test]
    fn full_selection_keeps_a_candidate_from_each_violated_rule() {
        let write_does_not_overwrite: TermExpr =
            "(Read Int Int (Write Int Int A i v) j)".parse().unwrap();
        let read_after_write: TermExpr = "(Read Int Int (Write Int Int B k w) k)".parse().unwrap();
        let constant_array: TermExpr = "(Read Int Int (ConstArr Int Int z) p)".parse().unwrap();
        let mut egraph = EGraph::<TermLanguage, ()>::default();
        egraph.add_expr(&write_does_not_overwrite);
        egraph.add_expr(&read_after_write);
        egraph.add_expr(&constant_array);
        egraph.rebuild();

        let mut result = generate_array_instantiation_candidates(
            &egraph,
            ZeroCost,
            &[("Int".into(), "Int".into())],
            InstantiationOptions {
                search_allowance: crate::policy::effort::WorkAllowance::default(),
                additional_terms: vec![],
                candidate_catalog: ArrayCandidateCatalog::default(),
                candidate_scope: CandidateScope::AllCandidates,
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                instrumentation: InstantiationInstrumentation {
                    artifact_capture: ArtifactCapture::default(),
                    profiling: None,
                },
            },
        );

        assert_eq!(result.selected().count(), 0);
        prepare_violations(&mut result, CandidateScope::AllCandidates);
        let rule_names = result
            .selected()
            .map(|candidate| candidate.rule.name().to_string())
            .collect::<HashSet<_>>();
        assert_eq!(
            rule_names,
            HashSet::from([
                "write-does-not-overwrite-Int-Int".to_string(),
                "read-after-write-Int-Int".to_string(),
                "constant-array-Int-Int".to_string(),
            ])
        );
    }

    #[test]
    fn generation_borrows_the_egraph_for_staged_expansion() {
        let expr: RecExpr<TermLanguage> = "(Read Int Int (Write Int Int A i v) j)".parse().unwrap();
        let mut egraph = EGraph::<TermLanguage, ()>::default();
        egraph.add_expr(&expr);
        egraph.rebuild();

        let _ = generate_array_instantiation_candidates(
            &egraph,
            ZeroCost,
            &[("Int".into(), "Int".into())],
            InstantiationOptions {
                search_allowance: crate::policy::effort::WorkAllowance::default(),
                additional_terms: vec![],
                candidate_catalog: ArrayCandidateCatalog::default(),
                candidate_scope: CandidateScope::AllCandidates,
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                instrumentation: InstantiationInstrumentation {
                    artifact_capture: ArtifactCapture::default(),
                    profiling: None,
                },
            },
        );

        assert!(
            egraph.lookup_expr(&expr).is_some(),
            "generation must leave the e-graph available for a later builder stage"
        );
    }

    #[test]
    fn source_ranker_defers_a_model_derived_join_until_full_search() {
        init();
        let expr: RecExpr<TermLanguage> =
            "(Read Int Int (Write Int Int A i 137) j)".parse().unwrap();

        let run = |scope| {
            let mut egraph = EGraph::<TermLanguage, ()>::default();
            egraph.add_expr(&expr);
            egraph.rebuild();
            generate_array_instantiation_candidates(
                &egraph,
                ZeroCost,
                &[("Int".into(), "Int".into())],
                InstantiationOptions {
                    search_allowance: crate::policy::effort::WorkAllowance::default(),
                    additional_terms: vec![],
                    candidate_catalog: ArrayCandidateCatalog::default(),
                    candidate_scope: scope,
                    refinement_step: 0,
                    selection_counts: FxHashMap::default(),
                    depth: 0,
                    instrumentation: InstantiationInstrumentation {
                        artifact_capture: ArtifactCapture::default(),
                        profiling: None,
                    },
                },
            )
        };

        let mut cone = run(CandidateScope::SourceGroundedOnly);
        let full = run(CandidateScope::AllCandidates);

        assert_eq!(cone.candidates.len(), 1);
        assert_eq!(
            cone.candidates[0].grounding,
            crate::instantiation::candidate::InstantiationGrounding::Derived
        );
        let summary = cone
            .prepare_with_ranker(
                CandidateScope::SourceGroundedOnly,
                &HashSet::new(),
                1,
                &PreferSourceInstantiationRanker,
                |term| Ok(term.to_string().starts_with("(not ").to_string()),
                |candidate| Some(candidate.expression.clone()),
            )
            .unwrap();
        assert_eq!(summary.rejected_ranker, 1);
        assert_eq!(cone.selected().count(), 0);
        assert_eq!(full.candidates.len(), 1);
        assert_eq!(full.selected().count(), 0);
    }

    #[test]
    fn source_selection_ranks_complete_violations_across_rule_matches() {
        let first: TermExpr = "(Read Int Int (Write Int Int A i v) j)".parse().unwrap();
        let second: TermExpr = "(Read Int Int (Write Int Int B p w) q)".parse().unwrap();
        let expected: TermExpr =
            "(=> (not (= q p)) (= (Read Int Int (Write Int Int B p w) q) (Read Int Int B q)))"
                .parse()
                .unwrap();
        let mut egraph = EGraph::<TermLanguage, ()>::default();
        egraph.add_expr(&first);
        egraph.add_expr(&second);
        egraph.rebuild();

        let mut result = generate_array_instantiation_candidates(
            &egraph,
            PreferB,
            &[("Int".into(), "Int".into())],
            InstantiationOptions {
                search_allowance: crate::policy::effort::WorkAllowance::default(),
                additional_terms: vec![],
                candidate_catalog: two_write_candidate_catalog(),
                candidate_scope: CandidateScope::SourceGroundedOnly,
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                instrumentation: InstantiationInstrumentation {
                    artifact_capture: ArtifactCapture::default(),
                    profiling: None,
                },
            },
        );

        assert_eq!(result.selected().count(), 0);
        prepare_violations(&mut result, CandidateScope::SourceGroundedOnly);
        assert_eq!(
            result
                .selected()
                .map(|candidate| candidate.expression.to_string())
                .collect::<Vec<_>>(),
            vec![expected.to_string()]
        );
    }

    #[test]
    fn costs_over_100_compete_without_special_classification() {
        let first: TermExpr = "(Read Int Int (Write Int Int A i v) j)".parse().unwrap();
        let second: TermExpr = "(Read Int Int (Write Int Int B p w) q)".parse().unwrap();
        let mut egraph = EGraph::<TermLanguage, ()>::default();
        egraph.add_expr(&first);
        egraph.add_expr(&second);
        egraph.rebuild();

        let mut result = generate_array_instantiation_candidates(
            &egraph,
            HighCostA,
            &[("Int".into(), "Int".into())],
            InstantiationOptions {
                search_allowance: crate::policy::effort::WorkAllowance::default(),
                additional_terms: vec![],
                candidate_catalog: two_write_candidate_catalog(),
                candidate_scope: CandidateScope::SourceGroundedOnly,
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                instrumentation: InstantiationInstrumentation {
                    artifact_capture: ArtifactCapture::default(),
                    profiling: None,
                },
            },
        );

        assert!(result
            .candidates
            .iter()
            .any(|candidate| candidate.cost > LEGACY_HIGH_COST_THRESHOLD));
        prepare_violations(&mut result, CandidateScope::SourceGroundedOnly);
        assert!(result
            .selected()
            .all(|candidate| candidate.cost <= LEGACY_HIGH_COST_THRESHOLD));

        result
            .candidates
            .retain(|candidate| candidate.cost > LEGACY_HIGH_COST_THRESHOLD);
        prepare_violations(&mut result, CandidateScope::SourceGroundedOnly);
        assert_eq!(result.selected().count(), 1);
    }

    #[test]
    fn full_selection_chooses_one_candidate_per_matched_eclass() {
        let first: TermExpr = "(Read Int Int (Write Int Int A i v) j)".parse().unwrap();
        let second: TermExpr = "(Read Int Int (Write Int Int B p w) q)".parse().unwrap();
        let expected: TermExpr =
            "(=> (not (= q p)) (= (Read Int Int (Write Int Int B p w) q) (Read Int Int B q)))"
                .parse()
                .unwrap();
        let mut egraph = EGraph::<TermLanguage, ()>::default();
        let first_id = egraph.add_expr(&first);
        let second_id = egraph.add_expr(&second);
        egraph.union(first_id, second_id);
        egraph.rebuild();

        let mut result = generate_array_instantiation_candidates(
            &egraph,
            PreferB,
            &[("Int".into(), "Int".into())],
            InstantiationOptions {
                search_allowance: crate::policy::effort::WorkAllowance::default(),
                additional_terms: vec![],
                candidate_catalog: ArrayCandidateCatalog::default(),
                candidate_scope: CandidateScope::AllCandidates,
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                instrumentation: InstantiationInstrumentation {
                    artifact_capture: ArtifactCapture::default(),
                    profiling: None,
                },
            },
        );

        prepare_violations(&mut result, CandidateScope::AllCandidates);
        assert_eq!(
            result
                .selected()
                .map(|candidate| candidate.expression.to_string())
                .collect::<Vec<_>>(),
            vec![expected.to_string()]
        );
    }

    #[test]
    fn matched_eclass_ties_use_canonical_expression_order() {
        let first: TermExpr = "(Read Int Int (ConstArr Int Int z) i)".parse().unwrap();
        let second: TermExpr = "(Read Int Int (ConstArr Int Int z) j)".parse().unwrap();
        let expected: TermExpr = "(= (Read Int Int (ConstArr Int Int z) i) z)"
            .parse()
            .unwrap();
        let mut egraph = EGraph::<TermLanguage, ()>::default();
        let second_id = egraph.add_expr(&second);
        let first_id = egraph.add_expr(&first);
        egraph.union(first_id, second_id);
        egraph.rebuild();

        let mut result = generate_array_instantiation_candidates(
            &egraph,
            ZeroCost,
            &[("Int".into(), "Int".into())],
            InstantiationOptions {
                search_allowance: crate::policy::effort::WorkAllowance::default(),
                additional_terms: vec![],
                candidate_catalog: ArrayCandidateCatalog::default(),
                candidate_scope: CandidateScope::AllCandidates,
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                instrumentation: InstantiationInstrumentation {
                    artifact_capture: ArtifactCapture::default(),
                    profiling: None,
                },
            },
        );

        prepare_violations(&mut result, CandidateScope::AllCandidates);
        assert_eq!(
            result
                .selected()
                .map(|candidate| candidate.expression.to_string())
                .collect::<Vec<_>>(),
            vec![expected.to_string()]
        );
    }

    #[test]
    fn whole_instantiation_capture_keeps_all_candidates_and_marks_one_selected() {
        let first: TermExpr = "(Read Int Int (Write Int Int A i v) j)".parse().unwrap();
        let second: TermExpr = "(Read Int Int (Write Int Int B p w) q)".parse().unwrap();
        let mut egraph = EGraph::<TermLanguage, ()>::default();
        egraph.add_expr(&first);
        egraph.add_expr(&second);
        egraph.rebuild();

        let mut result = generate_array_instantiation_candidates(
            &egraph,
            PreferB,
            &[("Int".into(), "Int".into())],
            InstantiationOptions {
                search_allowance: crate::policy::effort::WorkAllowance::default(),
                additional_terms: vec![],
                candidate_catalog: two_write_candidate_catalog(),
                candidate_scope: CandidateScope::SourceGroundedOnly,
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                instrumentation: InstantiationInstrumentation {
                    artifact_capture: ArtifactCapture {
                        decisions: true,
                        instantiation_provenance: true,
                        conflicts: false,
                    },
                    profiling: None,
                },
            },
        );

        assert!(result.selected().next().is_none());
        prepare_violations(&mut result, CandidateScope::SourceGroundedOnly);
        let abstract_instantiations = result
            .candidates
            .iter()
            .filter_map(|candidate| candidate.abstract_instantiation.as_ref())
            .collect::<Vec<_>>();
        assert!(abstract_instantiations.len() >= 2);
        assert_eq!(
            abstract_instantiations
                .iter()
                .filter(|record| record.was_selected)
                .count(),
            1
        );
        let selected_id = result
            .selected()
            .next()
            .unwrap()
            .provenance
            .abstract_instantiation_id();
        let selected_record = abstract_instantiations
            .iter()
            .find(|record| record.was_selected)
            .unwrap();
        assert_eq!(selected_record.abstract_instantiation_id, selected_id);
        assert!(!selected_record.substitution.is_empty());
        let decision_keys = result
            .candidates
            .iter()
            .flat_map(|candidate| candidate.decisions.iter())
            .map(|decision| decision.decision_key.clone())
            .collect::<HashSet<_>>();
        assert!(!decision_keys.is_empty());
        assert!(abstract_instantiations
            .iter()
            .flat_map(|record| record.decision_keys.iter())
            .all(|key| decision_keys.contains(key)));
    }

    #[test]
    fn decision_capture_does_not_change_selection() {
        fn run(artifact_capture: ArtifactCapture) -> InstantiationBatch {
            let expr: RecExpr<TermLanguage> =
                "(Read Int Int (Write Int Int A i v) j)".parse().unwrap();
            let mut egraph = EGraph::<TermLanguage, ()>::default();
            egraph.add_expr(&expr);
            egraph.rebuild();

            let mut result = generate_array_instantiation_candidates(
                &egraph,
                ZeroCost,
                &[("Int".into(), "Int".into())],
                InstantiationOptions {
                    search_allowance: crate::policy::effort::WorkAllowance::default(),
                    additional_terms: vec![],
                    candidate_catalog: ArrayCandidateCatalog::default(),
                    candidate_scope: CandidateScope::AllCandidates,
                    refinement_step: 0,
                    selection_counts: FxHashMap::default(),
                    depth: 0,
                    instrumentation: InstantiationInstrumentation {
                        artifact_capture,
                        profiling: None,
                    },
                },
            );
            prepare_violations(&mut result, CandidateScope::AllCandidates);
            result
        }

        let compact = run(ArtifactCapture::default());
        let recorded = run(ArtifactCapture {
            decisions: true,
            instantiation_provenance: true,
            conflicts: false,
        });

        let compact_instantiations = compact
            .selected()
            .map(|candidate| candidate.expression.to_string())
            .collect::<Vec<_>>();
        let recorded_instantiations = recorded
            .selected()
            .map(|candidate| candidate.expression.to_string())
            .collect::<Vec<_>>();
        let compact_history = compact
            .selected()
            .flat_map(|candidate| candidate.selection_history.iter())
            .map(|decision| (&decision.decision_key, &decision.chosen_term_hash))
            .collect::<Vec<_>>();
        let recorded_history = recorded
            .selected()
            .flat_map(|candidate| candidate.selection_history.iter())
            .map(|decision| (&decision.decision_key, &decision.chosen_term_hash))
            .collect::<Vec<_>>();

        assert_eq!(compact_instantiations, recorded_instantiations);
        assert_eq!(compact_history, recorded_history);
        assert!(compact
            .candidates
            .iter()
            .all(|candidate| candidate.decisions.is_empty()));
        assert!(recorded
            .candidates
            .iter()
            .any(|candidate| !candidate.decisions.is_empty()));
        assert!(compact
            .candidates
            .iter()
            .all(|candidate| candidate.abstract_instantiation.is_none()));
        assert!(recorded
            .candidates
            .iter()
            .any(|candidate| candidate.abstract_instantiation.is_some()));
    }
}
