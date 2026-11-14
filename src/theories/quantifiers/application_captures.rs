//! Concrete helper applications survive model-equality matching. Capture arguments
//! are context, not extraction choices: only the binder's variables are searched.
use super::{compiled_rule::CompiledBinderRule, BinderRule};
use crate::{
    rule_matching::search::RuleMatch,
    terms::language::{TermExpr, TermLanguage},
};
use egg::{Analysis, EGraph, Id, Language, Var};
use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

type CaptureTuple = Vec<(Var, TermExpr)>;
type CaptureTuples = Rc<Vec<CaptureTuple>>;

#[derive(Default)]
pub(super) struct ApplicationCaptures {
    // Distinct symbolic tuples remain distinct even when all arguments have
    // identical model values. The key is only an index into actual occurrences.
    tuples: HashMap<(String, Vec<Id>), CaptureTuples>,
}

impl ApplicationCaptures {
    pub fn new<N: Analysis<TermLanguage>>(
        rules: &[BinderRule],
        terms: &[TermExpr],
        graph: &EGraph<TermLanguage, N>,
    ) -> Self {
        let arities: HashMap<_, _> = rules
            .iter()
            .filter(|r| !r.unit_capture)
            .map(|r| (r.name.as_str(), r.captures.len()))
            .collect();
        let mut seen = HashSet::new();
        let mut applications = Vec::new();
        for expression in terms {
            for node in expression.as_ref() {
                let TermLanguage::Apply(children) = node else {
                    continue;
                };
                let Some((head, arguments)) = children.split_first() else {
                    continue;
                };
                let TermLanguage::Symbol(helper) = &expression[*head] else {
                    continue;
                };
                if arities.get(helper.as_str()) != Some(&arguments.len()) {
                    continue;
                }
                let application = node.build_recexpr(|id| expression[id].clone());
                if seen.insert(application.clone()) {
                    applications.push((helper.to_string(), application));
                }
            }
        }
        applications.sort_by_cached_key(|(_, term)| term.to_string());
        let mut result = Self::default();
        for (helper, application) in applications {
            let TermLanguage::Apply(children) = application.as_ref().last().unwrap() else {
                unreachable!()
            };
            let tuple: CaptureTuple = children[1..]
                .iter()
                .enumerate()
                .map(|(i, id)| {
                    (
                        format!("?binding{i}").parse().unwrap(),
                        application[*id].build_recexpr(|id| application[id].clone()),
                    )
                })
                .collect();
            let Some(classes) = tuple
                .iter()
                .map(|(_, term)| graph.lookup_expr(term).map(|id| graph.find(id)))
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            Rc::make_mut(result.tuples.entry((helper, classes)).or_default()).push(tuple);
        }
        result
    }

    pub fn occurrences<N: Analysis<TermLanguage>>(
        &self,
        rule: &CompiledBinderRule<N>,
        matched: RuleMatch,
        graph: &EGraph<TermLanguage, N>,
    ) -> CaptureMatches {
        // Explicit requests may introduce an application absent from vocabulary.
        // When all captures are literal, that request already names its context.
        let captures = &rule.details.captures;
        let fixed: CaptureTuple = rule
            .fixed_bindings()
            .iter()
            .filter(|(var, _)| captures.contains(var))
            .cloned()
            .collect();
        let tuples = if fixed.len() == captures.len() {
            Rc::new(vec![vec![]])
        } else {
            let classes = captures
                .iter()
                .map(|var| matched.substitution.get(*var).map(|id| graph.find(*id)))
                .collect::<Option<Vec<_>>>();
            let helper = match rule.metadata().provenance() {
                crate::rule_matching::rule::QuantifiedRuleProvenance::InputBinder { helper } => {
                    helper
                }
                _ => unreachable!("input binder application"),
            };
            classes
                .and_then(|classes| self.tuples.get(&(helper.clone(), classes)).cloned())
                .unwrap_or_default()
        };
        CaptureMatches {
            matched,
            tuples,
            fixed,
            next: 0,
        }
    }
}

pub(super) struct CaptureMatches {
    matched: RuleMatch,
    tuples: CaptureTuples,
    fixed: CaptureTuple,
    next: usize,
}
impl CaptureMatches {
    pub fn pending(&self) -> bool {
        self.next < self.tuples.len()
    }
    /// One occurrence per work unit, including literal-incompatible requests.
    pub fn step(&mut self) -> Option<RuleMatch> {
        let tuple = self.tuples.get(self.next)?;
        self.next += 1;
        if !tuple.is_empty() && self.fixed.iter().any(|binding| !tuple.contains(binding)) {
            return None;
        }
        let mut matched = self.matched.clone();
        matched.literal_bindings = tuple
            .iter()
            .filter(|(var, _)| !self.fixed.iter().any(|(fixed, _)| fixed == var))
            .cloned()
            .collect();
        Some(matched)
    }
}

#[cfg(test)]
mod tests {
    use super::super::{
        tests::{prepared_options, PreferLongName, PreparedFixture},
        *,
    };
    use super::*;
    use crate::{policy::effort::WorkAllowance, terms::language::expr_to_term};
    use smt2parser::vmt::array_abstractor::string_to_sort;

    fn fixture() -> PreparedFixture {
        fixture_with_kind(BinderKind::Forall)
    }

    fn fixture_with_kind(kind: BinderKind) -> PreparedFixture {
        let rule = BinderRule {
            name: "q".into(),
            kind,
            captures: vec![
                (Symbol("a".into()), string_to_sort("Int")),
                (Symbol("b".into()), string_to_sort("Int")),
            ],
            variables: vec![(Symbol("x".into()), string_to_sort("Int"))],
            body: "(p a b x)".parse().unwrap(),
            witnesses: vec!["w".into()],
            result_sort: string_to_sort("Bool"),
            unit_capture: false,
        };
        let plan = QuantifierPlan {
            rules: vec![rule],
            signatures: ["a", "b", "c", "d", "v0", "v1", "z"]
                .into_iter()
                .map(|s| (s.into(), (vec![], string_to_sort("Int"))))
                .collect(),
            ..Default::default()
        };
        // The third helper is nested in an admitted instance, not a source root.
        let terms: Vec<TermExpr> = [
            "(q a b)",
            "(q c d)",
            "(=> true (q (f a) d))",
            "true",
            "false",
            "v0",
            "v1",
            "z",
        ]
        .into_iter()
        .map(|s| translate_term_with_array_types(s.parse().unwrap(), &[]).unwrap())
        .collect();
        let mut graph = EGraph::<TermLanguage, ()>::default();
        for t in &terms {
            graph.add_expr(t);
        }
        let expr = |s: &str| translate_term_with_array_types(s.parse().unwrap(), &[]).unwrap();
        for (a, b) in [("a", "c"), ("a", "(f a)"), ("b", "d"), ("(q a b)", "true")] {
            let a = graph.lookup_expr(&expr(a)).unwrap();
            let b = graph.lookup_expr(&expr(b)).unwrap();
            graph.union(a, b);
            graph.rebuild();
        }
        let sort = graph.add(TermLanguage::SortTag("Int".into()));
        for s in ["v0", "v1"] {
            let v = graph.lookup_expr(&expr(s)).unwrap();
            graph.add(TermLanguage::Domain([sort, v]));
        }
        graph.rebuild();
        let mut representatives = HashMap::new();
        for t in &terms {
            for n in t.as_ref() {
                let sub = n.build_recexpr(|id| t[id].clone());
                let id = graph.find(graph.lookup_expr(&sub).unwrap());
                representatives.entry(id).or_insert(sub);
            }
        }
        let application_captures = ApplicationCaptures::new(&plan.rules, &terms, &graph);
        PreparedFixture {
            egraph: graph,
            search: PreparedQuantifierSearch {
                application_captures,
                graph_version: 0,
                additional_terms: terms,
                representatives,
                evaluations: HashMap::new(),
                compiled: plan.compiled(&[]).unwrap(),
                cursors: HashMap::new(),
                requests: HashMap::new(),
                obligations: HashMap::new(),
                catalog: Default::default(),
                cost_context: Default::default(),
            },
        }
    }

    #[test]
    fn merged_helpers_keep_every_actual_tuple_including_derived_applications() {
        let mut f = fixture();
        let mut found = HashSet::new();
        // A single model match covers three syntactically different applications.
        // Page size one must retain each, without constructing mixed tuples.
        for _ in 0..12 {
            let batch = f
                .candidates(
                    |_| Ok("false".into()),
                    BinderSearch::Page {
                        phase: SearchPhase::Conflicts,
                        rule: 0,
                        allowance: WorkAllowance {
                            binder_page_size: 1,
                            ..Default::default()
                        },
                    },
                    |_| PreferLongName,
                    prepared_options(),
                )
                .unwrap();
            assert!(batch.candidates.len() <= 1);
            for c in batch.candidates {
                assert!(
                    !c.model_violation_verified,
                    "literal captures require final independent validation"
                );
                assert!(found.insert(expr_to_term(c.expression).to_string()));
            }
            if !f.can_continue(SearchPhase::Conflicts) {
                break;
            }
        }
        let expected: HashSet<_> = [("a", "b"), ("c", "d"), ("(f a)", "d")]
            .into_iter()
            .flat_map(|(a, b)| ["v0", "v1"].map(|x| format!("(=> (q {a} {b}) (p {a} {b} {x}))")))
            .collect();
        assert_eq!(found, expected);
        assert!(!f.can_continue(SearchPhase::Conflicts));
    }

    #[test]
    fn partial_capture_requests_do_not_mix_equal_literal_arguments() {
        let mut f = fixture();
        let request = BinderSearchRequest {
            helper: "q".into(),
            phase: SearchPhase::Conflicts,
            bindings: vec![(Symbol("a".into()), "c".parse().unwrap())],
        };
        let batch = f
            .candidates(
                |_| Ok("false".into()),
                &request,
                |_| PreferLongName,
                prepared_options(),
            )
            .unwrap();
        assert_eq!(batch.candidates.len(), 2);
        for c in batch.candidates {
            let s = expr_to_term(c.expression).to_string();
            assert!(s.contains("(q c d)"), "{s}");
        }
    }

    #[test]
    fn explicit_capture_tuple_can_introduce_a_new_application() {
        let mut f = fixture();
        let request = BinderSearchRequest {
            helper: "q".into(),
            phase: SearchPhase::Expand,
            bindings: [("a", "z"), ("b", "b"), ("x", "v0")]
                .map(|(a, b)| (Symbol(a.into()), b.parse().unwrap()))
                .to_vec(),
        };
        let batch = f
            .candidates(
                |_| panic!("expand"),
                &request,
                |_| PreferLongName,
                prepared_options(),
            )
            .unwrap();
        assert_eq!(batch.candidates.len(), 1);
        assert_eq!(
            expr_to_term(batch.candidates[0].expression.clone()).to_string(),
            "(=> (q z b) (p z b v0))"
        );
    }

    #[test]
    fn occurrence_expansion_obeys_total_work_budget() {
        let mut f = fixture();
        let mut count = 0;
        for _ in 0..4 {
            let batch = f
                .candidates(
                    |_| Ok("false".into()),
                    BinderSearch::Page {
                        phase: SearchPhase::Conflicts,
                        rule: 0,
                        allowance: WorkAllowance {
                            binder_page_size: 1,
                            binder_search_limit: 2,
                            ..Default::default()
                        },
                    },
                    |_| PreferLongName,
                    prepared_options(),
                )
                .unwrap();
            count += batch.candidates.len();
            if !f.can_continue(SearchPhase::Conflicts) {
                assert!(!batch.search.budget_exhausted_rules.is_empty());
                break;
            }
        }
        assert_eq!(count, 2);
        assert!(!f.can_continue(SearchPhase::Conflicts));
    }
    #[test]
    fn witnesses_keep_the_same_capture_tuple_in_helper_and_witness_function() {
        let mut f = fixture_with_kind(BinderKind::Exists);
        let batch = f
            .candidates(
                |_| Ok("false".into()),
                SearchPhase::Witnesses,
                |_| PreferLongName,
                prepared_options(),
            )
            .unwrap();
        let actual: HashSet<_> = batch
            .candidates
            .into_iter()
            .map(|c| expr_to_term(c.expression).to_string())
            .collect();
        let expected = [("a", "b"), ("c", "d"), ("(f a)", "d")]
            .into_iter()
            .map(|(a, b)| format!("(=> (q {a} {b}) (p {a} {b} (w {a} {b})))"))
            .collect();
        assert_eq!(actual, expected);
    }

    #[test]
    fn graph_growth_registers_new_occurrences_and_resets_pending_pages() {
        let mut f = fixture();
        let first = f
            .candidates(
                |_| Ok("false".into()),
                BinderSearch::Page {
                    phase: SearchPhase::Conflicts,
                    rule: 0,
                    allowance: WorkAllowance {
                        binder_page_size: 1,
                        ..Default::default()
                    },
                },
                |_| PreferLongName,
                prepared_options(),
            )
            .unwrap();
        assert_eq!(first.candidates.len(), 1);
        assert!(f.can_continue(SearchPhase::Conflicts));
        let mut graph = crate::refinement_graph::RefinementGraph::new(Default::default());
        graph.egraph = f.egraph.clone();
        graph.terms = f.additional_terms.clone();
        let new = translate_term_with_array_types("(q a d)".parse().unwrap(), &[]).unwrap();
        graph.egraph.add_expr(&new);
        graph.terms.push(new);
        graph.rebuild();
        let representatives = f.representatives.clone();
        f.search.refresh_graph(&graph, 1);
        // This fixture constructs vocabulary directly; production admission
        // populates the graph's representatives at the same time.
        f.representatives = representatives;
        f.egraph = graph.egraph;
        let batch = f
            .candidates(
                |_| Ok("false".into()),
                SearchPhase::Conflicts,
                |_| PreferLongName,
                prepared_options(),
            )
            .unwrap();
        let actual: HashSet<_> = batch
            .candidates
            .into_iter()
            .map(|c| expr_to_term(c.expression).to_string())
            .collect();
        assert_eq!(actual.len(), 8);
        assert!(actual.contains("(=> (q a d) (p a d v0))"));
        assert!(actual.contains("(=> (q a d) (p a d v1))"));
    }
}
