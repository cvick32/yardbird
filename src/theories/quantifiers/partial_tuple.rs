//! Model-local typed-domain traversal with conservative prefix rejection.
//!
//! A signed Boolean plan describes *all* ways to violate the binder direction.
//! A prefix is impossible only when every alternative has a known false
//! requirement. Missing graph terms and unresolved model values never reject it.
use std::collections::HashMap;

use egg::{Analysis, EGraph, Id, MultiPattern, Pattern, Searcher, Subst, Var};

use crate::{
    policy::effort::WorkAllowance,
    rule_matching::search::{MatchedRules, RuleMatch},
    terms::language::{TermLanguage, TermPattern},
};

struct Atom {
    pattern: TermPattern,
    variables: Vec<Var>,
    truth: bool,
}

pub(super) struct PartialTuplePlan {
    anchor: MultiPattern<TermLanguage>,
    domains: Vec<(Var, String)>,
    atoms: Vec<Atom>,
    alternatives: Vec<Vec<usize>>,
}

impl PartialTuplePlan {
    pub(super) fn new(
        anchor: MultiPattern<TermLanguage>,
        mut domains: Vec<(Var, String)>,
        alternatives: Vec<Vec<(Pattern<TermLanguage>, bool)>>,
    ) -> Option<Self> {
        // Leave single-atom, all-variable bodies on the ordinary matcher: there
        // is no partial tuple to reject before constructing their full body.
        let bound = <MultiPattern<TermLanguage> as Searcher<TermLanguage, ()>>::vars(&anchor);
        let free = domains
            .iter()
            .filter(|(var, _)| !bound.contains(var))
            .map(|(var, _)| *var)
            .collect::<Vec<_>>();
        if !alternatives.iter().flatten().any(|(pattern, _)| {
            let vars = pattern.vars();
            free.iter().filter(|var| vars.contains(var)).count() < free.len()
        }) {
            return None;
        }
        let mut atoms = Vec::new();
        let alternatives = alternatives
            .into_iter()
            .map(|alternative| {
                alternative
                    .into_iter()
                    .map(|(pattern, truth)| {
                        let index = atoms.len();
                        atoms.push(Atom {
                            variables: pattern.vars(),
                            pattern: pattern.ast,
                            truth,
                        });
                        index
                    })
                    .collect()
            })
            .collect();
        // Bind the smallest condition first, then favor conditions needing the
        // fewest additional variables. Source order breaks ties deterministically.
        let mut ordered = Vec::new();
        while !domains.is_empty() {
            let next = atoms
                .iter()
                .map(|atom| {
                    domains
                        .iter()
                        .filter(|(v, _)| atom.variables.contains(v))
                        .map(|(v, _)| *v)
                        .collect::<Vec<_>>()
                })
                .filter(|vars| !vars.is_empty())
                .min_by_key(Vec::len)
                .unwrap_or_else(|| vec![domains[0].0]);
            for var in next {
                let index = domains.iter().position(|(v, _)| *v == var).unwrap();
                ordered.push(domains.remove(index));
            }
        }
        Some(Self {
            anchor,
            domains: ordered,
            atoms,
            alternatives,
        })
    }

    fn remaining(
        &self,
        alternatives: &[Vec<usize>],
        substitution: &Subst,
        evaluate: &mut impl FnMut(&TermPattern, &Subst) -> anyhow::Result<Option<bool>>,
        checks: &mut usize,
    ) -> anyhow::Result<Vec<Vec<usize>>> {
        let mut viable = Vec::new();
        for alternative in alternatives {
            let mut pending = Vec::new();
            let mut impossible = false;
            for &index in alternative {
                let atom = &self.atoms[index];
                if atom
                    .variables
                    .iter()
                    .all(|var| substitution.get(*var).is_some())
                {
                    *checks += 1;
                    if evaluate(&atom.pattern, substitution)?
                        .is_some_and(|truth| truth != atom.truth)
                    {
                        impossible = true;
                        break;
                    }
                    // An unresolved atom cannot disprove this alternative. Its
                    // value will still be checked in the complete formula.
                } else {
                    pending.push(index);
                }
            }
            if !impossible {
                if pending.is_empty() {
                    return Ok(vec![vec![]]);
                }
                viable.push(pending);
            }
        }
        Ok(viable)
    }
}

struct Prefix {
    substitution: Subst,
    alternatives: Vec<Vec<usize>>,
    next_value: usize,
}

pub(super) struct PartialTupleCursor {
    anchors: Vec<(Id, Subst)>,
    all_anchors: bool,
    next_anchor: usize,
    root: Option<Id>,
    domains: Vec<Vec<Id>>,
    stack: Vec<Prefix>,
    work: usize,
}

pub(super) struct PartialTuplePage {
    pub matched: MatchedRules,
    pub complete: bool,
    pub exhausted: bool,
    pub checks: usize,
    pub rejected: usize,
}

impl PartialTupleCursor {
    pub(super) fn new<N: Analysis<TermLanguage>>(
        graph: &EGraph<TermLanguage, N>,
        plan: &PartialTuplePlan,
        limit: usize,
    ) -> Self {
        let mut pools: HashMap<Id, Vec<Id>> = HashMap::new();
        for class in graph.classes() {
            for node in &class.nodes {
                if let TermLanguage::Domain([sort, value]) = node {
                    pools
                        .entry(graph.find(*sort))
                        .or_default()
                        .push(graph.find(*value));
                }
            }
        }
        for values in pools.values_mut() {
            values.sort_unstable();
            values.dedup();
        }
        let domains = plan
            .domains
            .iter()
            .map(|(_, sort)| {
                graph
                    .lookup(TermLanguage::SortTag(sort.as_str().into()))
                    .and_then(|id| pools.get(&graph.find(id)))
                    .cloned()
                    .unwrap_or_default()
            })
            .collect();
        let mut anchors = plan
            .anchor
            .search_with_limit(graph, limit + 1)
            .into_iter()
            .flat_map(|m| m.substs.into_iter().map(move |subst| (m.eclass, subst)))
            .collect::<Vec<_>>();
        let all_anchors = anchors.len() <= limit;
        anchors.truncate(limit);
        Self {
            anchors,
            all_anchors,
            next_anchor: 0,
            root: None,
            domains,
            stack: Vec::new(),
            work: 0,
        }
    }

    fn choices(&self, depth: usize, plan: &PartialTuplePlan) -> usize {
        let prefix = &self.stack[depth];
        if let Some(value) = prefix.substitution.get(plan.domains[depth].0) {
            usize::from(self.domains[depth].binary_search(value).is_ok())
        } else {
            self.domains[depth].len()
        }
    }

    fn backtrack(&mut self, plan: &PartialTuplePlan) {
        while let Some(depth) = self.stack.len().checked_sub(1) {
            if self.stack[depth].next_value < self.choices(depth, plan) {
                break;
            }
            self.stack.pop();
        }
    }

    pub(super) fn page(
        &mut self,
        plan: &PartialTuplePlan,
        rule_index: usize,
        allowance: &WorkAllowance,
        mut evaluate: impl FnMut(&TermPattern, &Subst) -> anyhow::Result<Option<bool>>,
    ) -> anyhow::Result<PartialTuplePage> {
        let mut page = PartialTuplePage {
            matched: MatchedRules::default(),
            complete: false,
            exhausted: false,
            checks: 0,
            rejected: 0,
        };
        let end = self
            .work
            .saturating_add(allowance.binder_page_size)
            .min(allowance.binder_search_limit);
        while self.work < end {
            self.backtrack(plan);
            if self.stack.is_empty() && self.next_anchor == self.anchors.len() {
                break;
            }
            self.work += 1;
            page.matched.report.examined_substitutions += 1;
            let (substitution, alternatives) = if self.stack.is_empty() {
                let (root, substitution) = &self.anchors[self.next_anchor];
                self.next_anchor += 1;
                self.root = Some(*root);
                (substitution.clone(), &plan.alternatives)
            } else {
                let depth = self.stack.len() - 1;
                let prefix = &mut self.stack[depth];
                let var = plan.domains[depth].0;
                let mut substitution = prefix.substitution.clone();
                let value = substitution
                    .get(var)
                    .copied()
                    .unwrap_or_else(|| self.domains[depth][prefix.next_value]);
                prefix.next_value += 1;
                substitution.insert(var, value);
                (substitution, &prefix.alternatives)
            };
            let remaining =
                plan.remaining(alternatives, &substitution, &mut evaluate, &mut page.checks)?;
            if remaining.is_empty() {
                page.rejected += 1;
            } else if self.stack.len() == plan.domains.len() {
                page.matched.matches.push(RuleMatch {
                    rule_index,
                    root: self.root.unwrap(),
                    substitution,
                    model_violation_verified: false,
                });
            } else {
                self.stack.push(Prefix {
                    substitution,
                    alternatives: remaining,
                    next_value: 0,
                });
            }
        }
        self.backtrack(plan);
        let finished = self.stack.is_empty() && self.next_anchor == self.anchors.len();
        page.complete = finished && self.all_anchors;
        page.exhausted = !page.complete && (finished || self.work >= allowance.binder_search_limit);
        page.matched.report.returned_substitutions = page.matched.matches.len();
        page.matched.report.rounds = 1;
        Ok(page)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theories::quantifiers::{app, string_to_sort, BinderKind, BinderRule, SearchPhase};
    use smt2parser::concrete::Symbol;

    fn fixture(
        kind: BinderKind,
        body: &str,
    ) -> (
        EGraph<TermLanguage, ()>,
        super::super::compiled_rule::CompiledBinderRule<()>,
    ) {
        let rule = BinderRule {
            name: "q".into(),
            kind,
            captures: vec![],
            variables: (0..3)
                .map(|i| (Symbol(format!("x{i}")), string_to_sort("Int")))
                .collect(),
            body: body.parse().unwrap(),
            witnesses: vec![],
            result_sort: string_to_sort("Bool"),
            unit_capture: true,
        }
        .compile(SearchPhase::Conflicts, &[])
        .unwrap()
        .unwrap();
        let mut graph = EGraph::default();
        let proxy = graph.add_expr(&"($apply q true)".parse().unwrap());
        let truth = graph.add_expr(
            &if kind == BinderKind::Forall {
                "true"
            } else {
                "false"
            }
            .parse()
            .unwrap(),
        );
        graph.union(proxy, truth);
        let sort = graph.add(TermLanguage::SortTag("Int".into()));
        for n in 0..3 {
            let value = graph.add(TermLanguage::Num(n));
            graph.add(TermLanguage::Domain([sort, value]));
        }
        graph.rebuild();
        (graph, rule)
    }

    fn ground(
        graph: &EGraph<TermLanguage, ()>,
        pattern: &TermPattern,
        subst: &Subst,
    ) -> smt2parser::concrete::Term {
        use crate::rule_matching::grounding::instantiate_with_bindings;
        use crate::terms::language::{expr_to_term, TermExpr};
        let values = Pattern::new(pattern.clone())
            .vars()
            .into_iter()
            .map(|var| {
                let number = graph[subst[var]]
                    .nodes
                    .iter()
                    .find_map(|n| {
                        if let TermLanguage::Num(n) = n {
                            Some(*n)
                        } else {
                            None
                        }
                    })
                    .unwrap();
                (var, number.to_string().parse::<TermExpr>().unwrap())
            })
            .collect::<HashMap<_, _>>();
        expr_to_term(instantiate_with_bindings(pattern, |var| Ok(&values[&var])).unwrap())
    }

    #[test]
    fn partial_search_matches_exhaustive_violations_in_both_directions() {
        use crate::rule_matching::grounding::instantiate_with_bindings;
        use crate::terms::language::expr_to_term;
        for kind in [BinderKind::Forall, BinderKind::Exists] {
            // Multiple alternatives: rejecting one conjunction must not reject
            // the other, and a negated atom requires the opposite model value.
            let body = "(and (=> (= x0 0) (= x1 x2)) (=> (not (= x0 0)) (= x1 1)))";
            let (graph, rule) = fixture(kind, body);
            let plan = rule.details.partial.as_ref().unwrap();
            let mut cursor = PartialTupleCursor::new(&graph, plan, 1000);
            let allowance = WorkAllowance {
                binder_page_size: 3,
                binder_search_limit: 1000,
                ..Default::default()
            };
            let mut actual = std::collections::HashSet::new();
            loop {
                let page = cursor
                    .page(plan, 0, &allowance, |pattern, subst| {
                        let term = ground(&graph, pattern, subst);
                        Ok(Some(eval(&term)))
                    })
                    .unwrap();
                assert!(page.matched.report.examined_substitutions <= 3);
                for matched in page.matched.matches {
                    // The production path must still validate this formula.
                    assert!(!matched.model_violation_verified);
                    let body = ground(&graph, &rule.formula, &matched.substitution).to_string();
                    assert!(actual.insert(body), "a resumed page replayed a tuple");
                }
                assert!(!page.exhausted);
                if page.complete {
                    break;
                }
            }
            let mut expected = std::collections::HashSet::new();
            for x0 in 0..3 {
                for x1 in 0..3 {
                    for x2 in 0..3 {
                        let values = [x0, x1, x2].map(|n: i32| n.to_string().parse().unwrap());
                        let expr = instantiate_with_bindings(&rule.formula, |var| {
                            let index: usize = var
                                .to_string()
                                .trim_start_matches("?binding")
                                .parse()
                                .unwrap();
                            Ok(&values[index])
                        })
                        .unwrap();
                        let term = expr_to_term(expr);
                        // Remove the helper wrapper; its active value is fixed by kind.
                        let smt2parser::concrete::Term::Application { arguments, .. } = &term
                        else {
                            unreachable!()
                        };
                        let body = &arguments[usize::from(kind == BinderKind::Forall)];
                        if eval(body) == (kind == BinderKind::Exists) {
                            expected.insert(term.to_string());
                        }
                    }
                }
            }
            assert_eq!(actual, expected, "{kind:?}");
            assert!(!actual.is_empty());
        }
    }

    fn eval(term: &smt2parser::concrete::Term) -> bool {
        use smt2parser::concrete::Term;
        let Term::Application {
            qual_identifier,
            arguments: a,
        } = term
        else {
            return *term == app("true", vec![]);
        };
        match qual_identifier.get_name().as_str() {
            "=" => a[0] == a[1],
            "not" => !eval(&a[0]),
            "and" => a.iter().all(eval),
            "=>" => !eval(&a[0]) || eval(&a[1]),
            other => panic!("unexpected operator {other}"),
        }
    }

    #[test]
    fn partial_requests_preserve_capture_and_literal_bindings() {
        let (mut graph, _) = fixture(BinderKind::Forall, "(=> (= x0 0) (= x1 x2))");
        let truth = graph.lookup_expr(&"true".parse().unwrap()).unwrap();
        for value in [0, 1] {
            let proxy = graph.add_expr(&format!("($apply q {value})").parse().unwrap());
            graph.union(proxy, truth);
        }
        graph.rebuild();
        let rule = BinderRule {
            name: "q".into(),
            kind: BinderKind::Forall,
            captures: vec![(Symbol("c".into()), string_to_sort("Int"))],
            variables: (0..3)
                .map(|i| (Symbol(format!("x{i}")), string_to_sort("Int")))
                .collect(),
            body: "(=> (= x0 c) (= x1 x2))".parse().unwrap(),
            witnesses: vec![],
            result_sort: string_to_sort("Bool"),
            unit_capture: false,
        }
        .compile_with_bindings(
            SearchPhase::Conflicts,
            &[],
            &[
                (Symbol("c".into()), "0".parse().unwrap()),
                (Symbol("x1".into()), "1".parse().unwrap()),
            ],
        )
        .unwrap()
        .unwrap();
        let plan = rule.details.partial.as_ref().unwrap();
        let allowance = WorkAllowance::default();
        let mut cursor = PartialTupleCursor::new(&graph, plan, allowance.binder_search_limit);
        let page = cursor
            .page(plan, 0, &allowance, |pattern, subst| {
                Ok(Some(eval(&ground(&graph, pattern, subst))))
            })
            .unwrap();
        assert!(page.complete);
        let formulas = page
            .matched
            .matches
            .iter()
            .map(|m| ground(&graph, &rule.formula, &m.substitution).to_string())
            .collect::<std::collections::HashSet<_>>();
        assert_eq!(
            formulas,
            [
                "(=> (q 0) (=> (= 0 0) (= 1 0)))".to_string(),
                "(=> (q 0) (=> (= 0 0) (= 1 2)))".to_string(),
            ]
            .into_iter()
            .collect()
        );
    }

    #[test]
    fn unknown_values_preserve_tuples_and_prefix_budgets_are_exact() {
        let (graph, rule) = fixture(BinderKind::Forall, "(=> (= x0 0) (= x1 x2))");
        let plan = rule.details.partial.as_ref().unwrap();
        // One anchor, then 3 + 9 + 27 domain extensions.
        for (limit, complete) in [(39, false), (40, true)] {
            let mut cursor = PartialTupleCursor::new(&graph, plan, limit);
            let allowance = WorkAllowance {
                binder_page_size: 100,
                binder_search_limit: limit,
                ..Default::default()
            };
            let page = cursor.page(plan, 0, &allowance, |_, _| Ok(None)).unwrap();
            assert_eq!(page.complete, complete);
            assert_eq!(page.exhausted, !complete);
            assert_eq!(page.matched.report.examined_substitutions, limit);
            assert_eq!(page.matched.matches.len(), if complete { 27 } else { 26 });
        }
    }

    #[test]
    fn rejected_prefix_skips_children_and_a_new_model_reconsiders_them() {
        let (graph, rule) = fixture(BinderKind::Forall, "(=> (= x0 0) (= x1 x2))");
        let plan = rule.details.partial.as_ref().unwrap();
        let allowance = WorkAllowance::default();
        let mut cursor = PartialTupleCursor::new(&graph, plan, allowance.binder_search_limit);
        let page = cursor
            .page(plan, 0, &allowance, |_, _| Ok(Some(false)))
            .unwrap();
        assert!(page.complete);
        assert!(page.matched.matches.is_empty());
        assert_eq!(page.rejected, 3);
        assert_eq!(page.matched.report.examined_substitutions, 4);
        let mut refreshed = PartialTupleCursor::new(&graph, plan, allowance.binder_search_limit);
        let page = refreshed
            .page(plan, 0, &allowance, |_, _| Ok(None))
            .unwrap();
        assert_eq!(page.matched.matches.len(), 27);
    }
}
