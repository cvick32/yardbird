//! Exact syntactic binder instances, without model equalities or extraction.
//! Incomplete triggers are left to ordinary e-matching; this is a fast path,
//! never a completeness test. Only complete, sort-checked tuples are emitted.
use std::collections::{HashMap, HashSet};

use super::{
    app, dependency_search::unify, BinderKind, BinderSearchRequest, QuantifierPlan, SearchPhase,
};
use crate::{
    policy::{effort::WorkReport, term_selection::TermCostFactory},
    rule_matching::{
        candidate::{InstantiationBatch, SymbolicInstance},
        rule::QuantifiedRule,
        search_context::SearchContext,
        symbolic_pool::SymbolicCandidatePool,
    },
};
use smt2parser::concrete::Term;

#[derive(Default)]
pub(crate) struct GroundBinders {
    patterns: Vec<Vec<Term>>,
    depth: Option<u16>,
    pool: SymbolicCandidatePool,
    offsets: HashMap<Term, usize>,
    next_helper: usize,
    scope: Option<BinderSearchRequest>,
}

fn head(term: &Term) -> Option<String> {
    match term {
        Term::Application {
            qual_identifier, ..
        } => Some(qual_identifier.get_name()),
        _ => None,
    }
}

fn walk<'a>(term: &'a Term, visit: &mut impl FnMut(&'a Term)) {
    visit(term);
    match term {
        Term::Application { arguments, .. } => {
            for child in arguments {
                walk(child, visit);
            }
        }
        Term::Attributes { term, .. } => walk(term, visit),
        _ => {}
    }
}

/// Immutable source vocabulary shared by scheduled requests in one solver model.
pub(super) struct GroundTerms {
    terms: Vec<Term>,
    by_head: HashMap<String, Vec<usize>>,
}
impl GroundTerms {
    pub(super) fn new(roots: Vec<&Term>) -> Self {
        let mut seen = HashSet::new();
        let mut terms = Vec::new();
        for root in roots {
            walk(root, &mut |term| {
                if head(term).is_some() && seen.insert(term.clone()) {
                    terms.push(term.clone());
                }
            });
        }
        terms.sort_by_cached_key(ToString::to_string);
        let mut by_head = HashMap::<String, Vec<usize>>::new();
        for (index, term) in terms.iter().enumerate() {
            by_head.entry(head(term).unwrap()).or_default().push(index);
        }
        Self { terms, by_head }
    }
}

impl GroundBinders {
    #[cfg(test)]
    fn new(plan: &QuantifierPlan) -> Self {
        Self::with_scope(plan, None)
    }

    pub(super) fn for_request(
        plan: &QuantifierPlan,
        request: BinderSearchRequest,
    ) -> anyhow::Result<Self> {
        let rule = plan
            .rules
            .iter()
            .find(|r| r.name == request.helper)
            .ok_or_else(|| anyhow::anyhow!("unknown binder helper {}", request.helper))?;
        super::binder_request::validate_request(rule, &plan.signatures, &request)?;
        Ok(Self::with_scope(plan, Some(request)))
    }

    fn with_scope(plan: &QuantifierPlan, scope: Option<BinderSearchRequest>) -> Self {
        let patterns = plan
            .rules
            .iter()
            .map(|rule| {
                if scope
                    .as_ref()
                    .is_some_and(|r| r.helper != rule.name || r.phase == SearchPhase::Witnesses)
                {
                    return Vec::new();
                }
                let variables = rule
                    .variables
                    .iter()
                    .map(|(v, _)| v.0.as_str())
                    .collect::<HashSet<_>>();
                // Lambda instances also expose their read-of-helper left side.
                let formula = rule.instantiate(
                    &rule
                        .captures
                        .iter()
                        .map(|(v, _)| app(&v.0, vec![]))
                        .collect::<Vec<_>>(),
                    &rule
                        .variables
                        .iter()
                        .map(|(v, _)| app(&v.0, vec![]))
                        .collect::<Vec<_>>(),
                );
                let mut patterns = Vec::new();
                walk(&formula, &mut |term| {
                    let Some(name) = head(term) else {
                        return;
                    };
                    if !plan.signatures.contains_key(&name) {
                        return;
                    }
                    let mut found = HashSet::new();
                    walk(term, &mut |subterm| {
                        if let Term::QualIdentifier(id) = subterm {
                            let name = id.get_name();
                            if variables.contains(name.as_str()) {
                                found.insert(name);
                            }
                        }
                    });
                    if !variables.is_empty()
                        && found.len() == variables.len()
                        && !patterns.contains(term)
                    {
                        patterns.push(term.clone());
                    }
                });
                patterns
            })
            .collect();
        Self {
            patterns,
            scope,
            ..Default::default()
        }
    }

    pub(super) fn candidates_indexed<F: TermCostFactory>(
        &mut self,
        context: &SearchContext<'_, F>,
        limit: usize,
        terms: &GroundTerms,
    ) -> anyhow::Result<(WorkReport, InstantiationBatch)> {
        if self.depth != Some(context.depth) {
            self.depth = Some(context.depth);
            self.pool = Default::default();
            self.offsets.clear();
            self.next_helper = 0;
        }
        let (instances, work) = self.generate_indexed(context.formulas.quantifiers, terms, limit);
        let returned = instances.len();
        self.pool.remember(instances);
        let mut batch = self.pool.candidates(context)?;
        batch.search.examined_substitutions = work;
        batch.search.returned_substitutions = returned;
        let mut report = WorkReport::from_batch(&batch);
        report.examined_substitutions = work;
        report.budget_exhausted = work == limit;
        Ok((report, batch))
    }

    #[cfg(test)]
    fn generate(
        &mut self,
        plan: &QuantifierPlan,
        roots: Vec<&Term>,
        limit: usize,
    ) -> (Vec<SymbolicInstance>, usize) {
        self.generate_indexed(plan, &GroundTerms::new(roots), limit)
    }

    fn generate_indexed(
        &mut self,
        plan: &QuantifierPlan,
        index: &GroundTerms,
        limit: usize,
    ) -> (Vec<SymbolicInstance>, usize) {
        let names = plan
            .rules
            .iter()
            .enumerate()
            .filter(|(_, r)| {
                self.scope
                    .as_ref()
                    .is_none_or(|scope| scope.helper == r.name)
            })
            .map(|(i, r)| (r.name.as_str(), i))
            .collect::<HashMap<_, _>>();
        let mut helpers = names
            .iter()
            .flat_map(|(name, &rule)| {
                index
                    .by_head
                    .get(*name)
                    .into_iter()
                    .flatten()
                    .map(move |&i| (&index.terms[i], rule))
            })
            .collect::<Vec<_>>();
        // Fully captured directed requests can introduce a helper without
        // admitting it to another request's immutable trigger vocabulary.
        let synthetic = self.scope.as_ref().and_then(|scope| {
            let rule = &plan.rules[names[scope.helper.as_str()]];
            rule.captures
                .iter()
                .map(|(v, _)| {
                    scope
                        .bindings
                        .iter()
                        .find(|(name, _)| name == v)
                        .map(|(_, t)| t.clone())
                })
                .collect::<Option<Vec<_>>>()
                .map(|arguments| app(&rule.name, arguments))
        });
        if let Some(helper) = &synthetic {
            if !helpers.iter().any(|(term, _)| *term == helper) {
                helpers.push((helper, names[self.scope.as_ref().unwrap().helper.as_str()]));
            }
        }
        helpers.sort_by_cached_key(|(term, _)| term.to_string());
        let share = (limit / helpers.len().max(1)).max(1);
        let mut work = 0;
        let mut visited = 0;
        let mut instances = Vec::new();
        for distance in 0..helpers.len() {
            if work == limit {
                break;
            }
            let (helper, rule_index) = helpers[(self.next_helper + distance) % helpers.len()];
            visited += 1;
            let rule = &plan.rules[rule_index];
            let Term::Application { arguments, .. } = helper else {
                unreachable!()
            };
            if arguments.len() != rule.captures.len() {
                continue;
            }
            if rule.unit_capture && arguments.first() != Some(&app("true", vec![])) {
                continue;
            }
            let variables = rule
                .captures
                .iter()
                .chain(&rule.variables)
                .cloned()
                .collect::<HashMap<_, _>>();
            let mut captures = self
                .scope
                .as_ref()
                .map(|r| r.bindings.iter().cloned().collect::<HashMap<_, _>>())
                .unwrap_or_default();
            // Reuse the typed unifier even for captures: reject malformed or
            // overloaded applications instead of constructing a partial lemma.
            if !rule.captures.iter().zip(arguments).all(|((v, _), value)| {
                unify(
                    &app(&v.0, vec![]),
                    value,
                    &variables,
                    &plan.signatures,
                    &mut captures,
                )
            }) {
                continue;
            }
            let ordinary = self
                .scope
                .as_ref()
                .is_none_or(|s| s.phase != SearchPhase::Witnesses);
            let direct = self.scope.as_ref().filter(|_| ordinary).and_then(|_| {
                rule.variables
                    .iter()
                    .map(|(v, _)| captures.get(v).cloned())
                    .collect::<Option<Vec<_>>>()
            });
            let patterns = if direct.is_some() {
                &[][..]
            } else {
                self.patterns[rule_index].as_slice()
            };
            let counts = patterns
                .iter()
                .map(|p| index.by_head.get(&head(p).unwrap()).map_or(0, Vec::len))
                .collect::<Vec<_>>();
            let witness = usize::from(
                rule.kind != BinderKind::Lambda
                    && self
                        .scope
                        .as_ref()
                        .is_none_or(|s| s.phase == SearchPhase::Witnesses),
            );
            let direct_count = usize::from(direct.is_some());
            let count = witness + direct_count + counts.iter().sum::<usize>();
            if count == 0 {
                continue;
            }
            let offset = self.offsets.entry(helper.clone()).or_default();
            let attempts = share.min(count).min(limit - work);
            for step in 0..attempts {
                work += 1;
                let job = (*offset + step) % count;
                if job < witness {
                    instances.push(SymbolicInstance {
                        rule: QuantifiedRule::input_binder(&rule.name),
                        term: rule.witness_instance(arguments).unwrap(),
                        bindings: rule
                            .captures
                            .iter()
                            .zip(arguments)
                            .map(|((s, _), t)| (s.0.clone(), t.clone()))
                            .collect(),
                    });
                    continue;
                }
                if let Some(values) = &direct {
                    instances.push(SymbolicInstance {
                        rule: QuantifiedRule::input_binder(&rule.name),
                        term: rule.instantiate(arguments, values),
                        bindings: rule
                            .captures
                            .iter()
                            .chain(&rule.variables)
                            .map(|(v, _)| (v.0.clone(), captures[v].clone()))
                            .collect(),
                    });
                    continue;
                }
                let mut job = job - witness - direct_count;
                for (pattern, count) in patterns.iter().zip(&counts) {
                    if job >= *count {
                        job -= count;
                        continue;
                    }
                    let ground = &index.terms[index.by_head[&head(pattern).unwrap()][job]];
                    let mut bindings = captures.clone();
                    if unify(pattern, ground, &variables, &plan.signatures, &mut bindings) {
                        if let Some(values) = rule
                            .variables
                            .iter()
                            .map(|(v, _)| bindings.get(v).cloned())
                            .collect::<Option<Vec<_>>>()
                        {
                            instances.push(SymbolicInstance {
                                rule: QuantifiedRule::input_binder(&rule.name),
                                term: rule.instantiate(arguments, &values),
                                bindings: rule
                                    .captures
                                    .iter()
                                    .chain(&rule.variables)
                                    .map(|(v, _)| (v.0.clone(), bindings[v].clone()))
                                    .collect(),
                            });
                        }
                    }
                    break;
                }
            }
            *offset = (*offset + attempts) % count;
        }
        if !helpers.is_empty() {
            self.next_helper = (self.next_helper + visited) % helpers.len();
        }
        (instances, work)
    }
}

#[cfg(test)]
mod tests {
    use super::super::BinderRule;
    use super::*;
    use smt2parser::{concrete::Symbol, vmt::array_abstractor::string_to_sort};

    fn plan() -> QuantifierPlan {
        let arr = string_to_sort("Array_Int_Int");
        let int = string_to_sort("Int");
        let boolean = string_to_sort("Bool");
        let rule = BinderRule {
            name: "q".into(),
            kind: BinderKind::Forall,
            captures: vec![(Symbol("a".into()), arr.clone())],
            variables: vec![(Symbol("i".into()), int.clone())],
            body: "(= (Read_Int_Int a i) i)".parse().unwrap(),
            witnesses: vec!["w".into()],
            result_sort: boolean.clone(),
            unit_capture: false,
        };
        QuantifierPlan {
            rules: vec![rule],
            signatures: HashMap::from([
                ("q".into(), (vec![arr.clone()], boolean)),
                ("w".into(), (vec![arr.clone()], int.clone())),
                ("Read_Int_Int".into(), (vec![arr.clone(), int.clone()], int)),
                ("a@0".into(), (vec![], arr.clone())),
                ("b@0".into(), (vec![], arr)),
            ]),
            ..Default::default()
        }
    }

    #[test]
    fn ground_binders_preserve_exact_captures_and_reject_wrong_sorts() {
        let plan = plan();
        let mut search = GroundBinders::new(&plan);
        let terms = [
            "(q a@0)",
            "(Read_Int_Int a@0 7)",
            "(Read_Int_Int b@0 9)",
            "(Read_Int_Int a@0 true)",
        ]
        .map(|s| s.parse::<Term>().unwrap());
        let (instances, _) = search.generate(&plan, terms.iter().collect(), 100);
        let a = "a@0".parse::<Term>().unwrap();
        assert!(instances
            .iter()
            .any(|i| i.term == plan.rules[0].instantiate(&[a.clone()], &["7".parse().unwrap()])));
        assert!(instances
            .iter()
            .any(|i| i.term == plan.rules[0].witness_instance(&[a.clone()]).unwrap()));
        assert_eq!(instances.len(), 2);
        assert!(instances
            .iter()
            .all(|i| i.bindings.iter().any(|(s, t)| s == "a" && t == &a)));
    }

    #[test]
    fn ground_binders_resume_past_a_satisfied_prefix_with_tiny_budgets() {
        let plan = plan();
        let mut search = GroundBinders::new(&plan);
        let terms = ["(q a@0)", "(Read_Int_Int a@0 7)", "(Read_Int_Int a@0 8)"]
            .map(|s| s.parse::<Term>().unwrap());
        let mut seen = HashSet::new();
        for _ in 0..3 {
            let (instances, work) = search.generate(&plan, terms.iter().collect(), 1);
            assert_eq!(work, 1);
            seen.extend(instances.into_iter().map(|i| i.term));
        }
        assert_eq!(seen.len(), 3);
    }

    #[test]
    fn ground_binders_leave_incomplete_triggers_to_fallback() {
        let mut plan = plan();
        plan.rules[0]
            .variables
            .push((Symbol("j".into()), string_to_sort("Int")));
        plan.rules[0].witnesses.push("wj".into());
        plan.rules[0].body = "(= (Read_Int_Int a i) (Read_Int_Int a j))".parse().unwrap();
        let search = GroundBinders::new(&plan);
        assert!(
            search.patterns[0].is_empty(),
            "neither read determines the complete tuple"
        );
    }

    #[test]
    fn ground_binders_reject_noncanonical_dummy_captures() {
        let mut plan = plan();
        plan.rules[0].captures = vec![(Symbol("unit".into()), string_to_sort("Bool"))];
        plan.rules[0].unit_capture = true;
        plan.rules[0].body = "(= (Read_Int_Int a@0 i) i)".parse().unwrap();
        plan.signatures.get_mut("q").unwrap().0 = vec![string_to_sort("Bool")];
        plan.signatures.get_mut("w").unwrap().0 = vec![string_to_sort("Bool")];
        let mut search = GroundBinders::new(&plan);
        let terms = ["(q false)", "(Read_Int_Int a@0 7)"].map(|s| s.parse::<Term>().unwrap());
        assert!(search
            .generate(&plan, terms.iter().collect(), 100)
            .0
            .is_empty());
    }

    #[test]
    fn ground_binders_instantiate_lambda_reads_without_witnesses() {
        let mut plan = plan();
        plan.rules[0].kind = BinderKind::Lambda;
        plan.rules[0].result_sort = smt2parser::concrete::Sort::Parameterized {
            identifier: smt2parser::concrete::Identifier::Simple {
                symbol: Symbol("Array".into()),
            },
            parameters: vec![string_to_sort("Int"), string_to_sort("Int")],
        };
        plan.rules[0].body = "(+ (Read_Int_Int a i) 1)".parse().unwrap();
        plan.signatures.get_mut("q").unwrap().1 = string_to_sort("Array_Int_Int");
        let mut search = GroundBinders::new(&plan);
        let terms = ["(q a@0)", "(Read_Int_Int (q a@0) 7)"].map(|s| s.parse::<Term>().unwrap());
        let (instances, _) = search.generate(&plan, terms.iter().collect(), 100);
        assert_eq!(instances.len(), 1);
        assert_eq!(
            instances[0].term,
            plan.rules[0].instantiate(&["a@0".parse().unwrap()], &["7".parse().unwrap()])
        );
    }
    fn request(phase: SearchPhase, bindings: &[(&str, &str)]) -> BinderSearchRequest {
        BinderSearchRequest {
            helper: "q".into(),
            phase,
            bindings: bindings
                .iter()
                .map(|(v, t)| (Symbol((*v).into()), t.parse().unwrap()))
                .collect(),
        }
    }

    #[test]
    fn scheduled_exact_respects_helper_phase_and_capture_bindings() {
        let mut plan = plan();
        let mut other = plan.rules[0].clone();
        other.name = "other".into();
        plan.rules.push(other);
        let terms = [
            "(q a@0)",
            "(q b@0)",
            "(other a@0)",
            "(Read_Int_Int a@0 7)",
            "(Read_Int_Int b@0 9)",
        ]
        .map(|s| s.parse::<Term>().unwrap());
        let a = "a@0".parse::<Term>().unwrap();
        let mut witnesses =
            GroundBinders::for_request(&plan, request(SearchPhase::Witnesses, &[("a", "a@0")]))
                .unwrap();
        let (instances, _) = witnesses.generate(&plan, terms.iter().collect(), 100);
        assert_eq!(instances.len(), 1);
        assert_eq!(
            instances[0].term,
            plan.rules[0].witness_instance(&[a.clone()]).unwrap()
        );
        let mut ordinary = GroundBinders::for_request(
            &plan,
            request(SearchPhase::TriggeredConflicts, &[("a", "a@0")]),
        )
        .unwrap();
        let (instances, _) = ordinary.generate(&plan, terms.iter().collect(), 100);
        assert_eq!(instances.len(), 1);
        assert_eq!(
            instances[0].term,
            plan.rules[0].instantiate(&[a], &["7".parse().unwrap()])
        );
        assert_eq!(instances[0].rule.name(), "input-binder-q");
    }

    #[test]
    fn scheduled_exact_complete_requests_do_not_need_existing_helper_terms() {
        let plan = plan();
        let mut ordinary = GroundBinders::for_request(
            &plan,
            request(SearchPhase::Expand, &[("a", "a@0"), ("i", "42")]),
        )
        .unwrap();
        let (instances, work) = ordinary.generate(&plan, Vec::new(), 1);
        assert_eq!(work, 1);
        assert_eq!(instances.len(), 1);
        assert_eq!(
            instances[0].term,
            plan.rules[0].instantiate(&["a@0".parse().unwrap()], &["42".parse().unwrap()])
        );
    }

    #[test]
    fn scheduled_exact_rejects_invalid_requests_before_grounding() {
        let plan = plan();
        for r in [
            request(SearchPhase::Expand, &[("i", "true")]),
            request(SearchPhase::Expand, &[("i", "1"), ("i", "2")]),
            request(SearchPhase::Expand, &[("missing", "1")]),
            request(SearchPhase::Witnesses, &[("i", "1")]),
        ] {
            assert!(GroundBinders::for_request(&plan, r).is_err());
        }
    }

    #[test]
    fn scheduled_exact_partial_bindings_never_leak_other_tuples() {
        let plan = plan();
        let terms = [
            "(q a@0)",
            "(q b@0)",
            "(Read_Int_Int a@0 7)",
            "(Read_Int_Int a@0 9)",
        ]
        .map(|s| s.parse::<Term>().unwrap());
        let mut ground = GroundBinders::for_request(
            &plan,
            request(SearchPhase::TriggeredConflicts, &[("i", "7")]),
        )
        .unwrap();
        let (instances, work) = ground.generate(&plan, terms.iter().collect(), 2);
        assert!(work <= 2);
        assert_eq!(instances.len(), 2);
        assert!(instances.iter().all(|instance| instance
            .bindings
            .iter()
            .any(|(name, value)| name == "i" && value == &"7".parse::<Term>().unwrap())));
        assert!(instances
            .iter()
            .all(|instance| instance.rule.name() == "input-binder-q"));
    }
}
