//! Signed Boolean explanations of a property violation and enabled action.
//! Witness expansion preserves captures; no Cartesian product is introduced.
use super::{app, BinderKind, QuantifierPlan};
use crate::{
    rule_matching::candidate::SymbolicInstance, rule_matching::rule::QuantifiedRule,
    theories::quantifiers::dependency_search::Goal, transition_index::TransitionIndex,
};
use smt2parser::concrete::Term;
use std::collections::{HashMap, HashSet, VecDeque};

pub(crate) struct ObligationExplanation {
    pub goals: Vec<Goal>,
    pub instances: Vec<SymbolicInstance>,
    pub constrained: Vec<(Term, bool)>,
    pub pending: Vec<(Term, bool)>,
}

impl QuantifierPlan {
    #[cfg(test)]
    pub(crate) fn explain_obligations(
        &self,
        roots: Vec<(Term, bool)>,
        index: &TransitionIndex,
        assertions: Vec<&Term>,
        evaluate: impl FnMut(&Term) -> anyhow::Result<String>,
        budget: usize,
    ) -> anyhow::Result<ObligationExplanation> {
        self.explain_slice(
            roots,
            index,
            &self.ground_instance_bodies(assertions),
            evaluate,
            budget,
        )
    }

    pub(crate) fn explain_slice(
        &self,
        roots: Vec<(Term, bool)>,
        index: &TransitionIndex,
        ground_bodies: &HashMap<Term, Vec<Term>>,
        mut evaluate: impl FnMut(&Term) -> anyhow::Result<String>,
        budget: usize,
    ) -> anyhow::Result<ObligationExplanation> {
        let mut queue = VecDeque::from(roots);
        let mut seen = HashSet::new();
        let mut demands = Vec::new();
        let mut instances = Vec::new();
        let mut work = 0;
        let mut constrained = Vec::new();
        while work < budget {
            let Some((term, truth)) = queue.pop_front() else {
                break;
            };
            if !seen.insert((term.clone(), truth)) {
                continue;
            }
            work += 1;
            if let Some(expanded) = index.expand_framed_leaf(&term) {
                queue.push_back((expanded, truth));
                continue;
            }
            if let Term::Attributes { term, .. } = term {
                queue.push_back((*term, truth));
                continue;
            }
            let Term::Application {
                qual_identifier,
                arguments,
            } = &term
            else {
                continue;
            };
            let name = qual_identifier.get_name();
            if let Some(rule) = self.rules.iter().find(|r| r.name == name) {
                if matches!(
                    (rule.kind, truth),
                    (BinderKind::Forall, true) | (BinderKind::Exists, false)
                ) {
                    constrained.push((term.clone(), truth));
                }
                if matches!(
                    (rule.kind, truth),
                    (BinderKind::Forall, false) | (BinderKind::Exists, true)
                ) {
                    let instance = rule.witness_instance(arguments).unwrap();
                    let Term::Application {
                        arguments: implication,
                        ..
                    } = &instance
                    else {
                        unreachable!()
                    };
                    queue.push_back((implication[1].clone(), true));
                    instances.push(SymbolicInstance {
                        rule: QuantifiedRule::input_binder(&rule.name),
                        term: instance,
                        bindings: rule
                            .captures
                            .iter()
                            .zip(arguments)
                            .map(|((s, _), t)| (s.0.clone(), t.clone()))
                            .collect(),
                    });
                } else if let Some(bodies) = ground_bodies.get(&term) {
                    // A true universal (or false existential) constrains each
                    // already asserted tuple. Keep the exact capture/frame
                    // application as the key; model equality is insufficient.
                    queue.extend(bodies.iter().map(|body| (body.clone(), truth)));
                }
                continue;
            }
            match (name.as_str(), arguments.as_slice()) {
                ("not", [inner]) => queue.push_back((inner.clone(), !truth)),
                ("and" | "or", args) => {
                    let all = (name == "and") == truth;
                    for arg in args {
                        if all || evaluate(arg)?.trim() == if truth { "true" } else { "false" } {
                            queue.push_back((arg.clone(), truth));
                        }
                    }
                }
                ("=>", [left, right]) => {
                    queue.push_back((
                        app("or", vec![app("not", vec![left.clone()]), right.clone()]),
                        truth,
                    ));
                }
                ("ite", [condition, yes, no]) => {
                    let enabled = evaluate(condition)?.trim() == "true";
                    queue.push_back((condition.clone(), enabled));
                    queue.push_back((if enabled { yes } else { no }.clone(), truth));
                }
                _ => demands.push(Goal::new(&term, !truth)),
            }
        }
        Ok(ObligationExplanation {
            goals: demands,
            instances,
            constrained,
            pending: queue.into(),
        })
    }

    pub(crate) fn ground_instance_bodies(
        &self,
        assertions: Vec<&Term>,
    ) -> HashMap<Term, Vec<Term>> {
        let kinds = self
            .rules
            .iter()
            .map(|r| (r.name.as_str(), r.kind))
            .collect::<HashMap<_, _>>();
        let mut bodies = HashMap::<Term, Vec<Term>>::new();
        let mut queue = VecDeque::from(assertions);
        while let Some(term) = queue.pop_front() {
            match term {
                Term::Attributes { term, .. } => queue.push_back(term),
                Term::Application {
                    qual_identifier,
                    arguments,
                } if qual_identifier.get_name() == "and" => queue.extend(arguments),
                Term::Application {
                    qual_identifier,
                    arguments,
                } if qual_identifier.get_name() == "=>" && arguments.len() == 2 => {
                    for (head, body, kind) in [
                        (&arguments[0], &arguments[1], BinderKind::Forall),
                        (&arguments[1], &arguments[0], BinderKind::Exists),
                    ] {
                        if let Term::Application {
                            qual_identifier, ..
                        } = head
                        {
                            if kinds.get(qual_identifier.get_name().as_str()) == Some(&kind) {
                                bodies.entry(head.clone()).or_default().push(body.clone());
                            }
                        }
                    }
                }
                // Do not collect formulas underneath a conditional or binder:
                // only top-level conjuncts are themselves asserted facts.
                _ => {}
            }
        }
        bodies
    }

    /// Fully bound dependency links can be constructed without consulting an
    /// e-class or requiring a model violation at discovery time.
    pub(crate) fn dependency_instance(
        &self,
        request: &super::BinderSearchRequest,
    ) -> Option<SymbolicInstance> {
        let rule = self.rules.iter().find(|rule| rule.name == request.helper)?;
        let bindings = request
            .bindings
            .iter()
            .cloned()
            .collect::<std::collections::HashMap<_, _>>();
        let captures = rule
            .captures
            .iter()
            .map(|(s, _)| bindings.get(s).cloned())
            .collect::<Option<Vec<_>>>()?;
        let values = rule
            .variables
            .iter()
            .map(|(s, _)| bindings.get(s).cloned())
            .collect::<Option<Vec<_>>>()?;
        Some(SymbolicInstance {
            rule: QuantifiedRule::input_binder(&rule.name),
            term: rule.instantiate(&captures, &values),
            bindings: request
                .bindings
                .iter()
                .map(|(s, t)| (s.0.clone(), t.clone()))
                .collect(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theories::quantifiers::{BinderKind, BinderRule};
    use smt2parser::{concrete::Symbol, vmt::array_abstractor::string_to_sort};

    #[test]
    fn follows_asserted_tuples_with_exact_captures_and_signed_bodies() {
        let make_rule = |name: &str, kind| BinderRule {
            name: name.into(),
            kind,
            captures: vec![(Symbol("a".into()), string_to_sort("Bool"))],
            variables: vec![(Symbol("x".into()), string_to_sort("Bool"))],
            body: "(p a x)".parse().unwrap(),
            witnesses: vec![format!("{name}_witness")],
            result_sort: string_to_sort("Bool"),
            unit_capture: false,
        };
        let plan = QuantifierPlan {
            rules: vec![
                make_rule("all", BinderKind::Forall),
                make_rule("some", BinderKind::Exists),
            ],
            ..Default::default()
        };
        let asserted: Term = "(and (=> (all a@1) (p a@1 n)) (=> (all a@0) (p a@0 old)) (=> (p a@1 m) (some a@1)) (=> disabled (=> (all a@1) (p a@1 hidden))))".parse().unwrap();
        let ObligationExplanation {
            goals,
            instances,
            constrained,
            ..
        } = plan
            .explain_obligations(
                vec![
                    ("(all a@1)".parse().unwrap(), true),
                    ("(some a@1)".parse().unwrap(), false),
                ],
                &TransitionIndex::default(),
                vec![&asserted],
                |_| panic!("atomic ground bodies need no model evaluation"),
                64,
            )
            .unwrap();
        assert!(
            instances.is_empty(),
            "following asserted bodies must not create new axioms"
        );
        assert_eq!(
            constrained,
            vec![
                ("(all a@1)".parse().unwrap(), true),
                ("(some a@1)".parse().unwrap(), false)
            ]
        );

        assert_eq!(
            goals,
            vec![
                Goal::new(&"(p a@1 n)".parse().unwrap(), false),
                Goal::new(&"(p a@1 m)".parse().unwrap(), true),
            ]
        );
    }

    #[test]
    fn only_relevant_signed_branches_expand_witnesses() {
        let plan = QuantifierPlan {
            rules: vec![BinderRule {
                name: "all".into(),
                kind: BinderKind::Forall,
                captures: vec![(Symbol("a".into()), string_to_sort("Bool"))],
                variables: vec![(Symbol("x".into()), string_to_sort("Bool"))],
                body: "(p a x)".parse().unwrap(),
                witnesses: vec!["witness".into()],
                result_sort: string_to_sort("Bool"),
                unit_capture: false,
            }],
            ..Default::default()
        };
        let mut evaluate = |term: &Term| -> anyhow::Result<String> {
            Ok(match term.to_string().as_str() {
                "(not (all true))" => "true",
                "(all false)" => "false",
                "c" => "false",
                other => panic!("unexpected evaluation {other}"),
            }
            .into())
        };
        // A true disjunction does not demand its false alternative. The true
        // negated universal does demand its false body at a Skolem witness.
        let ObligationExplanation {
            goals, instances, ..
        } = plan
            .explain_obligations(
                vec![("(or (not (all true)) (all false))".parse().unwrap(), true)],
                &TransitionIndex::default(),
                vec![],
                &mut evaluate,
                64,
            )
            .unwrap();
        assert_eq!(instances.len(), 1);
        assert_eq!(
            goals,
            vec![Goal::new(&"(p true (witness true))".parse().unwrap(), true)]
        );
        assert!(!instances[0].term.to_string().contains("all false"));
        // True universals do not gain arbitrary witness tuples.
        let ObligationExplanation { instances, .. } = plan
            .explain_obligations(
                vec![(
                    "(ite c (not (all true)) (all false))".parse().unwrap(),
                    true,
                )],
                &TransitionIndex::default(),
                vec![],
                &mut evaluate,
                64,
            )
            .unwrap();
        assert!(instances.is_empty());
    }
}
