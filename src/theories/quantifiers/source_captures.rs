//! Ground a closure's captures from one intact source application. A model
//! equality is a matching hint, never an asserted equality or a new capture.
use std::collections::{HashMap, HashSet};

use super::{compiled_rule::CompiledBinderRule, QuantifierPlan};
use crate::terms::language::{translate_term_with_array_types, TermExpr, TermLanguage};
use smt2parser::concrete::Term;

#[derive(Default)]
pub(super) struct SourceCaptures {
    tuples: HashMap<String, Vec<Vec<(egg::Var, TermExpr)>>>,
}

impl SourceCaptures {
    pub(super) fn new(
        plan: &QuantifierPlan,
        roots: Vec<&Term>,
        types: &[(String, String)],
    ) -> Self {
        let arities = plan
            .rules
            .iter()
            .map(|r| (r.name.as_str(), r.captures.len()))
            .collect::<HashMap<_, _>>();
        let mut helpers = HashSet::new();
        fn visit(term: &Term, arities: &HashMap<&str, usize>, helpers: &mut HashSet<Term>) {
            match term {
                Term::Application {
                    qual_identifier,
                    arguments,
                } => {
                    if arities.get(qual_identifier.get_name().as_str()) == Some(&arguments.len()) {
                        helpers.insert(term.clone());
                    }
                    for arg in arguments {
                        visit(arg, arities, helpers);
                    }
                }
                Term::Attributes { term, .. } => visit(term, arities, helpers),
                _ => {}
            }
        }
        for root in roots {
            visit(root, &arities, &mut helpers);
        }
        let mut helpers = helpers.into_iter().collect::<Vec<_>>();
        helpers.sort_by_cached_key(ToString::to_string);
        let mut result = Self::default();
        for helper in helpers {
            let Term::Application {
                qual_identifier,
                arguments,
            } = helper
            else {
                unreachable!()
            };
            let bindings = arguments
                .into_iter()
                .enumerate()
                .map(|(i, arg)| {
                    Some((
                        format!("?binding{i}").parse().unwrap(),
                        translate_term_with_array_types(arg, types)?,
                    ))
                })
                .collect::<Option<Vec<_>>>();
            if let Some(bindings) = bindings {
                result
                    .tuples
                    .entry(qual_identifier.get_name())
                    .or_default()
                    .push(bindings);
            }
        }
        result
    }

    pub(super) fn preferred(
        &self,
        rule: &CompiledBinderRule<()>,
        substitution: &egg::Subst,
        graph: &egg::EGraph<TermLanguage, ()>,
    ) -> Vec<(egg::Var, TermExpr)> {
        let crate::rule_matching::rule::QuantifiedRuleProvenance::InputBinder { helper } =
            rule.metadata().provenance()
        else {
            return vec![];
        };
        let Some(tuples) = self.tuples.get(helper) else {
            return vec![];
        };
        // Check the whole capture tuple before choosing any of its arguments.
        // Directed requests keep their literal bindings; only unfixed formula
        // variables are supplied to ordinary representative extraction.
        for tuple in tuples {
            let compatible = tuple.iter().all(|(var, expression)| {
                let expected = substitution
                    .get(*var)
                    .map(|id| graph.find(*id))
                    .or_else(|| {
                        rule.fixed_bindings()
                            .iter()
                            .find(|(v, _)| v == var)
                            .and_then(|(_, e)| graph.lookup_expr(e))
                            .map(|id| graph.find(id))
                    });
                expected.is_some()
                    && graph.lookup_expr(expression).map(|id| graph.find(id)) == expected
            });
            if compatible {
                return tuple
                    .iter()
                    .filter(|(var, _)| rule.formula_variables().contains(var))
                    .cloned()
                    .collect();
            }
        }
        // A derived/nested helper may have no source counterpart. Retain the
        // existing search in that case; this preference is not a scope filter.
        vec![]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theories::quantifiers::{app, BinderKind, BinderRule, SearchPhase};
    use smt2parser::{concrete::Symbol, vmt::array_abstractor::string_to_sort};

    #[test]
    fn capture_preference_keeps_tuples_and_respects_model_and_literal_bindings() {
        let rule = BinderRule {
            name: "q".into(),
            kind: BinderKind::Forall,
            captures: vec![
                (Symbol("a".into()), string_to_sort("Int")),
                (Symbol("b".into()), string_to_sort("Int")),
            ],
            variables: vec![(Symbol("x".into()), string_to_sort("Int"))],
            body: "(or (= x a) (= x b))".parse().unwrap(),
            witnesses: vec!["w".into()],
            result_sort: string_to_sort("Bool"),
            unit_capture: false,
        };
        let plan = QuantifierPlan {
            rules: vec![rule.clone()],
            ..Default::default()
        };
        let roots = [
            "(q source_a source_b)".parse().unwrap(),
            "(q other_a other_b)".parse().unwrap(),
        ];
        let captures = SourceCaptures::new(&plan, roots.iter().collect(), &[]);
        let compiled = rule.compile(SearchPhase::Conflicts, &[]).unwrap().unwrap();
        let mut graph = egg::EGraph::<TermLanguage, ()>::default();
        let mut ids = HashMap::new();
        for name in [
            "source_a", "source_b", "other_a", "other_b", "alias_a", "alias_b", "value",
        ] {
            ids.insert(name, graph.add_expr(&name.parse().unwrap()));
        }
        graph.rebuild();
        let mut substitution = egg::Subst::default();
        for (i, name) in ["alias_a", "alias_b", "value"].iter().enumerate() {
            substitution.insert(format!("?binding{i}").parse().unwrap(), ids[name]);
        }
        assert!(captures
            .preferred(&compiled, &substitution, &graph)
            .is_empty());
        graph.union(ids["alias_a"], ids["source_a"]);
        graph.union(ids["alias_b"], ids["source_b"]);
        graph.rebuild();
        let chosen = captures.preferred(&compiled, &substitution, &graph);
        assert_eq!(
            chosen
                .iter()
                .map(|(_, e)| e.to_string())
                .collect::<Vec<_>>(),
            ["source_a", "source_b"]
        );
        // Never assemble a source tuple from different helper applications.
        substitution.insert("?binding1".parse().unwrap(), ids["other_b"]);
        assert!(captures
            .preferred(&compiled, &substitution, &graph)
            .is_empty());
        substitution.insert("?binding1".parse().unwrap(), ids["alias_b"]);
        let directed = rule
            .compile_with_bindings(
                SearchPhase::Conflicts,
                &[],
                &[(Symbol("a".into()), app("alias_a", vec![]))],
            )
            .unwrap()
            .unwrap();
        let chosen = captures.preferred(&directed, &substitution, &graph);
        assert_eq!(chosen.len(), 1);
        assert_eq!(chosen[0].0.to_string(), "?binding1");
        assert_eq!(chosen[0].1.to_string(), "source_b");
    }
}
