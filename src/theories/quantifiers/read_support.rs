//! Source-capture instances over a frozen typed index pool. Single-variable
//! universals are a fast path; other binders retain ordinary guided search.
use super::{BinderKind, QuantifierPlan};
use crate::rule_matching::{
    candidate::SymbolicInstance, rule::QuantifiedRule, source_terms::SourceTerms,
};
use smt2parser::concrete::Term;
use std::{collections::VecDeque, rc::Rc};

struct Cursor {
    rule: usize,
    captures: Vec<Term>,
    indices: Rc<Vec<Term>>,
    next: usize,
}
#[derive(Default)]
pub(crate) struct QuantifierReadSupport {
    jobs: VecDeque<Cursor>,
}
impl QuantifierReadSupport {
    pub fn new(plan: &QuantifierPlan, source: &SourceTerms, types: &[(String, String)]) -> Self {
        let mut jobs = VecDeque::new();
        for (index, rule) in plan.rules.iter().enumerate() {
            if rule.kind != BinderKind::Forall || rule.variables.len() != 1 {
                continue;
            }
            if !indexes_read(&rule.body, &rule.variables[0].0 .0, types) {
                continue;
            }
            let Some(indices) = source
                .pools
                .get(&rule.variables[0].1)
                .filter(|v| !v.is_empty())
            else {
                continue;
            };
            for helper in source.applications.get(&rule.name).into_iter().flatten() {
                let Term::Application { arguments, .. } = helper else {
                    unreachable!()
                };
                if arguments.len() != rule.captures.len()
                    || (rule.unit_capture && arguments[0].to_string() != "true")
                {
                    continue;
                }
                jobs.push_back(Cursor {
                    rule: index,
                    captures: arguments.clone(),
                    indices: indices.clone(),
                    next: 0,
                });
            }
        }
        Self { jobs }
    }
    pub fn pending(&self) -> bool {
        !self.jobs.is_empty()
    }
    pub fn next(&mut self, plan: &QuantifierPlan) -> Option<SymbolicInstance> {
        let mut job = self.jobs.pop_front()?;
        let rule = &plan.rules[job.rule];
        let index = job.indices[job.next].clone();
        let instance = SymbolicInstance {
            rule: QuantifiedRule::input_binder(&rule.name),
            term: rule.instantiate(&job.captures, std::slice::from_ref(&index)),
            bindings: rule
                .captures
                .iter()
                .map(|(s, _)| s.0.clone())
                .zip(job.captures.iter().cloned())
                .chain(std::iter::once((rule.variables[0].0 .0.clone(), index)))
                .collect(),
        };
        job.next += 1;
        if job.next < job.indices.len() {
            self.jobs.push_back(job);
        }
        Some(instance)
    }
}

/// Lowered binder bodies have globally fresh bound names and no nested binders.
/// This is a search preference only: ineligible binders keep ordinary search.
fn indexes_read(term: &Term, variable: &str, types: &[(String, String)]) -> bool {
    match term {
        Term::Application { arguments, .. } => {
            (crate::theories::array::countermodel::is_read(term, types)
                && contains_symbol(&arguments[1], variable))
                || arguments
                    .iter()
                    .any(|term| indexes_read(term, variable, types))
        }
        Term::Attributes { term, .. } => indexes_read(term, variable, types),
        _ => false,
    }
}

fn contains_symbol(term: &Term, variable: &str) -> bool {
    if crate::transition_index::leaf_symbol(term).as_deref() == Some(variable) {
        return true;
    }
    match term {
        Term::Application { arguments, .. } => {
            arguments.iter().any(|term| contains_symbol(term, variable))
        }
        Term::Attributes { term, .. } => contains_symbol(term, variable),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theories::quantifiers::BinderRule;
    use smt2parser::{concrete::Symbol, vmt::array_abstractor::string_to_sort};
    #[test]
    fn source_tuples_are_intact_and_cursor_resumes_without_derived_feedback() {
        let mut plan = QuantifierPlan::default();
        plan.rules.push(BinderRule {
            name: "q".into(),
            kind: BinderKind::Forall,
            captures: vec![(Symbol("a".into()), string_to_sort("Array_Int_Int"))],
            variables: vec![(Symbol("i".into()), string_to_sort("Int"))],
            body: "(= (Read_Int_Int a i) 7)".parse().unwrap(),
            witnesses: vec![],
            result_sort: string_to_sort("Bool"),
            unit_capture: false,
        });
        let mut source = SourceTerms::default();
        source.pools.insert(
            string_to_sort("Int"),
            Rc::new(vec!["5".parse().unwrap(), "6".parse().unwrap()]),
        );
        source.applications.insert(
            "q".into(),
            vec!["(q a@0)".parse().unwrap(), "(q a@1)".parse().unwrap()],
        );
        let mut support =
            QuantifierReadSupport::new(&plan, &source, &[("Int".into(), "Int".into())]);
        let first = support.next(&plan).unwrap();
        assert_eq!(
            first.term.to_string(),
            "(=> (q a@0) (= (Read_Int_Int a@0 5) 7))"
        );
        let mut n = 1;
        while let Some(_) = support.next(&plan) {
            n += 1;
            assert!(n <= 4);
        }
        assert_eq!(n, 4);
        assert!(!support.pending());
    }

    #[test]
    fn relevance_requires_a_typed_read_index_not_a_value_or_unrelated_read() {
        let types = [("Int".into(), "Int".into())];
        for body in [
            "(= (Read_Int_Int a i) 7)",
            "(= (Read_Int_Int a (+ i 1)) 7)",
            "(and p (= (Read_Int_Int a (Read_Int_Int b i)) 7))",
        ] {
            assert!(indexes_read(&body.parse().unwrap(), "i", &types));
        }
        for body in [
            "(or (= i op1) (= i op2))",
            "(= (Read_Int_Int a 0) i)",
            "(= (Read_Int_Int a j) i)",
            "(Read_fake a i)",
        ] {
            assert!(!indexes_read(&body.parse().unwrap(), "i", &types));
        }
    }
}
