//! Symbolic index preferences from this model's read trace. No model value or
//! equality is asserted, and ordinary domains remain available as fallback.
use super::{BinderSearchRequest, QuantifierPlan, SearchPhase};
use crate::countermodel::CountermodelTrace;
use smt2parser::concrete::{Sort, Term};
use std::collections::{HashMap, HashSet};

#[derive(Default)]
pub(super) struct DemandedIndices {
    terms: Vec<(Sort, Term)>,
    attempted: HashSet<BinderSearchRequest>,
}

impl DemandedIndices {
    pub fn new(trace: &CountermodelTrace, plan: &QuantifierPlan) -> Self {
        let mut seen = HashSet::new();
        let mut terms = Vec::new();
        for node in &trace.nodes {
            if let Term::Application {
                qual_identifier,
                arguments,
            } = &node.expression
            {
                if qual_identifier.get_name().starts_with("Read_") && arguments.len() == 2 {
                    let index = &arguments[1];
                    if seen.insert(index.clone()) {
                        if let Ok(sort) = super::term_sort(index, &plan.signatures, &HashMap::new())
                        {
                            terms.push((sort, index.clone()));
                        }
                    }
                }
            }
        }
        // Prefer shallow demanded terms without excluding a legitimate nested
        // index. Stable sorting preserves trace order for equally small terms.
        terms.sort_by_key(|(_, term)| size(term));
        Self {
            terms,
            attempted: HashSet::new(),
        }
    }

    pub fn mark_attempted(&mut self, request: &BinderSearchRequest) {
        self.attempted.insert(request.clone());
    }

    pub fn requests(
        &self,
        plan: &QuantifierPlan,
        helper: &str,
        phase: SearchPhase,
        limit: usize,
    ) -> Vec<BinderSearchRequest> {
        if phase == SearchPhase::Witnesses || limit == 0 {
            return Vec::new();
        }
        let Some(rule) = plan.rules.iter().find(|r| r.name == helper) else {
            return Vec::new();
        };
        let mut result = Vec::new();
        for (sort, term) in &self.terms {
            for (variable, expected) in &rule.variables {
                if sort != expected {
                    continue;
                }
                let request = BinderSearchRequest {
                    helper: helper.to_owned(),
                    phase,
                    bindings: vec![(variable.clone(), term.clone())],
                };
                if !self.attempted.contains(&request) {
                    result.push(request);
                    if result.len() == limit {
                        return result;
                    }
                }
            }
        }
        result
    }
}

fn size(term: &Term) -> usize {
    match term {
        Term::Application { arguments, .. } => 1 + arguments.iter().map(size).sum::<usize>(),
        Term::Attributes { term, .. } => size(term),
        _ => 1,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theories::quantifiers::{BinderKind, BinderRule};
    use smt2parser::{concrete::Symbol, vmt::array_abstractor::string_to_sort};

    #[test]
    fn preferences_are_typed_resume_and_keep_nested_indices_and_other_directions() {
        let int = string_to_sort("Int");
        let mut plan = QuantifierPlan::default();
        plan.rules.push(BinderRule {
            name: "q".into(),
            kind: BinderKind::Forall,
            captures: vec![],
            variables: vec![(Symbol("i".into()), int.clone())],
            body: "(= i i)".parse().unwrap(),
            witnesses: vec![],
            result_sort: string_to_sort("Bool"),
            unit_capture: false,
        });
        let mut indices = DemandedIndices {
            terms: vec![
                (string_to_sort("Bool"), "true".parse().unwrap()),
                (int.clone(), "4".parse().unwrap()),
                (int, "(+ 4 1)".parse().unwrap()),
            ],
            attempted: HashSet::new(),
        };
        assert!(indices
            .requests(&plan, "q", SearchPhase::Witnesses, 4)
            .is_empty());
        let first = indices.requests(&plan, "q", SearchPhase::Conflicts, 1);
        assert_eq!(first[0].bindings[0].1.to_string(), "4");
        indices.mark_attempted(&first[0]);
        let second = indices.requests(&plan, "q", SearchPhase::Conflicts, 1);
        assert_eq!(second[0].bindings[0].1.to_string(), "(+ 4 1)");
        indices.mark_attempted(&second[0]);
        assert!(indices
            .requests(&plan, "q", SearchPhase::Conflicts, 4)
            .is_empty());
        assert_eq!(
            indices
                .requests(&plan, "q", SearchPhase::TriggeredConflicts, 4)
                .len(),
            2
        );
    }
}
