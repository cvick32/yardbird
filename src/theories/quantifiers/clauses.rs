//! Join signed frontier atoms to bind universal and existential instances. This
//! searches atoms already demanded by the explanation, not sort products.
use super::{
    dependency_search::{unify_capture_hints, unify_modulo, Goal},
    substitute, BinderKind, QuantifierPlan,
};
use crate::{
    problem_context::ProblemContext,
    rule_matching::{candidate::SymbolicInstance, rule::QuantifiedRule},
};
use smt2parser::concrete::{Symbol, Term};
use std::collections::{HashMap, HashSet, VecDeque};

/// Flatten a single disjunctive clause, preserving signs through negation.
/// Non-clausal bodies remain with the existing general search.
fn literals(term: &Term, truth: bool, result: &mut Vec<Goal>) -> bool {
    if let Term::Application {
        qual_identifier,
        arguments,
    } = term
    {
        match (qual_identifier.get_name().as_str(), arguments.as_slice()) {
            ("not", [inner]) => return literals(inner, !truth, result),
            ("or", args) if truth => return args.iter().all(|a| literals(a, truth, result)),
            ("and", args) if !truth => return args.iter().all(|a| literals(a, truth, result)),
            ("=>", [a, b]) if truth => {
                return literals(a, false, result) && literals(b, true, result)
            }
            ("and" | "or" | "=>" | "ite", _) => return false,
            _ => {}
        }
    }
    result.push(Goal::new(term, truth));
    true
}

/// Model-independent typed joins. New atoms and partial bindings schedule only
/// previously unseen pairs; exhausting a slice leaves the queue intact.
#[derive(Default)]
pub(crate) struct ClauseAgenda {
    clauses: Vec<Clause>,
    helpers: HashSet<Term>,
    goals: Vec<Goal>,
    frontier: HashMap<(String, bool), Vec<usize>>,
    queue: VecDeque<(usize, usize, usize, usize)>,
    scheduled: HashSet<(usize, usize, usize, usize)>,
}

struct Clause {
    rule: usize,
    arguments: Vec<Term>,
    captures: HashSet<Term>,
    patterns: Vec<Goal>,
    variables: HashMap<Symbol, smt2parser::concrete::Sort>,
    bindings: Vec<HashMap<Symbol, Term>>,
    seen: HashSet<Vec<Option<Term>>>,
}

impl ClauseAgenda {
    pub fn add_helper(&mut self, plan: &QuantifierPlan, helper: &Term) {
        self.add_clause(plan, helper, BinderKind::Forall, 2);
    }

    /// Search the ordinary instance direction of an observed helper. Captures
    /// come from that exact application; only quantified variables are joined.
    pub fn add_demand(&mut self, plan: &QuantifierPlan, helper: &Term, truth: bool) -> bool {
        self.add_clause(
            plan,
            helper,
            if truth {
                BinderKind::Forall
            } else {
                BinderKind::Exists
            },
            1,
        )
    }

    fn add_clause(
        &mut self,
        plan: &QuantifierPlan,
        helper: &Term,
        kind: BinderKind,
        minimum: usize,
    ) -> bool {
        let Term::Application {
            qual_identifier,
            arguments,
        } = helper
        else {
            return false;
        };
        let Some((rule_id, rule)) = plan
            .rules
            .iter()
            .enumerate()
            .find(|(_, r)| r.name == qual_identifier.get_name() && r.kind == kind)
        else {
            return false;
        };
        let mut patterns = Vec::new();
        if !literals(&rule.body, kind == BinderKind::Forall, &mut patterns)
            || patterns.len() < minimum
        {
            return false;
        }
        if !self.helpers.insert(helper.clone()) {
            return true;
        }
        let captures = rule
            .captures
            .iter()
            .map(|(s, _)| s.clone())
            .zip(arguments.iter().cloned())
            .collect::<Vec<_>>();
        let patterns = patterns
            .into_iter()
            .map(|g| Goal::new(&substitute(g.atom, captures.clone()), g.truth))
            .collect();
        let id = self.clauses.len();
        self.clauses.push(Clause {
            rule: rule_id,
            arguments: arguments.clone(),
            captures: arguments.iter().cloned().collect(),
            patterns,
            variables: rule.variables.iter().cloned().collect(),
            bindings: vec![HashMap::new()],
            seen: HashSet::new(),
        });
        self.schedule_binding(id, 0);
        true
    }

    pub fn wants(&self, atom: &Term) -> bool {
        let Some((name, _)) = Goal::new(atom, true).key() else {
            return false;
        };
        self.clauses.iter().any(|clause| {
            clause
                .patterns
                .iter()
                .any(|pattern| pattern.key().is_some_and(|(head, _)| head == name))
        })
    }

    pub fn add_goal(&mut self, goal: Goal) {
        let Some(key) = goal.key() else { return };
        let id = self.goals.len();
        self.goals.push(goal);
        self.frontier.entry(key.clone()).or_default().push(id);
        for (c, clause) in self.clauses.iter().enumerate() {
            for (p, pattern) in clause.patterns.iter().enumerate() {
                if pattern.key().as_ref() != Some(&key) {
                    continue;
                }
                for b in 0..clause.bindings.len() {
                    let job = (c, b, p, id);
                    if self.scheduled.insert(job) {
                        self.queue.push_back(job);
                    }
                }
            }
        }
    }

    fn schedule_binding(&mut self, c: usize, b: usize) {
        for (p, pattern) in self.clauses[c].patterns.iter().enumerate() {
            for &g in pattern
                .key()
                .and_then(|k| self.frontier.get(&k))
                .into_iter()
                .flatten()
            {
                let job = (c, b, p, g);
                if self.scheduled.insert(job) {
                    self.queue.push_back(job);
                }
            }
        }
    }

    pub fn pending(&self) -> usize {
        self.queue.len()
    }

    pub fn step(&mut self, plan: &QuantifierPlan) -> Option<SymbolicInstance> {
        self.step_modulo(plan, |_, _| false)
    }

    pub fn step_modulo(
        &mut self,
        plan: &QuantifierPlan,
        equivalent: impl FnMut(&Term, &Term) -> bool,
    ) -> Option<SymbolicInstance> {
        self.step_inner(plan, equivalent, false)
    }

    /// Propose tuples from structurally matching observations even when their
    /// captured state differs. The result is a hint, not a verified violation.
    pub fn step_capture_hints(
        &mut self,
        plan: &QuantifierPlan,
        equivalent: impl FnMut(&Term, &Term) -> bool,
    ) -> Option<SymbolicInstance> {
        self.step_inner(plan, equivalent, true)
    }

    fn step_inner(
        &mut self,
        plan: &QuantifierPlan,
        mut equivalent: impl FnMut(&Term, &Term) -> bool,
        capture_hints: bool,
    ) -> Option<SymbolicInstance> {
        let (c, b, p, g) = self.queue.pop_front()?;
        let clause = &mut self.clauses[c];
        let mut joined = clause.bindings[b].clone();
        let matched = if capture_hints {
            unify_capture_hints(
                &clause.patterns[p].atom,
                &self.goals[g].atom,
                &clause.variables,
                &plan.signatures,
                &mut joined,
                &mut equivalent,
                &clause.captures,
            )
        } else {
            unify_modulo(
                &clause.patterns[p].atom,
                &self.goals[g].atom,
                &clause.variables,
                &plan.signatures,
                &mut joined,
                &mut equivalent,
            )
        };
        if !matched || joined.len() == clause.bindings[b].len() {
            return None;
        }
        let rule = &plan.rules[clause.rule];
        let key = rule
            .variables
            .iter()
            .map(|(v, _)| joined.get(v).cloned())
            .collect::<Vec<_>>();
        if !clause.seen.insert(key) {
            return None;
        }
        if rule.variables.iter().all(|(v, _)| joined.contains_key(v)) {
            let values = rule
                .variables
                .iter()
                .map(|(v, _)| joined[v].clone())
                .collect::<Vec<_>>();
            return Some(SymbolicInstance {
                rule: QuantifiedRule::input_binder(&rule.name),
                term: rule.instantiate(&clause.arguments, &values),
                bindings: rule
                    .captures
                    .iter()
                    .chain(&rule.variables)
                    .map(|(s, _)| s.0.clone())
                    .zip(clause.arguments.iter().chain(&values).cloned())
                    .collect(),
            });
        }
        let id = clause.bindings.len();
        clause.bindings.push(joined);
        self.schedule_binding(c, id);
        None
    }
}

pub(crate) fn source_helpers(plan: &QuantifierPlan, smt: &dyn ProblemContext) -> Vec<Term> {
    let names = plan
        .rules
        .iter()
        .map(|r| r.name.as_str())
        .collect::<HashSet<_>>();
    let mut queue = VecDeque::from(smt.get_source_subterms());
    let mut seen = HashSet::new();
    let mut result = Vec::new();
    while let Some(term) = queue.pop_front() {
        if !seen.insert(term) {
            continue;
        }
        if let Term::Application {
            qual_identifier,
            arguments,
        } = term
        {
            if names.contains(qual_identifier.get_name().as_str()) {
                result.push(term.clone());
            }
            queue.extend(arguments);
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn new_frontier_atom_wakes_a_partial_tuple() {
        use super::super::{app, BinderRule};
        use smt2parser::vmt::array_abstractor::string_to_sort;
        let rule = BinderRule {
            name: "q".into(),
            kind: BinderKind::Forall,
            captures: vec![(Symbol("unit".into()), string_to_sort("Bool"))],
            variables: vec![
                (Symbol("x".into()), string_to_sort("Int")),
                (Symbol("y".into()), string_to_sort("Int")),
            ],
            body: "(=> (p x) (r y))".parse().unwrap(),
            witnesses: vec![],
            result_sort: string_to_sort("Bool"),
            unit_capture: true,
        };
        let expected = rule.instantiate(
            &[app("true", vec![])],
            &["1".parse().unwrap(), "2".parse().unwrap()],
        );
        let mut plan = QuantifierPlan::default();
        plan.rules.push(rule);
        let mut agenda = ClauseAgenda::default();
        agenda.add_helper(&plan, &"(q true)".parse().unwrap());
        agenda.add_goal(Goal::new(&"(p 1)".parse().unwrap(), false));
        while agenda.pending() > 0 {
            assert!(agenda.step(&plan).is_none());
        }
        agenda.add_goal(Goal::new(&"(r 2)".parse().unwrap(), true));
        let mut instances = Vec::new();
        while agenda.pending() > 0 {
            instances.extend(agenda.step(&plan));
        }
        assert_eq!(instances.len(), 1);
        assert_eq!(instances[0].term, expected);
    }

    #[test]
    fn implication_and_demorgan_preserve_clause_signs() {
        let mut actual = Vec::new();
        assert!(literals(
            &"(or (not (and (p a b) (p b c))) (p a c))".parse().unwrap(),
            true,
            &mut actual
        ));
        assert_eq!(
            actual,
            vec![
                Goal::new(&"(p a b)".parse().unwrap(), false),
                Goal::new(&"(p b c)".parse().unwrap(), false),
                Goal::new(&"(p a c)".parse().unwrap(), true),
            ]
        );
        let mut implication = Vec::new();
        assert!(literals(
            &"(=> (and (p a b) (p b c)) (p a c))".parse().unwrap(),
            true,
            &mut implication
        ));
        assert_eq!(actual, implication);
    }
    #[test]
    fn capture_hints_keep_target_state_and_repeated_variable_correlations() {
        use super::super::BinderRule;
        use smt2parser::vmt::array_abstractor::string_to_sort;
        let int = string_to_sort("Int");
        let rule = BinderRule {
            name: "q".into(),
            kind: BinderKind::Exists,
            captures: vec![(Symbol("state".into()), int.clone())],
            variables: vec![(Symbol("x".into()), int.clone())],
            body: "(p state x x)".parse().unwrap(),
            witnesses: vec![],
            result_sort: string_to_sort("Bool"),
            unit_capture: false,
        };
        let expected = rule.instantiate(&["state@1".parse().unwrap()], &["1".parse().unwrap()]);
        let mut plan = QuantifierPlan::default();
        plan.signatures
            .insert("state@0".into(), (vec![], int.clone()));
        plan.signatures.insert("state@1".into(), (vec![], int));
        plan.rules.push(rule);
        for hints in [false, true] {
            let mut agenda = ClauseAgenda::default();
            assert!(agenda.add_demand(&plan, &"(q state@1)".parse().unwrap(), false));
            // Neither inconsistent repeated values nor a wrongly typed capture
            // may supply a tuple, even in hint mode.
            for fact in ["(p state@0 1 2)", "(p true 1 1)"] {
                agenda.add_goal(Goal::new(&fact.parse().unwrap(), false));
                while agenda.pending() > 0 {
                    assert!(agenda.step_capture_hints(&plan, |_, _| false).is_none());
                }
            }
            agenda.add_goal(Goal::new(&"(p state@0 1 1)".parse().unwrap(), false));
            let mut instances = Vec::new();
            while agenda.pending() > 0 {
                instances.extend(if hints {
                    agenda.step_capture_hints(&plan, |_, _| false)
                } else {
                    agenda.step(&plan)
                });
            }
            assert_eq!(instances.len(), usize::from(hints));
            if hints {
                assert_eq!(instances[0].term, expected);
            }
        }
    }
}
