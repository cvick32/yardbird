//! Join signed frontier atoms to bind conditional universal instances. This
//! searches atoms already demanded by the explanation, not sort products.
use super::{
    dependency_search::{unify, Goal},
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
    patterns: Vec<Goal>,
    variables: HashMap<Symbol, smt2parser::concrete::Sort>,
    bindings: Vec<HashMap<Symbol, Term>>,
    seen: HashSet<Vec<Option<Term>>>,
}

impl ClauseAgenda {
    pub fn add_helper(&mut self, plan: &QuantifierPlan, helper: &Term) {
        if !self.helpers.insert(helper.clone()) {
            return;
        }
        let Term::Application {
            qual_identifier,
            arguments,
        } = helper
        else {
            return;
        };
        let Some((rule_id, rule)) =
            plan.rules.iter().enumerate().find(|(_, r)| {
                r.name == qual_identifier.get_name() && r.kind == BinderKind::Forall
            })
        else {
            return;
        };
        let mut patterns = Vec::new();
        if !literals(&rule.body, true, &mut patterns) || patterns.len() < 2 {
            return;
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
            patterns,
            variables: rule.variables.iter().cloned().collect(),
            bindings: vec![HashMap::new()],
            seen: HashSet::new(),
        });
        self.schedule_binding(id, 0);
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
        let (c, b, p, g) = self.queue.pop_front()?;
        let clause = &mut self.clauses[c];
        let mut joined = clause.bindings[b].clone();
        if !unify(
            &clause.patterns[p].atom,
            &self.goals[g].atom,
            &clause.variables,
            &plan.signatures,
            &mut joined,
        ) || joined.len() == clause.bindings[b].len()
        {
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
}
