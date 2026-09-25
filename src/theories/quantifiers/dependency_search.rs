//! Bounded backward search from witness atoms through unconditional universal
//! conclusions. Paths are scheduling hints, never additional logical axioms.
use super::*;
use crate::problem_context::ProblemContext;
use std::collections::VecDeque;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Goal {
    pub(crate) atom: Term,
    pub(crate) truth: bool,
}

impl Goal {
    pub(crate) fn new(term: &Term, truth: bool) -> Self {
        if let Term::Application {
            qual_identifier,
            arguments,
        } = term
        {
            match (qual_identifier.get_name().as_str(), arguments.as_slice()) {
                ("not", [inner]) => return Self::new(inner, !truth),
                ("=", [left, right]) => {
                    for (atom, value) in [(left, right), (right, left)] {
                        if let Some(value) = literal_bool(value) {
                            return Self::new(atom, truth == value);
                        }
                    }
                }
                _ => {}
            }
        }
        Self {
            atom: term.clone(),
            truth,
        }
    }

    pub(super) fn key(&self) -> Option<(String, bool)> {
        match &self.atom {
            Term::Application {
                qual_identifier, ..
            } => {
                let name = qual_identifier.get_name();
                (!matches!(name.as_str(), "and" | "or" | "=>" | "ite" | "not"))
                    .then_some((name, self.truth))
            }
            _ => None,
        }
    }
}

fn literal_bool(term: &Term) -> Option<bool> {
    match term {
        Term::QualIdentifier(id) => match id.get_name().as_str() {
            "true" => Some(true),
            "false" => Some(false),
            _ => None,
        },
        _ => None,
    }
}

struct Producer {
    rule: usize,
    conclusion: Goal,
}

#[derive(Default)]
pub(super) struct DependencyIndex {
    producers: HashMap<(String, bool), Vec<Producer>>,
    helpers: HashMap<String, usize>,
}

impl DependencyIndex {
    pub fn new(rules: &[BinderRule]) -> Self {
        let mut index = Self::default();
        for (ordinal, rule) in rules.iter().enumerate() {
            index.helpers.insert(rule.name.clone(), ordinal);
            if rule.kind != BinderKind::Forall {
                continue;
            }
            let mut terms = vec![&rule.body];
            while let Some(term) = terms.pop() {
                if let Term::Application {
                    qual_identifier,
                    arguments,
                } = term
                {
                    if qual_identifier.get_name() == "and" {
                        terms.extend(arguments.iter().rev());
                        continue;
                    }
                }
                let conclusion = Goal::new(term, true);
                if let Some(key) = conclusion.key() {
                    index.producers.entry(key).or_default().push(Producer {
                        rule: ordinal,
                        conclusion,
                    });
                }
            }
        }
        index
    }
}

/// Requests are in prerequisite-first order. The demand and helpers make the
/// chosen route inspectable without treating model truth as a proof premise.
pub(crate) struct DependencyPath {
    pub demand: Term,
    pub desired_truth: bool,
    pub requests: Vec<BinderSearchRequest>,
}

#[derive(Default)]
pub(crate) struct DependencySearch {
    pub paths: Vec<DependencyPath>,
    pub demands: usize,
    pub work: usize,
    pub budget_exhausted: bool,
}

fn applications(term: &Term, visit: &mut impl FnMut(&Term)) {
    if let Term::Application { arguments, .. } = term {
        visit(term);
        for argument in arguments {
            applications(argument, visit);
        }
    }
}

impl PreparedQuantifierSearch {
    #[cfg(test)]
    pub fn dependency_paths(
        &mut self,
        smt: &dyn ProblemContext,
    ) -> anyhow::Result<DependencySearch> {
        self.dependency_paths_with_allowance(smt, &crate::policy::effort::WorkAllowance::default())
    }
    pub fn dependency_paths_with_allowance(
        &mut self,
        smt: &dyn ProblemContext,
        allowance: &crate::policy::effort::WorkAllowance,
    ) -> anyhow::Result<DependencySearch> {
        let mut terms = smt
            .get_all_subterms()
            .into_iter()
            .cloned()
            .collect::<Vec<_>>();
        terms.sort_by_cached_key(ToString::to_string);
        // Source property helpers first, followed by nested helpers exposed by
        // previous witness instances. All terms retain their actual BMC frames.
        let mut property = smt
            .get_property_subterms()
            .into_iter()
            .map(|term| term.parse())
            .collect::<Result<Vec<Term>, _>>()?;
        property.sort_by_cached_key(ToString::to_string);
        // Top-level universal properties may already have been replaced with
        // witness constants before closure conversion. Their atoms are useful
        // demands even though there is no active helper to expand.
        let mut atoms = Vec::new();
        let mut atom_set = HashSet::new();
        let mut collect_atoms = |term: &Term| {
            applications(term, &mut |term| {
                if atoms.len() == allowance.dependency_demands {
                    return;
                }
                let goal = Goal::new(term, true);
                if goal.key().is_some_and(|(name, _)| {
                    !self.compiled.dependencies.helpers.contains_key(&name)
                }) && term_sort(term, &self.compiled.signatures, &HashMap::new()).ok()
                    == Some(string_to_sort("Bool"))
                    && atom_set.insert(term.clone())
                {
                    atoms.push(term.clone());
                }
            });
        };
        for term in &property {
            collect_atoms(term);
        }
        property.extend(terms);
        let mut seen = HashSet::new();
        let mut helpers = Vec::new();
        for term in property {
            applications(&term, &mut |term| {
                if let Term::Application {
                    qual_identifier, ..
                } = term
                {
                    if self
                        .compiled
                        .dependencies
                        .helpers
                        .contains_key(&qual_identifier.get_name())
                        && seen.insert(term.clone())
                    {
                        helpers.push(term.clone());
                    }
                }
            });
        }
        let mut demands = Vec::new();
        let mut seen = HashSet::new();
        let mut result = DependencySearch::default();
        for helper in helpers {
            if result.work >= allowance.dependency_helpers
                || result.work >= allowance.dependency_work
            {
                result.budget_exhausted = true;
                break;
            }
            result.work += 1;
            let Term::Application {
                qual_identifier,
                arguments,
            } = &helper
            else {
                unreachable!()
            };
            let rule = &self.compiled.sources
                [self.compiled.dependencies.helpers[&qual_identifier.get_name()]];
            let active = match rule.kind {
                BinderKind::Forall => "false",
                BinderKind::Exists => "true",
                BinderKind::Lambda => continue,
            };
            if model_value(&helper, smt, &mut self.evaluations)? != active {
                continue;
            }
            let witness = rule.witness_instance(arguments).unwrap();
            collect_atoms(&witness);
        }
        result.budget_exhausted |= atoms.len() == allowance.dependency_demands;
        for atom in atoms {
            if result.work >= allowance.dependency_work {
                result.budget_exhausted = true;
                break;
            }
            result.work += 1;
            let value = model_value(&atom, smt, &mut self.evaluations)?;
            let truth = match value.as_str() {
                "true" => false,
                "false" => true,
                _ => continue,
            };
            let goal = Goal::new(&atom, truth);
            if seen.insert(goal.clone()) {
                demands.push(goal);
            }
        }
        let remaining = crate::policy::effort::WorkAllowance {
            dependency_work: allowance.dependency_work.saturating_sub(result.work),
            ..*allowance
        };
        let explicit = self.paths_from_demands(smt, &remaining, demands)?;
        result.work += explicit.work;
        result.demands = explicit.demands;
        result.paths = explicit.paths;
        result.budget_exhausted |= explicit.budget_exhausted;
        Ok(result)
    }

    /// Preserve the requested sign even when a predecessor atom already has
    /// that value in this model. Its instances may be needed in the next model.
    pub(crate) fn paths_from_demands(
        &mut self,
        smt: &dyn ProblemContext,
        allowance: &crate::policy::effort::WorkAllowance,
        demands: Vec<Goal>,
    ) -> anyhow::Result<DependencySearch> {
        let mut roots = HashSet::new();
        for term in smt.get_source_subterms() {
            applications(term, &mut |term| {
                roots.insert(term.clone());
            });
        }
        let mut result = DependencySearch {
            demands: demands.len(),
            ..Default::default()
        };
        // One shared breadth-first queue prefers short routes across demands,
        // rather than exhausting a difficult demand before considering another.
        let mut queue = demands
            .into_iter()
            .map(|goal| (goal.clone(), goal, Vec::new(), HashSet::new()))
            .collect::<VecDeque<_>>();
        while let Some((demand, goal, requests, mut visited)) = queue.pop_front() {
            if result.work >= allowance.dependency_work {
                result.budget_exhausted = true;
                break;
            }
            result.work += 1;
            if !visited.insert(goal.clone()) {
                continue;
            }
            let Some(key) = goal.key() else {
                continue;
            };
            if goal.truth
                && self.compiled.dependencies.helpers.contains_key(&key.0)
                && roots.contains(&goal.atom)
                && model_value(&goal.atom, smt, &mut self.evaluations)? == "true"
            {
                let requests = requests.into_iter().rev().collect();
                result.paths.push(DependencyPath {
                    demand: demand.atom,
                    desired_truth: demand.truth,
                    requests,
                });
                if result.paths.len() == allowance.dependency_paths {
                    result.budget_exhausted |= !queue.is_empty();
                    break;
                }
                continue;
            }
            if requests.len() == allowance.dependency_links {
                result.budget_exhausted = true;
                continue;
            }
            for producer in self
                .compiled
                .dependencies
                .producers
                .get(&key)
                .into_iter()
                .flatten()
            {
                if result.work >= allowance.dependency_work {
                    result.budget_exhausted = true;
                    break;
                }
                result.work += 1;
                let rule = &self.compiled.sources[producer.rule];
                let variables = rule
                    .captures
                    .iter()
                    .chain(&rule.variables)
                    .cloned()
                    .collect::<HashMap<_, _>>();
                let mut bindings = HashMap::new();
                if !unify(
                    &producer.conclusion.atom,
                    &goal.atom,
                    &variables,
                    &self.compiled.signatures,
                    &mut bindings,
                ) {
                    continue;
                }
                if rule.unit_capture {
                    bindings.insert(rule.captures[0].0.clone(), app("true", vec![]));
                }
                let Some(arguments) = rule
                    .captures
                    .iter()
                    .map(|(name, _)| bindings.get(name).cloned())
                    .collect::<Option<Vec<_>>>()
                else {
                    continue;
                };
                let mut path = requests.clone();
                path.push(BinderSearchRequest {
                    helper: rule.name.clone(),
                    phase: SearchPhase::Conflicts,
                    bindings: rule
                        .captures
                        .iter()
                        .chain(&rule.variables)
                        .filter_map(|(name, _)| {
                            bindings.get(name).map(|term| (name.clone(), term.clone()))
                        })
                        .collect(),
                });
                queue.push_back((
                    demand.clone(),
                    Goal::new(&app(&rule.name, arguments), true),
                    path,
                    visited.clone(),
                ));
            }
        }
        Ok(result)
    }
}

/// Symbolic backward-search continuations; no e-class IDs or model values live
/// here. One step expands one queued goal and retains every unfinished path.
type DependencyJob = (Goal, Goal, Vec<BinderSearchRequest>, HashSet<Goal>);

pub(crate) struct DependencyAgenda {
    index: DependencyIndex,
    roots: HashSet<Term>,
    queue: VecDeque<DependencyJob>,
    waiting: HashMap<Term, Vec<DependencyJob>>,
}
impl DependencyAgenda {
    pub fn new(plan: &QuantifierPlan, roots: Vec<Term>) -> Self {
        Self {
            index: DependencyIndex::new(&plan.rules),
            roots: roots.into_iter().collect(),
            queue: VecDeque::new(),
            waiting: HashMap::new(),
        }
    }
    pub fn add_goal(&mut self, goal: Goal) {
        self.queue
            .push_back((goal.clone(), goal, vec![], HashSet::new()));
    }
    pub fn add_root(&mut self, root: Term) {
        if self.roots.insert(root.clone()) {
            self.queue
                .extend(self.waiting.remove(&root).into_iter().flatten());
        }
    }
    pub fn pending(&self) -> usize {
        self.queue.len()
    }
    pub fn step(
        &mut self,
        plan: &QuantifierPlan,
        mut evaluate: impl FnMut(&Term) -> anyhow::Result<String>,
    ) -> anyhow::Result<Vec<crate::rule_matching::candidate::SymbolicInstance>> {
        let Some((demand, goal, requests, mut visited)) = self.queue.pop_front() else {
            return Ok(vec![]);
        };
        // A helper discovered by another operation can activate this path
        // later. Keep its cursor before marking the goal visited.
        if goal.truth
            && goal
                .key()
                .is_some_and(|k| self.index.helpers.contains_key(&k.0))
            && !self.roots.contains(&goal.atom)
            && !visited.contains(&goal)
        {
            self.waiting.entry(goal.atom.clone()).or_default().push((
                demand.clone(),
                goal.clone(),
                requests.clone(),
                visited.clone(),
            ));
        }
        if !visited.insert(goal.clone()) {
            return Ok(vec![]);
        }
        let Some(key) = goal.key() else {
            return Ok(vec![]);
        };
        if goal.truth
            && self.index.helpers.contains_key(&key.0)
            && self.roots.contains(&goal.atom)
            && evaluate(&goal.atom)?.trim() == "true"
        {
            return Ok(requests
                .iter()
                .rev()
                .filter_map(|r| plan.dependency_instance(r))
                .collect());
        }
        for producer in self.index.producers.get(&key).into_iter().flatten() {
            let rule = &plan.rules[producer.rule];
            let variables = rule
                .captures
                .iter()
                .chain(&rule.variables)
                .cloned()
                .collect();
            let mut bindings = HashMap::new();
            if !unify(
                &producer.conclusion.atom,
                &goal.atom,
                &variables,
                &plan.signatures,
                &mut bindings,
            ) {
                continue;
            }
            if rule.unit_capture {
                bindings.insert(rule.captures[0].0.clone(), app("true", vec![]));
            }
            let Some(arguments) = rule
                .captures
                .iter()
                .map(|(n, _)| bindings.get(n).cloned())
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            let mut path = requests.clone();
            path.push(BinderSearchRequest {
                helper: rule.name.clone(),
                phase: SearchPhase::Conflicts,
                bindings: rule
                    .captures
                    .iter()
                    .chain(&rule.variables)
                    .filter_map(|(n, _)| bindings.get(n).map(|t| (n.clone(), t.clone())))
                    .collect(),
            });
            self.queue.push_back((
                demand.clone(),
                Goal::new(&app(&rule.name, arguments), true),
                path,
                visited.clone(),
            ));
        }
        Ok(vec![])
    }
}

fn model_value(
    term: &Term,
    smt: &dyn ProblemContext,
    cache: &mut HashMap<Term, String>,
) -> anyhow::Result<String> {
    if let Some(value) = cache.get(term) {
        return Ok(value.clone());
    }
    let value = smt.eval_to_string(term)?.trim().to_owned();
    cache.insert(term.clone(), value.clone());
    Ok(value)
}

pub(super) fn unify(
    pattern: &Term,
    ground: &Term,
    variables: &HashMap<Symbol, Sort>,
    signatures: &HashMap<String, (Vec<Sort>, Sort)>,
    bindings: &mut HashMap<Symbol, Term>,
) -> bool {
    if let Term::QualIdentifier(id) = pattern {
        let name = Symbol(id.get_name());
        if let Some(expected) = variables.get(&name) {
            if let Some(bound) = bindings.get(&name) {
                return bound == ground;
            }
            if term_sort(ground, signatures, &HashMap::new()).ok() != Some(expected.clone()) {
                return false;
            }
            bindings.insert(name, ground.clone());
            return true;
        }
    }
    match (pattern, ground) {
        (
            Term::Application {
                qual_identifier: a,
                arguments: left,
            },
            Term::Application {
                qual_identifier: b,
                arguments: right,
            },
        ) => {
            a == b
                && left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(a, b)| unify(a, b, variables, signatures, bindings))
        }
        _ => pattern == ground,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn conclusion_index_preserves_polarity_and_skips_conditional_boolean_shapes() {
        let rule = BinderRule {
            name: "root".into(), kind: BinderKind::Forall,
            captures: vec![(Symbol("unit".into()), string_to_sort("Bool"))],
            variables: vec![(Symbol("x".into()), string_to_sort("Bool"))],
            body: "(and (= (p x) false) (not (not (q x))) (=> (guard x) (r x)) (or (s x) (t x)) (not (and (u x) (v x))))".parse().unwrap(),
            witnesses: vec!["w".into()], result_sort: string_to_sort("Bool"), unit_capture: true,
        };
        let index = DependencyIndex::new(&[rule]);
        assert_eq!(index.producers.len(), 2);
        assert!(index.producers.contains_key(&("p".into(), false)));
        assert!(index.producers.contains_key(&("q".into(), true)));
        assert_eq!(
            Goal::new(&"(= false (p true))".parse().unwrap(), true),
            Goal::new(&"(p true)".parse().unwrap(), false)
        );
    }

    #[test]
    fn dependency_chains_resume_and_wake_when_their_root_is_discovered() {
        for length in [1, 2, 4, 8, 16] {
            let mut plan = QuantifierPlan::default();
            for i in 0..length {
                plan.rules.push(BinderRule {
                    name: format!("q{i}"),
                    kind: BinderKind::Forall,
                    captures: vec![(Symbol(format!("unit{i}")), string_to_sort("Bool"))],
                    variables: vec![(Symbol(format!("x{i}")), string_to_sort("Bool"))],
                    body: app(&format!("q{}", i + 1), vec![app(&format!("x{i}"), vec![])]),
                    witnesses: vec![format!("w{i}")],
                    result_sort: string_to_sort("Bool"),
                    unit_capture: true,
                });
            }
            let root = app("q0", vec![app("true", vec![])]);
            let mut agenda = DependencyAgenda::new(&plan, vec![]);
            agenda.add_goal(Goal::new(
                &app(&format!("q{length}"), vec![app("true", vec![])]),
                true,
            ));
            let mut steps = 0;
            while agenda.pending() > 0 {
                assert!(agenda
                    .step(&plan, |_| Ok("true".into()))
                    .unwrap()
                    .is_empty());
                steps += 1;
                assert!(steps <= length + 1);
            }
            agenda.add_root(root);
            assert!(agenda.pending() > 0, "new root must wake a suspended path");
            let instances = agenda.step(&plan, |_| Ok("true".into())).unwrap();
            assert_eq!(instances.len(), length, "must not truncate a long chain");
            assert_eq!(agenda.pending(), 0);
        }
    }

    #[test]
    fn structural_matching_checks_repeated_variables_and_sorts() {
        let variables = HashMap::from([(Symbol("x".into()), string_to_sort("Int"))]);
        let pattern: Term = "(p x x)".parse().unwrap();
        for (ground, expected) in [
            ("(p 1 1)", true),
            ("(p 1 2)", false),
            ("(p true true)", false),
        ] {
            assert_eq!(
                unify(
                    &pattern,
                    &ground.parse().unwrap(),
                    &variables,
                    &HashMap::new(),
                    &mut HashMap::new()
                ),
                expected
            );
        }
    }
}
