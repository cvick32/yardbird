//! Connect quantified obligations through their bodies, with scoped binders.
//! A false existential can take a tuple from an available universal body.
//! An active universal guard can request an existential witness whose signed
//! atoms conflict with the guard. Its prerequisite goes back through dependency
//! search. Both operations produce correlated tuples via structural joins.
//! Only original guarded binder instances are emitted; body matches and model
//! equalities are search hints. Unsupported Boolean shapes use general search.
use super::{app, substitute, term_sort, BinderKind, QuantifierPlan};
use crate::rule_matching::{candidate::SymbolicInstance, rule::QuantifiedRule};
use smt2parser::concrete::{QualIdentifier, Sort, Symbol, Term};
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Clone)]
enum Body {
    Bound(usize),
    Free(Symbol),
    Atom(Term),
    App(QualIdentifier, Vec<Body>),
    Binder(BinderKind, Vec<Sort>, Box<Body>),
}
impl Body {
    fn ground(&self) -> Option<Term> {
        match self {
            Self::Atom(t) => Some(t.clone()),
            Self::App(q, args) => Some(Term::Application {
                qual_identifier: q.clone(),
                arguments: args.iter().map(Self::ground).collect::<Option<_>>()?,
            }),
            _ => None,
        }
    }
}

fn expand(term: &Term, plan: &QuantifierPlan, free: &HashSet<Symbol>, bound: &[Symbol]) -> Body {
    match term {
        Term::QualIdentifier(q) => {
            let symbol = Symbol(q.get_name());
            if let Some(i) = bound.iter().rev().position(|s| s == &symbol) {
                Body::Bound(i)
            } else if free.contains(&symbol) {
                Body::Free(symbol)
            } else {
                Body::Atom(term.clone())
            }
        }
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            let name = qual_identifier.get_name();
            if let Some(rule) = plan
                .rules
                .iter()
                .find(|r| r.name == name && r.kind != BinderKind::Lambda)
            {
                let body = substitute(
                    rule.body.clone(),
                    rule.captures
                        .iter()
                        .map(|(s, _)| s.clone())
                        .zip(arguments.iter().cloned())
                        .collect(),
                );
                let mut scope = bound.to_vec();
                scope.extend(rule.variables.iter().map(|(s, _)| s.clone()));
                return Body::Binder(
                    rule.kind,
                    rule.variables.iter().map(|(_, s)| s.clone()).collect(),
                    Box::new(expand(&body, plan, free, &scope)),
                );
            }
            // Lowering can spell the same guard as implication or disjunction.
            if name == "=>" && arguments.len() == 2 {
                return expand(
                    &app(
                        "or",
                        vec![app("not", vec![arguments[0].clone()]), arguments[1].clone()],
                    ),
                    plan,
                    free,
                    bound,
                );
            }
            Body::App(
                qual_identifier.clone(),
                arguments
                    .iter()
                    .map(|a| expand(a, plan, free, bound))
                    .collect(),
            )
        }
        Term::Attributes { term, .. } => expand(term, plan, free, bound),
        _ => Body::Atom(term.clone()),
    }
}

fn matches(
    pattern: &Body,
    source: &Body,
    variables: &HashMap<Symbol, Sort>,
    plan: &QuantifierPlan,
    bindings: &mut HashMap<Symbol, Term>,
    evaluate: &mut impl FnMut(&Term) -> anyhow::Result<String>,
    schematic: bool,
) -> anyhow::Result<bool> {
    if schematic && matches!(pattern, Body::Bound(_)) {
        return Ok(matches!(source, Body::Bound(_)) || source.ground().is_some());
    }
    if let Body::Free(name) = pattern {
        let Some(term) = source.ground() else {
            return Ok(false);
        };
        if term_sort(&term, &plan.signatures, &HashMap::new()).ok() != Some(variables[name].clone())
        {
            return Ok(false);
        }
        if let Some(old) = bindings.get(name) {
            return Ok(
                old == &term || evaluate(&app("=", vec![old.clone(), term]))?.trim() == "true"
            );
        }
        bindings.insert(name.clone(), term);
        return Ok(true);
    }
    // Check an equality rather than retaining model-specific value names.
    // These equalities only choose tuples; they are never emitted as lemmas.
    if let (Some(left), Some(right)) = (pattern.ground(), source.ground()) {
        if left == right {
            return Ok(true);
        }
        let sort = |t: &Term| term_sort(t, &plan.signatures, &HashMap::new()).ok();
        if sort(&left).is_none() || sort(&left) != sort(&right) {
            return Ok(false);
        }
        return Ok(evaluate(&app("=", vec![left, right]))?.trim() == "true");
    }
    match (pattern, source) {
        (Body::Bound(a), Body::Bound(b)) => Ok(a == b),
        (Body::Binder(a, sa, ba), Body::Binder(b, sb, bb)) if a == b && sa == sb => {
            matches(ba, bb, variables, plan, bindings, evaluate, schematic)
        }
        (Body::App(a, aa), Body::App(b, bb)) if a == b && aa.len() == bb.len() => {
            for (a, b) in aa.iter().zip(bb) {
                if !matches(a, b, variables, plan, bindings, evaluate, schematic)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        _ => Ok(false),
    }
}

struct Demand {
    rule: usize,
    arguments: Vec<Term>,
    body: Body,
    variables: HashMap<Symbol, Sort>,
}

enum BodyJob {
    Instance(usize, usize),
    Witness {
        join: usize,
        guard: usize,
        atom: usize,
    },
    WitnessComplete(usize),
}

struct WitnessPattern {
    rule: usize,
    variables: HashMap<Symbol, Sort>,
    conclusions: Vec<(Body, bool)>,
}

struct WitnessJoin {
    pattern: usize,
    next: usize,
    bindings: HashMap<Symbol, Term>,
}

struct WitnessGuard {
    // Separate signs so each job tries one potentially compatible atom.
    positive: Vec<Body>,
    negative: Vec<Body>,
}
impl WitnessGuard {
    fn opposing(&self, sign: bool) -> &[Body] {
        if sign {
            &self.negative
        } else {
            &self.positive
        }
    }
}

#[derive(Default)]
pub(crate) struct BodyAgenda {
    demands: Vec<Demand>,
    demand_set: HashSet<Term>,
    sources: Vec<Body>,
    source_set: HashMap<Term, usize>,
    queue: VecDeque<BodyJob>,
    guards: HashSet<usize>,
    witness_patterns: Vec<WitnessPattern>,
    witness_guards: Vec<WitnessGuard>,
    witness_joins: Vec<WitnessJoin>,
    witness_join_keys: HashSet<(usize, usize, Vec<Option<Term>>)>,
    witness_roots: HashSet<Term>,
}
impl BodyAgenda {
    pub fn add_demand(&mut self, plan: &QuantifierPlan, helper: &Term) -> bool {
        let Term::Application {
            qual_identifier,
            arguments,
        } = helper
        else {
            return false;
        };
        let Some((id, rule)) =
            plan.rules.iter().enumerate().find(|(_, r)| {
                r.name == qual_identifier.get_name() && r.kind == BinderKind::Exists
            })
        else {
            return false;
        };
        if !self.demand_set.insert(helper.clone()) {
            return false;
        }
        let body = substitute(
            rule.body.clone(),
            rule.captures
                .iter()
                .map(|(s, _)| s.clone())
                .zip(arguments.iter().cloned())
                .collect(),
        );
        let free = rule.variables.iter().map(|(s, _)| s.clone()).collect();
        let id_demand = self.demands.len();
        self.demands.push(Demand {
            rule: id,
            arguments: arguments.clone(),
            body: expand(&body, plan, &free, &[]),
            variables: rule.variables.iter().cloned().collect(),
        });
        self.queue
            .extend((0..self.sources.len()).map(|s| BodyJob::Instance(id_demand, s)));
        true
    }
    pub fn add_source(&mut self, plan: &QuantifierPlan, helper: &Term) -> Option<usize> {
        let Term::Application {
            qual_identifier, ..
        } = helper
        else {
            return None;
        };
        if !plan
            .rules
            .iter()
            .any(|r| r.name == qual_identifier.get_name() && r.kind == BinderKind::Forall)
        {
            return None;
        }
        if let Some(id) = self.source_set.get(helper) {
            return Some(*id);
        }
        let source = self.sources.len();
        self.source_set.insert(helper.clone(), source);
        self.sources
            .push(expand(helper, plan, &HashSet::new(), &[]));
        self.queue
            .extend((0..self.demands.len()).map(|d| BodyJob::Instance(d, source)));
        Some(source)
    }
    pub fn add_guard(&mut self, plan: &QuantifierPlan, helper: &Term) {
        let Some(source) = self.add_source(plan, helper) else {
            return;
        };
        if !self.guards.insert(source) {
            return;
        }
        let mut body = &self.sources[source];
        while let Body::Binder(BinderKind::Forall, _, inner) = body {
            body = inner;
        }
        let mut literals = Vec::new();
        if !atoms(body, true, false, &mut literals) {
            return;
        }
        // Compile witness patterns only once, when the first usable guard arrives.
        if self.witness_guards.is_empty() {
            for (id, rule) in plan.rules.iter().enumerate() {
                if rule.kind != BinderKind::Exists {
                    continue;
                }
                let variables = rule.captures.iter().cloned().collect::<HashMap<_, _>>();
                let body = expand(
                    &rule.body,
                    plan,
                    &variables.keys().cloned().collect(),
                    &rule
                        .variables
                        .iter()
                        .map(|(s, _)| s.clone())
                        .collect::<Vec<_>>(),
                );
                let mut conclusions = Vec::new();
                if atoms(&body, true, true, &mut conclusions) {
                    let pattern = self.witness_patterns.len();
                    self.witness_patterns.push(WitnessPattern {
                        rule: id,
                        variables,
                        conclusions,
                    });
                    self.add_witness_join(plan, pattern, 0, HashMap::new());
                }
            }
        }
        let mut guard = WitnessGuard {
            positive: vec![],
            negative: vec![],
        };
        for (atom, sign) in literals {
            if sign {
                guard.positive.push(atom);
            } else {
                guard.negative.push(atom);
            }
        }
        let guard_id = self.witness_guards.len();
        self.witness_guards.push(guard);
        // Every retained partial tuple gets one chance with the new guard,
        // including tuples whose old work queue has already been exhausted.
        for join in 0..self.witness_joins.len() {
            self.schedule_witness_pair(join, guard_id);
        }
    }

    fn schedule_witness_pair(&mut self, join: usize, guard: usize) {
        let partial = &self.witness_joins[join];
        if let Some((_, sign)) = self.witness_patterns[partial.pattern]
            .conclusions
            .get(partial.next)
        {
            if !self.witness_guards[guard].opposing(*sign).is_empty() {
                self.queue.push_back(BodyJob::Witness {
                    join,
                    guard,
                    atom: 0,
                });
            }
        }
    }

    fn add_witness_join(
        &mut self,
        plan: &QuantifierPlan,
        pattern: usize,
        next: usize,
        bindings: HashMap<Symbol, Term>,
    ) {
        let rule = &plan.rules[self.witness_patterns[pattern].rule];
        let key = rule
            .captures
            .iter()
            .map(|(v, _)| bindings.get(v).cloned())
            .collect();
        if !self.witness_join_keys.insert((pattern, next, key)) {
            return;
        }
        let join = self.witness_joins.len();
        self.witness_joins.push(WitnessJoin {
            pattern,
            next,
            bindings,
        });
        if next == self.witness_patterns[pattern].conclusions.len() {
            self.queue.push_back(BodyJob::WitnessComplete(join));
        } else {
            for guard in 0..self.witness_guards.len() {
                self.schedule_witness_pair(join, guard);
            }
        }
    }
    pub fn pending(&self) -> usize {
        self.queue.len()
    }
    pub fn step(
        &mut self,
        plan: &QuantifierPlan,
        mut evaluate: impl FnMut(&Term) -> anyhow::Result<String>,
    ) -> anyhow::Result<Option<(SymbolicInstance, Option<Term>)>> {
        let Some(job) = self.queue.pop_front() else {
            return Ok(None);
        };
        let (d, s) = match job {
            BodyJob::Instance(d, s) => (d, s),
            BodyJob::Witness { join, guard, atom } => {
                let partial = &self.witness_joins[join];
                let pattern_id = partial.pattern;
                let next = partial.next;
                let pattern = &self.witness_patterns[pattern_id];
                let (conclusion, sign) = &pattern.conclusions[next];
                let atoms = self.witness_guards[guard].opposing(*sign);
                if atom + 1 < atoms.len() {
                    self.queue.push_back(BodyJob::Witness {
                        join,
                        guard,
                        atom: atom + 1,
                    });
                }
                let mut bindings = partial.bindings.clone();
                if matches(
                    conclusion,
                    &atoms[atom],
                    &pattern.variables,
                    plan,
                    &mut bindings,
                    &mut evaluate,
                    true,
                )? {
                    self.add_witness_join(plan, pattern_id, next + 1, bindings);
                }
                return Ok(None);
            }
            BodyJob::WitnessComplete(join) => {
                let partial = &self.witness_joins[join];
                let result = witness_instance(
                    plan,
                    self.witness_patterns[partial.pattern].rule,
                    partial.bindings.clone(),
                );
                return Ok(result.filter(|(_, root)| {
                    root.as_ref()
                        .is_none_or(|r| self.witness_roots.insert(r.clone()))
                }));
            }
        };
        let demand = &self.demands[d];
        let mut bindings = HashMap::new();
        if !matches(
            &demand.body,
            &self.sources[s],
            &demand.variables,
            plan,
            &mut bindings,
            &mut evaluate,
            false,
        )? {
            return Ok(None);
        }
        let rule = &plan.rules[demand.rule];
        let Some(values) = rule
            .variables
            .iter()
            .map(|(s, _)| bindings.get(s).cloned())
            .collect::<Option<Vec<_>>>()
        else {
            return Ok(None);
        };
        Ok(Some((
            SymbolicInstance {
                rule: QuantifiedRule::input_binder(&rule.name),
                term: rule.instantiate(&demand.arguments, &values),
                bindings: rule
                    .captures
                    .iter()
                    .chain(&rule.variables)
                    .map(|(s, _)| s.0.clone())
                    .zip(demand.arguments.iter().chain(&values).cloned())
                    .collect(),
            },
            None,
        )))
    }
}

/// Extract a conjunctive witness body or a disjunctive guard, preserving signs.
/// Other Boolean shapes are left to general matching.
fn atoms(body: &Body, truth: bool, conjunction: bool, result: &mut Vec<(Body, bool)>) -> bool {
    if let Body::App(q, args) = body {
        let name = q.get_name();
        if name == "not" && args.len() == 1 {
            return atoms(&args[0], !truth, conjunction, result);
        }
        if (name == "and" && truth == conjunction) || (name == "or" && truth != conjunction) {
            return args.iter().all(|a| atoms(a, truth, conjunction, result));
        }
        if matches!(name.as_str(), "and" | "or" | "ite") {
            return false;
        }
    }
    if matches!(body, Body::Binder(..)) {
        return false;
    }
    result.push((body.clone(), truth));
    true
}

fn witness_instance(
    plan: &QuantifierPlan,
    id: usize,
    mut bindings: HashMap<Symbol, Term>,
) -> Option<(SymbolicInstance, Option<Term>)> {
    let rule = &plan.rules[id];
    if rule.unit_capture {
        bindings.insert(rule.captures[0].0.clone(), app("true", vec![]));
    }
    let arguments = rule
        .captures
        .iter()
        .map(|(s, _)| bindings.get(s).cloned())
        .collect::<Option<Vec<_>>>()?;
    let root = app(&rule.name, arguments.clone());
    Some((
        SymbolicInstance {
            rule: QuantifiedRule::input_binder(&rule.name),
            term: rule
                .witness_instance(&arguments)
                .expect("existential witness"),
            bindings: rule
                .captures
                .iter()
                .map(|(s, _)| s.0.clone())
                .zip(arguments)
                .collect(),
        },
        Some(root),
    ))
}

#[cfg(test)]
mod tests {
    use super::super::BinderRule;
    use super::*;
    use smt2parser::vmt::array_abstractor::string_to_sort;

    fn plan() -> QuantifierPlan {
        let fields = |names: &[&str]| {
            names
                .iter()
                .map(|n| (Symbol((*n).into()), string_to_sort("Int")))
                .collect()
        };
        let rule =
            |name: &str, kind, captures: &[&str], variables: &[&str], body: &str| BinderRule {
                name: name.into(),
                kind,
                captures: fields(captures),
                variables: fields(variables),
                body: body.parse().unwrap(),
                witnesses: vec![],
                result_sort: string_to_sort("Bool"),
                unit_capture: false,
            };
        let mut plan = QuantifierPlan {
            rules: vec![
                rule(
                    "available",
                    BinderKind::Forall,
                    &["c", "a"],
                    &["n"],
                    "(or (not (edge n c)) (holds a n c))",
                ),
                rule(
                    "support",
                    BinderKind::Forall,
                    &["c", "a"],
                    &["different_name"],
                    "(=> (edge different_name c) (holds a different_name c))",
                ),
                rule("some", BinderKind::Exists, &["a"], &["q"], "(support q a)"),
            ],
            ..Default::default()
        };
        for name in ["chosen", "previous", "current"] {
            plan.signatures
                .insert(name.into(), (vec![], string_to_sort("Int")));
        }
        plan
    }

    #[test]
    fn existential_tuple_comes_from_an_alpha_equivalent_guard_and_keeps_captures() {
        let plan = plan();
        for source_first in [false, true] {
            let mut agenda = BodyAgenda::default();
            let demand = "(some current)".parse().unwrap();
            let source = "(available chosen previous)".parse().unwrap();
            if source_first {
                agenda.add_source(&plan, &source);
            }
            agenda.add_demand(&plan, &demand);
            if !source_first {
                agenda.add_source(&plan, &source);
            }
            assert_eq!(agenda.pending(), 1);
            let (instance, _) = agenda
                .step(&plan, |eq| {
                    assert_eq!(eq.to_string(), "(= current previous)");
                    Ok("true".into())
                })
                .unwrap()
                .unwrap();
            assert_eq!(agenda.pending(), 0);
            assert_eq!(
                instance.term.to_string(),
                "(=> (support chosen current) (some current))"
            );
            let oracle = z3::Solver::new();
            oracle.from_string(format!("(declare-fun edge (Int Int) Bool) (declare-fun holds (Int Int Int) Bool)
                (declare-const chosen Int) (declare-const current Int)
                (define-fun support ((c Int) (a Int)) Bool (forall ((n Int)) (=> (edge n c) (holds a n c))))
                (define-fun some ((a Int)) Bool (exists ((q Int)) (support q a)))
                (assert (not {}))", instance.term));
            assert_eq!(oracle.check(), z3::SatResult::Unsat);
        }
        let mut agenda = BodyAgenda::default();
        agenda.add_demand(&plan, &"(some current)".parse().unwrap());
        agenda.add_source(&plan, &"(available chosen previous)".parse().unwrap());
        assert!(agenda
            .step(&plan, |_| Ok("false".into()))
            .unwrap()
            .is_none());
    }

    #[test]
    fn active_guard_requests_a_correlated_witness_and_its_background_prerequisite() {
        use crate::theories::quantifiers::dependency_search::{DependencyAgenda, Goal};
        let mut plan = plan();
        plan.rules.push(BinderRule {
            name: "partner".into(),
            kind: BinderKind::Exists,
            captures: vec![
                (Symbol("c".into()), string_to_sort("Int")),
                (Symbol("d".into()), string_to_sort("Int")),
            ],
            variables: vec![(Symbol("n".into()), string_to_sort("Int"))],
            body: "(and (edge n c) (edge n d))".parse().unwrap(),
            witnesses: vec!["meet".into()],
            result_sort: string_to_sort("Bool"),
            unit_capture: false,
        });
        plan.rules.push(BinderRule {
            name: "background".into(),
            kind: BinderKind::Forall,
            captures: vec![(Symbol("unit".into()), string_to_sort("Bool"))],
            variables: vec![
                (Symbol("c".into()), string_to_sort("Int")),
                (Symbol("d".into()), string_to_sort("Int")),
            ],
            body: "(partner c d)".parse().unwrap(),
            witnesses: vec![],
            result_sort: string_to_sort("Bool"),
            unit_capture: true,
        });
        let mut agenda = BodyAgenda::default();
        agenda.add_guard(&plan, &"(available chosen previous)".parse().unwrap());
        let mut probes = Vec::new();
        while agenda.pending() > 0 {
            probes.extend(agenda.step(&plan, |_| panic!("structural probe")).unwrap());
        }
        assert_eq!(probes.len(), 1);
        let (instance, prerequisite) = probes.pop().unwrap();
        assert_eq!(instance.term.to_string(), "(=> (partner chosen chosen) (and (edge (meet chosen chosen) chosen) (edge (meet chosen chosen) chosen)))");
        let prerequisite = prerequisite.unwrap();
        assert_eq!(prerequisite.to_string(), "(partner chosen chosen)");
        let mut dependencies =
            DependencyAgenda::new(&plan, vec!["(background true)".parse().unwrap()]);
        dependencies.add_goal(Goal::new(&prerequisite, true));
        let mut links = Vec::new();
        while dependencies.pending() > 0 {
            links.extend(dependencies.step(&plan, |_| Ok("true".into())).unwrap());
        }
        assert_eq!(links.len(), 1);
        assert_eq!(
            links[0].term.to_string(),
            "(=> (background true) (partner chosen chosen))"
        );
        // Keep all correlated joins when the guard has multiple alternatives;
        // one work item must not silently discard later compatible tuples.
        plan.rules[0].body = "(or (not (edge n c)) (not (edge n a)) (holds a n c))"
            .parse()
            .unwrap();
        let mut agenda = BodyAgenda::default();
        agenda.add_guard(&plan, &"(available chosen previous)".parse().unwrap());
        let mut roots = HashSet::new();
        while agenda.pending() > 0 {
            if let Some((_, Some(root))) =
                agenda.step(&plan, |_| panic!("structural join")).unwrap()
            {
                roots.insert(root.to_string());
            }
        }
        assert_eq!(
            roots,
            [
                "(partner chosen chosen)",
                "(partner chosen previous)",
                "(partner previous chosen)",
                "(partner previous previous)"
            ]
            .into_iter()
            .map(str::to_owned)
            .collect()
        );

        // A source's own bound variable is not an available ground capture.
        plan.rules[0].captures = vec![(Symbol("a".into()), string_to_sort("Int"))];
        plan.rules[0].variables = vec![
            (Symbol("c".into()), string_to_sort("Int")),
            (Symbol("n".into()), string_to_sort("Int")),
        ];
        plan.rules[0].body = "(or (not (edge n c)) (holds a n c))".parse().unwrap();
        let mut agenda = BodyAgenda::default();
        agenda.add_guard(&plan, &"(available previous)".parse().unwrap());
        while agenda.pending() > 0 {
            assert!(agenda
                .step(&plan, |_| panic!("bound capture must be rejected"))
                .unwrap()
                .is_none());
        }
    }

    #[test]
    fn nested_bound_variables_cannot_escape_as_existential_choices() {
        let mut plan = plan();
        // Matching q to the universal's n would exchange exists/forall.
        // There is no single ground witness here, so no tuple may be emitted.
        plan.rules[0].body = "(or (not (edge n n)) (holds a n n))".parse().unwrap();
        let mut agenda = BodyAgenda::default();
        agenda.add_demand(&plan, &"(some current)".parse().unwrap());
        agenda.add_source(&plan, &"(available chosen current)".parse().unwrap());
        assert!(agenda
            .step(&plan, |_| panic!("no model equality required"))
            .unwrap()
            .is_none());
    }

    #[test]
    fn tuple_matching_rejects_wrong_sorts_and_inconsistent_repeated_variables() {
        let mut plan = plan();
        plan.rules[0].body = "(or (not (edge n c)) (holds a n 42))".parse().unwrap();
        let mut agenda = BodyAgenda::default();
        agenda.add_demand(&plan, &"(some current)".parse().unwrap());
        agenda.add_source(&plan, &"(available chosen current)".parse().unwrap());
        assert!(agenda
            .step(&plan, |_| Ok("false".into()))
            .unwrap()
            .is_none());
        plan.signatures
            .insert("chosen".into(), (vec![], string_to_sort("Bool")));
        let mut agenda = BodyAgenda::default();
        agenda.add_demand(&plan, &"(some current)".parse().unwrap());
        agenda.add_source(&plan, &"(available chosen current)".parse().unwrap());
        assert!(agenda
            .step(&plan, |_| panic!("sorts must be checked first"))
            .unwrap()
            .is_none());
    }
    fn intersection_plan() -> QuantifierPlan {
        let mut plan = plan();
        plan.rules.push(BinderRule {
            name: "partner".into(),
            kind: BinderKind::Exists,
            captures: vec![
                (Symbol("c".into()), string_to_sort("Int")),
                (Symbol("d".into()), string_to_sort("Int")),
            ],
            variables: vec![(Symbol("n".into()), string_to_sort("Int"))],
            body: "(and (edge n c) (edge n d))".parse().unwrap(),
            witnesses: vec!["meet".into()],
            result_sort: string_to_sort("Bool"),
            unit_capture: false,
        });
        plan
    }

    fn drain_witnesses(
        agenda: &mut BodyAgenda,
        plan: &QuantifierPlan,
    ) -> Vec<(SymbolicInstance, Option<Term>)> {
        let mut result = Vec::new();
        let mut work = 0;
        while agenda.pending() > 0 {
            work += 1;
            assert!(work < 1000, "join enumeration must finish");
            result.extend(agenda.step(plan, |_| Ok("false".into())).unwrap());
        }
        result
    }

    #[test]
    fn witness_joins_resume_when_another_guard_arrives_after_exhaustion() {
        let plan = intersection_plan();
        for reverse in [false, true] {
            for late in [false, true] {
                let mut guards = [
                    "(available chosen previous)",
                    "(available current previous)",
                ];
                if reverse {
                    guards.reverse();
                }
                let mut agenda = BodyAgenda::default();
                let first = guards[0].parse().unwrap();
                let second = guards[1].parse().unwrap();
                // Being a source alone does not make a universal an active guard.
                agenda.add_source(&plan, &second);
                agenda.add_guard(&plan, &first);
                let mut results = if late {
                    drain_witnesses(&mut agenda, &plan)
                } else {
                    vec![]
                };
                if late {
                    assert_eq!(results.len(), 1);
                }
                agenda.add_guard(&plan, &second);
                results.extend(drain_witnesses(&mut agenda, &plan));
                assert_eq!(results.len(), 4, "deduplicate complete tuples");
                let roots: HashSet<_> = results
                    .iter()
                    .map(|(_, r)| r.as_ref().unwrap().to_string())
                    .collect();
                assert_eq!(
                    roots,
                    [
                        "(partner chosen chosen)",
                        "(partner chosen current)",
                        "(partner current chosen)",
                        "(partner current current)"
                    ]
                    .into_iter()
                    .map(str::to_owned)
                    .collect()
                );
                let (instance, _) = results
                    .iter()
                    .find(|(_, r)| r.as_ref().unwrap().to_string() == "(partner chosen current)")
                    .unwrap();
                assert_eq!(instance.term.to_string(), "(=> (partner chosen current) (and (edge (meet chosen current) chosen) (edge (meet chosen current) current)))");
                assert_eq!(
                    instance.bindings,
                    vec![
                        ("c".into(), "chosen".parse().unwrap()),
                        ("d".into(), "current".parse().unwrap())
                    ]
                );
                agenda.add_guard(&plan, &first);
                agenda.add_guard(&plan, &second);
                assert_eq!(
                    agenda.pending(),
                    0,
                    "duplicate guards cannot restart search"
                );
            }
        }
    }

    #[test]
    fn witness_step_matches_only_one_atom_and_retains_alternatives() {
        let mut plan = intersection_plan();
        plan.rules[0].body = "(or (not (edge n c)) (not (edge n a)) (holds a n c))"
            .parse()
            .unwrap();
        let mut agenda = BodyAgenda::default();
        agenda.add_guard(&plan, &"(available chosen previous)".parse().unwrap());
        let before = agenda.witness_joins.len();
        assert!(agenda
            .step(&plan, |_| panic!("syntactic match"))
            .unwrap()
            .is_none());
        assert_eq!(
            agenda.witness_joins.len(),
            before + 1,
            "one atom attempt per work item"
        );
        assert!(agenda.pending() > 0);
        assert_eq!(drain_witnesses(&mut agenda, &plan).len(), 4);
    }

    #[test]
    fn cross_guard_repeated_captures_respect_each_models_equalities() {
        let mut plan = intersection_plan();
        let mut second = plan.rules[0].clone();
        second.name = "tagged".into();
        second.body = "(or (not (tag n c)) (holds a n c))".parse().unwrap();
        plan.rules.push(second);
        let partner = plan.rules.iter_mut().find(|r| r.name == "partner").unwrap();
        partner.captures.truncate(1);
        partner.body = "(and (edge n c) (tag n c))".parse().unwrap();
        for equal in [true, false] {
            // A fresh model-local agenda must not reuse equality-dependent joins.
            let mut agenda = BodyAgenda::default();
            agenda.add_guard(&plan, &"(available chosen previous)".parse().unwrap());
            agenda.add_guard(&plan, &"(tagged current previous)".parse().unwrap());
            let mut results = Vec::new();
            while agenda.pending() > 0 {
                results.extend(
                    agenda
                        .step(&plan, |term| {
                            assert_eq!(term.to_string(), "(= chosen current)");
                            Ok(equal.to_string())
                        })
                        .unwrap(),
                );
            }
            assert_eq!(results.len(), usize::from(equal));
            if equal {
                assert_eq!(results[0].0.term.to_string(), "(=> (partner chosen) (and (edge (meet chosen) chosen) (tag (meet chosen) chosen)))");
            }
        }
    }
    #[test]
    fn joined_witness_uses_shared_validation_ranking_and_installation() {
        use crate::{
            instance_installation::request::InstantiationRequest,
            policy::{
                effort::WorkAllowance,
                instance_selection::{InstantiationRanker, TermCostInstantiationRanker},
                term_selection::array::ArrayAstSize,
            },
            problem_context::ProblemContext,
            refinement_graph::RefinementGraph,
            rule_matching::{
                candidate::InstantiationCandidate, scope::CandidateScope,
                search_context::SearchContext, symbolic_pool::SymbolicCandidatePool,
            },
            smtlib_problem::SMTLIBProblem,
            smtlib_refinement_session::SmtlibRefinementSession,
            solver::SolverCheckResult,
            strategies::{Abstract, ProofStrategy, RefinementState},
            terms::language::expr_to_term,
            SolverBackend, YardbirdPolicy,
        };
        #[derive(Clone, Debug)]
        struct Reject;
        impl InstantiationRanker for Reject {
            fn clone_box(&self) -> Box<dyn InstantiationRanker> {
                Box::new(self.clone())
            }
            fn compare(
                &self,
                a: &InstantiationCandidate,
                b: &InstantiationCandidate,
            ) -> std::cmp::Ordering {
                a.cost.cmp(&b.cost)
            }
            fn is_eligible(&self, _: &InstantiationCandidate, _: CandidateScope) -> bool {
                false
            }
        }
        let input = r#"
            (declare-fun chosen () Int) (declare-fun current () Int) (declare-fun previous () Int)
            (declare-fun partner (Int Int) Bool) (declare-fun meet (Int Int) Int)
            (declare-fun edge (Int Int) Bool)
            (assert (not (= chosen current)))
            (assert (partner chosen current))
            (assert (not (partner chosen chosen)))
            (assert (not (partner current chosen)))
            (assert (not (partner current current)))
            (assert (not (edge (meet chosen current) current)))
        "#;
        let commands = smt2parser::CommandStream::new(
            input.as_bytes(),
            smt2parser::concrete::SyntaxBuilder,
            None,
        )
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
        let problem = SMTLIBProblem::from_commands(commands).unwrap();
        let strategy: Box<dyn ProofStrategy<'_, RefinementState>> =
            Box::new(Abstract::<ArrayAstSize>::new(
                1,
                false,
                YardbirdPolicy::new(()),
                false,
            ));
        let mut smt = SmtlibRefinementSession::new_with_array_types(
            &problem,
            &strategy,
            SolverBackend::Z3,
            false,
            vec![("Int".into(), "Int".into())],
            None,
        )
        .unwrap();
        assert_eq!(smt.check_current_query(), SolverCheckResult::Sat);
        let plan = intersection_plan();
        let mut agenda = BodyAgenda::default();
        agenda.add_guard(&plan, &"(available chosen previous)".parse().unwrap());
        agenda.add_guard(&plan, &"(available current previous)".parse().unwrap());
        let mut pool = SymbolicCandidatePool::default();
        pool.remember(
            drain_witnesses(&mut agenda, &plan)
                .into_iter()
                .map(|(instance, _)| instance),
        );
        let mut context = SearchContext::<ArrayAstSize> {
            formulas: crate::rule_matching::search_context::SearchFormulas {
                index: None,
                quantifiers: &plan,
            },
            model_version: 0,
            graph: &RefinementGraph::default(),
            graph_version: 0,
            smt: &smt,
            term_config: &(),
            ranker: &Reject,
            allowance: WorkAllowance {
                winners: 1,
                ..Default::default()
            },
            operation_id: None,
            pending_instances: &HashSet::new(),
            selection_counts: &Default::default(),
            artifact_capture: Default::default(),
            depth: 0,
            refinement_step: 0,
            profiling: None,
        };
        let rejected = pool.candidates(&context).unwrap();
        assert_eq!(
            rejected.candidates.len(),
            1,
            "only the false complete instance is offered"
        );
        assert_eq!(rejected.selected().count(), 0);
        context.ranker = &TermCostInstantiationRanker;
        let selected = pool
            .candidates(&context)
            .unwrap()
            .into_selected()
            .collect::<Vec<_>>();
        assert_eq!(selected.len(), 1);
        let candidate = &selected[0];
        assert_eq!(
            candidate.provenance.relative_bindings(),
            &[
                ("c".into(), "chosen".parse().unwrap()),
                ("d".into(), "current".parse().unwrap())
            ]
        );
        let instance = smt
            .make_unquantified_instance(expr_to_term(candidate.expression.clone()))
            .unwrap();
        let installed = smt.add_instantiation(InstantiationRequest::provenanced(
            instance,
            candidate.provenance.clone(),
        ));
        assert_eq!(installed.solver_assertions_added(), 1);
        assert_eq!(smt.check_current_query(), SolverCheckResult::Unsat);
    }
}
