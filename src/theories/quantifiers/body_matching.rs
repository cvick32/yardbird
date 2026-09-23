//! Connect quantified obligations through their bodies, with scoped binders.
//! A false existential can take a tuple from an available universal body.
//! An active universal guard can request an existential witness whose signed
//! atoms conflict with the guard. Its prerequisite goes back through dependency
//! search. Both operations produce correlated tuples via structural joins.
//! Only original guarded binder instances are emitted; body matches and model
//! equalities are search hints. Unsupported Boolean shapes use general search.
use super::{abstract_sort, app, substitute, term_sort, BinderKind, QuantifierPlan};
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
                    rule.variables
                        .iter()
                        .map(|(_, s)| abstract_sort(s))
                        .collect(),
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
        if term_sort(&term, &plan.signatures, &HashMap::new())
            .ok()
            .map(|s| abstract_sort(&s))
            != Some(abstract_sort(&variables[name]))
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
        let sort = |t: &Term| {
            term_sort(t, &plan.signatures, &HashMap::new())
                .ok()
                .map(|s| abstract_sort(&s))
        };
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
    Witness(usize, usize, usize, HashMap<Symbol, Term>),
}

#[derive(Default)]
pub(crate) struct BodyAgenda {
    demands: Vec<Demand>,
    demand_set: HashSet<Term>,
    sources: Vec<Body>,
    source_set: HashMap<Term, usize>,
    queue: VecDeque<BodyJob>,
    guards: HashSet<usize>,
    witness_joins: HashSet<(usize, usize, usize, Vec<Option<Term>>)>,
    witness_roots: HashSet<Term>,
}
impl BodyAgenda {
    pub fn add_demand(&mut self, plan: &QuantifierPlan, helper: &Term) {
        let Term::Application {
            qual_identifier,
            arguments,
        } = helper
        else {
            return;
        };
        let Some((id, rule)) =
            plan.rules.iter().enumerate().find(|(_, r)| {
                r.name == qual_identifier.get_name() && r.kind == BinderKind::Exists
            })
        else {
            return;
        };
        if !self.demand_set.insert(helper.clone()) {
            return;
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
        if self.guards.insert(source) {
            self.queue.extend(
                plan.rules
                    .iter()
                    .enumerate()
                    .filter(|(_, r)| r.kind == BinderKind::Exists)
                    .map(|(r, _)| BodyJob::Witness(r, source, 0, HashMap::new())),
            );
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
            BodyJob::Witness(r, s, next, bindings) => {
                let (result, continuations) =
                    witness_probe(plan, r, &self.sources[s], next, bindings, &mut evaluate)?;
                for bindings in continuations {
                    let key = plan.rules[r]
                        .captures
                        .iter()
                        .map(|(v, _)| bindings.get(v).cloned())
                        .collect();
                    if self.witness_joins.insert((r, s, next + 1, key)) {
                        self.queue
                            .push_back(BodyJob::Witness(r, s, next + 1, bindings));
                    }
                }
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

type WitnessPage = (
    Option<(SymbolicInstance, Option<Term>)>,
    Vec<HashMap<Symbol, Term>>,
);

fn witness_probe(
    plan: &QuantifierPlan,
    id: usize,
    source: &Body,
    next: usize,
    mut bindings: HashMap<Symbol, Term>,
    evaluate: &mut impl FnMut(&Term) -> anyhow::Result<String>,
) -> anyhow::Result<WitnessPage> {
    let rule = &plan.rules[id];
    let mut source = source;
    while let Body::Binder(BinderKind::Forall, _, body) = source {
        source = body;
    }
    let mut guards = Vec::new();
    if !atoms(source, true, false, &mut guards) {
        return Ok((None, vec![]));
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
    if !atoms(&body, true, true, &mut conclusions) {
        return Ok((None, vec![]));
    }
    if let Some((conclusion, sign)) = conclusions.get(next) {
        let mut continuations = Vec::new();
        for (guard, guard_sign) in &guards {
            if sign == guard_sign {
                continue;
            }
            let mut candidate = bindings.clone();
            if matches(
                conclusion,
                guard,
                &variables,
                plan,
                &mut candidate,
                evaluate,
                true,
            )? {
                continuations.push(candidate);
            }
        }
        return Ok((None, continuations));
    }
    if rule.unit_capture {
        bindings.insert(rule.captures[0].0.clone(), app("true", vec![]));
    }
    let Some(arguments) = rule
        .captures
        .iter()
        .map(|(s, _)| bindings.get(s).cloned())
        .collect::<Option<Vec<_>>>()
    else {
        return Ok((None, vec![]));
    };
    let root = app(&rule.name, arguments.clone());
    Ok((
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
        )),
        vec![],
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
}
