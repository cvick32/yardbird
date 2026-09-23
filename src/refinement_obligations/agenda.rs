//! A resumable symbolic search context. All model-dependent choices are logged
//! and must still hold before this context can be resumed on a different model.
use super::*;
use crate::theories::quantifiers::{
    body_matching::BodyAgenda,
    clauses::{source_helpers, ClauseAgenda},
    dependency_search::DependencyAgenda,
    equations::{EquationCompiler, EquationCursor},
};

pub(super) struct Agenda {
    decisions: HashMap<Term, String>,
    active: HashMap<u16, Option<String>>,
    roots: Vec<(Term, bool)>,
    explain: VecDeque<(Term, bool)>,
    explained: HashSet<(Term, bool)>,
    ground: HashMap<Term, Vec<Term>>,
    assertions: HashSet<Term>,
    constrained: HashSet<(Term, bool)>,
    goals: Vec<Goal>,
    goal_set: HashSet<Goal>,
    transport: VecDeque<usize>,
    equations: Vec<QuantifiedEquations>,
    equation_compilers: VecDeque<EquationCompiler>,
    equation_jobs: VecDeque<(usize, usize, EquationCursor)>,
    clauses: ClauseAgenda,
    bodies: BodyAgenda,
    dependencies: DependencyAgenda,
    helpers: VecDeque<Term>,
    generated: HashSet<Term>,
    turn: usize,
}

fn evaluate(
    smt: &dyn ProblemContext,
    decisions: &mut HashMap<Term, String>,
    term: &Term,
) -> anyhow::Result<String> {
    if let Some(v) = decisions.get(term) {
        return Ok(v.clone());
    }
    let value = smt.eval_to_string(term)?.trim().to_owned();
    decisions.insert(term.clone(), value.clone());
    Ok(value)
}

impl Agenda {
    pub fn new(
        plan: &QuantifierPlan,
        index: &TransitionIndex,
        smt: &dyn ProblemContext,
        depth: u16,
    ) -> anyhow::Result<Self> {
        let mut decisions = HashMap::new();
        let mut eval = |t: &Term| evaluate(smt, &mut decisions, t);
        let mut roots = vec![(index.index_term(index.property(), depth), false)];
        let mut active = HashMap::new();
        for frame in (0..depth).rev() {
            let selected = index.selected_action(frame, &mut eval)?.map(str::to_owned);
            if let Some(action) = selected.as_ref().and_then(|a| index.actions().get(a)) {
                for requirement in &action.requirements {
                    if requirement.guards.iter().all(|g| {
                        eval(&index.index_term(&g.expression, frame))
                            .is_ok_and(|v| v == if g.required_value { "true" } else { "false" })
                    }) {
                        roots.push((index.index_term(&requirement.body, frame), true));
                    }
                }
            }
            active.insert(frame, selected);
        }
        let helpers = source_helpers(plan, smt);
        Ok(Self {
            decisions,
            active,
            explain: roots.clone().into(),
            roots,
            explained: HashSet::new(),
            ground: HashMap::new(),
            assertions: HashSet::new(),
            constrained: HashSet::new(),
            goals: vec![],
            goal_set: HashSet::new(),
            transport: VecDeque::new(),
            equations: vec![],
            equation_compilers: VecDeque::new(),
            equation_jobs: VecDeque::new(),
            clauses: ClauseAgenda::default(),
            bodies: BodyAgenda::default(),
            dependencies: DependencyAgenda::new(plan, helpers.clone()),
            helpers: helpers.into(),
            generated: HashSet::new(),
            turn: 0,
        })
    }

    pub fn valid_for(
        &self,
        mut evaluate: impl FnMut(&Term) -> anyhow::Result<String>,
    ) -> anyhow::Result<bool> {
        for (term, old) in &self.decisions {
            if evaluate(term)?.trim() != old {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub fn refresh(&mut self, plan: &QuantifierPlan, smt: &dyn ProblemContext) {
        let added = smt
            .get_asserted_instantiation_terms()
            .into_iter()
            .filter(|t| self.assertions.insert((*t).clone()))
            .cloned()
            .collect::<Vec<_>>();
        for term in &added {
            self.register_formula(plan, term);
        }
        // New ground bodies can expose more helper applications. Replay only
        // the Boolean explanation; syntactic matching/join cursors stay put.
        if !added.is_empty() {
            self.explained.clear();
            self.explain.extend(self.roots.clone());
            self.helpers.extend(source_helpers(plan, smt));
        }
    }

    fn register_formula(&mut self, plan: &QuantifierPlan, term: &Term) {
        for (head, bodies) in plan.ground_instance_bodies(vec![term]) {
            let entries = self.ground.entry(head.clone()).or_default();
            for body in bodies {
                if entries.contains(&body) {
                    continue;
                }
                for truth in [true, false] {
                    if self.constrained.contains(&(head.clone(), truth)) {
                        self.explain.push_back((body.clone(), truth));
                    }
                }
                entries.push(body);
            }
        }
    }

    fn add_goal(&mut self, goal: Goal) {
        if !self.goal_set.insert(goal.clone()) {
            return;
        }
        let g = self.goals.len();
        self.goals.push(goal.clone());
        self.transport.push_back(g);
        for e in 0..self.equations.len() {
            self.equation_jobs
                .push_back((e, g, EquationCursor::default()));
        }
        self.clauses.add_goal(goal.clone());
        self.dependencies.add_goal(goal);
    }

    fn add_constraint(&mut self, plan: &QuantifierPlan, root: Term, truth: bool) {
        if !self.constrained.insert((root.clone(), truth)) {
            return;
        }
        if let Some(bodies) = self.ground.get(&root) {
            self.explain
                .extend(bodies.iter().cloned().map(|b| (b, truth)));
        }
        // False existentials constrain ground bodies with the opposite sign;
        // only true universals produce equations and backward-search roots.
        if !truth {
            self.bodies.add_demand(plan, &root);
            return;
        }
        self.bodies.add_guard(plan, &root);
        self.clauses.add_helper(plan, &root);
        self.dependencies.add_root(root.clone());
        self.equation_compilers
            .push_back(EquationCompiler::new(root));
    }

    pub fn pending(&self) -> usize {
        self.explain.len()
            + self.transport.len()
            + self.equation_jobs.len()
            + self.equation_compilers.len()
            + self.clauses.pending()
            + self.dependencies.pending()
            + self.helpers.len()
            + self.bodies.pending()
    }
    pub fn demands(&self) -> usize {
        self.goals.len()
    }

    pub fn advance(
        &mut self,
        plan: &QuantifierPlan,
        index: &TransitionIndex,
        smt: &dyn ProblemContext,
        budget: usize,
    ) -> anyhow::Result<(Vec<SymbolicInstance>, usize)> {
        let mut output = Vec::new();
        let mut decisions = std::mem::take(&mut self.decisions);
        let mut eval = |t: &Term| evaluate(smt, &mut decisions, t);
        let types = smt.get_array_types();
        let mut work = 0;
        let result = (|| {
            while work < budget && self.pending() > 0 {
                let phase = self.turn % 8;
                self.turn += 1;
                let mut instances = Vec::new();
                match phase {
                    0 => {
                        let Some((term, truth)) = self.explain.pop_front() else {
                            continue;
                        };
                        work += 1;
                        if !self.explained.insert((term.clone(), truth)) {
                            continue;
                        }
                        let e = plan.explain_slice(
                            vec![(term, truth)],
                            index,
                            &self.ground,
                            &mut eval,
                            1,
                        )?;
                        self.explain.extend(e.pending);
                        for (root, truth) in e.constrained {
                            self.add_constraint(plan, root, truth);
                        }
                        for goal in e.goals {
                            self.add_goal(goal);
                        }
                        instances = e.instances;
                    }
                    1 => {
                        let Some(g) = self.transport.pop_front() else {
                            continue;
                        };
                        work += 1;
                        let goal = self.goals[g].clone();
                        let mut alternatives = Vec::new();
                        transport(
                            &goal.atom,
                            false,
                            index,
                            &mut eval,
                            &self.active,
                            &types,
                            &mut instances,
                            &mut alternatives,
                            usize::MAX,
                        );
                        // Re-enter Boolean explanation, including constants and
                        // conditionals exposed by read-over-write reasoning.
                        self.explain
                            .extend(alternatives.into_iter().map(|t| (t, !goal.truth)));
                    }
                    2 => {
                        let Some((e, g, mut cursor)) = self.equation_jobs.pop_front() else {
                            continue;
                        };
                        work += 1;
                        let goal = &self.goals[g];
                        if let Some(term) =
                            cursor.step(&self.equations[e], &goal.atom, plan, &mut instances)
                        {
                            self.explain.push_back((term, !goal.truth));
                        }
                        if cursor.pending() {
                            self.equation_jobs.push_front((e, g, cursor));
                        }
                    }
                    3 => {
                        if self.clauses.pending() == 0 {
                            continue;
                        }
                        work += 1;
                        instances.extend(self.clauses.step(plan));
                    }
                    4 => {
                        if self.dependencies.pending() == 0 {
                            continue;
                        }
                        work += 1;
                        instances = self.dependencies.step(plan, &mut eval)?;
                    }
                    5 => {
                        let Some(helper) = self.helpers.pop_front() else {
                            continue;
                        };
                        work += 1;
                        if eval(&helper)? == "true" {
                            self.clauses.add_helper(plan, &helper);
                            self.bodies.add_source(plan, &helper);
                        }
                    }
                    6 => {
                        if self.bodies.pending() == 0 {
                            continue;
                        }
                        work += 1;
                        if let Some((instance, root)) = self.bodies.step(plan, &mut eval)? {
                            if let Some(root) = root {
                                self.explain.push_back((root.clone(), true));
                                self.dependencies.add_goal(Goal::new(&root, true));
                            }
                            instances.push(instance);
                        }
                    }
                    _ => {
                        let Some(mut compiler) = self.equation_compilers.pop_front() else {
                            continue;
                        };
                        work += 1;
                        compiler.step(plan);
                        if compiler.pending() {
                            self.equation_compilers.push_back(compiler);
                        } else {
                            let equations = compiler.finish();
                            if !equations.is_empty() {
                                let e = self.equations.len();
                                self.equations.push(equations);
                                for g in 0..self.goals.len() {
                                    self.equation_jobs
                                        .push_back((e, g, EquationCursor::default()));
                                }
                            }
                        }
                    }
                }
                for instance in instances {
                    if self.generated.insert(instance.term.clone()) {
                        self.register_formula(plan, &instance.term);
                        output.push(instance);
                    }
                }
            }
            Ok((output, work))
        })();
        self.decisions = decisions;
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        policy::term_selection::array::ArrayAstSize,
        smtlib_problem::SMTLIBProblem,
        smtlib_refinement_session::SmtlibRefinementSession,
        strategies::{Abstract, ProofStrategy, RefinementState},
        theories::quantifiers::{BinderKind, BinderRule},
        SolverBackend, YardbirdPolicy,
    };
    use smt2parser::{concrete::Symbol, vmt::array_abstractor::string_to_sort};

    #[test]
    fn equation_slice_does_not_expand_an_entire_wide_body() {
        let width = 128;
        let int = string_to_sort("Int");
        let body = format!(
            "(and {})",
            (0..width)
                .map(|i| format!("(= (f x) (g{i} x))"))
                .collect::<Vec<_>>()
                .join(" ")
        );
        let mut plan = QuantifierPlan::default();
        plan.rules = vec![BinderRule {
            name: "root".into(),
            kind: BinderKind::Forall,
            captures: vec![(Symbol("a".into()), int.clone())],
            variables: vec![(Symbol("x".into()), int)],
            body: body.parse().unwrap(),
            witnesses: vec![],
            result_sort: string_to_sort("Bool"),
            unit_capture: false,
        }];
        let problem = SMTLIBProblem::from_commands(vec![]).unwrap();
        let strategy: Box<dyn ProofStrategy<'_, RefinementState>> =
            Box::new(Abstract::<ArrayAstSize>::new(
                2,
                false,
                YardbirdPolicy::new(()),
                false,
            ));
        let smt = SmtlibRefinementSession::new_with_array_types(
            &problem,
            &strategy,
            SolverBackend::Z3,
            false,
            vec![("Int".into(), "Int".into())],
            None,
        )
        .unwrap();
        let index = TransitionIndex::default();
        let mut agenda = Agenda::new(&plan, &index, &smt, 0).unwrap();
        agenda.explain.clear();
        agenda.add_constraint(&plan, "(root 7)".parse().unwrap(), true);
        agenda.add_goal(Goal::new(&"(f 0)".parse().unwrap(), true));
        assert!(
            agenda.equations.is_empty(),
            "admission must not compile the body"
        );
        let mut compilation_work = 0;
        while !agenda.equation_compilers.is_empty() {
            agenda.turn = 7;
            let (_, work) = agenda.advance(&plan, &index, &smt, 1).unwrap();
            assert_eq!(work, 1);
            compilation_work += work;
            assert!(compilation_work <= width + 2);
        }
        assert_eq!(
            compilation_work,
            width + 2,
            "charge the helper, conjunction, and each equation"
        );
        agenda.turn = 2;
        let (_, work) = agenda.advance(&plan, &index, &smt, 1).unwrap();
        assert_eq!(work, 1);
        let alternatives = |agenda: &Agenda| {
            agenda.explain.iter().filter(|(t, _)| {
            matches!(t, Term::Application { qual_identifier, .. } if qual_identifier.get_name().starts_with('g'))
        }).count()
        };
        assert!(
            alternatives(&agenda) <= 1,
            "one work unit expanded {} equation alternatives",
            alternatives(&agenda)
        );
        assert_eq!(alternatives(&agenda), 1);
        let mut matching_work = work;
        while !agenda.equation_jobs.is_empty() {
            agenda.turn = 2;
            let before = alternatives(&agenda);
            let (_, work) = agenda.advance(&plan, &index, &smt, 1).unwrap();
            assert_eq!(work, 1);
            assert!(alternatives(&agenda) - before <= 1);
            matching_work += work;
            assert!(matching_work <= width + 1);
        }
        assert_eq!(
            alternatives(&agenda),
            width,
            "continuation must retain every alternative"
        );
        assert_eq!(
            matching_work,
            width + 1,
            "charge each attempt and traversal completion"
        );
    }
}
