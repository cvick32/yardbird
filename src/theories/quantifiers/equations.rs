//! Demand-directed instances of universally quantified equations. Source
//! helper captures anchor a path; matching an equation supplies its tuple.
//! Replacements are search hints only. Every emitted lemma retains its helper.
use super::{app, dependency_search::unify, substitute, BinderKind, QuantifierPlan};
use crate::rule_matching::{candidate::SymbolicInstance, rule::QuantifiedRule};
use smt2parser::concrete::{Sort, Symbol, Term};
use std::collections::{HashMap, VecDeque};

struct Equation {
    left: Term,
    right: Term,
    variables: HashMap<Symbol, Sort>,
    path: Vec<SymbolicInstance>,
}

#[derive(Default)]
pub(crate) struct QuantifiedEquations {
    by_head: HashMap<String, Vec<Equation>>,
}

impl QuantifiedEquations {
    pub(crate) fn is_empty(&self) -> bool {
        self.by_head.is_empty()
    }
}

struct CompilationFrame {
    terms: std::vec::IntoIter<Term>,
    variables: HashMap<Symbol, Sort>,
    path: Vec<SymbolicInstance>,
}

/// Retain sibling and binder-body traversal across policy slices. One step
/// visits one source node; a wide conjunction does not enqueue all its children.
pub(crate) struct EquationCompiler {
    equations: QuantifiedEquations,
    queue: VecDeque<CompilationFrame>,
}

impl EquationCompiler {
    pub fn new(root: Term) -> Self {
        Self {
            equations: QuantifiedEquations::default(),
            queue: VecDeque::from([CompilationFrame {
                terms: vec![root].into_iter(),
                variables: HashMap::new(),
                path: Vec::new(),
            }]),
        }
    }

    pub fn pending(&self) -> bool {
        !self.queue.is_empty()
    }

    pub fn finish(self) -> QuantifiedEquations {
        assert!(
            !self.pending(),
            "equation compilation must finish before matching"
        );
        self.equations
    }

    pub fn step(&mut self, plan: &QuantifierPlan) {
        let Some(mut frame) = self.queue.pop_front() else {
            return;
        };
        let term = frame.terms.next().expect("nonempty compilation frame");
        let mut variables = frame.variables.clone();
        let mut path = frame.path.clone();
        if frame.terms.len() > 0 {
            self.queue.push_front(frame);
        }
        let Term::Application {
            qual_identifier,
            arguments,
        } = term
        else {
            return;
        };
        let name = qual_identifier.get_name();
        if name == "and" {
            if !arguments.is_empty() {
                self.queue.push_back(CompilationFrame {
                    terms: arguments.into_iter(),
                    variables,
                    path,
                });
            }
        } else if name == "=" && arguments.len() == 2 {
            for (left, right) in [
                (&arguments[0], &arguments[1]),
                (&arguments[1], &arguments[0]),
            ] {
                let Term::Application {
                    qual_identifier, ..
                } = left
                else {
                    continue;
                };
                // Boolean connectives describe a body, not a function to
                // look up. Either orientation of a functional equality is usable.
                let head = qual_identifier.get_name();
                if matches!(head.as_str(), "and" | "or" | "not" | "=>" | "ite" | "=") {
                    continue;
                }
                self.equations
                    .by_head
                    .entry(head)
                    .or_default()
                    .push(Equation {
                        left: left.clone(),
                        right: right.clone(),
                        variables: variables.clone(),
                        path: path.clone(),
                    });
            }
        } else if let Some(rule) = plan
            .rules
            .iter()
            .find(|r| r.name == name && r.kind == BinderKind::Forall)
        {
            if arguments.len() != rule.captures.len() {
                return;
            }
            // Binder nesting is finite in the lowered source DAG.
            variables.extend(rule.variables.iter().cloned());
            let values = rule
                .variables
                .iter()
                .map(|(s, _)| app(&s.0, vec![]))
                .collect::<Vec<_>>();
            let instance = rule.instantiate(&arguments, &values);
            let Term::Application {
                arguments: implication,
                ..
            } = &instance
            else {
                unreachable!()
            };
            let body = implication[1].clone();
            path.push(SymbolicInstance {
                rule: QuantifiedRule::input_binder(&rule.name),
                term: instance,
                bindings: rule
                    .captures
                    .iter()
                    .chain(&rule.variables)
                    .map(|(s, _)| s.0.clone())
                    .zip(arguments.iter().chain(&values).cloned())
                    .collect(),
            });
            self.queue.push_back(CompilationFrame {
                terms: vec![body].into_iter(),
                variables,
                path,
            });
        }
    }
}

#[derive(Default)]
struct MatchFrame {
    /// Argument of the parent term; absent for the root.
    child: Option<usize>,
    equation: usize,
    next_child: usize,
}

/// A depth-first cursor over one goal and its same-head equation alternatives.
/// One step attempts one equation or advances one traversal edge. Even subtrees
/// with no matching equation consume work, and opaque captures stay intact.
pub(crate) struct EquationCursor {
    stack: Vec<MatchFrame>,
}

impl Default for EquationCursor {
    fn default() -> Self {
        Self {
            stack: vec![MatchFrame::default()],
        }
    }
}

impl EquationCursor {
    pub fn pending(&self) -> bool {
        !self.stack.is_empty()
    }

    pub fn step(
        &mut self,
        equations: &QuantifiedEquations,
        root: &Term,
        plan: &QuantifierPlan,
        instances: &mut Vec<SymbolicInstance>,
    ) -> Option<Term> {
        let mut term = root;
        let mut parents = Vec::new();
        for frame in self.stack.iter().skip(1) {
            let Term::Application {
                qual_identifier,
                arguments,
            } = term
            else {
                unreachable!("cursor descends only into applications")
            };
            let child = frame.child.unwrap();
            parents.push((qual_identifier, arguments, child));
            term = &arguments[child];
        }
        let frame = self.stack.last_mut()?;
        let Term::Application {
            qual_identifier,
            arguments,
        } = term
        else {
            self.stack.pop();
            return None;
        };
        let name = qual_identifier.get_name();
        if let Some(equation) = equations
            .by_head
            .get(&name)
            .and_then(|eqs| eqs.get(frame.equation))
        {
            frame.equation += 1;
            let mut bindings = HashMap::new();
            if !unify(
                &equation.left,
                term,
                &equation.variables,
                &plan.signatures,
                &mut bindings,
            ) || equation.variables.keys().any(|v| !bindings.contains_key(v))
            {
                return None;
            }
            let bindings = bindings.into_iter().collect::<Vec<_>>();
            for template in &equation.path {
                instances.push(SymbolicInstance {
                    rule: template.rule.clone(),
                    term: substitute(template.term.clone(), bindings.clone()),
                    bindings: template
                        .bindings
                        .iter()
                        .map(|(s, t)| (s.clone(), substitute(t.clone(), bindings.clone())))
                        .collect(),
                });
            }
            let mut alternative = substitute(equation.right.clone(), bindings);
            for (identifier, arguments, child) in parents.into_iter().rev() {
                let mut arguments = arguments.clone();
                arguments[child] = alternative;
                alternative = Term::Application {
                    qual_identifier: identifier.clone(),
                    arguments,
                };
            }
            return Some(alternative);
        }
        // Reads descend into their array only, never into opaque witness indices.
        let children = if name.starts_with("Read_") {
            arguments.len().min(1)
        } else if matches!(
            name.as_str(),
            "=" | "distinct"
                | "not"
                | "and"
                | "or"
                | "=>"
                | "ite"
                | "<"
                | ">"
                | "<="
                | ">="
                | "+"
                | "-"
                | "*"
        ) {
            arguments.len()
        } else {
            0
        };
        if frame.next_child < children {
            let child = frame.next_child;
            frame.next_child += 1;
            self.stack.push(MatchFrame {
                child: Some(child),
                ..Default::default()
            });
        } else {
            self.stack.pop();
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theories::quantifiers::BinderRule;
    use smt2parser::vmt::array_abstractor::string_to_sort;

    fn alternatives(
        equations: &QuantifiedEquations,
        term: &Term,
        plan: &QuantifierPlan,
        remaining: &mut usize,
        instances: &mut Vec<SymbolicInstance>,
    ) -> Vec<Term> {
        let mut cursor = EquationCursor::default();
        let mut output = Vec::new();
        while *remaining > 0 && cursor.pending() {
            *remaining -= 1;
            output.extend(cursor.step(equations, term, plan, instances));
        }
        output
    }

    #[test]
    fn matching_cursor_resumes_nested_terms_and_charges_failed_attempts() {
        let plan = QuantifierPlan::default();
        let int = string_to_sort("Int");
        let equations = QuantifiedEquations {
            by_head: HashMap::from([(
                "f".into(),
                vec![Equation {
                    left: "(f x)".parse().unwrap(),
                    right: "(g x)".parse().unwrap(),
                    variables: HashMap::from([(Symbol("x".into()), int)]),
                    path: vec![],
                }],
            )]),
        };
        let goal: Term = "(and (= (f 0) 0) (= (f true) 0) (= (f 1) 1) (= (opaque (f 2)) 2))"
            .parse()
            .unwrap();
        let expected: Vec<Term> = [
            "(and (= (g 0) 0) (= (f true) 0) (= (f 1) 1) (= (opaque (f 2)) 2))",
            "(and (= (f 0) 0) (= (f true) 0) (= (g 1) 1) (= (opaque (f 2)) 2))",
        ]
        .into_iter()
        .map(|t| t.parse().unwrap())
        .collect();
        let mut cursor = EquationCursor::default();
        let mut output = Vec::new();
        let mut work = 0;
        while cursor.pending() {
            output.extend(cursor.step(&equations, &goal, &plan, &mut Vec::new()));
            work += 1;
            assert!(work < 100, "nested traversal must eventually finish");
        }
        assert_eq!(output, expected);
        assert!(
            work > output.len(),
            "failed attempts and traversal also consume work"
        );
        assert_eq!(
            output,
            alternatives(&equations, &goal, &plan, &mut 100, &mut Vec::new())
        );

        // A failed same-head equation is still one full attempt, even without
        // emitted instances. The next step must not retry that equation.
        let bad_goal = "(f true)".parse().unwrap();
        let mut cursor = EquationCursor::default();
        assert!(cursor
            .step(&equations, &bad_goal, &plan, &mut Vec::new())
            .is_none());
        assert!(cursor.pending());
        assert!(cursor
            .step(&equations, &bad_goal, &plan, &mut Vec::new())
            .is_none());
        assert!(!cursor.pending());

        // Read indices (and opaque applications above) must not be rewritten.
        let read = "(Read_Int_Int (f 0) (f 1))".parse().unwrap();
        assert_eq!(
            alternatives(&equations, &read, &plan, &mut 100, &mut Vec::new()),
            vec!["(Read_Int_Int (g 0) (f 1))".parse::<Term>().unwrap()]
        );
    }

    #[test]
    fn demand_binds_nested_equation_path_without_changing_captures() {
        let int = string_to_sort("Int");
        let bool_sort = string_to_sort("Bool");
        let fields = |names: &[&str]| {
            names
                .iter()
                .map(|s| (Symbol((*s).into()), int.clone()))
                .collect()
        };
        let rule = |name: &str, captures: &[&str], variables: &[&str], body: &str| BinderRule {
            name: name.into(),
            kind: BinderKind::Forall,
            captures: fields(captures),
            variables: fields(variables),
            body: body.parse().unwrap(),
            witnesses: vec![],
            result_sort: bool_sort.clone(),
            unit_capture: false,
        };
        let plan = QuantifierPlan {
            rules: vec![
                rule("outer", &["a", "b"], &["x"], "(inner a b x)"),
                rule(
                    "inner",
                    &["a", "b", "i"],
                    &["y"],
                    "(= (at b i y) (or (at a i y) (p i y)))",
                ),
            ],
            signatures: HashMap::from([
                ("old".into(), (vec![], int.clone())),
                ("new".into(), (vec![], int.clone())),
                ("at".into(), (vec![int.clone(); 3], bool_sort.clone())),
                ("p".into(), (vec![int.clone(); 2], bool_sort.clone())),
            ]),
            ..Default::default()
        };
        let mut remaining = 128;
        let mut compiler = EquationCompiler::new("(outer old@0 new@1)".parse().unwrap());
        while compiler.pending() {
            compiler.step(&plan);
        }
        let equations = compiler.finish();
        let mut instances = Vec::new();
        let output = alternatives(
            &equations,
            &"(at new@1 4 9)".parse().unwrap(),
            &plan,
            &mut remaining,
            &mut instances,
        );
        assert_eq!(
            output,
            vec!["(or (at old@0 4 9) (p 4 9))".parse::<Term>().unwrap()]
        );
        assert_eq!(instances.len(), 2);
        assert_eq!(
            instances[0].term.to_string(),
            "(=> (outer old@0 new@1) (inner old@0 new@1 4))"
        );
        // An independent quantified oracle checks the actual emitted lemmas,
        // including their helper guards, without assuming the root is true.
        let solver = z3::Solver::new();
        solver.from_string(format!("(declare-fun at (Int Int Int) Bool) (declare-fun p (Int Int) Bool)
            (define-fun inner ((a Int) (b Int) (i Int)) Bool (forall ((y Int)) (= (at b i y) (or (at a i y) (p i y)))))
            (define-fun outer ((a Int) (b Int)) Bool (forall ((x Int)) (inner a b x)))
            (declare-const old@0 Int) (declare-const new@1 Int)
            (assert (not (and {} {})))", instances[0].term, instances[1].term));
        assert_eq!(solver.check(), z3::SatResult::Unsat);
        for term in [
            "(at new@2 4 9)",
            "(opaque (at new@1 4 9))",
            "(at new@1 true 9)",
        ] {
            assert!(
                alternatives(
                    &equations,
                    &term.parse().unwrap(),
                    &plan,
                    &mut remaining,
                    &mut Vec::new()
                )
                .is_empty(),
                "{term}"
            );
        }
        assert!(alternatives(
            &equations,
            &"(at new@1 4 9)".parse().unwrap(),
            &plan,
            &mut 0,
            &mut Vec::new()
        )
        .is_empty());
    }
}
