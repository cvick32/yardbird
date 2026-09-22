//! Model-independent, typed binder instances shared by native and lowered solvers.
use std::cmp::Reverse;
use std::collections::{BTreeMap, BinaryHeap, HashSet};

use smt2parser::concrete::{Command, Term};
use smt2parser::vmt::{
    bmc::BMCBuilder, definition_graph::DefinitionFrameInfo, ReadsAndWrites, VMTModel,
};

use super::{abstract_sort, app, substitute, BinderKind, BinderRule, QuantifierPlan};
use crate::policy::{
    eager::EagerInstantiation,
    term_selection::{context::TermCostContext, TermCostFactory},
};
use crate::terms::language::translate_term_with_array_types;
use crate::theories::array::{
    eager::{Seed, Vocabulary},
    eager_source::EagerSource,
};

pub(crate) struct EagerBinders {
    pub source: EagerSource,
    plan: QuantifierPlan,
    builder: BMCBuilder,
    pub declarations: Vec<Command>,
}

impl EagerBinders {
    pub fn prepare(model: &VMTModel) -> anyhow::Result<Self> {
        // The same preparation as the abstract coordinator, before array rewrites.
        // Concrete uses this plan only to choose instances, retaining its native model.
        let mut quantifiers = super::refinement::QuantifierRefinement::default();
        let lowered = quantifiers.configure_eager_model(model.clone());
        if let Some(error) = quantifiers.configuration_error {
            anyhow::bail!(error);
        }
        let originals = model
            .as_commands()
            .into_iter()
            .filter_map(|command| match command {
                Command::DeclareFun { symbol, .. } | Command::DeclareConst { symbol, .. } => {
                    Some(symbol.0)
                }
                Command::DefineFun { sig, .. } => Some(sig.name.0),
                _ => None,
            })
            .collect::<HashSet<_>>();
        let seed_functions = quantifiers
            .plan
            .seeds
            .iter()
            .filter_map(|(_, term)| match term {
                Term::Application {
                    qual_identifier, ..
                } => Some(qual_identifier.get_name()),
                _ => None,
            })
            .collect::<HashSet<_>>();
        // Only nonempty-sort seeds are shared additions to the source vocabulary.
        // Abstract property witnesses must not become eager choices: the native
        // solver has its own property witnesses, so those would bias the ablation.
        let declarations = lowered
            .as_commands()
            .into_iter()
            .filter(|command| match command {
                Command::DeclareFun { symbol, .. } => {
                    !originals.contains(&symbol.0) && seed_functions.contains(&symbol.0)
                }
                _ => false,
            })
            .collect();
        let current = lowered.get_all_current_variable_names();
        let next = lowered.get_next_to_current_varible_names();
        let frames = DefinitionFrameInfo::new(lowered.get_helper_definitions(), &current, &next);
        let builder = BMCBuilder::with_definition_frames(current, next, frames);
        Ok(Self {
            source: EagerSource::vmt(&lowered),
            plan: quantifiers.plan,
            builder,
            declarations,
        })
    }

    pub fn generate<F: TermCostFactory>(
        &self,
        original: &EagerSource,
        cost_config: &F::Config,
        config: EagerInstantiation,
        lowered_binders: bool,
        abstract_arrays: bool,
    ) -> anyhow::Result<Vec<Seed>> {
        if config.max_candidates == 0 || config.max_instances == 0 {
            return Ok(vec![]);
        }
        let mut vocabulary = Vocabulary::new(&original.vocabulary);
        vocabulary.add_declarations(&self.declarations);
        let ground_terms = |input: &[Term]| {
            let mut terms = BTreeMap::new();
            for term in input {
                collect_ground(term, &HashSet::new(), &mut terms);
            }
            terms
        };
        let initial = ground_terms(&original.vocabulary.initial_and_transition);
        let property = ground_terms(&original.vocabulary.property);
        let cost_terms = |input: &BTreeMap<String, Term>| {
            input
                .values()
                .filter_map(|t| vocabulary.normalize(t))
                .map(|t| t.to_string())
                .collect()
        };
        let mut reads_writes = ReadsAndWrites::default();
        for term in initial
            .values()
            .chain(property.values())
            .filter_map(|t| vocabulary.normalize(t))
        {
            let _ = term.accept_term_visitor(&mut reads_writes);
        }
        let context = TermCostContext::source_vocabulary(
            cost_terms(&initial),
            cost_terms(&property),
            reads_writes,
        );
        let mut terms = initial;
        terms.extend(property);
        // Include source constants even if their only occurrences are bound up
        // in quantified formulas. Index state variables just once at frames 0/1.
        let mut builder = self.builder.clone();
        for command in original
            .vocabulary
            .declarations
            .iter()
            .chain(&self.declarations)
        {
            if let Command::DeclareFun {
                symbol, parameters, ..
            } = command
            {
                if parameters.is_empty() {
                    let term = builder.index_single_step_term(app(&symbol.0, vec![]));
                    terms.insert(term.to_string(), term);
                }
            }
        }
        for (_, term) in &self.plan.seeds {
            terms.insert(term.to_string(), term.clone());
        }
        let cost = F::from_context(&context, 0, cost_config);
        let score = |term: &Term| {
            vocabulary
                .expression(term)
                .map(|expr| cost.clone().cost_rec(&expr))
        };
        let mut pools = BTreeMap::<String, Vec<(u32, Term)>>::new();
        for term in terms.into_values() {
            if let (Some(sort), Some(cost)) = (vocabulary.sort(&term), score(&term)) {
                pools
                    .entry(abstract_sort(&sort).to_string())
                    .or_default()
                    .push((cost, term));
            }
        }
        for pool in pools.values_mut() {
            pool.sort_by_key(|(cost, term)| (*cost, term.to_string()));
            pool.truncate(config.max_candidates);
        }
        let source_globals = original
            .vocabulary
            .declarations
            .iter()
            .filter_map(|command| match command {
                Command::DeclareFun {
                    symbol, parameters, ..
                } if parameters.is_empty() => Some(symbol.0.clone()),
                Command::DeclareConst { symbol, .. } => Some(symbol.0.clone()),
                Command::DefineFun { sig, .. } if sig.parameters.is_empty() => {
                    Some(sig.name.0.clone())
                }
                _ => None,
            })
            .collect::<HashSet<_>>();
        let mut frontiers = Vec::new();
        for rule in &self.plan.rules {
            // Lowering can erase semantically unused outer parameters (e.g.
            // unary distinct). Do not emit a native formula with an unbound
            // parameter that no longer belongs to the abstract closure.
            let mut free = BTreeMap::new();
            let captures = rule.captures.iter().map(|(s, _)| s.0.clone()).collect();
            collect_ground(&self.plan.native_binders[&rule.name], &captures, &mut free);
            if free
                .values()
                .any(|t| matches!(t, Term::QualIdentifier(_)) && vocabulary.sort(t).is_none())
            {
                continue;
            }
            let mut domains = Vec::new();
            for (symbol, sort) in &rule.captures {
                let fixed = if rule.unit_capture {
                    Some(app("true", vec![]))
                } else if source_globals.contains(&symbol.0) {
                    Some(builder.index_single_step_term(app(&symbol.0, vec![])))
                } else {
                    None
                };
                domains.push(match fixed {
                    Some(term) => vec![(score(&term).unwrap_or(0), term)],
                    None => pools.get(&sort.to_string()).cloned().unwrap_or_default(),
                });
            }
            for (_, sort) in &rule.variables {
                domains.push(pools.get(&sort.to_string()).cloned().unwrap_or_default());
            }
            if domains.iter().any(Vec::is_empty) {
                continue;
            }
            frontiers.push((rule, Tuples::new(domains)));
        }
        let mut seeds = Vec::new();
        // Bound the Cartesian frontier and visit each binder before taking its
        // next tuple. Neither a model nor recursively generated terms enter pools.
        loop {
            let mut progress = false;
            for (rule, tuples) in &mut frontiers {
                let Some((cost, tuple)) = tuples.next() else {
                    continue;
                };
                progress = true;
                let (arguments, values) = tuple.split_at(rule.captures.len());
                let normalize = |terms: &[Term]| {
                    terms
                        .iter()
                        .map(|t| {
                            vocabulary.normalize(t).ok_or_else(|| {
                                anyhow::anyhow!("cannot normalize eager binder term {t}")
                            })
                        })
                        .collect::<anyhow::Result<Vec<_>>>()
                };
                let abstract_term = rule.instantiate(&normalize(arguments)?, &normalize(values)?);
                let normalized = translate_term_with_array_types(
                    abstract_term.clone(),
                    &original.vocabulary.array_types,
                )
                .ok_or_else(|| anyhow::anyhow!("cannot translate eager binder {}", rule.name))?;
                let term = if lowered_binders {
                    abstract_term
                } else {
                    let native = builder.index_single_step_term(native_instance(
                        rule,
                        &self.plan.native_binders[&rule.name],
                        arguments,
                        values,
                    ));
                    if abstract_arrays {
                        vocabulary.normalize_formula(&native).ok_or_else(|| {
                            anyhow::anyhow!("cannot abstract eager binder {}", rule.name)
                        })?
                    } else {
                        native
                    }
                };
                let bindings = rule
                    .captures
                    .iter()
                    .chain(&rule.variables)
                    .zip(tuple)
                    .map(|((s, _), t)| {
                        let t = if abstract_arrays {
                            vocabulary.normalize(&t).expect("validated binder term")
                        } else {
                            t
                        };
                        (s.0.clone(), t)
                    })
                    .collect();
                seeds.push(Seed {
                    term,
                    normalized,
                    rule: format!("input-binder-{}", rule.name),
                    bindings,
                    cost,
                    family: rule.name.clone(),
                });
                if seeds.len() == config.max_candidates {
                    return Ok(seeds);
                }
            }
            if !progress {
                break;
            }
        }
        Ok(seeds)
    }
}

fn native_instance(rule: &BinderRule, native: &Term, arguments: &[Term], values: &[Term]) -> Term {
    let capture_bindings = rule
        .captures
        .iter()
        .map(|(s, _)| s.clone())
        .zip(arguments.iter().cloned())
        .collect::<Vec<_>>();
    let proxy = substitute(native.clone(), capture_bindings.clone());
    let body = match native {
        Term::Forall { term, .. } | Term::Exists { term, .. } | Term::Lambda { term, .. } => {
            *term.clone()
        }
        _ => unreachable!(),
    };
    let mut bindings = capture_bindings;
    bindings.extend(
        rule.variables
            .iter()
            .map(|(s, _)| s.clone())
            .zip(values.iter().cloned()),
    );
    let body = substitute(body, bindings);
    match rule.kind {
        BinderKind::Forall => app("=>", vec![proxy, body]),
        BinderKind::Exists => app("=>", vec![body, proxy]),
        BinderKind::Lambda => app(
            "=",
            vec![
                values.iter().fold(proxy, |array, index| {
                    app("select", vec![array, index.clone()])
                }),
                body,
            ],
        ),
    }
}

/// Return whether a subtree is ground, while retaining ground children under binders.
fn collect_ground(term: &Term, bound: &HashSet<String>, out: &mut BTreeMap<String, Term>) -> bool {
    let ground = match term {
        Term::QualIdentifier(id) => !bound.contains(&id.get_name()),
        Term::Constant(_) => true,
        Term::Application { arguments, .. } => {
            let mut ground = true;
            for term in arguments {
                ground &= collect_ground(term, bound, out);
            }
            ground
        }
        Term::Forall { vars, term } | Term::Exists { vars, term } | Term::Lambda { vars, term } => {
            let mut inner = bound.clone();
            inner.extend(vars.iter().map(|(s, _)| s.0.clone()));
            collect_ground(term, &inner, out);
            false
        }
        Term::Attributes { term, .. } => {
            collect_ground(term, bound, out);
            false
        }
        _ => false,
    };
    if ground {
        out.insert(term.to_string(), term.clone());
    }
    ground
}

struct Tuples {
    domains: Vec<Vec<(u32, Term)>>,
    pending: BinaryHeap<Reverse<(u32, Vec<usize>)>>,
    seen: HashSet<Vec<usize>>,
}
impl Tuples {
    fn new(domains: Vec<Vec<(u32, Term)>>) -> Self {
        let initial = vec![0; domains.len()];
        let cost = domains
            .iter()
            .fold(0_u32, |sum, d| sum.saturating_add(d[0].0));
        Self {
            domains,
            pending: [Reverse((cost, initial.clone()))].into(),
            seen: [initial].into(),
        }
    }
    fn next(&mut self) -> Option<(u32, Vec<Term>)> {
        let Reverse((cost, indices)) = self.pending.pop()?;
        for slot in 0..indices.len() {
            let mut next = indices.clone();
            next[slot] += 1;
            if next[slot] < self.domains[slot].len() && self.seen.insert(next.clone()) {
                let score = next.iter().enumerate().fold(0_u32, |sum, (i, &j)| {
                    sum.saturating_add(self.domains[i][j].0)
                });
                self.pending.push(Reverse((score, next)));
            }
        }
        Some((
            cost,
            indices
                .into_iter()
                .enumerate()
                .map(|(i, j)| self.domains[i][j].1.clone())
                .collect(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::policy::term_selection::array::ArrayAstSize;
    use smt2parser::{concrete::SyntaxBuilder, CommandStream};

    fn model(input: &str) -> VMTModel {
        VMTModel::checked_from(
            CommandStream::new(input.as_bytes(), SyntaxBuilder, None)
                .collect::<Result<Vec<_>, _>>()
                .unwrap(),
        )
        .unwrap()
    }

    const INPUT: &str = r#"
        (declare-sort S 0)
        (declare-fun k () S)
        (declare-fun p (S) Bool)
        (declare-fun r (S S) Bool)
        (declare-fun flag () Bool)
        (define-fun init () Bool (!
          (and (not (forall ((x S)) (p x)))
               (=> flag (forall ((x S) (y S)) (r x y)))) :init true))
        (define-fun trans () Bool (!
          (exists ((x S)) (forall ((y S)) (r x y))) :trans true))
        (define-fun prop () Bool (! false :invar-property 0))
    "#;

    fn assert_native_instances_valid(input: &str) {
        let model = model(input);
        let source = EagerSource::vmt(&model);
        let binders = EagerBinders::prepare(&model).unwrap();
        let seeds = binders
            .generate::<ArrayAstSize>(
                &source,
                &(),
                EagerInstantiation {
                    max_candidates: 100,
                    ..Default::default()
                },
                false,
                false,
            )
            .unwrap();
        assert!(!seeds.is_empty());
        let mut builder = binders.builder.clone();
        let declarations = model
            .as_commands()
            .into_iter()
            .chain(binders.declarations.clone())
            .filter(|c| matches!(c, Command::DeclareFun { .. } | Command::DeclareSort { .. }))
            .map(|c| c.accept(&mut builder).unwrap().to_string())
            .collect::<Vec<_>>()
            .join("\n");
        for seed in seeds {
            let solver = z3::Solver::new();
            solver.from_string(format!("{declarations}\n(assert (not {}))", seed.term));
            assert_eq!(
                solver.check(),
                z3::SatResult::Unsat,
                "invalid seed: {}",
                seed.term
            );
        }
    }

    #[test]
    fn native_instances_are_valid_with_negation_conditionals_and_nested_binders() {
        assert_native_instances_valid(INPUT);
    }

    #[test]
    fn sorts_without_source_constants_receive_shared_nonempty_sort_seeds() {
        assert_native_instances_valid(&INPUT.replace("(declare-fun k () S)", ""));
    }

    #[test]
    fn lambda_and_shadowed_binder_instances_are_valid_across_frames() {
        assert_native_instances_valid(
            r#"
            (declare-fun k () Int)
            (define-fun .k () Int (! k :next k.next))
            (declare-fun a () (Array Int Int))
            (define-fun init () Bool (! true :init true))
            (define-fun trans () Bool (!
                (and (= a (lambda ((x Int)) (+ x k.next)))
                     (forall ((k Int)) (exists ((k Int)) (= k 0)))) :trans true))
            (define-fun prop () Bool (! false :invar-property 0))
        "#,
        );
    }

    #[test]
    fn tuple_frontier_is_bounded_and_cost_ordered() {
        let mut tuples = Tuples::new(vec![
            vec![(1, app("a", vec![])), (8, app("b", vec![]))],
            vec![(2, app("c", vec![])), (3, app("d", vec![]))],
        ]);
        let costs = std::iter::from_fn(|| tuples.next())
            .map(|(cost, _)| cost)
            .collect::<Vec<_>>();
        assert_eq!(costs, [3, 4, 10, 11]);
        let model = model(INPUT);
        let binders = EagerBinders::prepare(&model).unwrap();
        let seeds = binders
            .generate::<ArrayAstSize>(
                &EagerSource::vmt(&model),
                &(),
                EagerInstantiation {
                    max_candidates: 3,
                    ..Default::default()
                },
                true,
                true,
            )
            .unwrap();
        assert_eq!(seeds.len(), 3);
        assert_eq!(
            seeds.iter().map(|s| &s.rule).collect::<HashSet<_>>().len(),
            3
        );
    }

    #[test]
    fn abstract_property_witnesses_do_not_bias_eager_choices() {
        let input = INPUT.replace(
            "(! false :invar-property 0)",
            "(! (forall ((x S)) (exists ((y S)) (r x y))) :invar-property 0)",
        );
        let model = model(&input);
        let binders = EagerBinders::prepare(&model).unwrap();
        assert!(binders
            .declarations
            .iter()
            .all(|d| !d.to_string().contains("herbrand")));
        let source = EagerSource::vmt(&model);
        for lowered in [false, true] {
            let seeds = binders
                .generate::<ArrayAstSize>(
                    &source,
                    &(),
                    EagerInstantiation::default(),
                    lowered,
                    lowered,
                )
                .unwrap();
            assert!(!seeds.is_empty());
            assert!(seeds
                .iter()
                .all(|s| !s.term.to_string().contains("herbrand")));
        }
        assert_native_instances_valid(&input);
    }

    #[test]
    fn bound_variables_never_leak_into_source_pools() {
        let term = "(forall ((x Int)) (= (+ x 1) (+ k 2)))".parse().unwrap();
        let mut terms = BTreeMap::new();
        collect_ground(&term, &HashSet::new(), &mut terms);
        assert!(terms.contains_key("(+ k 2)"));
        assert!(!terms.contains_key("x"));
        assert!(!terms.contains_key("(+ x 1)"));
    }
}
