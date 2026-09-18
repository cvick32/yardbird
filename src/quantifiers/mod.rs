//! Closure conversion for quantified formulas and SMT array lambdas.
//!
//! A helper denotes the value of each binder expression as a function of its
//! free variables. Universal instances constrain one direction; a Skolem
//! witness constrains the other. Keeping both directions makes this valid in
//! arbitrary Boolean positions, including negated and alternating quantifiers.
use std::collections::{BTreeMap, HashMap, HashSet};

use smt2parser::{
    concrete::{Command, Constant, Identifier, QualIdentifier, Sort, Symbol, Term},
    let_extract::LetExtract,
    vmt::{array_abstractor::string_to_sort, split_framed_symbol, VMTModel},
};

use crate::instantiation::language::TermLanguage;
mod lowering;
pub mod provenance;
#[cfg(test)]
use lowering::lower_model;
use lowering::sort_name;
pub(crate) use lowering::{
    abstract_sort, app, contains_binders, lower_model_with_provenance, substitute, term_sort,
};
mod binder_request;
#[cfg(test)]
mod binder_request_tests;
mod dependency_search;
mod violation_plan;
use crate::instantiation::{
    candidate::InstantiationBatch,
    engine::{CompiledQuantifiedRule, InstantiationOptions},
    language::translate_term_with_array_types,
    rule::QuantifiedRule,
};
pub(crate) use binder_request::{BinderSearch, BinderSearchRequest};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BinderKind {
    Forall,
    Exists,
    Lambda,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum SearchPhase {
    Witnesses,
    TriggeredConflicts,
    Conflicts,
    Expand,
}

#[derive(Clone, Debug)]
pub(crate) struct BinderRule {
    pub name: String,
    pub kind: BinderKind,
    pub captures: Vec<(Symbol, Sort)>,
    pub variables: Vec<(Symbol, Sort)>,
    pub body: Term,
    pub witnesses: Vec<String>,
    pub result_sort: Sort,
    /// A dummy argument keeps a closed helper rigid; it is always literal true.
    pub unit_capture: bool,
}

impl BinderRule {
    pub fn instantiate(&self, arguments: &[Term], values: &[Term]) -> Term {
        let bindings = self
            .captures
            .iter()
            .map(|(s, _)| s.clone())
            .zip(arguments.iter().cloned())
            .chain(
                self.variables
                    .iter()
                    .map(|(s, _)| s.clone())
                    .zip(values.iter().cloned()),
            )
            .collect();
        let body = substitute(self.body.clone(), bindings);
        let proxy = app(&self.name, arguments.to_vec());
        match self.kind {
            BinderKind::Forall => app("=>", vec![proxy, body]),
            BinderKind::Exists => app("=>", vec![body, proxy]),
            BinderKind::Lambda => {
                let mut read = proxy;
                let mut sort = self.result_sort.clone();
                // The native result sort is retained for recovering nested read types.
                for (value, (_, index)) in values.iter().zip(&self.variables) {
                    let Sort::Parameterized { parameters, .. } = sort else {
                        unreachable!()
                    };
                    sort = parameters[1].clone();
                    read = app(
                        &format!("Read_{}_{}", sort_name(index), sort_name(&sort)),
                        vec![read, value.clone()],
                    );
                }
                app("=", vec![read, body])
            }
        }
    }

    pub fn witness_instance(&self, arguments: &[Term]) -> Option<Term> {
        if self.kind == BinderKind::Lambda {
            return None;
        }
        let values = self
            .witnesses
            .iter()
            .map(|name| app(name, arguments.to_vec()))
            .collect::<Vec<_>>();
        let bindings = self
            .captures
            .iter()
            .map(|(s, _)| s.clone())
            .zip(arguments.iter().cloned())
            .chain(self.variables.iter().map(|(s, _)| s.clone()).zip(values))
            .collect();
        let body = substitute(self.body.clone(), bindings);
        let proxy = app(&self.name, arguments.to_vec());
        Some(match self.kind {
            BinderKind::Forall => app("=>", vec![app("not", vec![proxy]), app("not", vec![body])]),
            BinderKind::Exists => app("=>", vec![proxy, body]),
            BinderKind::Lambda => unreachable!(),
        })
    }
}

impl BinderRule {
    fn compile(
        &self,
        phase: SearchPhase,
        types: &[(String, String)],
    ) -> Option<anyhow::Result<CompiledQuantifiedRule<()>>> {
        self.compile_with_bindings(phase, types, &[])
    }

    fn compile_with_bindings(
        &self,
        phase: SearchPhase,
        types: &[(String, String)],
        supplied: &[(Symbol, Term)],
    ) -> Option<anyhow::Result<CompiledQuantifiedRule<()>>> {
        self.compile_plan(phase, types, supplied, None)
    }

    fn compile_plan(
        &self,
        phase: SearchPhase,
        types: &[(String, String)],
        supplied: &[(Symbol, Term)],
        plan: Option<&[violation_plan::SignedAtom]>,
    ) -> Option<anyhow::Result<CompiledQuantifiedRule<()>>> {
        use egg::{ENodeOrVar, MultiPattern, Pattern, Var};
        let arguments = if self.unit_capture {
            vec![app("true", vec![])]
        } else {
            self.captures
                .iter()
                .map(|(symbol, _)| app(&symbol.0, vec![]))
                .collect::<Vec<_>>()
        };
        let values = self
            .variables
            .iter()
            .map(|(symbol, _)| app(&symbol.0, vec![]))
            .collect::<Vec<_>>();
        let formula = if phase == SearchPhase::Witnesses {
            self.witness_instance(&arguments)?
        } else {
            self.instantiate(&arguments, &values)
        };
        Some((|| {
            let bindings = self
                .captures
                .iter()
                .chain(&self.variables)
                .enumerate()
                .map(|(index, (symbol, _))| {
                    (
                        symbol.0.clone(),
                        format!("?binding{index}").parse::<Var>().unwrap(),
                    )
                })
                .collect::<HashMap<_, _>>();
            let pattern = |term: Term| -> anyhow::Result<Pattern<TermLanguage>> {
                let expression = translate_term_with_array_types(term, types)
                    .ok_or_else(|| anyhow::anyhow!("could not compile binder {}", self.name))?;
                let ast = expression
                    .as_ref()
                    .iter()
                    .map(|node| match node {
                        TermLanguage::Symbol(symbol) if bindings.contains_key(symbol.as_str()) => {
                            ENodeOrVar::Var(bindings[symbol.as_str()])
                        }
                        node => ENodeOrVar::ENode(node.clone()),
                    })
                    .collect::<Vec<_>>()
                    .into();
                Ok(Pattern::new(ast))
            };
            let fixed_bindings = supplied
                .iter()
                .map(|(symbol, term)| {
                    let expression = translate_term_with_array_types(term.clone(), types)
                        .ok_or_else(|| anyhow::anyhow!("cannot translate binder binding {term}"))?;
                    Ok((bindings[&symbol.0], expression))
                })
                .collect::<anyhow::Result<Vec<_>>>()?;
            let original_formula = pattern(formula)?;
            let formula = binder_request::specialize(original_formula.clone(), &fixed_bindings);
            let anchor = pattern(app(&self.name, arguments))?;
            // Bind supplied arguments before the helper, trigger, and domain
            // joins. Ground terms are inserted as ENodes, never reinterpreted
            // as binder variables even if symbol names happen to coincide.
            let mut patterns = fixed_bindings
                .iter()
                .map(|(var, expression)| {
                    (
                        *var,
                        expression
                            .as_ref()
                            .iter()
                            .cloned()
                            .map(ENodeOrVar::ENode)
                            .collect::<Vec<_>>()
                            .into(),
                    )
                })
                .collect::<Vec<_>>();
            patterns.push(("?root".parse().unwrap(), anchor.ast));
            // Search only the active direction of the binder equivalence.
            // In particular, expansion must not invent terms from a vacuous
            // universal direction while its opposite witness is active.
            if self.kind != BinderKind::Lambda {
                let proxy_is_true =
                    (self.kind == BinderKind::Exists) == (phase == SearchPhase::Witnesses);
                let value = if proxy_is_true { "true" } else { "false" };
                patterns.push(("?root".parse().unwrap(), pattern(app(value, vec![]))?.ast));
            }
            let mut filters = Vec::new();
            if let Some(plan) = plan {
                // Each alternative gets an independent cursor. Predicates bind
                // shared variables and their required truth values before any
                // remaining typed-domain completion.
                for (index, atom) in plan.iter().enumerate() {
                    let atom_pattern = pattern(atom.term.clone())?;
                    if violation_plan::is_filter(atom) {
                        filters.push((
                            binder_request::specialize(atom_pattern, &fixed_bindings).ast,
                            atom.truth,
                        ));
                    } else {
                        let variable = format!("?atom{index}").parse().unwrap();
                        patterns.push((variable, atom_pattern.ast));
                        patterns.push((
                            variable,
                            pattern(app(if atom.truth { "true" } else { "false" }, vec![]))?.ast,
                        ));
                    }
                }
            } else if phase == SearchPhase::TriggeredConflicts {
                use egg::Language;
                let bound = self
                    .variables
                    .iter()
                    .map(|(symbol, _)| bindings[&symbol.0])
                    .collect::<HashSet<_>>();
                let mut triggers = original_formula
                    .ast
                    .as_ref()
                    .iter()
                    .filter_map(|node| {
                        if !matches!(
                            node,
                            ENodeOrVar::ENode(TermLanguage::ReadTyped(_) | TermLanguage::Apply(_))
                        ) {
                            return None;
                        }
                        let ast = node.build_recexpr(|id| original_formula.ast[id].clone());
                        let pattern = Pattern::new(ast);
                        let coverage = pattern
                            .vars()
                            .iter()
                            .filter(|variable| bound.contains(variable))
                            .count();
                        (coverage > 0).then_some((coverage, pattern))
                    })
                    .collect::<Vec<_>>();
                // Prefer an atom binding many quantified variables, with a
                // small deterministic trigger when coverage ties.
                triggers.sort_by_key(|(coverage, pattern)| {
                    (
                        std::cmp::Reverse(*coverage),
                        pattern.ast.as_ref().len(),
                        pattern.to_string(),
                    )
                });
                if let Some((_, trigger)) = triggers.into_iter().next() {
                    patterns.push(("?body_match".parse().unwrap(), trigger.ast));
                }
            }
            if phase != SearchPhase::Witnesses {
                for (index, (symbol, sort)) in self.variables.iter().enumerate() {
                    let mut domain = egg::PatternAst::default();
                    let sort = domain.add(ENodeOrVar::ENode(TermLanguage::SortTag(
                        sort.to_string().into(),
                    )));
                    let value = domain.add(ENodeOrVar::Var(bindings[&symbol.0]));
                    domain.add(ENodeOrVar::ENode(TermLanguage::Domain([sort, value])));
                    patterns.push((format!("?domain{index}").parse().unwrap(), domain));
                }
            }
            Ok(CompiledQuantifiedRule::input_binder(
                QuantifiedRule::input_binder(&self.name),
                MultiPattern::new(patterns),
                formula,
                fixed_bindings,
            )
            .with_binder_filters(filters, plan.is_some()))
        })())
    }
}

#[derive(Default)]
pub(crate) struct QuantifierPlan {
    pub rules: Vec<BinderRule>,
    pub signatures: HashMap<String, (Vec<Sort>, Sort)>,
    pub seeds: Vec<(Sort, Term)>,
    compiled: std::cell::RefCell<Option<std::rc::Rc<CompiledBinderRules>>>,
}

impl QuantifierPlan {
    fn compiled(
        &self,
        types: &[(String, String)],
    ) -> anyhow::Result<std::rc::Rc<CompiledBinderRules>> {
        let mut cached = self.compiled.borrow_mut();
        if let Some(rules) = cached.as_ref().filter(|rules| rules.types == types) {
            return Ok(rules.clone());
        }
        let mut phases = HashMap::new();
        for phase in [
            SearchPhase::Witnesses,
            SearchPhase::TriggeredConflicts,
            SearchPhase::Conflicts,
            SearchPhase::Expand,
        ] {
            let mut rules = Vec::new();
            for rule in &self.rules {
                if phase == SearchPhase::TriggeredConflicts {
                    if let Some(plans) = violation_plan::plans(rule) {
                        for plan in plans {
                            if let Some(compiled) =
                                rule.compile_plan(phase, types, &[], Some(&plan))
                            {
                                rules.push(compiled?);
                            }
                        }
                        continue;
                    }
                }
                if let Some(compiled) = rule.compile(phase, types) {
                    rules.push(compiled?);
                }
            }
            if phase == SearchPhase::Expand {
                // Even satisfied witnesses can expose previously unseen inner helpers.
                rules.extend(
                    self.rules
                        .iter()
                        .filter_map(|rule| rule.compile(SearchPhase::Witnesses, types))
                        .collect::<anyhow::Result<Vec<_>>>()?,
                );
            }
            phases.insert(phase, rules);
        }
        let rules = std::rc::Rc::new(CompiledBinderRules {
            types: types.to_vec(),
            phases,
            sources: self.rules.clone(),
            signatures: self.signatures.clone(),
            dependencies: dependency_search::DependencyIndex::new(&self.rules),
        });
        *cached = Some(rules.clone());
        Ok(rules)
    }

    /// Prepared after the property check, owned by the refinement state. It is
    /// reused during staged searches and dropped before the next solver model.
    pub fn prepare(
        &self,
        smt: &dyn crate::problem_context::ProblemContext,
        graph: &mut crate::refinement_graph::RefinementGraph,
    ) -> anyhow::Result<PreparedQuantifierSearch> {
        let types = smt.get_array_types();
        let compiled = self.compiled(&types)?;
        let mut terms = smt
            .get_all_subterms()
            .into_iter()
            .cloned()
            .collect::<Vec<_>>();
        terms.extend(self.seeds.iter().map(|(_, term)| term.clone()));
        terms.extend([app("true", vec![]), app("false", vec![]), "0".parse()?]);
        terms.sort_by_cached_key(ToString::to_string);
        terms.dedup();
        let mut needed_sorts = self
            .rules
            .iter()
            .flat_map(|rule| {
                rule.captures
                    .iter()
                    .chain(&rule.variables)
                    .map(|(_, sort)| sort.clone())
            })
            .collect::<HashSet<_>>();
        needed_sorts.insert(string_to_sort("Bool"));
        graph.set_domain_sorts(needed_sorts);
        for term in terms {
            if translate_term_with_array_types(term.clone(), &types).is_some() {
                graph.admit(smt, &term, false)?;
            }
        }
        graph.rebuild();
        let catalog = smt.get_array_candidate_catalog();
        let cost_context = crate::cost_functions::array::ArrayCostContext::from_problem(
            smt,
            &catalog,
            crate::instantiation::scope::CandidateScope::AllCandidates,
        );
        Ok(PreparedQuantifierSearch {
            graph_version: 0,
            additional_terms: graph.terms.clone(),
            representatives: graph.representatives(),
            evaluations: graph.evaluations.clone(),
            compiled,
            cursors: HashMap::new(),
            requests: HashMap::new(),
            obligations: HashMap::new(),
            catalog,
            cost_context,
        })
    }
}

struct CompiledBinderRules {
    types: Vec<(String, String)>,
    phases: HashMap<SearchPhase, Vec<CompiledQuantifiedRule<()>>>,
    sources: Vec<BinderRule>,
    signatures: HashMap<String, (Vec<Sort>, Sort)>,
    dependencies: dependency_search::DependencyIndex,
}

pub(crate) struct PreparedQuantifierSearch {
    graph_version: u64,
    additional_terms: Vec<crate::instantiation::language::TermExpr>,
    representatives: HashMap<egg::Id, crate::instantiation::language::TermExpr>,
    evaluations: HashMap<Term, String>,
    // A fixed formula's value depends only on its typed model-eclass bindings.
    // Reuse it across triggered/domain searches before rebuilding a ground AST.
    obligations: HashMap<(String, bool, Vec<egg::Id>), bool>,
    compiled: std::rc::Rc<CompiledBinderRules>,
    cursors: HashMap<SearchPhase, crate::instantiation::search::BinderSearchCursor>,
    requests: HashMap<BinderSearchRequest, binder_request::PreparedBinderRequest>,
    pub catalog: crate::problem_context::ArrayCandidateCatalog,
    pub cost_context: crate::cost_functions::array::ArrayCostContext,
}

impl SearchPhase {
    pub fn timing_key(self) -> &'static str {
        match self {
            Self::Witnesses => "input_binder_witnesses",
            Self::TriggeredConflicts => "input_binder_triggered_conflicts",
            Self::Conflicts => "input_binder_conflicts",
            Self::Expand => "input_binder_expansion",
        }
    }
}

impl PreparedQuantifierSearch {
    pub(crate) fn graph_version(&self) -> u64 {
        self.graph_version
    }
    pub(crate) fn refresh_graph(
        &mut self,
        graph: &crate::refinement_graph::RefinementGraph,
        version: u64,
    ) {
        if self.graph_version == version {
            return;
        }
        self.graph_version = version;
        self.additional_terms = graph.terms.clone();
        self.representatives = graph.representatives();
        self.evaluations.extend(graph.evaluations.clone());
        self.cursors.clear();
        self.obligations.clear();
        for request in self.requests.values_mut() {
            request.cursor = Default::default();
        }
    }

    pub fn start_phase(&mut self, phase: SearchPhase, next_rule: usize) {
        // Array-stage attempts can change representative-use history without
        // changing the solver model. Reuse model facts, but allow the new
        // selection context to reconsider matches from an earlier pass.
        // Only the scheduling position survives a new pass/model; offsets and
        // completeness refer to this pass's unchanged model-equivalence graph.
        self.cursors.insert(
            phase,
            crate::instantiation::search::BinderSearchCursor::starting_at(next_rule),
        );
    }

    #[cfg(test)]
    pub fn can_continue<'a>(&self, search: impl Into<BinderSearch<'a>>) -> bool {
        let cursor = match search.into() {
            #[cfg(test)]
            BinderSearch::Phase(phase) => self.cursors.get(&phase),
            #[cfg(test)]
            BinderSearch::Request(request) => self.requests.get(request).map(|state| &state.cursor),
            BinderSearch::Page { phase, .. } => self.cursors.get(&phase),
            BinderSearch::RequestPage(request, _) => {
                self.requests.get(request).map(|state| &state.cursor)
            }
        };
        cursor.is_some_and(|cursor| cursor.can_continue())
    }

    pub(crate) fn pending_rules(&self, phase: SearchPhase) -> Vec<(usize, String)> {
        let rules = &self.compiled.phases[&phase];
        let pending = self.cursors.get(&phase).map_or_else(
            || (0..rules.len()).collect(),
            |c| c.pending_rules(rules.len()),
        );
        pending
            .into_iter()
            .map(|i| (i, rules[i].metadata().name().to_owned()))
            .collect()
    }
    pub(crate) fn rule_count(&self, phase: SearchPhase) -> usize {
        self.compiled.phases[&phase].len()
    }

    pub fn candidates<'a, CF>(
        &mut self,
        egraph: &egg::EGraph<TermLanguage, ()>,
        mut evaluate: impl FnMut(&Term) -> anyhow::Result<String>,
        search: impl Into<BinderSearch<'a>>,
        make_cost: impl FnOnce(&crate::cost_functions::array::ArrayCostContext) -> CF,
        mut options: InstantiationOptions,
    ) -> anyhow::Result<InstantiationBatch>
    where
        CF: crate::cost_functions::YardbirdCostFunction<TermLanguage> + 'static,
    {
        use crate::instantiation::{
            engine::instantiate_quantified_matches, grounding::instantiate_with_bindings,
            language::expr_to_term, search::search_binder_page_at,
        };
        let (phase, request, page) = match search.into() {
            #[cfg(test)]
            BinderSearch::Phase(phase) => (phase, None, None),
            #[cfg(test)]
            BinderSearch::Request(request) => (request.phase, Some(request), None),
            BinderSearch::Page {
                phase,
                rule,
                allowance,
            } => (phase, None, Some((rule, allowance))),
            BinderSearch::RequestPage(request, allowance) => {
                (request.phase, Some(request), Some((0, allowance)))
            }
        };
        let requested_rule = request
            .map(|request| self.prepare_request(request))
            .transpose()?;
        if let (Some(request), Some((_, allowance))) = (request, page) {
            let state = self.requests.get_mut(request).unwrap();
            if state.allowance != Some(allowance) {
                state.cursor = Default::default();
                state.allowance = Some(allowance);
            }
        }
        let profiling = options.instrumentation.profiling.clone();
        let rules = match &requested_rule {
            Some(rule) => std::slice::from_ref(rule.as_ref()),
            None => self.compiled.phases[&phase].as_slice(),
        };
        let start = std::time::Instant::now();
        let cursor = match request {
            Some(request) => &mut self.requests.get_mut(request).unwrap().cursor,
            None => self.cursors.entry(phase).or_default(),
        };
        let mut matched = match page {
            Some((rule, allowance)) => {
                search_binder_page_at(egraph, rules, cursor, rule, &allowance, &profiling)
            }
            #[cfg(test)]
            None => {
                crate::instantiation::search::search_binder_page(egraph, rules, cursor, &profiling)
            }
            #[cfg(not(test))]
            None => unreachable!("production search requires an explicit rule"),
        };
        if let Some(profiling) = &profiling {
            let mut profiling = profiling.borrow_mut();
            profiling.record_timing("input_binder_matching", start.elapsed());
            if !matched.report.budget_exhausted_rules.is_empty() {
                profiling.add_counter(
                    "input_binder_search_budget_exhausted",
                    matched.report.budget_exhausted_rules.len() as u64,
                );
            }
        }
        let start = std::time::Instant::now();
        let mut kept = Vec::new();
        let mut needed_classes = HashSet::new();
        let mut rejected = 0;
        let mut cached_obligations = 0;
        for mut candidate in matched.matches {
            let rule = &rules[candidate.rule_index];
            let candidate_start = profiling.as_ref().map(|_| std::time::Instant::now());
            let count = |key: &str| {
                if let Some(p) = &profiling {
                    p.borrow_mut()
                        .record_quantifier_counter(rule.metadata().name(), key, 1);
                }
            };
            count("matches_examined");
            if rule.uses_violation_plan() {
                count("violation_plan_matches");
                let filter_start = std::time::Instant::now();
                let mut rejected_by_filter = false;
                for (filter, truth) in rule.binder_filters() {
                    let expression = instantiate_with_bindings(filter, |variable| {
                        let id = egraph.find(candidate.substitution[variable]);
                        self.representatives.get(&id).ok_or_else(|| {
                            anyhow::anyhow!("No original term for binder e-class {id}")
                        })
                    })?;
                    let term = expr_to_term(expression);
                    let value = match self.evaluations.get(&term) {
                        Some(value) => value.clone(),
                        None => {
                            let value = evaluate(&term)?;
                            self.evaluations.insert(term, value.clone());
                            value
                        }
                    };
                    count("violation_plan_filter_checks");
                    if value.trim() != if *truth { "true" } else { "false" } {
                        rejected_by_filter = true;
                        break;
                    }
                }
                if let Some(p) = &profiling {
                    p.borrow_mut().record_quantifier_timing(
                        rule.metadata().name(),
                        "violation_plan_filters",
                        filter_start.elapsed(),
                    );
                }
                if rejected_by_filter {
                    count("violation_plan_filter_rejections");
                    rejected += 1;
                    continue;
                }
            }
            let bindings = rule
                .formula_variables()
                .iter()
                .map(|variable| egraph.find(candidate.substitution[*variable]))
                .collect::<Vec<_>>();
            if phase != SearchPhase::Expand {
                let key = (
                    rule.metadata().name().to_owned(),
                    phase == SearchPhase::Witnesses,
                    bindings.clone(),
                );
                // Specialized formulas have literal bindings in addition to
                // these remaining variables. Keep their values in the exact
                // term cache, not the unrestricted rule's e-class cache.
                let cached = request
                    .is_none()
                    .then(|| self.obligations.get(&key))
                    .flatten();
                let violated = if let Some(violated) = cached {
                    cached_obligations += 1;
                    count("obligation_cache_hits");
                    *violated
                } else {
                    count("obligation_cache_misses");
                    count("full_formula_constructions");
                    let construction_start = profiling.as_ref().map(|_| std::time::Instant::now());
                    let expression = instantiate_with_bindings(rule.formula(), |variable| {
                        let id = egraph.find(candidate.substitution[variable]);
                        self.representatives.get(&id).ok_or_else(|| {
                            anyhow::anyhow!("No original term for binder e-class {id}")
                        })
                    })?;
                    let term = expr_to_term(expression);
                    if let (Some(p), Some(start)) = (&profiling, construction_start) {
                        p.borrow_mut().record_quantifier_timing(
                            rule.metadata().name(),
                            "formula_construction",
                            start.elapsed(),
                        );
                    }
                    let value = match self.evaluations.get(&term) {
                        Some(value) => {
                            count("evaluation_cache_hits");
                            value.clone()
                        }
                        None => {
                            count("model_evaluations");
                            let evaluation_start =
                                profiling.as_ref().map(|_| std::time::Instant::now());
                            let value = evaluate(&term);
                            if let (Some(p), Some(start)) = (&profiling, evaluation_start) {
                                p.borrow_mut().record_quantifier_timing(
                                    rule.metadata().name(),
                                    "model_evaluation",
                                    start.elapsed(),
                                );
                            }
                            let value = value?;
                            self.evaluations.insert(term, value.clone());
                            value
                        }
                    };
                    let violated = value.trim() == "false";
                    if request.is_none() {
                        self.obligations.insert(key, violated);
                    }
                    violated
                };
                if !violated {
                    rejected += 1;
                    count("satisfied_or_unresolved_matches");
                    if let (Some(p), Some(start)) = (&profiling, candidate_start) {
                        p.borrow_mut().record_quantifier_timing(
                            rule.metadata().name(),
                            "model_filter",
                            start.elapsed(),
                        );
                    }
                    continue;
                }
                candidate.model_violation_verified = true;
            }
            count("matches_to_ground");
            if let (Some(p), Some(start)) = (&profiling, candidate_start) {
                p.borrow_mut().record_quantifier_timing(
                    rule.metadata().name(),
                    "model_filter",
                    start.elapsed(),
                );
            }
            needed_classes.extend(bindings);
            needed_classes.extend(
                rule.fixed_bindings()
                    .iter()
                    .filter_map(|(_, term)| egraph.lookup_expr(term).map(|id| egraph.find(id))),
            );
            kept.push(candidate);
        }
        matched.matches = kept;
        if let Some(profiling) = &profiling {
            let mut profiling = profiling.borrow_mut();
            profiling.record_timing("input_binder_model_filter", start.elapsed());
            profiling.add_counter("model_satisfied_matches_filtered", rejected);
            profiling.add_counter("input_binder_obligation_cache_hits", cached_obligations);
            profiling.add_counter(
                "input_binder_matches_to_ground",
                matched.matches.len() as u64,
            );
        }
        options.additional_terms = self.additional_terms.clone();
        let batch = instantiate_quantified_matches(
            egraph,
            || make_cost(&self.cost_context),
            rules,
            options,
            matched,
            None,
            Some(&needed_classes),
        )?;
        // Congruence must preserve the cheap obligation's value when typed,
        // model-equivalent representatives are chosen by the cost function.
        #[cfg(debug_assertions)]
        if phase != SearchPhase::Expand {
            for candidate in &batch.candidates {
                debug_assert_eq!(
                    evaluate(&expr_to_term(candidate.expression.clone()))?.trim(),
                    "false"
                );
            }
        }
        Ok(batch)
    }
}

#[cfg(test)]
mod tests;
