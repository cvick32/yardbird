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

use crate::theories::array::array_axioms::ArrayLanguage;
mod binder_request;
#[cfg(test)]
mod binder_request_tests;
mod dependency_search;
mod violation_plan;
use crate::{
    quantified_rule::QuantifiedRule,
    theories::array::{
        array_axioms::{
            translate_term_with_array_types, ArrayInstantiationOptions, CompiledQuantifiedRule,
        },
        instantiation_candidate::InstantiationBatch,
    },
};
pub(crate) use binder_request::{BinderSearch, BinderSearchRequest};

pub(crate) fn app(name: &str, arguments: Vec<Term>) -> Term {
    if arguments.is_empty() {
        Term::QualIdentifier(QualIdentifier::simple(name))
    } else {
        Term::Application {
            qual_identifier: QualIdentifier::simple(name),
            arguments,
        }
    }
}

pub(crate) fn substitute(term: Term, bindings: Vec<(Symbol, Term)>) -> Term {
    LetExtract::substitute(Term::Let {
        var_bindings: bindings,
        term: Box::new(term),
    })
}

fn sort_name(sort: &Sort) -> String {
    match sort {
        Sort::Parameterized {
            identifier,
            parameters,
        } => format!(
            "{}_{}",
            identifier,
            parameters
                .iter()
                .map(sort_name)
                .collect::<Vec<_>>()
                .join("_")
        ),
        _ => ArrayLanguage::sort_to_name(sort),
    }
}

pub(crate) fn abstract_sort(sort: &Sort) -> Sort {
    match sort {
        Sort::Parameterized { identifier, .. } if identifier.to_string() == "Array" => {
            string_to_sort(&sort_name(sort))
        }
        _ => sort.clone(),
    }
}

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
            let pattern = |term: Term| -> anyhow::Result<Pattern<ArrayLanguage>> {
                let expression = translate_term_with_array_types(term, types)
                    .ok_or_else(|| anyhow::anyhow!("could not compile binder {}", self.name))?;
                let ast = expression
                    .as_ref()
                    .iter()
                    .map(|node| match node {
                        ArrayLanguage::Symbol(symbol) if bindings.contains_key(symbol.as_str()) => {
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
                            ENodeOrVar::ENode(
                                ArrayLanguage::ReadTyped(_) | ArrayLanguage::Apply(_)
                            )
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
                    let sort = domain.add(ENodeOrVar::ENode(ArrayLanguage::SortTag(
                        sort.to_string().into(),
                    )));
                    let value = domain.add(ENodeOrVar::Var(bindings[&symbol.0]));
                    domain.add(ENodeOrVar::ENode(ArrayLanguage::Domain([sort, value])));
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
            crate::theories::array::candidate_scope::CandidateScope::AllCandidates,
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
    additional_terms: Vec<crate::theories::array::array_axioms::ArrayExpr>,
    representatives: HashMap<egg::Id, crate::theories::array::array_axioms::ArrayExpr>,
    evaluations: HashMap<Term, String>,
    // A fixed formula's value depends only on its typed model-eclass bindings.
    // Reuse it across triggered/domain searches before rebuilding a ground AST.
    obligations: HashMap<(String, bool, Vec<egg::Id>), bool>,
    compiled: std::rc::Rc<CompiledBinderRules>,
    cursors: HashMap<SearchPhase, crate::theories::array::quantified_search::BinderSearchCursor>,
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
            crate::theories::array::quantified_search::BinderSearchCursor::starting_at(next_rule),
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
        egraph: &egg::EGraph<ArrayLanguage, ()>,
        mut evaluate: impl FnMut(&Term) -> anyhow::Result<String>,
        search: impl Into<BinderSearch<'a>>,
        make_cost: impl FnOnce(&crate::cost_functions::array::ArrayCostContext) -> CF,
        mut options: ArrayInstantiationOptions,
    ) -> anyhow::Result<InstantiationBatch>
    where
        CF: crate::cost_functions::YardbirdCostFunction<ArrayLanguage> + 'static,
    {
        use crate::theories::array::{
            array_axioms::{expr_to_term, instantiate_quantified_matches},
            array_grounding::instantiate_with_bindings,
            quantified_search::search_binder_page_at,
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
            None => crate::theories::array::quantified_search::search_binder_page(
                egraph, rules, cursor, &profiling,
            ),
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

struct Lowerer<'a> {
    provenance: &'a mut crate::quantifier_provenance::QuantifierProvenance,
    signatures: HashMap<String, (Vec<Sort>, Sort)>,
    reserved: HashSet<String>,
    next_id: usize,
    declarations: Vec<Command>,
    rules: Vec<BinderRule>,
}

pub(crate) fn term_sort(
    term: &Term,
    signatures: &HashMap<String, (Vec<Sort>, Sort)>,
    scope: &HashMap<String, Sort>,
) -> anyhow::Result<Sort> {
    match term {
        Term::QualIdentifier(id) => {
            let name = id.get_name();
            if name == "true" || name == "false" {
                return Ok(string_to_sort("Bool"));
            }
            if let Some(sort) = scope.get(&name) {
                return Ok(sort.clone());
            }
            let base = split_framed_symbol(&name)
                .map(|(name, _)| name)
                .unwrap_or(name.clone());
            signatures
                .get(&name)
                .or_else(|| signatures.get(&base))
                .or_else(|| signatures.get(base.trim_matches('|')))
                .map(|(_, sort)| sort.clone())
                .ok_or_else(|| anyhow::anyhow!("unknown sort for {name}"))
        }
        Term::Constant(Constant::Numeral(_)) => Ok(string_to_sort("Int")),
        Term::Constant(Constant::Decimal(_)) => Ok(string_to_sort("Real")),
        Term::Constant(Constant::Binary(bits)) => {
            Ok(string_to_sort(&format!("BitVec{}", bits.len())))
        }
        Term::Constant(Constant::Hexadecimal(digits)) => {
            Ok(string_to_sort(&format!("BitVec{}", digits.len() * 4)))
        }
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            let name = qual_identifier.get_name();
            if let Some((_, sort)) = signatures.get(&name) {
                return Ok(sort.clone());
            }
            match name.as_str() {
                "and" | "or" | "not" | "=>" | "=" | "distinct" | "<" | "<=" | ">" | ">="
                | "xor" => Ok(string_to_sort("Bool")),
                "ite" => term_sort(&arguments[1], signatures, scope),
                "select" => match term_sort(&arguments[0], signatures, scope)? {
                    Sort::Parameterized { parameters, .. } => Ok(parameters[1].clone()),
                    sort => anyhow::bail!("select requires an array, got {sort}"),
                },
                "const" => match qual_identifier {
                    QualIdentifier::Sorted { sort, .. } => Ok(sort.clone()),
                    _ => anyhow::bail!("array constant needs a sort"),
                },
                "to_real" => Ok(string_to_sort("Real")),
                "to_int" => Ok(string_to_sort("Int")),
                _ if name.starts_with("Read_") => {
                    // Read signatures are registered when native selects are lowered.
                    anyhow::bail!("unregistered abstract array function {name}")
                }
                _ if !arguments.is_empty() => term_sort(&arguments[0], signatures, scope),
                _ => anyhow::bail!("cannot determine result sort of {term}"),
            }
        }
        Term::Forall { .. } | Term::Exists { .. } => Ok(string_to_sort("Bool")),
        Term::Lambda { vars, term } => {
            let mut inner = scope.clone();
            inner.extend(vars.iter().map(|(s, t)| (s.0.clone(), t.clone())));
            let result = term_sort(term, signatures, &inner)?;
            Ok(vars
                .iter()
                .rev()
                .fold(result, |result, (_, index)| Sort::Parameterized {
                    identifier: Identifier::Simple {
                        symbol: Symbol("Array".into()),
                    },
                    parameters: vec![index.clone(), result],
                }))
        }
        Term::Attributes { term, .. } => term_sort(term, signatures, scope),
        Term::Let { .. } => term_sort(&LetExtract::substitute(term.clone()), signatures, scope),
        _ => anyhow::bail!("unsupported binder body {term}"),
    }
}

impl Lowerer<'_> {
    fn fresh(&mut self, kind: &str) -> String {
        loop {
            let name = format!("__yardbird_{kind}_{}", self.next_id);
            self.next_id += 1;
            if self.reserved.insert(name.clone()) {
                return name;
            }
        }
    }

    fn declare(&mut self, name: String, parameters: Vec<Sort>, sort: Sort) {
        self.signatures
            .insert(name.clone(), (parameters.clone(), sort.clone()));
        self.declarations.push(Command::DeclareFun {
            symbol: Symbol(name),
            parameters,
            sort,
        });
    }

    fn array_function(&mut self, name: String, parameters: Vec<Sort>, sort: Sort) {
        if !self.signatures.contains_key(&name) {
            self.declare(name, parameters, sort);
        }
    }

    fn lower(&mut self, term: Term, scope: &HashMap<String, Sort>) -> anyhow::Result<Term> {
        match term {
            Term::Forall { vars, term } => self.binder(BinderKind::Forall, vars, *term, scope),
            Term::Exists { vars, term } => self.binder(BinderKind::Exists, vars, *term, scope),
            Term::Lambda { vars, term } => self.binder(BinderKind::Lambda, vars, *term, scope),
            Term::Attributes { term, attributes } => Ok(Term::Attributes {
                term: Box::new(self.lower(*term, scope)?),
                attributes,
            }),
            Term::Let { .. } => self.lower(LetExtract::substitute(term), scope),
            Term::Application {
                qual_identifier,
                arguments,
            } => {
                let name = qual_identifier.get_name();
                let array_sort = if name == "select" || name == "store" {
                    Some(term_sort(&arguments[0], &self.signatures, scope)?)
                } else {
                    None
                };
                let arguments = arguments
                    .into_iter()
                    .map(|arg| self.lower(arg, scope))
                    .collect::<anyhow::Result<Vec<_>>>()?;
                if name == "distinct" {
                    let mut pairs = Vec::new();
                    for left in 0..arguments.len() {
                        for right in left + 1..arguments.len() {
                            pairs.push(app(
                                "not",
                                vec![app(
                                    "=",
                                    vec![arguments[left].clone(), arguments[right].clone()],
                                )],
                            ));
                        }
                    }
                    return Ok(if pairs.is_empty() {
                        app("true", vec![])
                    } else {
                        app("and", pairs)
                    });
                }
                if name == "const" {
                    if let QualIdentifier::Sorted {
                        sort: Sort::Parameterized { parameters, .. },
                        ..
                    } = &qual_identifier
                    {
                        let function = format!(
                            "ConstArr_{}_{}",
                            sort_name(&parameters[0]),
                            sort_name(&parameters[1])
                        );
                        let result = Sort::Parameterized {
                            identifier: Identifier::Simple {
                                symbol: Symbol("Array".into()),
                            },
                            parameters: parameters.clone(),
                        };
                        self.array_function(function.clone(), vec![parameters[1].clone()], result);
                        return Ok(app(&function, arguments));
                    }
                }
                if let Some(Sort::Parameterized { parameters, .. }) = array_sort {
                    let index = &parameters[0];
                    let value = &parameters[1];
                    let function = format!(
                        "{}_{}_{}",
                        if name == "select" { "Read" } else { "Write" },
                        sort_name(index),
                        sort_name(value)
                    );
                    // These signatures are also needed while lowering enclosing lambdas.
                    let array = Sort::Parameterized {
                        identifier: Identifier::Simple {
                            symbol: Symbol("Array".into()),
                        },
                        parameters: parameters.clone(),
                    };
                    let result = if name == "select" {
                        value.clone()
                    } else {
                        array.clone()
                    };
                    let mut sorts = vec![array, index.clone()];
                    if name == "store" {
                        sorts.push(value.clone());
                    }
                    self.array_function(function.clone(), sorts, result);
                    Ok(app(&function, arguments))
                } else {
                    Ok(Term::Application {
                        qual_identifier,
                        arguments,
                    })
                }
            }
            Term::Match { .. } => {
                anyhow::bail!("match expressions are not supported by quantifier abstraction")
            }
            other => Ok(other),
        }
    }

    fn binder(
        &mut self,
        kind: BinderKind,
        vars: Vec<(Symbol, Sort)>,
        body: Term,
        scope: &HashMap<String, Sort>,
    ) -> anyhow::Result<Term> {
        let source_id = self.provenance.source_for_variables(&vars);
        let scoped_variables = source_id.as_ref().map(|_| vars.clone()).unwrap_or_default();
        let mut inner = scope.clone();
        let mut renaming = Vec::new();
        let variables = vars
            .into_iter()
            .map(|(symbol, sort)| {
                let fresh = self.fresh("bound");
                renaming.push((symbol, app(&fresh, vec![])));
                inner.insert(fresh.clone(), sort.clone());
                (Symbol(fresh), sort)
            })
            .collect::<Vec<_>>();
        let body = self.lower(substitute(body, renaming), &inner)?;
        let result_sort = if kind == BinderKind::Lambda {
            let result = term_sort(&body, &self.signatures, &inner)?;
            variables
                .iter()
                .rev()
                .fold(result, |result, (_, index)| Sort::Parameterized {
                    identifier: Identifier::Simple {
                        symbol: Symbol("Array".into()),
                    },
                    parameters: vec![index.clone(), result],
                })
        } else {
            string_to_sort("Bool")
        };
        if kind == BinderKind::Lambda {
            let mut depends_on_binder = false;
            collect_symbols(&body, &mut |name| {
                depends_on_binder |= variables.iter().any(|(symbol, _)| symbol.0 == name);
            });
            if !depends_on_binder {
                if let Some(id) = &source_id {
                    self.provenance
                        .sources
                        .get_mut(id)
                        .unwrap()
                        .eliminated_as_constant_array = true;
                }
                let mut value_sort = term_sort(&body, &self.signatures, &inner)?;
                let mut constant = body;
                for (_, index) in variables.iter().rev() {
                    let function =
                        format!("ConstArr_{}_{}", sort_name(index), sort_name(&value_sort));
                    let element_sort = value_sort;
                    value_sort = Sort::Parameterized {
                        identifier: Identifier::Simple {
                            symbol: Symbol("Array".into()),
                        },
                        parameters: vec![index.clone(), element_sort.clone()],
                    };
                    self.array_function(function.clone(), vec![element_sort], value_sort.clone());
                    constant = app(&function, vec![constant]);
                }
                return Ok(constant);
            }
        }
        let mut free = BTreeMap::new();
        collect_symbols(&body, &mut |name| {
            if variables.iter().any(|(s, _)| s.0 == name) {
                return;
            }
            if let Some(sort) = inner.get(name).or_else(|| {
                self.signatures
                    .get(name)
                    .filter(|(params, _)| params.is_empty())
                    .map(|(_, sort)| sort)
            }) {
                free.insert(name.to_string(), sort.clone());
            }
        });
        let mut captures = free
            .into_iter()
            .map(|(s, t)| (Symbol(s), t))
            .collect::<Vec<_>>();
        let mut arguments = captures
            .iter()
            .map(|(s, _)| app(&s.0, vec![]))
            .collect::<Vec<_>>();
        // Helpers always have an argument, so VMT never classifies a rigid
        // helper as a per-frame input variable.
        let unit_capture = captures.is_empty();
        if unit_capture {
            captures.push((Symbol(self.fresh("unit")), string_to_sort("Bool")));
            arguments.push(app("true", vec![]));
        }
        let name = self.fresh(if kind == BinderKind::Lambda {
            "lambda"
        } else {
            "quantifier"
        });
        let parameters = captures
            .iter()
            .map(|(_, sort)| sort.clone())
            .collect::<Vec<_>>();
        self.declare(name.clone(), parameters.clone(), result_sort.clone());
        let witnesses = if kind == BinderKind::Lambda {
            vec![]
        } else {
            variables
                .iter()
                .map(|(_, sort)| {
                    let witness = self.fresh("witness");
                    self.declare(witness.clone(), parameters.clone(), sort.clone());
                    witness
                })
                .collect()
        };
        log::info!(
            "Quantified rule {name} ({kind:?}):\n  captures: {}\n  variables: {}\n  body: {body}\n  witnesses: {}",
            captures
                .iter()
                .map(|(symbol, sort)| format!("({symbol} {sort})"))
                .collect::<Vec<_>>()
                .join(" "),
            variables
                .iter()
                .map(|(symbol, sort)| format!("({symbol} {sort})"))
                .collect::<Vec<_>>()
                .join(" "),
            witnesses.join(" "),
        );
        if let Some(source_id) = source_id {
            use crate::quantifier_provenance::{LoweredQuantifier, LoweredVariable};
            self.provenance.rules.insert(
                QuantifiedRule::input_binder(&name).name().into(),
                LoweredQuantifier {
                    source_id,
                    helper: name.clone(),
                    kind: format!("{kind:?}").to_lowercase(),
                    variables: scoped_variables
                        .iter()
                        .zip(&variables)
                        .map(|((scoped, _), (lowered, _))| LoweredVariable {
                            scoped_name: scoped.0.clone(),
                            lowered_name: lowered.0.clone(),
                        })
                        .collect(),
                    captures: captures
                        .iter()
                        .map(|(s, t)| (s.to_string(), t.to_string()))
                        .collect(),
                    witnesses: witnesses.clone(),
                    lowered_body: body.to_string(),
                },
            );
        }
        self.rules.push(BinderRule {
            name: name.clone(),
            kind,
            captures,
            variables,
            body,
            witnesses,
            result_sort,
            unit_capture,
        });
        Ok(app(&name, arguments))
    }
}

fn collect_symbols(term: &Term, visit: &mut impl FnMut(&str)) {
    match term {
        Term::QualIdentifier(id) => visit(&id.get_name()),
        Term::Application { arguments, .. } => {
            for term in arguments {
                collect_symbols(term, visit);
            }
        }
        Term::Attributes { term, .. } => collect_symbols(term, visit),
        _ => {}
    }
}

pub(crate) fn contains_binders(term: &Term) -> bool {
    match term {
        Term::Forall { .. } | Term::Exists { .. } | Term::Lambda { .. } => true,
        Term::Application { arguments, .. } => arguments.iter().any(contains_binders),
        Term::Let { var_bindings, term } => {
            var_bindings.iter().any(|(_, term)| contains_binders(term)) || contains_binders(term)
        }
        Term::Attributes { term, .. } => contains_binders(term),
        Term::Match { term, cases } => {
            contains_binders(term) || cases.iter().any(|(_, term)| contains_binders(term))
        }
        _ => false,
    }
}

/// Lower every binder before array abstraction, including helper definitions
/// and background assertions. The returned model contains no binder terms.
#[cfg(test)]
pub(crate) fn lower_model(model: VMTModel) -> anyhow::Result<(VMTModel, QuantifierPlan)> {
    lower_model_with_provenance(model, &mut Default::default())
}

pub(crate) fn lower_model_with_provenance(
    model: VMTModel,
    provenance: &mut crate::quantifier_provenance::QuantifierProvenance,
) -> anyhow::Result<(VMTModel, QuantifierPlan)> {
    let commands = model.as_commands();
    if !commands.iter().any(|command| match command {
        Command::DefineFun { term, .. } | Command::Assert { term } => contains_binders(term),
        _ => false,
    }) {
        return Ok((model, QuantifierPlan::default()));
    }
    let mut signatures = HashMap::new();
    for command in &commands {
        match command {
            Command::DeclareFun {
                symbol,
                parameters,
                sort,
            } => {
                signatures.insert(symbol.0.clone(), (parameters.clone(), sort.clone()));
            }
            Command::DefineFun { sig, .. } => {
                signatures.insert(
                    sig.name.0.clone(),
                    (
                        sig.parameters
                            .iter()
                            .map(|(_, sort)| sort.clone())
                            .collect(),
                        sig.result.clone(),
                    ),
                );
            }
            _ => {}
        }
    }
    // Reserve binder and local names as well as global declarations.
    let mut reserved = signatures.keys().cloned().collect::<HashSet<_>>();
    for command in &commands {
        for token in command
            .to_string()
            .split(|c: char| c.is_whitespace() || c == '(' || c == ')' || c == '|')
        {
            reserved.insert(token.to_string());
        }
    }
    let mut lowerer = Lowerer {
        provenance,
        signatures,
        reserved,
        next_id: 0,
        declarations: vec![],
        rules: vec![],
    };
    let mut lowered = Vec::new();
    for command in commands {
        lowered.push(match command {
            Command::DefineFun { sig, term } => {
                let scope = sig
                    .parameters
                    .iter()
                    .map(|(s, t)| (s.0.clone(), t.clone()))
                    .collect();
                Command::DefineFun {
                    sig,
                    term: lowerer.lower(term, &scope)?,
                }
            }
            Command::Assert { term } => Command::Assert {
                term: lowerer.lower(term, &HashMap::new())?,
            },
            other => other,
        });
    }
    let mut seeds = Vec::new();
    let sorts = lowerer
        .rules
        .iter()
        .flat_map(|rule| rule.variables.iter().map(|(_, sort)| sort.clone()))
        .collect::<HashSet<_>>();
    let mut sorts = sorts.into_iter().collect::<Vec<_>>();
    sorts.sort_by_key(ToString::to_string);
    for sort in sorts {
        let name = lowerer.fresh("seed");
        lowerer.declare(name.clone(), vec![string_to_sort("Bool")], sort.clone());
        seeds.push((abstract_sort(&sort), app(&name, vec![app("true", vec![])])));
    }
    // Declare closures before any zero-argument helpers that use them.
    let mut declarations = lowerer.declarations;
    declarations.extend(lowered);
    let model = VMTModel::checked_from(declarations)?;
    for rule in &mut lowerer.rules {
        for (_, sort) in rule.captures.iter_mut().chain(&mut rule.variables) {
            *sort = abstract_sort(sort);
        }
    }
    let signatures = lowerer
        .signatures
        .into_iter()
        .map(|(name, (params, result))| {
            (
                name,
                (
                    params.iter().map(abstract_sort).collect(),
                    abstract_sort(&result),
                ),
            )
        })
        .collect();
    Ok((
        model,
        QuantifierPlan {
            rules: lowerer.rules,
            signatures,
            seeds,
            compiled: Default::default(),
        },
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theories::array::array_axioms::generate_quantified_candidates;
    use crate::{Driver, SolverBackend, Strategy, YardbirdOptions};

    fn model(source: &str) -> VMTModel {
        let commands = smt2parser::CommandStream::new(
            std::io::Cursor::new(source.as_bytes()),
            smt2parser::concrete::SyntaxBuilder,
            None,
        )
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
        VMTModel::checked_from(commands).unwrap()
    }

    fn formula_model(init: &str, property: &str) -> VMTModel {
        model(&format!(
            "(declare-fun a () (Array Bool Bool))
            (define-fun init () Bool (! {init} :init true))
            (define-fun trans () Bool (! true :trans true))
            (define-fun prop () Bool (! {property} :invar-property 0))"
        ))
    }

    fn check(init: &str, property: &str) -> crate::Result<crate::ProofLoopResult> {
        check_model(formula_model(init, property))
    }

    fn check_model(model: VMTModel) -> crate::Result<crate::ProofLoopResult> {
        let mut options = YardbirdOptions::from_filename("unused.vmt".into());
        options.strategy = Strategy::Abstract;
        let mut driver = Driver::new(
            model,
            options.build_instantiation_strategy(),
            SolverBackend::Z3,
        );
        driver.check_strategy(1, options.build_array_strategy())
    }

    #[test]
    fn provenance_preserves_nested_shadowing_and_lowered_bindings() {
        let input = formula_model("(forall ((x Int)) (exists ((x Int)) (= x 0)))", "false");
        let (scoped, mut provenance) =
            crate::quantifier_provenance::scope_model(input.clone(), true).unwrap();
        let (without_profile, empty) =
            crate::quantifier_provenance::scope_model(input, false).unwrap();
        assert_eq!(scoped.as_commands(), without_profile.as_commands());
        assert!(empty.sources.is_empty());
        assert_eq!(provenance.sources.len(), 2);
        let child = provenance
            .sources
            .values()
            .find(|s| s.kind == "exists")
            .unwrap();
        let parent = &provenance.sources[child.parent_source_id.as_ref().unwrap()];
        assert_eq!(parent.kind, "forall");
        assert_eq!(child.variables[0].name, "x");
        assert_eq!(parent.variables[0].name, "x");
        assert_ne!(
            child.variables[0].scoped_name,
            parent.variables[0].scoped_name
        );
        assert_eq!(child.formula, "(exists ((x Int)) (= x 0))");
        let (lowered, plan) = lower_model_with_provenance(scoped.clone(), &mut provenance).unwrap();
        let (untracked, _) = lower_model(scoped).unwrap();
        assert_eq!(lowered.as_commands(), untracked.as_commands());
        assert_eq!(provenance.rules.len(), plan.rules.len());
        for (name, rule) in &provenance.rules {
            assert_eq!(name, QuantifiedRule::input_binder(&rule.helper).name());
            assert_eq!(rule.witnesses.len(), rule.variables.len());
            let source = &provenance.sources[&rule.source_id];
            assert_eq!(
                rule.variables[0].scoped_name,
                source.variables[0].scoped_name
            );
            assert!(rule.variables[0]
                .lowered_name
                .starts_with("__yardbird_bound_"));
        }
    }

    #[test]
    fn provenance_tracks_property_witnesses_without_binder_rules() {
        let input = formula_model("true", "(forall ((i Int)) (= i i))");
        let (scoped, mut provenance) =
            crate::quantifier_provenance::scope_model(input, true).unwrap();
        let (rewritten, bindings) = scoped.herbrandize_universal_property_with_bindings();
        provenance.record_property_witnesses(&bindings);
        let (_, plan) = lower_model_with_provenance(rewritten, &mut provenance).unwrap();
        assert_eq!(bindings.len(), 1);
        assert!(plan.rules.is_empty());
        assert!(provenance.rules.is_empty());
        let source = provenance.sources.values().next().unwrap();
        assert_eq!(source.formula, "(forall ((i Int)) (= i i))");
        assert_eq!(
            source.property_witnesses[0].scoped_variable,
            source.variables[0].scoped_name
        );
        assert_eq!(source.property_witnesses[0].witness, bindings[0].1 .0);
    }

    #[test]
    fn provenance_keeps_one_source_for_let_copies_and_constant_lambdas() {
        let input = formula_model("(let ((p (forall ((x Int)) (= x 0)))) (and p p))", "false");
        let (scoped, mut provenance) =
            crate::quantifier_provenance::scope_model(input, true).unwrap();
        lower_model_with_provenance(scoped, &mut provenance).unwrap();
        assert_eq!(provenance.sources.len(), 1);
        assert_eq!(provenance.rules.len(), 2);
        assert!(provenance
            .rules
            .values()
            .all(|r| provenance.sources.contains_key(&r.source_id)));
        let input = formula_model("(= (select (lambda ((i Int)) 0) 0) 0)", "true");
        let (scoped, mut provenance) =
            crate::quantifier_provenance::scope_model(input, true).unwrap();
        lower_model_with_provenance(scoped, &mut provenance).unwrap();
        assert!(provenance.rules.is_empty());
        assert!(
            provenance
                .sources
                .values()
                .next()
                .unwrap()
                .eliminated_as_constant_array
        );
    }

    #[test]
    fn provenance_and_work_are_retained_on_timeout_and_exhaustion() {
        for timeout in [Some(std::time::Duration::ZERO), None] {
            let input = formula_model(
                "(forall ((i Int)) (= (select a true) (select a true)))",
                "false",
            );
            let mut options = YardbirdOptions::from_filename("provenance.vmt".into());
            options.profile = true;
            let mut driver = Driver::new(
                input,
                options.build_instantiation_strategy(),
                SolverBackend::Z3,
            )
            .with_profiler(options.build_profiler())
            .with_wall_timeout(timeout);
            let result = match driver.check_strategy(1, options.build_array_strategy()) {
                Ok(result) => result,
                Err(_) => driver.take_failed_result().unwrap(),
            };
            assert!(!result.profiling.quantifier_provenance.sources.is_empty());
            assert!(!result.profiling.quantifier_provenance.rules.is_empty());
            let serialized = serde_json::to_value(&result.profiling).unwrap();
            let roundtrip: crate::profiling::ProfilingRunRecord =
                serde_json::from_value(serialized).unwrap();
            assert_eq!(roundtrip.quantifier_provenance.sources.len(), 1);
            if timeout.is_none() {
                assert!(result
                    .profiling
                    .cost_records
                    .iter()
                    .any(|r| !r.quantifier_work.is_empty()));
            }
        }
        let legacy: crate::profiling::ProfilingRunRecord = serde_json::from_str("{}").unwrap();
        assert!(legacy.quantifier_provenance.sources.is_empty());
    }

    #[test]
    fn provenance_joins_successful_rule_work_and_actual_installations() {
        let input = formula_model("(forall ((x Bool)) (select a x))", "(select a true)");
        let mut options = YardbirdOptions::from_filename("provenance.vmt".into());
        options.profile = true;
        let mut driver = Driver::new(
            input,
            options.build_instantiation_strategy(),
            SolverBackend::Z3,
        )
        .with_profiler(options.build_profiler());
        let result = driver
            .check_strategy(1, options.build_array_strategy())
            .unwrap();
        let mut installed = 0;
        let mut examined = 0;
        for record in &result.profiling.cost_records {
            for (rule, phases) in &record.quantifier_work {
                let source_id = &result.profiling.quantifier_provenance.rules[rule].source_id;
                assert!(result
                    .profiling
                    .quantifier_provenance
                    .sources
                    .contains_key(source_id));
                for work in phases.values() {
                    examined += work.counters.get("matches_examined").copied().unwrap_or(0);
                    installed += work
                        .counters
                        .get("abstract_instances_added")
                        .copied()
                        .unwrap_or(0);
                }
            }
        }
        assert!(examined > 0);
        assert!(installed > 0);
        let old_record = r#"{"scope":"legacy","bmc_depth":0,"refinement_step":0,"array_types":[],"timing_secs":{},"counters":{},"cost_rec":{"total_calls":0,"total_secs":0.0,"total_expr_nodes":0,"max_expr_nodes":0,"by_site":{}},"egraph":{},"rule_instantiation":{"rule_search_calls":0,"rule_instantiation_calls":0,"skipped_instantiation_calls":0,"matches_total":0,"substitutions_total":0,"substitutions_explored":0,"candidates_generated":0,"candidates_selected":0,"by_rule":{}}}"#;
        let legacy: crate::profiling::ProfilingRecord = serde_json::from_str(old_record).unwrap();
        assert!(legacy.quantifier_work.is_empty());
    }

    #[derive(Clone)]
    pub(super) struct PreferLongName;

    impl egg::CostFunction<ArrayLanguage> for PreferLongName {
        type Cost = u32;
        fn cost<C>(&mut self, node: &ArrayLanguage, mut child: C) -> u32
        where
            C: FnMut(egg::Id) -> u32,
        {
            use egg::Language;
            let own = match node {
                ArrayLanguage::Symbol(symbol) if symbol.as_str() == "long_preferred_term" => 1,
                ArrayLanguage::Symbol(symbol) if symbol.as_str() == "a" => 100,
                _ => 2,
            };
            node.fold(own, |sum, id| sum + child(id))
        }
    }
    impl crate::cost_functions::YardbirdCostFunction<ArrayLanguage> for PreferLongName {
        fn get_string_terms(&self) -> Vec<String> {
            vec![]
        }
        fn get_reads_and_writes(&self) -> smt2parser::vmt::ReadsAndWrites {
            Default::default()
        }
    }

    #[derive(Clone, Default)]
    struct CountCosts(std::rc::Rc<std::cell::RefCell<Vec<String>>>);

    impl egg::CostFunction<ArrayLanguage> for CountCosts {
        type Cost = u32;
        fn cost<C>(&mut self, node: &ArrayLanguage, children: C) -> u32
        where
            C: FnMut(egg::Id) -> u32,
        {
            self.0.borrow_mut().push(node.to_string());
            PreferLongName.cost(node, children)
        }
    }

    impl crate::cost_functions::YardbirdCostFunction<ArrayLanguage> for CountCosts {
        fn get_string_terms(&self) -> Vec<String> {
            vec![]
        }
        fn get_reads_and_writes(&self) -> smt2parser::vmt::ReadsAndWrites {
            Default::default()
        }
    }

    pub(crate) struct PreparedFixture {
        pub(crate) egraph: egg::EGraph<ArrayLanguage, ()>,
        pub(crate) search: PreparedQuantifierSearch,
    }
    impl std::ops::Deref for PreparedFixture {
        type Target = PreparedQuantifierSearch;
        fn deref(&self) -> &Self::Target {
            &self.search
        }
    }
    impl std::ops::DerefMut for PreparedFixture {
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut self.search
        }
    }
    impl PreparedFixture {
        pub(crate) fn candidates<'a, CF>(
            &mut self,
            evaluate: impl FnMut(&Term) -> anyhow::Result<String>,
            search: impl Into<BinderSearch<'a>>,
            make_cost: impl FnOnce(&crate::cost_functions::array::ArrayCostContext) -> CF,
            options: ArrayInstantiationOptions,
        ) -> anyhow::Result<InstantiationBatch>
        where
            CF: crate::cost_functions::YardbirdCostFunction<ArrayLanguage> + 'static,
        {
            self.search
                .candidates(&self.egraph, evaluate, search, make_cost, options)
        }
    }

    pub(super) fn prepared_fixture(variable_count: usize, value_count: usize) -> PreparedFixture {
        let variables = (0..variable_count)
            .map(|i| (Symbol(format!("x{i}")), string_to_sort("Int")))
            .collect::<Vec<_>>();
        let rule = BinderRule {
            name: "q".into(),
            kind: BinderKind::Forall,
            captures: vec![(Symbol("unit".into()), string_to_sort("Bool"))],
            body: app(
                "p",
                variables
                    .iter()
                    .map(|(symbol, _)| app(&symbol.0, vec![]))
                    .collect(),
            ),
            witnesses: (0..variable_count).map(|i| format!("witness{i}")).collect(),
            variables,
            result_sort: string_to_sort("Bool"),
            unit_capture: true,
        };
        let plan = QuantifierPlan {
            rules: vec![rule],
            signatures: (0..value_count)
                .map(|i| (format!("v{i}"), (vec![], string_to_sort("Int"))))
                .collect(),
            ..Default::default()
        };
        let mut graph = egg::EGraph::<ArrayLanguage, ()>::default();
        let mut terms = vec![];
        for term in ["(q true)".to_string(), "true".into(), "false".into()]
            .into_iter()
            .chain((0..value_count).map(|i| format!("v{i}")))
        {
            let expression = translate_term_with_array_types(term.parse().unwrap(), &[]).unwrap();
            graph.add_expr(&expression);
            terms.push(expression);
        }
        let proxy = graph.lookup_expr(&terms[0]).unwrap();
        let truth = graph.lookup_expr(&terms[1]).unwrap();
        graph.union(proxy, truth);
        let sort = graph.add(ArrayLanguage::SortTag("Int".into()));
        for expression in &terms[3..] {
            let value = graph.lookup_expr(expression).unwrap();
            graph.add(ArrayLanguage::Domain([sort, value]));
        }
        graph.rebuild();
        let mut representatives = HashMap::new();
        for expression in &terms {
            representatives
                .entry(graph.find(graph.lookup_expr(expression).unwrap()))
                .or_insert(expression.clone());
        }
        PreparedFixture {
            egraph: graph,
            search: PreparedQuantifierSearch {
                graph_version: 0,
                additional_terms: terms,
                representatives,
                evaluations: HashMap::new(),
                compiled: plan.compiled(&[]).unwrap(),
                cursors: HashMap::new(),
                requests: HashMap::new(),
                obligations: HashMap::new(),
                catalog: Default::default(),
                cost_context: Default::default(),
            },
        }
    }

    pub(super) fn prepared_options() -> ArrayInstantiationOptions {
        ArrayInstantiationOptions {
            match_scope: None,
            search_allowance: crate::policy::effort::WorkAllowance::default(),
            candidate_catalog: Default::default(),
            additional_terms: vec![],
            candidate_scope: crate::theories::array::candidate_scope::CandidateScope::AllCandidates,
            refinement_step: 0,
            selection_counts: Default::default(),
            depth: 0,
            instrumentation:
                crate::theories::array::array_axioms::ArrayInstantiationInstrumentation {
                    artifact_capture: Default::default(),
                    profiling: None,
                },
        }
    }

    #[test]
    fn satisfied_matches_do_not_invoke_costs_or_extraction() {
        let mut prepared = prepared_fixture(1, 5);
        let cost = CountCosts::default();
        let factories = std::cell::Cell::new(0);
        let batch = prepared
            .candidates(
                |_| Ok("true".into()),
                SearchPhase::Conflicts,
                |_| {
                    factories.set(factories.get() + 1);
                    cost.clone()
                },
                prepared_options(),
            )
            .unwrap();
        assert!(batch.candidates.is_empty());
        assert_eq!(
            factories.get(),
            0,
            "even heuristic construction must wait for a violation"
        );
        assert!(
            cost.0.borrow().is_empty(),
            "satisfied matches must not initialize ranked extraction"
        );
    }

    #[test]
    fn a_surviving_match_does_not_score_rejected_binding_classes() {
        let mut prepared = prepared_fixture(1, 5);
        let cost = CountCosts::default();
        let batch = prepared
            .candidates(
                |term| {
                    Ok(if term.to_string().contains("(p v4)") {
                        "false"
                    } else {
                        "true"
                    }
                    .into())
                },
                SearchPhase::Conflicts,
                |_| cost.clone(),
                prepared_options(),
            )
            .unwrap();
        assert_eq!(batch.candidates.len(), 1);
        assert!(batch.candidates[0].model_violation_verified);
        let calls = cost.0.borrow();
        assert!(calls.iter().any(|symbol| symbol == "v4"));
        assert!(!calls
            .iter()
            .any(|symbol| ["v0", "v1", "v2", "v3"].contains(&symbol.as_str())));
    }

    #[test]
    fn fallback_optimizes_surviving_bindings_without_costing_unrelated_classes() {
        let mut prepared = prepared_fixture(1, 2);
        prepared.additional_terms.clear(); // Exercise the shared e-graph fallback.
        let preferred =
            translate_term_with_array_types("long_preferred_term".parse().unwrap(), &[]).unwrap();
        let preferred_id = prepared.egraph.add_expr(&preferred);
        let original = prepared.egraph.lookup_expr(&"v0".parse().unwrap()).unwrap();
        prepared.egraph.union(original, preferred_id);
        prepared.egraph.rebuild();
        let cost = CountCosts::default();
        let batch = prepared
            .candidates(
                |term| {
                    Ok(if term.to_string().contains("v1") {
                        "true"
                    } else {
                        "false"
                    }
                    .into())
                },
                SearchPhase::Conflicts,
                |_| cost.clone(),
                prepared_options(),
            )
            .unwrap();
        assert_eq!(batch.candidates.len(), 1);
        assert!(batch.candidates[0]
            .expression
            .to_string()
            .contains("long_preferred_term"));
        assert!(!cost.0.borrow().iter().any(|symbol| symbol == "v1"));
    }

    #[test]
    fn triggered_and_domain_search_share_model_obligation_results() {
        let mut prepared = prepared_fixture(1, 2);
        // Keep this test focused on sharing evaluations across the historical
        // trigger and domain paths; signed-plan matching is tested separately.
        let legacy = prepared.compiled.sources[0]
            .compile(SearchPhase::TriggeredConflicts, &[])
            .unwrap()
            .unwrap();
        std::rc::Rc::get_mut(&mut prepared.compiled)
            .unwrap()
            .phases
            .insert(SearchPhase::TriggeredConflicts, vec![legacy]);
        for atom in ["(p v0)", "(p v1)"] {
            prepared
                .egraph
                .add_expr(&translate_term_with_array_types(atom.parse().unwrap(), &[]).unwrap());
        }
        prepared.egraph.rebuild();
        let mut checks = 0;
        prepared
            .candidates(
                |_| {
                    checks += 1;
                    Ok("true".into())
                },
                SearchPhase::TriggeredConflicts,
                |_| CountCosts::default(),
                prepared_options(),
            )
            .unwrap();
        assert_eq!(checks, 2);
        let batch = prepared
            .candidates(
                |_| panic!("the same model obligation was already evaluated"),
                SearchPhase::Conflicts,
                |_| CountCosts::default(),
                prepared_options(),
            )
            .unwrap();
        assert!(batch.candidates.is_empty());
    }

    #[test]
    fn optimized_binding_preserves_the_cheap_obligations_value() {
        let mut prepared = prepared_fixture(1, 1);
        let preferred =
            translate_term_with_array_types("long_preferred_term".parse().unwrap(), &[]).unwrap();
        let preferred_id = prepared.egraph.add_expr(&preferred);
        let original = prepared.egraph.lookup_expr(&"v0".parse().unwrap()).unwrap();
        prepared.egraph.union(original, preferred_id);
        prepared.egraph.rebuild();
        prepared.additional_terms.push(preferred);
        let batch = prepared
            .candidates(
                |term| {
                    assert_eq!(
                        term.to_string().replace("long_preferred_term", "v0"),
                        "(=> (q true) (p v0))"
                    );
                    Ok("false".into())
                },
                SearchPhase::Conflicts,
                |_| CountCosts::default(),
                prepared_options(),
            )
            .unwrap();
        assert_eq!(batch.candidates.len(), 1);
        assert!(batch.candidates[0]
            .expression
            .to_string()
            .contains("long_preferred_term"));
        assert!(batch.candidates[0].model_violation_verified);
    }

    #[test]
    fn a_new_phase_pass_reconsiders_bindings_after_history_changes() {
        let mut prepared = prepared_fixture(1, 1);
        let preferred =
            translate_term_with_array_types("long_preferred_term".parse().unwrap(), &[]).unwrap();
        let preferred_id = prepared.egraph.add_expr(&preferred);
        let original = prepared.egraph.lookup_expr(&"v0".parse().unwrap()).unwrap();
        prepared.egraph.union(original, preferred_id);
        prepared.egraph.rebuild();
        prepared.additional_terms.push(preferred.clone());
        let first = prepared
            .candidates(
                |_| unreachable!(),
                SearchPhase::Expand,
                |_| CountCosts::default(),
                prepared_options(),
            )
            .unwrap();
        assert!(first.candidates[0]
            .expression
            .to_string()
            .contains("long_preferred_term"));
        let mut options = prepared_options();
        options
            .selection_counts
            .insert(crate::training::canonical_term_hash(&preferred), 100);
        prepared.start_phase(SearchPhase::Expand, 0);
        let second = prepared
            .candidates(
                |_| unreachable!(),
                SearchPhase::Expand,
                |_| CountCosts::default(),
                options,
            )
            .unwrap();
        assert_eq!(second.candidates.len(), 1);
        assert!(second.candidates[0].expression.to_string().contains("v0"));
        assert!(!second.candidates[0]
            .expression
            .to_string()
            .contains("long_preferred_term"));
    }

    #[test]
    fn binder_profiling_separates_matching_from_grounding() {
        for violated in [false, true] {
            let profiling = std::rc::Rc::new(std::cell::RefCell::new(
                crate::profiling::ArrayProfilingCollector::new("test", None, None, vec![]),
            ));
            let mut prepared = prepared_fixture(1, 2);
            let mut options = prepared_options();
            options.instrumentation.profiling = Some(profiling.clone());
            prepared
                .candidates(
                    |_| Ok(if violated { "false" } else { "true" }.into()),
                    SearchPhase::Conflicts,
                    |_| CountCosts::default(),
                    options,
                )
                .unwrap();
            let record = std::rc::Rc::try_unwrap(profiling)
                .ok()
                .unwrap()
                .into_inner()
                .finish();
            assert!(record.timing_secs.contains_key("rule_matching_total"));
            assert_eq!(
                record.timing_secs.contains_key("rule_grounding_total"),
                violated
            );
            assert!(!record.timing_secs.contains_key("rule_search_total"));
        }
    }

    #[test]
    fn binder_continuation_finds_a_violation_after_a_satisfied_prefix() {
        use crate::theories::array::{
            array_axioms::expr_to_term,
            array_grounding::instantiate_with_bindings,
            quantified_search::{search_binder_page, BinderSearchCursor},
        };
        let mut prepared = prepared_fixture(2, 11); // 121 typed substitutions.
        let rules = &prepared.compiled.phases[&SearchPhase::Conflicts];
        let mut cursor = BinderSearchCursor::default();
        let first = search_binder_page(&prepared.egraph, rules, &mut cursor, &None);
        assert_eq!(first.matches.len(), 100);
        assert_eq!(first.report.continuable_rules.len(), 1);
        assert!(first.report.budget_exhausted_rules.is_empty());
        let second = search_binder_page(&prepared.egraph, rules, &mut cursor, &None);
        assert_eq!(second.matches.len(), 21);
        assert!(second.report.continuable_rules.is_empty());
        assert!(second.report.budget_exhausted_rules.is_empty());
        let last = second.matches.last().unwrap();
        let target = expr_to_term(
            instantiate_with_bindings(rules[0].formula(), |variable| {
                Ok(&prepared.representatives[&prepared.egraph.find(last.substitution[variable])])
            })
            .unwrap(),
        );
        let evaluate = |term: &Term| Ok(if *term == target { "false" } else { "true" }.into());
        let cost = CountCosts::default();
        let profiling = std::rc::Rc::new(std::cell::RefCell::new(
            crate::profiling::ArrayProfilingCollector::new("test", None, None, vec![]),
        ));
        let mut options = prepared_options();
        options.instrumentation.profiling = Some(profiling.clone());
        let first = prepared
            .candidates(evaluate, SearchPhase::Conflicts, |_| cost.clone(), options)
            .unwrap();
        assert!(first.candidates.is_empty());
        assert!(prepared.can_continue(SearchPhase::Conflicts));
        assert!(cost.0.borrow().is_empty());
        let record = std::rc::Rc::try_unwrap(profiling)
            .ok()
            .unwrap()
            .into_inner()
            .finish();
        assert_eq!(
            record
                .counters
                .get("rule_search_truncated")
                .copied()
                .unwrap_or(0),
            0
        );
        assert_eq!(record.counters["rule_search_continuations_available"], 1);
        assert_eq!(record.counters["rule_search_budget_exhausted"], 0);
        let second = prepared
            .candidates(
                evaluate,
                SearchPhase::Conflicts,
                |_| cost,
                prepared_options(),
            )
            .unwrap();
        assert_eq!(second.candidates.len(), 1);
        assert_eq!(
            expr_to_term(second.candidates[0].expression.clone()),
            target
        );
        assert!(!prepared.can_continue(SearchPhase::Conflicts));
    }

    #[test]
    fn expansion_can_materialize_a_satisfied_obligation() {
        let mut prepared = prepared_fixture(1, 1);
        let batch = prepared
            .candidates(
                |_| panic!("expansion must not require a violation"),
                SearchPhase::Expand,
                |_| CountCosts::default(),
                prepared_options(),
            )
            .unwrap();
        assert_eq!(batch.candidates.len(), 1);
        assert!(!batch.candidates[0].model_violation_verified);
    }

    #[test]
    fn compiled_rules_are_reused_until_array_types_change() {
        let plan = QuantifierPlan::default();
        let first = plan.compiled(&[]).unwrap();
        assert!(std::rc::Rc::ptr_eq(&first, &plan.compiled(&[]).unwrap()));
        let changed = plan.compiled(&[("Int".into(), "Bool".into())]).unwrap();
        assert!(!std::rc::Rc::ptr_eq(&first, &changed));
    }

    #[test]
    fn binder_work_limit_is_reported_as_budget_exhaustion_not_continuation() {
        use crate::theories::array::quantified_search::{search_binder_page, BinderSearchCursor};
        let prepared = prepared_fixture(2, 257); // 66,049 > the 65,536 work window.
        let rules = &prepared.compiled.phases[&SearchPhase::Conflicts];
        let mut cursor = BinderSearchCursor::default();
        let mut count = 0;
        let mut examined = 0;
        loop {
            let page = search_binder_page(&prepared.egraph, rules, &mut cursor, &None);
            count += page.matches.len();
            examined += page.report.examined_substitutions;
            assert_eq!(
                page.report.continuable_rules.len(),
                usize::from(cursor.can_continue())
            );
            assert_eq!(
                page.report.budget_exhausted_rules.len(),
                usize::from(!cursor.can_continue())
            );
            if !cursor.can_continue() {
                break;
            }
        }
        assert_eq!(count, 65_536);
        assert_eq!(
            examined, 21_550_192,
            "prefix re-examination must also be bounded"
        );
        let exhausted = search_binder_page(&prepared.egraph, rules, &mut cursor, &None);
        assert!(exhausted.matches.is_empty());
        assert_eq!(exhausted.report.examined_substitutions, 0);
        assert!(exhausted.report.continuable_rules.is_empty());
        assert_eq!(exhausted.report.budget_exhausted_rules.len(), 1);
    }

    #[test]
    fn binder_exact_work_limit_completes_without_budget_exhaustion() {
        use crate::theories::array::quantified_search::{search_binder_page, BinderSearchCursor};
        let prepared = prepared_fixture(2, 256); // Exactly 65,536 substitutions.
        let rules = &prepared.compiled.phases[&SearchPhase::Conflicts];
        let mut cursor = BinderSearchCursor::default();
        let mut count = 0;
        loop {
            let page = search_binder_page(&prepared.egraph, rules, &mut cursor, &None);
            count += page.matches.len();
            assert!(page.report.budget_exhausted_rules.is_empty());
            assert_eq!(
                page.report.continuable_rules.len(),
                usize::from(cursor.can_continue())
            );
            if !cursor.can_continue() {
                break;
            }
        }
        assert_eq!(count, 65_536);
    }

    #[test]
    fn nested_binder_search_prepares_once_per_model_and_refreshes_after_checks() {
        let mut options = YardbirdOptions::from_filename("unused.vmt".into());
        options.profile = true;
        let mut driver = Driver::new(
            formula_model("(exists ((x Bool)) (forall ((y Bool)) (= x y)))", "false"),
            options.build_instantiation_strategy(),
            SolverBackend::Z3,
        )
        .with_profiler(options.build_profiler());
        let result = driver
            .check_strategy(1, options.build_array_strategy())
            .unwrap();
        let sat_models = result
            .profiling
            .solver_checks
            .iter()
            .filter(|check| check.result == crate::solver::SolverCheckResult::Sat)
            .count();
        let preparations: u64 = result
            .profiling
            .cost_records
            .iter()
            .map(|record| {
                record
                    .counters
                    .get("input_binder_model_preparations")
                    .copied()
                    .unwrap_or(0)
            })
            .sum();
        assert!(
            sat_models > 1,
            "the fixture must require fresh counterexample models"
        );
        assert_eq!(preparations, sat_models as u64);
        assert!(result.profiling.cost_records.iter().any(|record| record
            .timing_secs
            .contains_key("input_binder_triggered_conflicts")));
        assert!(!result.counterexample);
    }

    fn ranked_binder_fixture(phase: SearchPhase) -> InstantiationBatch {
        use crate::theories::array::{
            array_axioms::ArrayInstantiationInstrumentation, candidate_scope::CandidateScope,
        };
        let rule = BinderRule {
            name: "q".into(),
            kind: BinderKind::Forall,
            captures: vec![(Symbol("unit".into()), string_to_sort("Bool"))],
            variables: vec![(Symbol("x".into()), string_to_sort("Int"))],
            body: "(p x)".parse().unwrap(),
            witnesses: vec!["witness".into()],
            result_sort: string_to_sort("Bool"),
            unit_capture: true,
        };
        let mut graph = egg::EGraph::<ArrayLanguage, ()>::default();
        let mut catalog = crate::problem_context::ArrayCandidateCatalog::default();
        let mut add = |text: &str| {
            catalog.source_grounded.terms.push(text.to_string());
            graph.add_expr(&translate_term_with_array_types(text.parse().unwrap(), &[]).unwrap())
        };
        if phase == SearchPhase::TriggeredConflicts {
            add("(p b)");
        }
        let proxy = add("(q true)");
        let truth = add("true");
        let falsity = add("false");
        let a = add("a");
        let preferred = add("long_preferred_term");
        let b = add("b");
        // A Bool term with a different typed domain must never bind the Int slot.
        let boolean = add("flag");
        // Sort names can also be term names; equal values for those terms
        // must not merge the typed domains.
        let named_int = add("Int");
        let named_bool = add("Bool");
        graph.union(named_int, named_bool);
        graph.union(a, preferred);
        graph.union(truth, boolean);
        graph.union(
            proxy,
            if phase == SearchPhase::Witnesses {
                falsity
            } else {
                truth
            },
        );
        let int_sort = graph.add(ArrayLanguage::SortTag("Int".into()));
        let bool_sort = graph.add(ArrayLanguage::SortTag("Bool".into()));
        graph.add(ArrayLanguage::Domain([int_sort, a]));
        graph.add(ArrayLanguage::Domain([int_sort, b]));
        graph.add(ArrayLanguage::Domain([bool_sort, boolean]));
        graph.rebuild();
        generate_quantified_candidates(
            &graph,
            PreferLongName,
            &[rule.compile(phase, &[]).unwrap().unwrap()],
            ArrayInstantiationOptions {
                match_scope: None,
                search_allowance: crate::policy::effort::WorkAllowance::default(),
                additional_terms: catalog
                    .source_grounded
                    .terms
                    .iter()
                    .map(|term| {
                        translate_term_with_array_types(term.parse().unwrap(), &[]).unwrap()
                    })
                    .collect(),
                candidate_catalog: catalog,
                candidate_scope: CandidateScope::AllCandidates,
                refinement_step: 0,
                selection_counts: Default::default(),
                depth: 0,
                instrumentation: ArrayInstantiationInstrumentation {
                    artifact_capture:
                        crate::theories::array::array_rule_instantiator::ArrayArtifactCapture {
                            decisions: true,
                            instantiation_provenance: true,
                            conflicts: true,
                        },
                    profiling: None,
                },
            },
            None,
        )
        .unwrap()
    }

    #[test]
    fn input_binders_use_costed_typed_egg_grounding_and_record_decisions() {
        use egg::CostFunction;
        let batch = ranked_binder_fixture(SearchPhase::Conflicts);
        assert_eq!(batch.candidates.len(), 2);
        let rendered = batch
            .candidates
            .iter()
            .map(|candidate| {
                assert_eq!(
                    candidate.cost,
                    PreferLongName.cost_rec(&candidate.expression)
                );
                assert!(!candidate.selected, "generation must not bypass selection");
                assert!(!candidate.decisions.is_empty());
                assert!(!candidate.selection_history.is_empty());
                assert!(candidate.abstract_instantiation.is_some());
                assert!(
                    candidate.conflict.is_none(),
                    "input binders are not auxiliary array conflicts"
                );
                crate::theories::array::array_axioms::expr_to_term(candidate.expression.clone())
                    .to_string()
            })
            .collect::<Vec<_>>();
        assert!(rendered
            .iter()
            .any(|text| text.contains("(p long_preferred_term)")));
        assert!(rendered.iter().any(|text| text.contains("(p b)")));
        assert!(rendered
            .iter()
            .all(|text| !text.contains("flag") && !text.contains("(p a)")));
    }

    #[test]
    fn input_binders_match_existing_body_atoms_before_domain_fallback() {
        let triggered = ranked_binder_fixture(SearchPhase::TriggeredConflicts);
        assert_eq!(triggered.candidates.len(), 1);
        let term = crate::theories::array::array_axioms::expr_to_term(
            triggered.candidates[0].expression.clone(),
        );
        assert!(term.to_string().contains("(p b)"));
        assert_eq!(
            ranked_binder_fixture(SearchPhase::Conflicts)
                .candidates
                .len(),
            2
        );
    }

    #[test]
    fn input_binder_batches_obey_rankers_budgets_and_novelty() {
        use crate::theories::array::{
            candidate_scope::CandidateScope,
            instantiation_ranker::{InstantiationRanker, TermCostInstantiationRanker},
        };
        #[derive(Clone, Debug)]
        struct Reverse;
        impl InstantiationRanker for Reverse {
            fn clone_box(&self) -> Box<dyn InstantiationRanker> {
                Box::new(self.clone())
            }
            fn compare(
                &self,
                left: &crate::theories::array::instantiation_candidate::InstantiationCandidate,
                right: &crate::theories::array::instantiation_candidate::InstantiationCandidate,
            ) -> std::cmp::Ordering {
                TermCostInstantiationRanker.compare(right, left)
            }
        }
        let prepare = |batch: &mut InstantiationBatch,
                       ranker: &dyn InstantiationRanker,
                       budget,
                       known: &HashSet<String>| {
            batch
                .prepare_with_ranker(
                    CandidateScope::AllCandidates,
                    known,
                    budget,
                    ranker,
                    |_| panic!("expansion need not violate the model"),
                    |candidate| Some(candidate.expression.to_string()),
                )
                .unwrap()
        };
        let mut batch = ranked_binder_fixture(SearchPhase::Expand);
        assert_eq!(
            prepare(&mut batch, &TermCostInstantiationRanker, 1, &HashSet::new()).selected_count(),
            1
        );
        let first = batch.selected().next().unwrap().expression.to_string();
        assert_eq!(
            prepare(&mut batch, &Reverse, 1, &HashSet::new()).selected_count(),
            1
        );
        assert_ne!(
            first,
            batch.selected().next().unwrap().expression.to_string()
        );
        assert_eq!(
            prepare(&mut batch, &Reverse, 40, &HashSet::new()).selected_count(),
            2
        );
        assert_eq!(
            prepare(
                &mut batch,
                &TermCostInstantiationRanker,
                1,
                &HashSet::from([first.clone()])
            )
            .selected_count(),
            1
        );
        assert_ne!(
            first,
            batch.selected().next().unwrap().expression.to_string()
        );

        let mut witnesses = ranked_binder_fixture(SearchPhase::Witnesses);
        assert_eq!(witnesses.candidates.len(), 1);
        assert!(witnesses.candidates[0]
            .expression
            .to_string()
            .contains("witness"));
        assert_eq!(
            prepare(
                &mut witnesses,
                &TermCostInstantiationRanker,
                1,
                &HashSet::new()
            )
            .selected_count(),
            1
        );
    }

    #[test]
    fn let_aliases_are_not_captured_by_quantifiers_or_property_witnesses() {
        let source = |init: &str, property: &str| {
            model(&format!(
                "(declare-fun a () (Array Bool Bool))
            (declare-fun x () Bool)
            (define-fun init () Bool (! {init} :init true))
            (define-fun trans () Bool (! true :trans true))
            (define-fun prop () Bool (! {property} :invar-property 0))"
            ))
        };
        let alias = "(let ((alias x)) (forall ((x Bool)) alias))";
        assert!(check_model(source("x", alias)).is_ok());
        assert!(matches!(
            check_model(source(&format!("(and x {alias})"), "false")),
            Err(crate::Error::AbstractionExhausted { .. })
        ));
    }

    #[test]
    fn arrays_that_only_occur_in_binder_expressions_are_declared() {
        let result = check_model(model("(define-fun init () Bool (! true :init true))
            (define-fun trans () Bool (! true :trans true))
            (define-fun prop () Bool (! (forall ((x Bool)) (select (lambda ((y Bool)) true) x)) :invar-property 0))")).unwrap();
        assert!(!result.counterexample);
    }

    #[test]
    fn arithmetic_hidden_in_a_quantifier_selects_a_sufficient_logic() {
        assert!(check("(forall ((x Int)) (< (* x x) 0))", "false").is_ok());
    }

    #[test]
    fn every_protocol_lowers_to_quantifier_free_commands_and_rules() {
        let root =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/distributed_protocols");
        let mut files = Vec::new();
        for directory in std::fs::read_dir(root).unwrap().flatten() {
            if !directory.path().is_dir() {
                continue;
            }
            for entry in std::fs::read_dir(directory.path()).unwrap().flatten() {
                if entry
                    .path()
                    .extension()
                    .is_some_and(|extension| extension == "vmt")
                {
                    files.push(entry.path());
                }
            }
        }
        assert!(files.len() >= 30, "protocol inventory unexpectedly shrank");
        files.sort();
        for file in files {
            let (lowered, plan) = lower_model(VMTModel::from_path(&file).unwrap())
                .unwrap_or_else(|error| panic!("{}: {error}", file.display()));
            let (abstracted, _) = lowered.abstract_array_theory();
            for command in abstracted.as_commands() {
                if let Command::Assert { term } | Command::DefineFun { term, .. } = command {
                    assert!(!contains_binders(&term), "{} leaked {term}", file.display());
                }
            }
            for rule in plan.rules {
                assert!(
                    !contains_binders(&rule.body),
                    "{} leaked binder in rule {}",
                    file.display(),
                    rule.name
                );
            }
        }
    }

    #[test]
    fn existential_witness_depends_on_the_enclosing_universal() {
        let (_, plan) = lower_model(formula_model(
            "(forall ((x Bool)) (exists ((y Bool)) (= x y)))",
            "false",
        ))
        .unwrap();
        let exists = plan
            .rules
            .iter()
            .find(|rule| rule.kind == BinderKind::Exists)
            .unwrap();
        assert_eq!(exists.captures.len(), 1);
        let witness = exists.witness_instance(&[app("true", vec![])]).unwrap();
        assert!(witness
            .to_string()
            .contains(&format!("({} true)", exists.witnesses[0])));
        assert!(!contains_binders(&witness));
    }

    #[test]
    fn shadowed_binders_have_distinct_capture_free_names() {
        let (_, plan) = lower_model(formula_model(
            "(forall ((x Bool)) (and x (exists ((x Bool)) (not x))))",
            "false",
        ))
        .unwrap();
        let outer = plan
            .rules
            .iter()
            .find(|rule| rule.kind == BinderKind::Forall)
            .unwrap();
        let inner = plan
            .rules
            .iter()
            .find(|rule| rule.kind == BinderKind::Exists)
            .unwrap();
        assert_ne!(outer.variables[0].0, inner.variables[0].0);
        assert!(!inner
            .captures
            .iter()
            .any(|(symbol, _)| symbol == &outer.variables[0].0));
    }

    #[test]
    fn nested_constant_lambdas_use_nested_constant_arrays() {
        let source = model("(declare-fun a () (Array Bool (Array Bool Bool)))
            (define-fun init () Bool (! (= a (lambda ((x Bool)) (lambda ((y Bool)) false))) :init true))
            (define-fun trans () Bool (! true :trans true))
            (define-fun prop () Bool (! true :invar-property 0))");
        let (lowered, plan) = lower_model(source).unwrap();
        assert!(plan.rules.is_empty());
        let (abstracted, types) = lowered.abstract_array_theory();
        assert!(types.contains(&("Bool".into(), "Bool".into())));
        assert!(types.contains(&("Bool".into(), "Array_Bool_Bool".into())));
        assert!(abstracted
            .as_vmt_string()
            .contains("(ConstArr_Bool_Array_Bool_Bool (ConstArr_Bool_Bool false))"));
    }

    #[test]
    fn quantifier_polarities_and_alternation_are_sound_over_booleans() {
        // These formulas are unsatisfiable; either polarity can require
        // universal instances as well as existential witnesses.
        for init in [
            "(forall ((x Bool)) x)",
            "(not (exists ((x Bool)) x))",
            "(exists ((x Bool)) (forall ((y Bool)) (= x y)))",
            "(not (forall ((x Bool)) (exists ((y Bool)) (= x y))))",
            "(= false (exists ((x Bool) (y Bool)) (distinct x y)))",
        ] {
            let result = check(init, "false").unwrap_or_else(|error| panic!("{init}: {error}"));
            assert!(!result.counterexample);
            assert_eq!(
                result
                    .solver_statistics
                    .get_f64("concrete_validation_checks"),
                Some(0.0)
            );
        }
        // Exhaustion is inconclusive. It must never prove these satisfiable
        // formulas inconsistent or delegate their quantifiers to Z3.
        for init in [
            "(exists ((x Bool)) x)",
            "(not (forall ((x Bool)) x))",
            "(forall ((x Bool)) (exists ((y Bool)) (= x y)))",
            "(exists ((x Bool)) (and x (forall ((x Bool)) (= x x))))",
        ] {
            assert!(
                matches!(
                    check(init, "false"),
                    Err(crate::Error::AbstractionExhausted { .. })
                ),
                "{init}"
            );
        }
    }

    #[test]
    fn binder_page_rotate_and_preserve_each_rules_position() {
        use crate::theories::array::quantified_search::{search_binder_page, BinderSearchCursor};

        let prepared = prepared_fixture(2, 11);
        let other = prepared_fixture(2, 11);

        let mut first_compiled = std::rc::Rc::try_unwrap(prepared.search.compiled)
            .ok()
            .unwrap();
        let mut second_comiled = std::rc::Rc::try_unwrap(other.search.compiled).ok().unwrap();

        let mut rules = first_compiled
            .phases
            .remove(&SearchPhase::Conflicts)
            .unwrap();
        rules.extend(
            second_comiled
                .phases
                .remove(&SearchPhase::Conflicts)
                .unwrap(),
        );

        assert_eq!(rules.len(), 2);

        let mut cursor = BinderSearchCursor::default();
        let mut seen = [
            HashSet::<Vec<egg::Id>>::new(),
            HashSet::<Vec<egg::Id>>::new(),
        ];

        for (rule_index, count, pending) in [(0, 100, 2), (1, 100, 2), (0, 21, 1), (1, 21, 0)] {
            let page = search_binder_page(&prepared.egraph, &rules, &mut cursor, &None);

            assert_eq!(page.matches.len(), count);
            assert_eq!(page.report.rounds, 1);
            assert_eq!(page.report.continuable_rules.len(), pending);
            assert_eq!(cursor.can_continue(), pending > 0);
            assert!(page.report.budget_exhausted_rules.is_empty());

            for matched in page.matches {
                assert_eq!(matched.rule_index, rule_index);
                let bindings = rules[rule_index]
                    .formula_variables()
                    .iter()
                    .map(|var| prepared.egraph.find(matched.substitution[*var]))
                    .collect::<Vec<_>>();

                assert!(
                    seen[rule_index].insert(bindings),
                    "a binding was returned more than once for rule {rule_index}"
                );
            }
        }

        assert_eq!(seen[0].len(), 121);
        assert_eq!(seen[1].len(), 121);

        let finished = search_binder_page(&prepared.egraph, &rules, &mut cursor, &None);

        assert!(finished.matches.is_empty());
        assert_eq!(finished.report.rounds, 0);
        assert_eq!(finished.report.examined_substitutions, 0);
        assert!(finished.report.continuable_rules.is_empty());
        assert!(finished.report.budget_exhausted_rules.is_empty());
    }

    #[test]
    fn binder_pages_skip_completed_rules() {
        use crate::theories::array::quantified_search::{search_binder_page, BinderSearchCursor};

        // Both rules use the same domain of 11 values.
        // One variable gives 11 matches; two give 121.
        let short = prepared_fixture(1, 11);
        let long = prepared_fixture(2, 11);

        let mut short_compiled = std::rc::Rc::try_unwrap(short.search.compiled).ok().unwrap();
        let mut long_compiled = std::rc::Rc::try_unwrap(long.search.compiled).ok().unwrap();

        let mut rules = short_compiled
            .phases
            .remove(&SearchPhase::Conflicts)
            .unwrap();
        rules.extend(
            long_compiled
                .phases
                .remove(&SearchPhase::Conflicts)
                .unwrap(),
        );
        assert_eq!(rules.len(), 2);

        let mut cursor = BinderSearchCursor::default();

        for (rule_index, count, more) in [(0, 11, true), (1, 100, true), (1, 21, false)] {
            let page = search_binder_page(&long.egraph, &rules, &mut cursor, &None);

            assert_eq!(page.matches.len(), count);
            assert!(page
                .matches
                .iter()
                .all(|matched| matched.rule_index == rule_index));
            assert_eq!(page.report.rounds, 1);
            assert_eq!(page.report.continuable_rules.len(), usize::from(more));
            assert!(page.report.budget_exhausted_rules.is_empty());
            assert_eq!(cursor.can_continue(), more);
        }

        let finished = search_binder_page(&long.egraph, &rules, &mut cursor, &None);
        assert!(finished.matches.is_empty());
        assert_eq!(finished.report.examined_substitutions, 0);
        assert_eq!(finished.report.rounds, 0);
        assert!(!cursor.can_continue());
    }
}
