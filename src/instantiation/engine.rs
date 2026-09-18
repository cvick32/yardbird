//! Shared matching and complete-instance construction.
use std::{cell::RefCell, rc::Rc, time::Instant};

use super::language::{TermExpr, TermLanguage, TermPattern};
use egg::*;
use rustc_hash::FxHashMap;

use crate::{
    cost_functions::YardbirdCostFunction,
    instantiation::{
        candidate::InstantiationBatch,
        extractor::{TermExtractor, TermExtractorOptions},
        instantiator::{
            ArtifactCapture, CandidateDemand, RuleInstantiator, RuleInstantiatorOptions,
        },
        rule::QuantifiedRule,
        scope::CandidateScope,
    },
    problem_context::ArrayCandidateCatalog,
    profiling::ArrayProfilingCollector,
};

pub struct InstantiationInstrumentation {
    pub artifact_capture: ArtifactCapture,
    pub profiling: Option<Rc<RefCell<ArrayProfilingCollector>>>,
}

pub struct InstantiationOptions {
    pub search_allowance: crate::policy::effort::WorkAllowance,
    pub candidate_catalog: ArrayCandidateCatalog,
    pub additional_terms: Vec<TermExpr>,
    pub candidate_scope: CandidateScope,
    pub refinement_step: u32,
    pub selection_counts: FxHashMap<String, u32>,
    pub depth: u16,
    pub instrumentation: InstantiationInstrumentation,
}

fn egraph_node_count<N>(egraph: &EGraph<TermLanguage, N>) -> usize
where
    N: Analysis<TermLanguage>,
{
    egraph.classes().map(|class| class.nodes.len()).sum()
}

/// Shared matching, representative extraction and complete-instance scoring.
pub(crate) fn generate_quantified_candidates<CF, N>(
    egraph: &EGraph<TermLanguage, N>,
    cost_fn: CF,
    rules: &[CompiledQuantifiedRule<N>],
    options: InstantiationOptions,
    demand: Option<CandidateDemand<'_>>,
) -> anyhow::Result<InstantiationBatch>
where
    N: Analysis<TermLanguage> + 'static,
    CF: YardbirdCostFunction<TermLanguage> + 'static,
{
    let matched = crate::instantiation::search::search_array_rules(
        egraph,
        rules,
        &options.search_allowance,
        &options.instrumentation.profiling,
    );
    instantiate_quantified_matches(egraph, || cost_fn, rules, options, matched, demand, None)
}

/// Ground only matches that passed the caller's semantic eligibility check.
pub(crate) fn instantiate_quantified_matches<CF, N>(
    egraph: &EGraph<TermLanguage, N>,
    make_cost: impl FnOnce() -> CF,
    rules: &[CompiledQuantifiedRule<N>],
    options: InstantiationOptions,
    matched: crate::instantiation::search::MatchedRules,
    demand: Option<CandidateDemand<'_>>,
    needed_classes: Option<&std::collections::HashSet<Id>>,
) -> anyhow::Result<InstantiationBatch>
where
    N: Analysis<TermLanguage> + 'static,
    CF: YardbirdCostFunction<TermLanguage> + 'static,
{
    let InstantiationOptions {
        search_allowance: _,
        candidate_catalog,
        additional_terms,
        candidate_scope,
        refinement_step,
        selection_counts,
        depth,
        instrumentation,
    } = options;
    let InstantiationInstrumentation {
        artifact_capture,
        profiling,
    } = instrumentation;
    if let Some(profiling) = &profiling {
        profiling
            .borrow_mut()
            .set_egraph_before_rule_search(egraph.number_of_classes(), egraph_node_count(egraph));
    }
    if let Some(profiling) = &profiling {
        let mut profiling = profiling.borrow_mut();
        profiling.add_counter(
            "rule_search_substitutions_examined",
            matched.report.examined_substitutions as u64,
        );
        profiling.add_counter(
            "rule_search_continuations_available",
            matched.report.continuable_rules.len() as u64,
        );
        profiling.add_counter(
            "rule_search_budget_exhausted",
            matched.report.budget_exhausted_rules.len() as u64,
        );
    }
    if matched.matches.is_empty() {
        return Ok(InstantiationBatch {
            candidates: vec![],
            search: matched.report,
        });
    }
    let cost_fn = make_cost();
    let instantiation_cost_fn = cost_fn.clone();
    let extractor_start = Instant::now();
    let mut extractor = TermExtractor::for_eclasses(
        egraph,
        cost_fn,
        TermExtractorOptions {
            candidate_catalog,
            candidate_scope,
            refinement_step,
            selection_counts,
            depth,
            profiling: profiling.clone(),
        },
        needed_classes,
    );
    extractor.admit_terms_for_eclasses(egraph, &additional_terms, needed_classes);
    if let Some(profiling) = &profiling {
        profiling
            .borrow_mut()
            .record_timing("extractor_init", extractor_start.elapsed());
    }
    let mut instantiator = RuleInstantiator::new(
        instantiation_cost_fn,
        extractor,
        RuleInstantiatorOptions {
            refinement_step,
            depth,
            artifact_capture,
            profiling: profiling.clone(),
        },
    );
    let grounding_start = Instant::now();
    let search_rounds = matched.report.rounds;
    instantiator.instantiate_matches(egraph, rules, matched.matches, demand)?;
    if let Some(profiling) = &profiling {
        profiling
            .borrow_mut()
            .record_timing("rule_grounding_total", grounding_start.elapsed());
        profiling.borrow_mut().set_egraph_after_rule_search(
            egraph.number_of_classes(),
            egraph_node_count(egraph),
            search_rounds,
        );
    }

    let candidates = instantiator.into_candidates();

    #[cfg(debug_assertions)]
    {
        log::debug!("=== FINAL INSTANTIATIONS ===");
        for (index, candidate) in candidates.iter().enumerate() {
            log::debug!("  [{}] {}", index, candidate.expression);
        }
        log::debug!("============================\n");
    }

    Ok(InstantiationBatch {
        candidates,
        search: matched.report,
    })
}

#[derive(Clone, Copy)]
enum RuleGrouping {
    MatchRoot,
    Rule,
}

pub(crate) struct CompiledQuantifiedRule<N>
where
    N: Analysis<TermLanguage>,
{
    metadata: QuantifiedRule,
    searcher: Box<dyn Searcher<TermLanguage, N> + Send + Sync>,
    trigger: Option<TermPattern>,
    consequence: Option<TermPattern>,
    formula: TermPattern,
    formula_variables: Vec<Var>,
    /// Symbolic bindings supplied by a directed binder request. These remain
    /// literal terms in the formula rather than being chosen by extraction.
    fixed_bindings: Vec<(Var, TermExpr)>,
    binder_filters: Vec<(TermPattern, bool)>,
    uses_violation_plan: bool,
    grouping: RuleGrouping,
}

impl<N> CompiledQuantifiedRule<N>
where
    N: Analysis<TermLanguage>,
{
    pub(crate) fn new<S>(
        metadata: QuantifiedRule,
        searcher: S,
        consequence: Pattern<TermLanguage>,
        formula: Pattern<TermLanguage>,
    ) -> Result<Self, String>
    where
        S: Searcher<TermLanguage, N> + Send + Sync + 'static,
    {
        let trigger = searcher
            .get_pattern_ast()
            .cloned()
            .ok_or_else(|| format!("quantified rule {} has no trigger pattern", metadata.name()))?;
        let bound_variables = searcher.vars();
        for variable in consequence.vars().into_iter().chain(formula.vars()) {
            if !bound_variables.contains(&variable) {
                return Err(format!(
                    "quantified rule {} refers to unbound variable {variable}",
                    metadata.name()
                ));
            }
        }

        Ok(Self {
            metadata,
            searcher: Box::new(searcher),
            trigger: Some(trigger),
            consequence: Some(consequence.ast),
            formula_variables: formula.vars(),
            formula: formula.ast,
            fixed_bindings: vec![],
            binder_filters: vec![],
            uses_violation_plan: false,
            grouping: RuleGrouping::MatchRoot,
        })
    }

    /// Input binders use a typed multi-pattern join. Their arbitrary Boolean
    /// formulas are checked against the SMT model during batch preparation.
    pub(crate) fn input_binder(
        metadata: QuantifiedRule,
        searcher: MultiPattern<TermLanguage>,
        formula: Pattern<TermLanguage>,
        fixed_bindings: Vec<(Var, TermExpr)>,
    ) -> Self {
        let variables = <MultiPattern<TermLanguage> as Searcher<TermLanguage, N>>::vars(&searcher);
        assert!(formula.vars().iter().all(|var| variables.contains(var)));
        Self {
            metadata,
            searcher: Box::new(searcher),
            // All formula variables participate in ordinary term grounding.
            trigger: None,
            consequence: None,
            formula_variables: formula.vars(),
            formula: formula.ast,
            fixed_bindings,
            binder_filters: vec![],
            uses_violation_plan: false,
            grouping: RuleGrouping::Rule,
        }
    }

    pub(crate) fn group(&self, root: Id) -> crate::instantiation::candidate::CandidateGroup {
        use crate::instantiation::candidate::CandidateGroup;
        match self.grouping {
            RuleGrouping::MatchRoot => CandidateGroup::MatchRoot(root),
            RuleGrouping::Rule => CandidateGroup::Rule,
        }
    }

    pub(crate) fn with_binder_filters(
        mut self,
        filters: Vec<(TermPattern, bool)>,
        planned: bool,
    ) -> Self {
        self.binder_filters = filters;
        self.uses_violation_plan = planned;
        self
    }

    pub(crate) fn binder_filters(&self) -> &[(TermPattern, bool)] {
        &self.binder_filters
    }

    pub(crate) fn uses_violation_plan(&self) -> bool {
        self.uses_violation_plan
    }

    pub(crate) fn metadata(&self) -> &QuantifiedRule {
        &self.metadata
    }

    pub(crate) fn search_with_limit<'a>(
        &'a self,
        egraph: &EGraph<TermLanguage, N>,
        limit: usize,
    ) -> Vec<SearchMatches<'a, TermLanguage>> {
        if let Some((_, expression)) = self.fixed_bindings.first() {
            // The first multipattern clause binds this exact symbolic term.
            // Start at its class rather than scanning the graph for it.
            egraph
                .lookup_expr(expression)
                .and_then(|id| self.searcher.search_eclass_with_limit(egraph, id, limit))
                .into_iter()
                .collect()
        } else {
            self.searcher.search_with_limit(egraph, limit)
        }
    }

    pub(crate) fn fixed_bindings(&self) -> &[(Var, TermExpr)] {
        &self.fixed_bindings
    }

    pub(crate) fn is_direct_binder_instance(&self) -> bool {
        !self.fixed_bindings.is_empty() && self.formula_variables.is_empty()
    }

    pub(crate) fn trigger(&self) -> &TermPattern {
        self.trigger.as_ref().unwrap_or(&self.formula)
    }

    pub(crate) fn consequence(&self) -> Option<&TermPattern> {
        self.consequence.as_ref()
    }

    pub(crate) fn formula_variables(&self) -> &[Var] {
        &self.formula_variables
    }

    pub(crate) fn formula(&self) -> &TermPattern {
        &self.formula
    }
}
