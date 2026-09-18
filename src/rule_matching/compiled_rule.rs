//! Executable rule representation shared by theory searches.
use crate::rule_matching::rule::QuantifiedRule;
use crate::terms::language::{TermExpr, TermLanguage, TermPattern};
use egg::*;

#[derive(Clone, Copy)]
pub(crate) enum RuleGrouping {
    MatchRoot,
    Rule,
}

/// Theory annotations travel with the rule; shared matching never inspects them.
pub(crate) struct CompiledQuantifiedRule<N, M = ()>
where
    N: Analysis<TermLanguage>,
{
    pub(crate) metadata: QuantifiedRule,
    pub(crate) searcher: Box<dyn Searcher<TermLanguage, N> + Send + Sync>,
    pub(crate) trigger: Option<TermPattern>,
    pub(crate) consequence: Option<TermPattern>,
    pub(crate) formula: TermPattern,
    pub(crate) formula_variables: Vec<Var>,
    /// Symbolic bindings supplied by a directed binder request. These remain
    /// literal terms in the formula rather than being chosen by extraction.
    pub(crate) fixed_bindings: Vec<(Var, TermExpr)>,
    pub(crate) details: M,
    pub(crate) grouping: RuleGrouping,
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
            details: (),
            grouping: RuleGrouping::MatchRoot,
        })
    }
}

impl<N: Analysis<TermLanguage>, M> CompiledQuantifiedRule<N, M> {
    pub(crate) fn group(&self, root: Id) -> crate::rule_matching::candidate::CandidateGroup {
        use crate::rule_matching::candidate::CandidateGroup;
        match self.grouping {
            RuleGrouping::MatchRoot => CandidateGroup::MatchRoot(root),
            RuleGrouping::Rule => CandidateGroup::Rule,
        }
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
