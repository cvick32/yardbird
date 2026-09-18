//! Quantifier-specific compilation and model-violation filter metadata.
use crate::{
    rule_matching::{
        compiled_rule::{CompiledQuantifiedRule, RuleGrouping},
        rule::QuantifiedRule,
    },
    terms::language::{TermExpr, TermLanguage, TermPattern},
};
use egg::*;

#[derive(Default)]
pub(crate) struct BinderMatchPlan {
    filters: Vec<(TermPattern, bool)>,
    planned: bool,
}

pub(crate) type CompiledBinderRule<N> = CompiledQuantifiedRule<N, BinderMatchPlan>;

impl<N: Analysis<TermLanguage>> CompiledBinderRule<N> {
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
            details: BinderMatchPlan::default(),
            grouping: RuleGrouping::Rule,
        }
    }

    pub(crate) fn with_binder_filters(
        mut self,
        filters: Vec<(TermPattern, bool)>,
        planned: bool,
    ) -> Self {
        self.details.filters = filters;
        self.details.planned = planned;
        self
    }

    pub(crate) fn binder_filters(&self) -> &[(TermPattern, bool)] {
        &self.details.filters
    }

    pub(crate) fn uses_violation_plan(&self) -> bool {
        self.details.planned
    }

    pub(crate) fn is_direct_binder_instance(&self) -> bool {
        !self.fixed_bindings.is_empty() && self.formula_variables.is_empty()
    }
}
