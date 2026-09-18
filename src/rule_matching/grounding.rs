//! Shared substitutions and term grounding with theory-owned structural handling.
use crate::theories::array::grounding::{ground_expected_read, ground_expected_write};
use egg::Language;
use log::{debug, trace};

use crate::egg_utils::RecExprRoot;
use crate::policy::term_selection::YardbirdCostFunction;
use crate::rule_matching::candidate::SelectionHistoryDecision;
use crate::rule_matching::extractor::{CandidateOrigin, TermExtractor};
use crate::terms::language::{TermExpr, TermLanguage, TermPattern};
use crate::training::{canonical_term_hash, DecisionRecord};

fn trace_conflicts_enabled() -> bool {
    log::log_enabled!(log::Level::Trace)
}

fn trace_conflicts(message: impl AsRef<str>) {
    trace!("[yardbird::conflict-trace] {}", message.as_ref());
}

#[derive(Debug, Clone)]
pub(crate) struct GroundBinding {
    variable: egg::Var,
    eclass: egg::Id,
    pub(crate) expression: TermExpr,
    origin: CandidateOrigin,
}

#[derive(Default, Debug, Clone)]
pub(crate) struct GroundSubstitution {
    bindings: Vec<GroundBinding>,
    decisions: Vec<DecisionRecord>,
    selection_history: Vec<SelectionHistoryDecision>,
    pub(crate) used_derived_candidate: bool,
}

#[derive(Clone, Copy)]
pub(crate) struct GroundContext<'a> {
    record_decisions: bool,
    rule_name: &'a str,
    rule_category: crate::rule_matching::rule::QuantifiedRuleCategory,
}

impl<'a> GroundContext<'a> {
    pub(crate) fn new(
        record_decisions: bool,
        rule_name: &'a str,
        rule_category: crate::rule_matching::rule::QuantifiedRuleCategory,
    ) -> Self {
        Self {
            record_decisions,
            rule_name,
            rule_category,
        }
    }
}

impl GroundSubstitution {
    pub(crate) fn decisions(&self) -> &[DecisionRecord] {
        &self.decisions
    }

    pub(crate) fn selection_history(&self) -> &[SelectionHistoryDecision] {
        &self.selection_history
    }

    pub(crate) fn used_derived_candidate(&self) -> bool {
        self.used_derived_candidate
    }

    pub(crate) fn variable_expressions(&self) -> impl Iterator<Item = (egg::Var, &TermExpr)> {
        self.bindings
            .iter()
            .map(|binding| (binding.variable, &binding.expression))
    }

    // For binding an expression given from the extractor.
    fn bind_extracted<N, CF>(
        &mut self,
        variable: egg::Var,
        eclass: egg::Id,
        egraph: &egg::EGraph<TermLanguage, N>,
        extractor: &TermExtractor<CF>,
        context: GroundContext<'_>,
    ) -> anyhow::Result<()>
    where
        N: egg::Analysis<TermLanguage>,
        CF: YardbirdCostFunction<TermLanguage>,
    {
        let canonical_eclass = egraph.find(eclass);

        if let Some(existing) = self.get_binding(variable) {
            anyhow::ensure!(
                egraph.find(existing.eclass) == canonical_eclass,
                "Variable {variable} matched incompatible eclasses"
            );
            return Ok(());
        }

        let expression = extractor.extract_for_decision(
            egraph,
            canonical_eclass,
            context.rule_name,
            context.rule_category,
            variable,
        );

        debug!(
            "   extraction: {} -> {}",
            canonical_eclass,
            expression.pretty(80)
        );

        self.bind_choice(
            variable,
            canonical_eclass,
            expression,
            egraph,
            extractor,
            context,
        )
    }

    // For binding a particular choice we already have, be it from the extractor or elsewhere.
    fn bind_choice<N, CF>(
        &mut self,
        variable: egg::Var,
        eclass: egg::Id,
        expression: TermExpr,
        egraph: &egg::EGraph<TermLanguage, N>,
        extractor: &TermExtractor<CF>,
        context: GroundContext<'_>,
    ) -> anyhow::Result<()>
    where
        N: egg::Analysis<TermLanguage>,
        CF: YardbirdCostFunction<TermLanguage>,
    {
        let eclass = egraph.find(eclass); // why?

        if let Some(existing) = self.get_binding(variable) {
            anyhow::ensure!(
                egraph.find(existing.eclass) == eclass,
                "Variable {variable} matched incompatible eclasses"
            );
            return Ok(());
        }

        let origin = extractor.candidate_origin(egraph, eclass, &expression);
        self.bind_recorded_choice(variable, expression, egraph, extractor, context, origin)
    }

    pub(crate) fn bind_source_choice<N, CF>(
        &mut self,
        variable: egg::Var,
        expression: TermExpr,
        egraph: &egg::EGraph<TermLanguage, N>,
        extractor: &TermExtractor<CF>,
        context: GroundContext<'_>,
    ) -> anyhow::Result<()>
    where
        N: egg::Analysis<TermLanguage>,
        CF: YardbirdCostFunction<TermLanguage>,
    {
        let eclass = egraph
            .lookup_expr(&expression)
            .map(|eclass| egraph.find(eclass))
            .ok_or_else(|| anyhow::anyhow!("Source write choice is absent from the e-graph"))?;
        if let Some(existing) = self.get_binding(variable) {
            anyhow::ensure!(
                egraph.find(existing.eclass) == eclass,
                "Variable {variable} matched incompatible eclasses"
            );
            return Ok(());
        }
        self.bind_recorded_choice(
            variable,
            expression,
            egraph,
            extractor,
            context,
            CandidateOrigin::SourceGrounded,
        )
    }

    fn bind_recorded_choice<N, CF>(
        &mut self,
        variable: egg::Var,
        expression: TermExpr,
        egraph: &egg::EGraph<TermLanguage, N>,
        extractor: &TermExtractor<CF>,
        context: GroundContext<'_>,
        origin: CandidateOrigin,
    ) -> anyhow::Result<()>
    where
        N: egg::Analysis<TermLanguage>,
        CF: YardbirdCostFunction<TermLanguage>,
    {
        let eclass = egraph
            .lookup_expr(&expression)
            .map(|eclass| egraph.find(eclass))
            .ok_or_else(|| anyhow::anyhow!("Ground choice is absent from the e-graph"))?;

        let chosen_term_hash = canonical_term_hash(&expression);
        let decision_key = extractor.decision_key(context.rule_name, variable, eclass);

        if trace_conflicts_enabled() {
            trace_conflicts(format!(
                "   choice variable={variable} axiom={} eclass={eclass} expr={expression}",
                context.rule_name,
            ));
        }

        self.selection_history.push(SelectionHistoryDecision {
            decision_key: decision_key.clone(),
            chosen_term_hash,
        });

        if context.record_decisions {
            self.decisions.push(extractor.decision_record(
                egraph,
                eclass,
                context.rule_name,
                variable,
                &expression,
                decision_key,
            ));
        }

        self.bind(GroundBinding {
            variable,
            eclass,
            expression,
            origin,
        })
    }

    fn bind(&mut self, binding: GroundBinding) -> anyhow::Result<()> {
        if let Some(existing) = self
            .bindings
            .iter()
            .find(|existing| existing.variable == binding.variable)
        {
            anyhow::ensure!(
                existing.eclass == binding.eclass
                    && existing.expression == binding.expression
                    && existing.origin == binding.origin,
                "Conflicting binding for {}",
                binding.variable
            );
            return Ok(());
        }
        self.used_derived_candidate |= binding.origin == CandidateOrigin::Derived;
        self.bindings.push(binding);
        Ok(())
    }

    pub(crate) fn get_binding(&self, var: egg::Var) -> Option<&GroundBinding> {
        self.bindings.iter().find(|binding| binding.variable == var)
    }
}

pub(crate) fn ground_pattern_variables<N, CF>(
    pattern: &TermPattern,
    subst: &egg::Subst,
    grounding: &mut GroundSubstitution,
    egraph: &egg::EGraph<TermLanguage, N>,
    extractor: &TermExtractor<CF>,
    context: GroundContext<'_>,
) -> anyhow::Result<()>
where
    N: egg::Analysis<TermLanguage>,
    CF: YardbirdCostFunction<TermLanguage>,
{
    for node in pattern.as_ref() {
        let egg::ENodeOrVar::Var(variable) = node else {
            continue;
        };

        let eclass = subst.get(*variable).copied().ok_or_else(|| {
            anyhow::anyhow!("Pattern variable {variable} is missing from the egg substitution")
        })?;

        grounding.bind_extracted(*variable, eclass, egraph, extractor, context)?;
    }

    Ok(())
}

/// The existing best grounding first, followed by intact source-write sites.
/// Scalar representatives are still chosen by the existing extractor. Alternative
/// bindings and their decision records are only constructed when requested.
pub(crate) fn groundings<'a, N, CF>(
    pattern: &'a TermPattern,
    expected_eclass: egg::Id,
    subst: egg::Subst,
    egraph: &'a egg::EGraph<TermLanguage, N>,
    extractor: std::rc::Rc<TermExtractor<CF>>,
    context: GroundContext<'a>,
) -> impl Iterator<Item = GroundSubstitution> + 'a
where
    N: egg::Analysis<TermLanguage> + 'a,
    CF: YardbirdCostFunction<TermLanguage> + 'a,
{
    let mut first = true;
    let mut alternatives = None;
    let mut seen = std::collections::HashSet::new();
    std::iter::from_fn(move || {
        if first {
            first = false;
            let mut grounding = GroundSubstitution::default();
            ground_pattern(
                pattern,
                Some(expected_eclass),
                &subst,
                &mut grounding,
                egraph,
                &extractor,
                context,
            )
            .expect("egg search must bind every trigger variable");
            seen.insert(
                instantiate_pattern(pattern, &grounding)
                    .unwrap()
                    .to_string(),
            );
            return Some(grounding);
        }
        alternatives
            .get_or_insert_with(|| {
                crate::theories::array::grounding::source_write_groundings(
                    pattern,
                    expected_eclass,
                    subst.clone(),
                    egraph,
                    extractor.clone(),
                    context,
                    seen.clone(),
                )
            })
            .next()
    })
}

pub(crate) fn choose_best_grounding<CF, C, I, F>(
    extractor: &TermExtractor<CF>,
    grounding: &mut GroundSubstitution,
    candidates: I,
    mut build_expression: F,
) -> anyhow::Result<bool>
where
    CF: YardbirdCostFunction<TermLanguage>,
    I: IntoIterator<Item = C>,
    F: FnMut(C, &mut GroundSubstitution) -> anyhow::Result<TermExpr>,
{
    let mut best: Option<(u32, String, GroundSubstitution)> = None;

    for candidate in candidates {
        let mut candidate_grounding = grounding.clone();
        let expression = build_expression(candidate, &mut candidate_grounding)?;
        let cost = extractor.cost_of(&expression);
        let rendered = expression.to_string();
        let should_replace = best.as_ref().is_none_or(|(best_cost, best_rendered, _)| {
            (cost, rendered.as_str()) < (*best_cost, best_rendered.as_str())
        });

        if should_replace {
            best = Some((cost, rendered, candidate_grounding));
        }
    }
    let Some((_, _, chosen_grounding)) = best else {
        return Ok(false);
    };

    *grounding = chosen_grounding;
    Ok(true)
}

pub(crate) fn ground_pattern<N, CF>(
    pattern: &TermPattern,
    expected_eclass: Option<egg::Id>,
    subst: &egg::Subst,
    grounding: &mut GroundSubstitution,
    egraph: &egg::EGraph<TermLanguage, N>,
    extractor: &TermExtractor<CF>,
    context: GroundContext<'_>,
) -> anyhow::Result<()>
where
    N: egg::Analysis<TermLanguage>,
    CF: YardbirdCostFunction<TermLanguage>,
{
    if let Some(expected_eclass) = expected_eclass {
        if ground_expected_write(
            pattern,
            expected_eclass,
            subst,
            grounding,
            egraph,
            extractor,
            context,
        )? {
            return Ok(());
        }
        if ground_expected_read(
            pattern,
            expected_eclass,
            subst,
            grounding,
            egraph,
            extractor,
            context,
        )? {
            return Ok(());
        }
        if let [egg::ENodeOrVar::Var(variable)] = pattern.as_ref() {
            return grounding.bind_extracted(
                *variable,
                expected_eclass,
                egraph,
                extractor,
                context,
            );
        }
    }

    ground_pattern_variables(pattern, subst, grounding, egraph, extractor, context)
}

pub(crate) fn bind_exact_variable<N, CF>(
    pattern: &TermPattern,
    eclass: egg::Id,
    expression: &TermExpr,
    grounding: &mut GroundSubstitution,
    egraph: &egg::EGraph<TermLanguage, N>,
    extractor: &TermExtractor<CF>,
    context: GroundContext<'_>,
) -> anyhow::Result<bool>
where
    N: egg::Analysis<TermLanguage>,
    CF: YardbirdCostFunction<TermLanguage>,
{
    let [egg::ENodeOrVar::Var(variable)] = pattern.as_ref() else {
        return Ok(false);
    };

    grounding.bind_choice(
        *variable,
        eclass,
        expression.clone(),
        egraph,
        extractor,
        context,
    )?;

    Ok(true)
}

pub(crate) fn bind_exact_source_variable<N, CF>(
    pattern: &TermPattern,
    expression: &TermExpr,
    grounding: &mut GroundSubstitution,
    egraph: &egg::EGraph<TermLanguage, N>,
    extractor: &TermExtractor<CF>,
    context: GroundContext<'_>,
) -> anyhow::Result<bool>
where
    N: egg::Analysis<TermLanguage>,
    CF: YardbirdCostFunction<TermLanguage>,
{
    let [egg::ENodeOrVar::Var(variable)] = pattern.as_ref() else {
        return Ok(false);
    };

    grounding.bind_source_choice(*variable, expression.clone(), egraph, extractor, context)?;

    Ok(true)
}

// Have to remap the IDs out the output expr to account for the IDs of the input expr.
fn append_expr(output: &mut TermExpr, input: &TermExpr) -> anyhow::Result<egg::Id> {
    let mut roots = Vec::<egg::Id>::with_capacity(input.as_ref().len());

    for node in input.as_ref() {
        let node = node.clone().map_children(|child| roots[usize::from(child)]);
        roots.push(output.add(node));
    }

    roots
        .last()
        .copied()
        .ok_or_else(|| anyhow::anyhow!("Cannot append to an empty expression"))
}

pub(crate) fn instantiate_pattern(
    pattern: &TermPattern,
    substitution: &GroundSubstitution,
) -> anyhow::Result<TermExpr> {
    instantiate_with_bindings(pattern, |var| {
        substitution
            .get_binding(var)
            .map(|binding| &binding.expression)
            .ok_or_else(|| anyhow::anyhow!("Missing binding for {var}"))
    })
}

/// Substitute a fixed rule formula without choosing or scoring representatives.
pub(crate) fn instantiate_with_bindings<'a>(
    pattern: &TermPattern,
    mut binding: impl FnMut(egg::Var) -> anyhow::Result<&'a TermExpr>,
) -> anyhow::Result<TermExpr> {
    let mut result_expression = TermExpr::default();
    let mut roots = Vec::<egg::Id>::with_capacity(pattern.as_ref().len());

    for node in pattern.as_ref() {
        let root = match node {
            egg::ENodeOrVar::ENode(node) => {
                let node = node.clone().map_children(|child| roots[usize::from(child)]);
                result_expression.add(node)
            }
            egg::ENodeOrVar::Var(var) => append_expr(&mut result_expression, binding(*var)?)?,
        };
        roots.push(root);
    }

    anyhow::ensure!(!roots.is_empty(), "Cannot instantiate empty pattern");
    Ok(result_expression)
}

pub(crate) fn subpattern(
    pattern: &egg::PatternAst<TermLanguage>,
    root: egg::Id,
) -> egg::PatternAst<TermLanguage> {
    let node = pattern[root].clone();
    if node.is_leaf() {
        vec![node].into()
    } else {
        node.build_recexpr(|id| pattern[id].clone())
    }
}

pub(crate) fn pattern_sort_symbol(
    pattern: &egg::PatternAst<TermLanguage>,
    id: egg::Id,
) -> Option<String> {
    match &pattern[id] {
        egg::ENodeOrVar::ENode(TermLanguage::Symbol(symbol)) => Some(symbol.to_string()),
        _ => None,
    }
}

pub(crate) fn egraph_contains_at<N>(
    egraph: &egg::EGraph<TermLanguage, N>,
    expr: &TermExpr,
    expected_eclass: egg::Id,
) -> bool
where
    N: egg::Analysis<TermLanguage>,
{
    egraph
        .lookup_expr(expr)
        .is_some_and(|actual| egraph.find(actual) == egraph.find(expected_eclass))
}

pub(crate) fn child_patterns_compatible<const N_CHILDREN: usize, N>(
    egraph: &egg::EGraph<TermLanguage, N>,
    subst: &egg::Subst,
    patterns: [&egg::PatternAst<TermLanguage>; N_CHILDREN],
    candidate_eclasses: [egg::Id; N_CHILDREN],
) -> bool
where
    N: egg::Analysis<TermLanguage>,
{
    patterns
        .into_iter()
        .zip(candidate_eclasses)
        .all(|(pattern, candidate_eclass)| {
            pattern_matches_eclass(pattern, candidate_eclass, egraph, subst)
        })
}

fn pattern_matches_eclass<N>(
    pattern: &egg::PatternAst<TermLanguage>,
    candidate_eclass: egg::Id,
    egraph: &egg::EGraph<TermLanguage, N>,
    subst: &egg::Subst,
) -> bool
where
    N: egg::Analysis<TermLanguage>,
{
    match pattern.rooted() {
        egg::ENodeOrVar::Var(var) => {
            egraph.find(candidate_eclass) == egraph.find(*subst.get(*var).unwrap())
        }
        egg::ENodeOrVar::ENode(pattern_node) => egraph[candidate_eclass].nodes.iter().any(|node| {
            pattern_node.matches(node)
                && pattern_node.children().iter().zip(node.children()).all(
                    |(pattern_child, candidate_child)| {
                        pattern_matches_eclass(
                            &subpattern(pattern, *pattern_child),
                            *candidate_child,
                            egraph,
                            subst,
                        )
                    },
                )
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        problem_context::ArrayCandidateCatalog,
        rule_matching::{extractor::TermExtractorOptions, scope::CandidateScope},
    };
    use rustc_hash::FxHashMap;
    use smt2parser::vmt::ReadsAndWrites;
    #[derive(Clone)]
    struct ZeroCost;

    impl egg::CostFunction<TermLanguage> for ZeroCost {
        type Cost = u32;

        fn cost<C>(&mut self, _enode: &TermLanguage, _costs: C) -> Self::Cost
        where
            C: FnMut(egg::Id) -> Self::Cost,
        {
            0
        }
    }

    impl YardbirdCostFunction<TermLanguage> for ZeroCost {
        fn get_string_terms(&self) -> Vec<String> {
            vec![]
        }

        fn get_reads_and_writes(&self) -> ReadsAndWrites {
            ReadsAndWrites::default()
        }
    }

    #[test]
    fn instantiates_multiple_and_repeated_variables() {
        let pattern: TermPattern = "(= (+ ?x ?y) (+ ?x ?y))".parse().unwrap();
        let x: egg::Var = "?x".parse().unwrap();
        let y: egg::Var = "?y".parse().unwrap();

        let mut grounding = GroundSubstitution::default();
        grounding
            .bind(GroundBinding {
                variable: x,
                eclass: egg::Id::from(0),
                expression: "a".parse().unwrap(),
                origin: CandidateOrigin::SourceGrounded,
            })
            .unwrap();
        grounding
            .bind(GroundBinding {
                variable: y,
                eclass: egg::Id::from(1),
                expression: "b".parse().unwrap(),
                origin: CandidateOrigin::SourceGrounded,
            })
            .unwrap();

        let instantiated = instantiate_pattern(&pattern, &grounding).unwrap();

        assert_eq!(instantiated.to_string(), "(= (+ a b) (+ a b))");
    }

    #[test]
    fn grounds_each_variable_once_from_egg_substitution() {
        let pattern: TermPattern = "(= (+ ?x ?y) (+ ?x ?y))".parse().unwrap();
        let x: egg::Var = "?x".parse().unwrap();
        let y: egg::Var = "?y".parse().unwrap();

        let mut egraph = egg::EGraph::<TermLanguage, ()>::default();
        let a: TermExpr = "a".parse().unwrap();
        let b: TermExpr = "b".parse().unwrap();
        let a_eclass = egraph.add_expr(&a);
        let b_eclass = egraph.add_expr(&b);
        egraph.rebuild();

        let mut subst = egg::Subst::default();
        subst.insert(x, a_eclass);
        subst.insert(y, b_eclass);

        let extractor = TermExtractor::new(
            &egraph,
            ZeroCost,
            TermExtractorOptions {
                candidate_catalog: ArrayCandidateCatalog::default(),
                candidate_scope: CandidateScope::AllCandidates,
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                profiling: None,
            },
        );

        let mut grounding = GroundSubstitution::default();
        ground_pattern_variables(
            &pattern,
            &subst,
            &mut grounding,
            &egraph,
            &extractor,
            GroundContext {
                record_decisions: false,
                rule_name: "test-rule",
                rule_category: crate::rule_matching::rule::QuantifiedRuleCategory::InputBinder,
            },
        )
        .unwrap();

        assert_eq!(grounding.bindings.len(), 2);
        assert_eq!(grounding.selection_history.len(), 2);
        assert!(grounding.decisions.is_empty());

        assert_eq!(
            grounding.get_binding(x).unwrap().expression.to_string(),
            "a"
        );
        assert_eq!(
            grounding.get_binding(y).unwrap().expression.to_string(),
            "b"
        );
    }
}
