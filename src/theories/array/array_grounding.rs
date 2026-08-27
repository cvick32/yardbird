use egg::Language;
use log::{debug, trace};

use crate::{
    cost_functions::YardbirdCostFunction,
    egg_utils::RecExprRoot,
    theories::array::{
        array_axioms::{ArrayExpr, ArrayLanguage, ArrayPattern},
        array_term_extractor::{ArrayTermExtractor, CandidateOrigin},
        instantiation_candidate::SelectionHistoryDecision,
    },
    training::{canonical_term_hash, DecisionRecord},
};

fn trace_conflicts_enabled() -> bool {
    log::log_enabled!(log::Level::Trace)
}

fn trace_conflicts(message: impl AsRef<str>) {
    trace!("[yardbird::conflict-trace] {}", message.as_ref());
}

#[derive(Debug, Clone)]
struct GroundBinding {
    variable: egg::Var,
    eclass: egg::Id,
    expression: ArrayExpr,
    origin: CandidateOrigin,
}

#[derive(Default, Debug, Clone)]
pub(super) struct GroundSubstitution {
    bindings: Vec<GroundBinding>,
    decisions: Vec<DecisionRecord>,
    selection_history: Vec<SelectionHistoryDecision>,
    used_derived_candidate: bool,
}

#[derive(Clone, Copy)]
pub(super) struct GroundContext<'a> {
    record_decisions: bool,
    rule_name: &'a str,
    rule_category: crate::quantified_rule::QuantifiedRuleCategory,
}

impl<'a> GroundContext<'a> {
    pub(super) fn new(
        record_decisions: bool,
        rule_name: &'a str,
        rule_category: crate::quantified_rule::QuantifiedRuleCategory,
    ) -> Self {
        Self {
            record_decisions,
            rule_name,
            rule_category,
        }
    }
}

impl GroundSubstitution {
    pub(super) fn decisions(&self) -> &[DecisionRecord] {
        &self.decisions
    }

    pub(super) fn selection_history(&self) -> &[SelectionHistoryDecision] {
        &self.selection_history
    }

    pub(super) fn used_derived_candidate(&self) -> bool {
        self.used_derived_candidate
    }

    pub(super) fn variable_expressions(&self) -> impl Iterator<Item = (egg::Var, &ArrayExpr)> {
        self.bindings
            .iter()
            .map(|binding| (binding.variable, &binding.expression))
    }

    // For binding an expression given from the extractor.
    fn bind_extracted<N, CF>(
        &mut self,
        variable: egg::Var,
        eclass: egg::Id,
        egraph: &egg::EGraph<ArrayLanguage, N>,
        extractor: &ArrayTermExtractor<CF>,
        context: GroundContext<'_>,
    ) -> anyhow::Result<()>
    where
        N: egg::Analysis<ArrayLanguage>,
        CF: YardbirdCostFunction<ArrayLanguage>,
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
        expression: ArrayExpr,
        egraph: &egg::EGraph<ArrayLanguage, N>,
        extractor: &ArrayTermExtractor<CF>,
        context: GroundContext<'_>,
    ) -> anyhow::Result<()>
    where
        N: egg::Analysis<ArrayLanguage>,
        CF: YardbirdCostFunction<ArrayLanguage>,
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

    fn get_binding(&self, var: egg::Var) -> Option<&GroundBinding> {
        self.bindings.iter().find(|binding| binding.variable == var)
    }
}

fn ground_pattern_variables<N, CF>(
    pattern: &ArrayPattern,
    subst: &egg::Subst,
    grounding: &mut GroundSubstitution,
    egraph: &egg::EGraph<ArrayLanguage, N>,
    extractor: &ArrayTermExtractor<CF>,
    context: GroundContext<'_>,
) -> anyhow::Result<()>
where
    N: egg::Analysis<ArrayLanguage>,
    CF: YardbirdCostFunction<ArrayLanguage>,
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

fn choose_best_grounding<CF, C, I, F>(
    extractor: &ArrayTermExtractor<CF>,
    grounding: &mut GroundSubstitution,
    candidates: I,
    mut build_expression: F,
) -> anyhow::Result<bool>
where
    CF: YardbirdCostFunction<ArrayLanguage>,
    I: IntoIterator<Item = C>,
    F: FnMut(C, &mut GroundSubstitution) -> anyhow::Result<ArrayExpr>,
{
    let mut best: Option<(u32, bool, String, GroundSubstitution)> = None;

    for candidate in candidates {
        let mut candidate_grounding = grounding.clone();
        let expression = build_expression(candidate, &mut candidate_grounding)?;
        let cost = extractor.cost_of(&expression);
        let rendered = expression.to_string();
        let candidate_is_derived = candidate_grounding.used_derived_candidate;

        let should_replace =
            best.as_ref()
                .is_none_or(|(best_cost, best_is_derived, best_rendered, _)| {
                    if extractor.prefers_source_on_cost_tie() {
                        (cost, candidate_is_derived, rendered.as_str())
                            < (*best_cost, *best_is_derived, best_rendered.as_str())
                    } else {
                        (cost, rendered.as_str()) < (*best_cost, best_rendered.as_str())
                    }
                });

        if should_replace {
            best = Some((cost, candidate_is_derived, rendered, candidate_grounding));
        }
    }
    let Some((_, _, _, chosen_grounding)) = best else {
        return Ok(false);
    };

    *grounding = chosen_grounding;
    Ok(true)
}

pub(super) fn ground_pattern<N, CF>(
    pattern: &ArrayPattern,
    expected_eclass: Option<egg::Id>,
    subst: &egg::Subst,
    grounding: &mut GroundSubstitution,
    egraph: &egg::EGraph<ArrayLanguage, N>,
    extractor: &ArrayTermExtractor<CF>,
    context: GroundContext<'_>,
) -> anyhow::Result<()>
where
    N: egg::Analysis<ArrayLanguage>,
    CF: YardbirdCostFunction<ArrayLanguage>,
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

fn ground_expected_write<N, CF>(
    pattern: &ArrayPattern,
    expected_eclass: egg::Id,
    subst: &egg::Subst,
    grounding: &mut GroundSubstitution,
    egraph: &egg::EGraph<ArrayLanguage, N>,
    extractor: &ArrayTermExtractor<CF>,
    context: GroundContext<'_>,
) -> anyhow::Result<bool>
where
    N: egg::Analysis<ArrayLanguage>,
    CF: YardbirdCostFunction<ArrayLanguage>,
{
    let egg::ENodeOrVar::ENode(ArrayLanguage::WriteTyped(
        [index_sort, value_sort, array, index, value],
    )) = pattern.rooted().clone()
    else {
        return Ok(false);
    };

    let index_sort = pattern_sort_symbol(pattern, index_sort)
        .ok_or_else(|| anyhow::anyhow!("Write pattern is missing its index sort"))?;
    let value_sort = pattern_sort_symbol(pattern, value_sort)
        .ok_or_else(|| anyhow::anyhow!("Write pattern is missing its value sort"))?;
    let array_pattern = subpattern(pattern, array);
    let index_pattern = subpattern(pattern, index);
    let value_pattern = subpattern(pattern, value);
    let expected_eclass = egraph.find(expected_eclass);

    let candidates = egraph[expected_eclass].nodes.iter().filter_map(|node| {
        let ArrayLanguage::WriteTyped([_, _, array_eclass, index_eclass, value_eclass]) = node
        else {
            return None;
        };

        child_patterns_compatible(
            egraph,
            subst,
            [&array_pattern, &index_pattern, &value_pattern],
            [*array_eclass, *index_eclass, *value_eclass],
        )
        .then_some((*array_eclass, *index_eclass, *value_eclass))
    });

    choose_best_grounding(
        extractor,
        grounding,
        candidates,
        |(array_eclass, index_eclass, value_eclass), candidate_grounding| {
            ground_pattern(
                &array_pattern,
                Some(array_eclass),
                subst,
                candidate_grounding,
                egraph,
                extractor,
                context,
            )?;
            let array_expression = instantiate_pattern(&array_pattern, candidate_grounding)?;
            let exact_children = best_matching_write_children(
                egraph,
                extractor,
                &array_expression,
                &index_sort,
                &value_sort,
                index_eclass,
                value_eclass,
            );

            if let Some((index_expression, value_expression)) = exact_children.as_ref() {
                if !bind_exact_variable(
                    &index_pattern,
                    index_eclass,
                    index_expression,
                    candidate_grounding,
                    egraph,
                    extractor,
                    context,
                )? {
                    ground_pattern(
                        &index_pattern,
                        Some(index_eclass),
                        subst,
                        candidate_grounding,
                        egraph,
                        extractor,
                        context,
                    )?;
                }
                if !bind_exact_variable(
                    &value_pattern,
                    value_eclass,
                    value_expression,
                    candidate_grounding,
                    egraph,
                    extractor,
                    context,
                )? {
                    ground_pattern(
                        &value_pattern,
                        Some(value_eclass),
                        subst,
                        candidate_grounding,
                        egraph,
                        extractor,
                        context,
                    )?;
                }
            } else {
                ground_pattern(
                    &index_pattern,
                    Some(index_eclass),
                    subst,
                    candidate_grounding,
                    egraph,
                    extractor,
                    context,
                )?;
                ground_pattern(
                    &value_pattern,
                    Some(value_eclass),
                    subst,
                    candidate_grounding,
                    egraph,
                    extractor,
                    context,
                )?;
            }

            ground_pattern_variables(
                pattern,
                subst,
                candidate_grounding,
                egraph,
                extractor,
                context,
            )?;

            let write = instantiate_pattern(pattern, candidate_grounding)?;
            if !extractor.is_source_write(&write) {
                candidate_grounding.used_derived_candidate = true;
            }
            Ok(write)
        },
    )
}

fn ground_expected_read<N, CF>(
    pattern: &ArrayPattern,
    expected_eclass: egg::Id,
    subst: &egg::Subst,
    grounding: &mut GroundSubstitution,
    egraph: &egg::EGraph<ArrayLanguage, N>,
    extractor: &ArrayTermExtractor<CF>,
    context: GroundContext<'_>,
) -> anyhow::Result<bool>
where
    N: egg::Analysis<ArrayLanguage>,
    CF: YardbirdCostFunction<ArrayLanguage>,
{
    let egg::ENodeOrVar::ENode(ArrayLanguage::ReadTyped([_, _, array, index])) =
        pattern.rooted().clone()
    else {
        return Ok(false);
    };

    let array_pattern = subpattern(pattern, array);
    let index_pattern = subpattern(pattern, index);
    let expected_eclass = egraph.find(expected_eclass);

    let candidates = egraph[expected_eclass].nodes.iter().filter_map(|node| {
        let ArrayLanguage::ReadTyped([_, _, array_eclass, index_eclass]) = node else {
            return None;
        };

        child_patterns_compatible(
            egraph,
            subst,
            [&array_pattern, &index_pattern],
            [*array_eclass, *index_eclass],
        )
        .then_some((*array_eclass, *index_eclass))
    });

    choose_best_grounding(
        extractor,
        grounding,
        candidates,
        |(array_eclass, index_eclass), candidate_grounding| {
            ground_pattern(
                &array_pattern,
                Some(array_eclass),
                subst,
                candidate_grounding,
                egraph,
                extractor,
                context,
            )?;
            ground_pattern(
                &index_pattern,
                Some(index_eclass),
                subst,
                candidate_grounding,
                egraph,
                extractor,
                context,
            )?;

            ground_pattern_variables(
                pattern,
                subst,
                candidate_grounding,
                egraph,
                extractor,
                context,
            )?;

            instantiate_pattern(pattern, candidate_grounding)
        },
    )
}

fn bind_exact_variable<N, CF>(
    pattern: &ArrayPattern,
    eclass: egg::Id,
    expression: &ArrayExpr,
    grounding: &mut GroundSubstitution,
    egraph: &egg::EGraph<ArrayLanguage, N>,
    extractor: &ArrayTermExtractor<CF>,
    context: GroundContext<'_>,
) -> anyhow::Result<bool>
where
    N: egg::Analysis<ArrayLanguage>,
    CF: YardbirdCostFunction<ArrayLanguage>,
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

// Have to remap the IDs out the output expr to account for the IDs of the input expr.
fn append_expr(output: &mut ArrayExpr, input: &ArrayExpr) -> anyhow::Result<egg::Id> {
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

pub(super) fn instantiate_pattern(
    pattern: &ArrayPattern,
    substitution: &GroundSubstitution,
) -> anyhow::Result<ArrayExpr> {
    let mut result_expression = ArrayExpr::default();
    let mut roots = Vec::<egg::Id>::with_capacity(pattern.as_ref().len());

    for node in pattern.as_ref() {
        let root = match node {
            egg::ENodeOrVar::ENode(node) => {
                let node = node.clone().map_children(|child| roots[usize::from(child)]);
                result_expression.add(node)
            }
            egg::ENodeOrVar::Var(var) => {
                let binding = substitution.get_binding(*var).ok_or_else(|| {
                    anyhow::anyhow!("Missing binding for {} in {:#?}", var, substitution)
                })?;
                append_expr(&mut result_expression, &binding.expression)?
            }
        };
        roots.push(root);
    }

    anyhow::ensure!(!roots.is_empty(), "Cannot instantiate empty pattern");
    Ok(result_expression)
}

fn subpattern(
    pattern: &egg::PatternAst<ArrayLanguage>,
    root: egg::Id,
) -> egg::PatternAst<ArrayLanguage> {
    let node = pattern[root].clone();
    if node.is_leaf() {
        vec![node].into()
    } else {
        node.build_recexpr(|id| pattern[id].clone())
    }
}

fn pattern_sort_symbol(pattern: &egg::PatternAst<ArrayLanguage>, id: egg::Id) -> Option<String> {
    match &pattern[id] {
        egg::ENodeOrVar::ENode(ArrayLanguage::Symbol(symbol)) => Some(symbol.to_string()),
        _ => None,
    }
}

fn best_matching_write_children<N, CF>(
    egraph: &egg::EGraph<ArrayLanguage, N>,
    extractor: &ArrayTermExtractor<CF>,
    array_expr: &ArrayExpr,
    index_sort: &str,
    value_sort: &str,
    index_eclass: egg::Id,
    value_eclass: egg::Id,
) -> Option<(ArrayExpr, ArrayExpr)>
where
    N: egg::Analysis<ArrayLanguage>,
    CF: YardbirdCostFunction<ArrayLanguage>,
{
    let index_eclass = egraph.find(index_eclass);
    let value_eclass = egraph.find(value_eclass);
    if let Some(cached) = extractor.cached_matching_write(
        array_expr,
        index_sort,
        value_sort,
        index_eclass,
        value_eclass,
    ) {
        return cached;
    }

    let best_in_pool = |candidates: &[(ArrayExpr, ArrayExpr)]| {
        let mut best: Option<(u32, String, ArrayExpr, ArrayExpr)> = None;
        for (index_expr, value_expr) in candidates {
            if !egraph_contains_at(egraph, index_expr, index_eclass) {
                continue;
            }
            if !egraph_contains_at(egraph, value_expr, value_eclass) {
                continue;
            }

            let write_expr = ArrayLanguage::write_typed(
                index_sort,
                value_sort,
                array_expr.clone(),
                index_expr.clone(),
                value_expr.clone(),
            );
            let cost = extractor.cost_of_at("best_matching_write_child", &write_expr);
            let rendered = write_expr.to_string();
            let should_replace = best
                .as_ref()
                .is_none_or(|(best_cost, best_rendered, _, _)| {
                    (cost, rendered.as_str()) < (*best_cost, best_rendered.as_str())
                });
            if should_replace {
                best = Some((cost, rendered, index_expr.clone(), value_expr.clone()));
            }
        }
        best
    };

    let best = if extractor.prefers_source_on_cost_tie() {
        best_in_pool(extractor.source_write_candidates(array_expr))
    } else {
        best_in_pool(extractor.all_write_candidates(array_expr))
    };
    let result = best.map(|(_, _, index_expr, value_expr)| (index_expr, value_expr));
    extractor.cache_matching_write(
        array_expr,
        index_sort,
        value_sort,
        index_eclass,
        value_eclass,
        result.clone(),
    );
    result
}

fn egraph_contains_at<N>(
    egraph: &egg::EGraph<ArrayLanguage, N>,
    expr: &ArrayExpr,
    expected_eclass: egg::Id,
) -> bool
where
    N: egg::Analysis<ArrayLanguage>,
{
    egraph
        .lookup_expr(expr)
        .is_some_and(|actual| egraph.find(actual) == egraph.find(expected_eclass))
}

fn child_patterns_compatible<const N_CHILDREN: usize, N>(
    egraph: &egg::EGraph<ArrayLanguage, N>,
    subst: &egg::Subst,
    patterns: [&egg::PatternAst<ArrayLanguage>; N_CHILDREN],
    candidate_eclasses: [egg::Id; N_CHILDREN],
) -> bool
where
    N: egg::Analysis<ArrayLanguage>,
{
    patterns
        .into_iter()
        .zip(candidate_eclasses)
        .all(|(pattern, candidate_eclass)| {
            pattern_matches_eclass(pattern, candidate_eclass, egraph, subst)
        })
}

fn pattern_matches_eclass<N>(
    pattern: &egg::PatternAst<ArrayLanguage>,
    candidate_eclass: egg::Id,
    egraph: &egg::EGraph<ArrayLanguage, N>,
    subst: &egg::Subst,
) -> bool
where
    N: egg::Analysis<ArrayLanguage>,
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
mod test {
    use rustc_hash::FxHashMap;
    use smt2parser::vmt::ReadsAndWrites;

    use crate::{
        problem_context::{ArrayCandidateCatalog, ArrayCandidatePool},
        theories::array::{
            array_axioms::{ArrayLanguage, ArrayPattern},
            array_grounding::*,
            array_term_extractor::ArrayTermExtractorOptions,
            candidate_scope::CandidateScope,
        },
    };

    #[derive(Clone)]
    struct ZeroCost;

    impl egg::CostFunction<ArrayLanguage> for ZeroCost {
        type Cost = u32;

        fn cost<C>(&mut self, _enode: &ArrayLanguage, _costs: C) -> Self::Cost
        where
            C: FnMut(egg::Id) -> Self::Cost,
        {
            0
        }
    }

    impl YardbirdCostFunction<ArrayLanguage> for ZeroCost {
        fn get_string_terms(&self) -> Vec<String> {
            vec![]
        }

        fn get_reads_and_writes(&self) -> ReadsAndWrites {
            ReadsAndWrites::default()
        }
    }

    #[test]
    fn source_only_lookup_returns_the_exact_source_write_children() {
        let write: ArrayExpr = "(Write Int Int A i v)".parse().unwrap();
        let array: ArrayExpr = "A".parse().unwrap();
        let index: ArrayExpr = "i".parse().unwrap();
        let value: ArrayExpr = "v".parse().unwrap();
        let mut egraph = egg::EGraph::<ArrayLanguage, ()>::default();
        egraph.add_expr(&write);
        egraph.rebuild();
        let index_eclass = egraph.lookup_expr(&index).unwrap();
        let value_eclass = egraph.lookup_expr(&value).unwrap();
        let source_reads_and_writes = ReadsAndWrites::from(
            std::collections::HashSet::new(),
            std::collections::HashSet::from([("A".to_string(), "i".to_string(), "v".to_string())]),
        );
        let extractor = ArrayTermExtractor::new(
            &egraph,
            ZeroCost,
            ArrayTermExtractorOptions {
                candidate_catalog: ArrayCandidateCatalog {
                    source_grounded: ArrayCandidatePool {
                        terms: vec![
                            "A".to_string(),
                            "i".to_string(),
                            "v".to_string(),
                            "(Write_Int_Int A i v)".to_string(),
                        ],
                        reads_and_writes: source_reads_and_writes,
                    },
                    derived: ArrayCandidatePool::default(),
                },
                candidate_scope: CandidateScope::SourceGroundedOnly,
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                profiling: None,
            },
        );

        assert_eq!(
            best_matching_write_children(
                &egraph,
                &extractor,
                &array,
                "Int",
                "Int",
                index_eclass,
                value_eclass,
            ),
            Some((index, value))
        );
    }

    #[test]
    fn source_write_lookup_canonicalizes_nested_array_lineage() {
        let array: ArrayExpr = "(Write Int Int A outer previous)".parse().unwrap();
        let index: ArrayExpr = "i".parse().unwrap();
        let value: ArrayExpr = "v".parse().unwrap();
        let mut egraph = egg::EGraph::<ArrayLanguage, ()>::default();
        egraph.add_expr(&array);
        let index_eclass = egraph.add_expr(&index);
        let value_eclass = egraph.add_expr(&value);
        egraph.rebuild();
        let extractor = ArrayTermExtractor::new(
            &egraph,
            ZeroCost,
            ArrayTermExtractorOptions {
                candidate_catalog: ArrayCandidateCatalog {
                    source_grounded: ArrayCandidatePool {
                        terms: vec![],
                        reads_and_writes: ReadsAndWrites::from(
                            std::collections::HashSet::new(),
                            std::collections::HashSet::from([(
                                "(Write_Int_Int A outer previous)".into(),
                                "i".into(),
                                "v".into(),
                            )]),
                        ),
                    },
                    derived: ArrayCandidatePool::default(),
                },
                candidate_scope: CandidateScope::SourceGroundedOnly,
                refinement_step: 0,
                selection_counts: FxHashMap::default(),
                depth: 0,
                profiling: None,
            },
        );

        assert_eq!(
            best_matching_write_children(
                &egraph,
                &extractor,
                &array,
                "Int",
                "Int",
                index_eclass,
                value_eclass,
            ),
            Some((index, value))
        );
    }

    #[test]
    fn instantiates_multiple_and_repeated_variables() {
        let pattern: ArrayPattern = "(= (+ ?x ?y) (+ ?x ?y))".parse().unwrap();
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
        let pattern: ArrayPattern = "(= (+ ?x ?y) (+ ?x ?y))".parse().unwrap();
        let x: egg::Var = "?x".parse().unwrap();
        let y: egg::Var = "?y".parse().unwrap();

        let mut egraph = egg::EGraph::<ArrayLanguage, ()>::default();
        let a: ArrayExpr = "a".parse().unwrap();
        let b: ArrayExpr = "b".parse().unwrap();
        let a_eclass = egraph.add_expr(&a);
        let b_eclass = egraph.add_expr(&b);
        egraph.rebuild();

        let mut subst = egg::Subst::default();
        subst.insert(x, a_eclass);
        subst.insert(y, b_eclass);

        let extractor = ArrayTermExtractor::new(
            &egraph,
            ZeroCost,
            ArrayTermExtractorOptions {
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
                rule_category: crate::quantified_rule::QuantifiedRuleCategory::Other,
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
