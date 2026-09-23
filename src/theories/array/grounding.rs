//! Array read/write grounding and intact source-write alternatives.
use crate::{
    egg_utils::RecExprRoot,
    policy::term_selection::YardbirdCostFunction,
    rule_matching::{
        extractor::TermExtractor,
        grounding::{
            bind_exact_source_variable, bind_exact_variable, child_patterns_compatible,
            choose_best_grounding, egraph_contains_at, ground_pattern, ground_pattern_variables,
            instantiate_pattern, pattern_sort_symbol, subpattern, GroundContext,
            GroundSubstitution,
        },
    },
    terms::language::{TermExpr, TermLanguage, TermPattern},
};

pub(crate) fn source_write_groundings<'a, N, CF>(
    pattern: &'a TermPattern,
    expected_eclass: egg::Id,
    subst: egg::Subst,
    egraph: &'a egg::EGraph<TermLanguage, N>,
    extractor: std::rc::Rc<TermExtractor<CF>>,
    context: GroundContext<'a>,
    mut seen: std::collections::HashSet<String>,
) -> impl Iterator<Item = GroundSubstitution> + 'a
where
    N: egg::Analysis<TermLanguage> + 'a,
    CF: YardbirdCostFunction<TermLanguage> + 'a,
{
    let mut sites = None;
    std::iter::from_fn(move || {
        if !extractor.requires_source_grounded_candidates() {
            return None;
        }
        // The array axioms bind the three write children as variables. Keep
        // more general patterns on the existing one-grounding path for now.
        let (index_sort, value_sort, variables) = pattern.as_ref().iter().find_map(|node| {
            let egg::ENodeOrVar::ENode(TermLanguage::WriteTyped([is, vs, a, i, v])) = node else {
                return None;
            };
            let [egg::ENodeOrVar::Var(a), egg::ENodeOrVar::Var(i), egg::ENodeOrVar::Var(v)] =
                [&pattern[*a], &pattern[*i], &pattern[*v]]
            else {
                return None;
            };
            Some((
                pattern_sort_symbol(pattern, *is)?,
                pattern_sort_symbol(pattern, *vs)?,
                [*a, *i, *v],
            ))
        })?;
        let sites = sites.get_or_insert_with(|| {
            let mut ranked = matching_source_write_sites(
                egraph,
                &extractor,
                subst[variables[0]],
                subst[variables[1]],
                subst[variables[2]],
            )
            .into_iter()
            .map(|(a, i, v)| {
                let write = TermLanguage::write_typed(
                    &index_sort,
                    &value_sort,
                    a.clone(),
                    i.clone(),
                    v.clone(),
                );
                (extractor.cost_of(&write), write.to_string(), [a, i, v])
            })
            .collect::<Vec<_>>();
            ranked.sort_by(|left, right| (left.0, &left.1).cmp(&(right.0, &right.1)));
            ranked.into_iter()
        });
        for (_, _, expressions) in sites.by_ref() {
            let mut grounding = GroundSubstitution::default();
            let mut compatible = true;
            for (variable, expression) in variables.into_iter().zip(expressions) {
                if grounding
                    .get_binding(variable)
                    .is_some_and(|binding| binding.expression != expression)
                {
                    compatible = false;
                    break;
                }
                grounding
                    .bind_source_choice(variable, expression, egraph, &extractor, context)
                    .expect("matching source sites must bind compatible eclasses");
            }
            if !compatible {
                continue;
            }
            ground_pattern_variables(pattern, &subst, &mut grounding, egraph, &extractor, context)
                .expect("egg search must bind every trigger variable");
            let expression = instantiate_pattern(pattern, &grounding).unwrap();
            if egraph.lookup_expr(&expression).map(|id| egraph.find(id))
                != Some(egraph.find(expected_eclass))
            {
                continue;
            }
            if seen.insert(expression.to_string()) {
                return Some(grounding);
            }
        }
        None
    })
}

pub(crate) fn ground_expected_write<N, CF>(
    pattern: &TermPattern,
    expected_eclass: egg::Id,
    subst: &egg::Subst,
    grounding: &mut GroundSubstitution,
    egraph: &egg::EGraph<TermLanguage, N>,
    extractor: &TermExtractor<CF>,
    context: GroundContext<'_>,
) -> anyhow::Result<bool>
where
    N: egg::Analysis<TermLanguage>,
    CF: YardbirdCostFunction<TermLanguage>,
{
    let egg::ENodeOrVar::ENode(TermLanguage::WriteTyped(
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

    let mut candidates = Vec::new();
    for node in &egraph[expected_eclass].nodes {
        let TermLanguage::WriteTyped([_, _, array_eclass, index_eclass, value_eclass]) = node
        else {
            continue;
        };
        if !child_patterns_compatible(
            egraph,
            subst,
            [&array_pattern, &index_pattern, &value_pattern],
            [*array_eclass, *index_eclass, *value_eclass],
        ) {
            continue;
        }

        if extractor.requires_source_grounded_candidates() {
            candidates.extend(
                matching_source_write_sites(
                    egraph,
                    extractor,
                    *array_eclass,
                    *index_eclass,
                    *value_eclass,
                )
                .into_iter()
                .map(|site| (*array_eclass, *index_eclass, *value_eclass, Some(site))),
            );
        } else {
            candidates.push((*array_eclass, *index_eclass, *value_eclass, None));
        }
    }

    choose_best_grounding(
        extractor,
        grounding,
        candidates,
        |(array_eclass, index_eclass, value_eclass, exact_source_site), candidate_grounding| {
            let uses_exact_source_site = exact_source_site.is_some();
            let exact_children =
                if let Some((array_expression, index_expression, value_expression)) =
                    exact_source_site
                {
                    if !bind_exact_source_variable(
                        &array_pattern,
                        &array_expression,
                        candidate_grounding,
                        egraph,
                        extractor,
                        context,
                    )? {
                        ground_pattern(
                            &array_pattern,
                            Some(array_eclass),
                            subst,
                            candidate_grounding,
                            egraph,
                            extractor,
                            context,
                        )?;
                    }
                    Some((index_expression, value_expression))
                } else {
                    ground_pattern(
                        &array_pattern,
                        Some(array_eclass),
                        subst,
                        candidate_grounding,
                        egraph,
                        extractor,
                        context,
                    )?;
                    let array_expression =
                        instantiate_pattern(&array_pattern, candidate_grounding)?;
                    best_matching_write_children(
                        egraph,
                        extractor,
                        &array_expression,
                        &index_sort,
                        &value_sort,
                        index_eclass,
                        value_eclass,
                    )
                };

            if let Some((index_expression, value_expression)) = exact_children.as_ref() {
                let index_bound = if uses_exact_source_site {
                    bind_exact_source_variable(
                        &index_pattern,
                        index_expression,
                        candidate_grounding,
                        egraph,
                        extractor,
                        context,
                    )?
                } else {
                    bind_exact_variable(
                        &index_pattern,
                        index_eclass,
                        index_expression,
                        candidate_grounding,
                        egraph,
                        extractor,
                        context,
                    )?
                };
                if !index_bound {
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
                let value_bound = if uses_exact_source_site {
                    bind_exact_source_variable(
                        &value_pattern,
                        value_expression,
                        candidate_grounding,
                        egraph,
                        extractor,
                        context,
                    )?
                } else {
                    bind_exact_variable(
                        &value_pattern,
                        value_eclass,
                        value_expression,
                        candidate_grounding,
                        egraph,
                        extractor,
                        context,
                    )?
                };
                if !value_bound {
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

pub(crate) fn ground_expected_read<N, CF>(
    pattern: &TermPattern,
    expected_eclass: egg::Id,
    subst: &egg::Subst,
    grounding: &mut GroundSubstitution,
    egraph: &egg::EGraph<TermLanguage, N>,
    extractor: &TermExtractor<CF>,
    context: GroundContext<'_>,
) -> anyhow::Result<bool>
where
    N: egg::Analysis<TermLanguage>,
    CF: YardbirdCostFunction<TermLanguage>,
{
    let egg::ENodeOrVar::ENode(TermLanguage::ReadTyped([_, _, array, index])) =
        pattern.rooted().clone()
    else {
        return Ok(false);
    };

    let array_pattern = subpattern(pattern, array);
    let index_pattern = subpattern(pattern, index);
    let expected_eclass = egraph.find(expected_eclass);

    let candidates = egraph[expected_eclass].nodes.iter().filter_map(|node| {
        let TermLanguage::ReadTyped([_, _, array_eclass, index_eclass]) = node else {
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

fn best_matching_write_children<N, CF>(
    egraph: &egg::EGraph<TermLanguage, N>,
    extractor: &TermExtractor<CF>,
    array_expr: &TermExpr,
    index_sort: &str,
    value_sort: &str,
    index_eclass: egg::Id,
    value_eclass: egg::Id,
) -> Option<(TermExpr, TermExpr)>
where
    N: egg::Analysis<TermLanguage>,
    CF: YardbirdCostFunction<TermLanguage>,
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

    let best_in_pool = |candidates: &[(TermExpr, TermExpr)]| {
        let mut best: Option<(u32, String, TermExpr, TermExpr)> = None;
        for (index_expr, value_expr) in candidates {
            if !egraph_contains_at(egraph, index_expr, index_eclass) {
                continue;
            }
            if !egraph_contains_at(egraph, value_expr, value_eclass) {
                continue;
            }

            let write_expr = TermLanguage::write_typed(
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

    let best = if extractor.requires_source_grounded_candidates() {
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

fn matching_source_write_sites<N, CF>(
    egraph: &egg::EGraph<TermLanguage, N>,
    extractor: &TermExtractor<CF>,
    array_eclass: egg::Id,
    index_eclass: egg::Id,
    value_eclass: egg::Id,
) -> Vec<(TermExpr, TermExpr, TermExpr)>
where
    N: egg::Analysis<TermLanguage>,
    CF: YardbirdCostFunction<TermLanguage>,
{
    let mut sites = Vec::new();
    for array in extractor.source_candidates_for_eclass(egraph, array_eclass) {
        for (index, value) in extractor.source_write_candidates(&array) {
            if egraph_contains_at(egraph, index, index_eclass)
                && egraph_contains_at(egraph, value, value_eclass)
            {
                sites.push((array.clone(), index.clone(), value.clone()));
            }
        }
    }
    sites.sort_by_cached_key(|(array, index, value)| format!("{array}\u{0}{index}\u{0}{value}"));
    sites.dedup();
    sites
}

#[cfg(test)]
mod test {
    use rustc_hash::FxHashMap;
    use smt2parser::vmt::ReadsAndWrites;

    use super::*;
    use crate::problem_context::{ArrayCandidateCatalog, ArrayCandidatePool};
    use crate::rule_matching::extractor::TermExtractorOptions;
    use crate::rule_matching::scope::CandidateScope;
    use crate::terms::language::{TermLanguage, TermPattern};

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
    fn source_only_lookup_returns_the_exact_source_write_children() {
        let write: TermExpr = "(Write Int Int A i v)".parse().unwrap();
        let array: TermExpr = "A".parse().unwrap();
        let index: TermExpr = "i".parse().unwrap();
        let value: TermExpr = "v".parse().unwrap();
        let mut egraph = egg::EGraph::<TermLanguage, ()>::default();
        egraph.add_expr(&write);
        egraph.rebuild();
        let index_eclass = egraph.lookup_expr(&index).unwrap();
        let value_eclass = egraph.lookup_expr(&value).unwrap();
        let source_reads_and_writes = ReadsAndWrites::from(
            std::collections::HashSet::new(),
            std::collections::HashSet::from([("A".to_string(), "i".to_string(), "v".to_string())]),
        );
        let extractor = TermExtractor::new(
            &egraph,
            ZeroCost,
            TermExtractorOptions {
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
        let array: TermExpr = "(Write Int Int A outer previous)".parse().unwrap();
        let index: TermExpr = "i".parse().unwrap();
        let value: TermExpr = "v".parse().unwrap();
        let mut egraph = egg::EGraph::<TermLanguage, ()>::default();
        egraph.add_expr(&array);
        let index_eclass = egraph.add_expr(&index);
        let value_eclass = egraph.add_expr(&value);
        egraph.rebuild();
        let extractor = TermExtractor::new(
            &egraph,
            ZeroCost,
            TermExtractorOptions {
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
    fn expected_read_grounds_the_read_matching_the_egg_substitution() {
        let pattern: TermPattern = "(Read Int Int ?array ?index)".parse().unwrap();
        let array_var: egg::Var = "?array".parse().unwrap();
        let index_var: egg::Var = "?index".parse().unwrap();

        let first_read: TermExpr = "(Read Int Int A i)".parse().unwrap();
        let matching_read: TermExpr = "(Read Int Int B j)".parse().unwrap();
        let matching_array: TermExpr = "B".parse().unwrap();
        let matching_index: TermExpr = "j".parse().unwrap();
        let mut egraph = egg::EGraph::<TermLanguage, ()>::default();
        let first_read_eclass = egraph.add_expr(&first_read);
        let matching_read_eclass = egraph.add_expr(&matching_read);
        egraph.union(first_read_eclass, matching_read_eclass);
        egraph.rebuild();

        let mut subst = egg::Subst::default();
        subst.insert(array_var, egraph.lookup_expr(&matching_array).unwrap());
        subst.insert(index_var, egraph.lookup_expr(&matching_index).unwrap());

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

        let grounded = ground_expected_read(
            &pattern,
            matching_read_eclass,
            &subst,
            &mut grounding,
            &egraph,
            &extractor,
            GroundContext::new(
                false,
                "read-after-write",
                crate::rule_matching::rule::QuantifiedRuleCategory::InputBinder,
            ),
        )
        .unwrap();

        assert!(grounded);
        assert_eq!(
            instantiate_pattern(&pattern, &grounding)
                .unwrap()
                .to_string(),
            "(Read Int Int B j)"
        );
    }

    #[test]
    fn expected_write_preserves_the_index_and_value_from_one_source_write() {
        let pattern: TermPattern = "(Write Int Int ?array ?index ?value)".parse().unwrap();
        let array_var: egg::Var = "?array".parse().unwrap();
        let index_var: egg::Var = "?index".parse().unwrap();
        let value_var: egg::Var = "?value".parse().unwrap();

        let source_write: TermExpr = "(Write Int Int A i v)".parse().unwrap();
        let array: TermExpr = "A".parse().unwrap();
        let index: TermExpr = "i".parse().unwrap();
        let index_alias: TermExpr = "index_alias".parse().unwrap();
        let value: TermExpr = "v".parse().unwrap();
        let value_alias: TermExpr = "value_alias".parse().unwrap();
        let mut egraph = egg::EGraph::<TermLanguage, ()>::default();
        let expected_write_eclass = egraph.add_expr(&source_write);
        let index_eclass = egraph.lookup_expr(&index).unwrap();
        let index_alias_eclass = egraph.add_expr(&index_alias);
        let value_eclass = egraph.lookup_expr(&value).unwrap();
        let value_alias_eclass = egraph.add_expr(&value_alias);
        egraph.union(index_eclass, index_alias_eclass);
        egraph.union(value_eclass, value_alias_eclass);
        egraph.rebuild();

        let mut subst = egg::Subst::default();
        subst.insert(array_var, egraph.lookup_expr(&array).unwrap());
        subst.insert(index_var, egraph.find(index_eclass));
        subst.insert(value_var, egraph.find(value_eclass));

        let extractor = TermExtractor::new(
            &egraph,
            ZeroCost,
            TermExtractorOptions {
                candidate_catalog: ArrayCandidateCatalog {
                    source_grounded: ArrayCandidatePool {
                        // Deliberately omit the scalar terms. The specialized write
                        // grounding path must recover them as one coherent write site.
                        terms: vec!["(Write_Int_Int A i v)".to_string()],
                        reads_and_writes: ReadsAndWrites::from(
                            std::collections::HashSet::new(),
                            std::collections::HashSet::from([(
                                "A".to_string(),
                                "i".to_string(),
                                "v".to_string(),
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
        let mut grounding = GroundSubstitution::default();

        let grounded = ground_expected_write(
            &pattern,
            expected_write_eclass,
            &subst,
            &mut grounding,
            &egraph,
            &extractor,
            GroundContext::new(
                false,
                "write-grounding",
                crate::rule_matching::rule::QuantifiedRuleCategory::InputBinder,
            ),
        )
        .unwrap();

        assert!(grounded);
        assert_eq!(
            instantiate_pattern(&pattern, &grounding)
                .unwrap()
                .to_string(),
            "(Write Int Int A i v)"
        );
    }

    #[test]
    fn expected_write_keeps_an_intact_source_site_when_the_base_has_a_cheaper_alias() {
        let pattern: TermPattern = "(Write Int Int ?array ?index ?value)".parse().unwrap();
        let array_var: egg::Var = "?array".parse().unwrap();
        let index_var: egg::Var = "?index".parse().unwrap();
        let value_var: egg::Var = "?value".parse().unwrap();

        let source_write: TermExpr = "(Write Int Int source_array i v)".parse().unwrap();
        let source_array: TermExpr = "source_array".parse().unwrap();
        let cheaper_alias: TermExpr = "alias".parse().unwrap();
        let index: TermExpr = "i".parse().unwrap();
        let value: TermExpr = "v".parse().unwrap();
        let mut egraph = egg::EGraph::<TermLanguage, ()>::default();
        let expected_write_eclass = egraph.add_expr(&source_write);
        let source_array_eclass = egraph.lookup_expr(&source_array).unwrap();
        let alias_eclass = egraph.add_expr(&cheaper_alias);
        egraph.union(source_array_eclass, alias_eclass);
        egraph.rebuild();

        let mut subst = egg::Subst::default();
        subst.insert(array_var, egraph.find(source_array_eclass));
        subst.insert(index_var, egraph.lookup_expr(&index).unwrap());
        subst.insert(value_var, egraph.lookup_expr(&value).unwrap());

        let extractor = TermExtractor::new(
            &egraph,
            ZeroCost,
            TermExtractorOptions {
                candidate_catalog: ArrayCandidateCatalog {
                    source_grounded: ArrayCandidatePool {
                        terms: vec![
                            "alias".to_string(),
                            "source_array".to_string(),
                            "i".to_string(),
                            "v".to_string(),
                            "(Write_Int_Int source_array i v)".to_string(),
                        ],
                        reads_and_writes: ReadsAndWrites::from(
                            std::collections::HashSet::new(),
                            std::collections::HashSet::from([(
                                "source_array".to_string(),
                                "i".to_string(),
                                "v".to_string(),
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
        let mut grounding = GroundSubstitution::default();

        let grounded = ground_expected_write(
            &pattern,
            expected_write_eclass,
            &subst,
            &mut grounding,
            &egraph,
            &extractor,
            GroundContext::new(
                false,
                "write-grounding",
                crate::rule_matching::rule::QuantifiedRuleCategory::InputBinder,
            ),
        )
        .unwrap();

        assert!(grounded);
        assert!(!grounding.used_derived_candidate());
        assert_eq!(
            instantiate_pattern(&pattern, &grounding)
                .unwrap()
                .to_string(),
            "(Write Int Int source_array i v)"
        );
    }
}
