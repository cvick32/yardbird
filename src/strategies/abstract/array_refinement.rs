//! Array abstraction, encodings and axiom selection over a borrowed model graph.
//! Graph construction and assertion installation are coordinated by Abstract.
use super::{search_context::SearchContext, trace_conflicts_enabled};
use crate::{
    cost_functions::array::{ArrayCostContext, ArrayCostFactory},
    instantiation_strategy::assertion_tracker::canonical_instantiation_key,
    theories::array::{
        array_axioms::{
            expr_to_term, generate_array_instantiation_candidates_with_budget,
            ArrayInstantiationInstrumentation, ArrayInstantiationOptions, ArrayLanguage,
        },
        array_dataflow::{build_property_cone, PropertyCone},
        array_egraph_builder::ArrayEGraphExpansion,
        encodings::{EncodingOptions, EncodingPlan},
        instantiation_candidate::InstantiationBatch,
    },
};
use log::trace;
use smt2parser::vmt::VMTModel;
use std::{
    collections::{HashMap, HashSet},
    time::Instant,
};

#[derive(Default)]
pub(super) struct ArrayRefinement {
    pub(super) array_types: Vec<(String, String)>,
    pub(super) property_cone: PropertyCone,
    pub(super) encoding_plan: EncodingPlan,
}

impl ArrayRefinement {
    pub(super) fn configure_model(
        &mut self,
        model: VMTModel,
        preprocess: bool,
        encoding_options: EncodingOptions,
        requires_property_cone: bool,
    ) -> VMTModel {
        let (abstracted_model, discovered_types) =
            model.abstract_array_theory_with_preprocessing(preprocess);
        let (abstracted_model, encoding_plan) =
            EncodingPlan::apply(abstracted_model, &discovered_types, encoding_options);
        self.encoding_plan = encoding_plan;
        self.property_cone = if requires_property_cone {
            build_property_cone(&abstracted_model)
        } else {
            PropertyCone::default()
        };
        self.array_types = discovered_types;
        abstracted_model
    }

    pub(super) fn candidates<F: ArrayCostFactory + 'static>(
        &self,
        egraph: &egg::EGraph<ArrayLanguage, ()>,
        array_types: &[(String, String)],
        expansion: &ArrayEGraphExpansion,
        context: &SearchContext<'_, F>,
    ) -> anyhow::Result<InstantiationBatch> {
        let smt = context.smt;
        let refinement_step = context.refinement_step;
        let profiling = &context.profiling;
        let cost_factory_start = Instant::now();
        let candidate_catalog = if expansion.candidate_scope.tracks_provenance()
            || context.ranker.requires_source_provenance()
        {
            smt.get_array_candidate_catalog()
        } else {
            crate::problem_context::ArrayCandidateCatalog::default()
        };
        let cost_context =
            ArrayCostContext::from_problem(smt, &candidate_catalog, expansion.candidate_scope);
        let cost_fn = context.term_cost(&cost_context, context.depth as u32);
        if let Some(profiling) = profiling {
            profiling
                .borrow_mut()
                .record_timing("cost_factory", cost_factory_start.elapsed());
        }

        let mut known_instantiations = smt
            .get_instantiations()
            .into_iter()
            .map(|term| canonical_instantiation_key(&term))
            .collect::<HashSet<_>>();
        known_instantiations.extend(context.pending_instances.iter().cloned());

        let instantiation_start = Instant::now();
        let mut seen = HashSet::new();
        let mut accepted_by_rule = HashMap::new();
        let array_candidates = generate_array_instantiation_candidates_with_budget(
            egraph,
            cost_fn.clone(),
            array_types,
            ArrayInstantiationOptions {
                match_scope: Some(context.graph.array_match_scope()),
                search_allowance: context.allowance,
                additional_terms: vec![],
                candidate_catalog: candidate_catalog.clone(),
                candidate_scope: expansion.candidate_scope,
                refinement_step,
                selection_counts: context.selection_counts.clone(),
                depth: context.depth,
                instrumentation: ArrayInstantiationInstrumentation {
                    artifact_capture: context.artifact_capture,
                    profiling: profiling.clone(),
                },
            },
            context.allowance.winners,
            |candidate| {
                if !context
                    .ranker
                    .is_eligible(candidate, expansion.candidate_scope)
                {
                    return Ok(false);
                }
                let rule_kind = candidate.rule.kind();
                let count = accepted_by_rule.entry(rule_kind).or_insert(0);
                if *count
                    >= context
                        .ranker
                        .source_batch_limit(rule_kind, context.allowance.winners)
                {
                    return Ok(false);
                }
                let Some(key) = context.installable_expression(&candidate.expression) else {
                    return Ok(false);
                };
                if known_instantiations.contains(&key) || seen.contains(&key) {
                    return Ok(false);
                }
                if smt
                    .eval_to_string(&expr_to_term(candidate.expression.clone()))?
                    .trim()
                    != "false"
                {
                    return Ok(false);
                }
                seen.insert(key);
                *count += 1;
                Ok(true)
            },
        )?;
        let mut candidate_batch = array_candidates;
        let summary = candidate_batch.prepare_with_ranker(
            expansion.candidate_scope,
            &known_instantiations,
            context.allowance.winners,
            context.ranker,
            |term| smt.eval_to_string(term),
            |candidate| context.installable_expression(&candidate.expression),
        )?;

        if let Some(profiling) = profiling {
            let mut profiling = profiling.borrow_mut();
            for (rule_name, counts) in &summary.by_rule {
                profiling.record_rule_candidates(rule_name, counts.generated, counts.selected);
            }
            profiling.add_counter(
                "model_satisfied_instantiations_filtered",
                summary.rejected_model as u64,
            );
            profiling.add_counter(
                "duplicate_or_uninstallable_instantiations_filtered",
                summary.rejected_known as u64,
            );
            profiling.add_counter(
                "instantiation_ranker_candidates_filtered",
                summary.rejected_ranker as u64,
            );
        }

        if let Some(profiling) = profiling {
            profiling
                .borrow_mut()
                .record_timing("instantiation_total", instantiation_start.elapsed());
        }

        if trace_conflicts_enabled() {
            trace!(
                "[yardbird::conflict-trace] sat depth={} refinement_step={} build_stage={} selected_guards={} selected_arrays={} conflicts={}",
                context.depth,
                refinement_step,
                expansion.stage.as_str(),
                summary.selected_guards,
                summary.selected_arrays,
                summary.conflicts,
            );
        }
        Ok(candidate_batch)
    }
}
