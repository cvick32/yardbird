//! Optional problem-derived array encodings.
//!
//! This module is the single seam between the array strategy and individual
//! encodings. Every transformation is disabled unless its explicit option is
//! enabled.

mod guarded_read_updates;
mod recurrent_products;
mod stability;

use log::info;
use smt2parser::{concrete::Term, vmt::VMTModel};
use std::collections::HashSet;

use self::guarded_read_updates::{plan_guarded_read_updates, GuardedReadUpdatePlan};
use crate::{
    instantiation_provenance::InstantiationRequest,
    instantiation_strategy::assertion_tracker::canonical_instantiation_key,
    problem_context::ProblemContext, utils::SolverStatistics,
};

use self::recurrent_products::{abstract_proven_recurrent_products, RecurrentProductReport};

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct EncodingOptions {
    pub(crate) recurrent_products: bool,
    pub(crate) guarded_read_updates: bool,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct EncodingPlan {
    recurrent_products: RecurrentProductReport,
    guarded: Option<GuardedReadUpdatePlan>,
    installed_guarded: HashSet<Term>,
    guarded_model_evaluations: u64,
    guarded_model_violations: u64,
    guarded_schemas_installed: u64,
    guarded_max_batch: u64,
}

impl EncodingPlan {
    pub(crate) fn apply(
        mut model: VMTModel,
        array_types: &[(String, String)],
        options: EncodingOptions,
    ) -> (VMTModel, Self) {
        let mut plan = Self::default();

        if options.recurrent_products {
            let (rewritten, report) = abstract_proven_recurrent_products(model, array_types);
            model = rewritten;
            plan.recurrent_products = report;
        }

        if options.guarded_read_updates {
            let guarded = plan_guarded_read_updates(&model, true);
            for update in &guarded.eager_updates {
                model.add_transition_constraint(update.clone());
            }
            info!(
                "Guarded read updates: writes={} lazy_schemas={} eager_schemas={}",
                guarded.writes_detected,
                guarded.updates.len(),
                guarded.eager_updates.len(),
            );
            plan.guarded = Some(guarded);
        }

        info!(
            "Array encodings: recurrent_products={} recurrent_candidates={} recurrent_applied={} recurrent_rejected={}",
            options.recurrent_products,
            plan.recurrent_products.stable_factor_candidates,
            plan.recurrent_products.products_abstracted,
            plan.recurrent_products.rejected_unproven_recurrence,
        );

        (model, plan)
    }

    /// Select previously unasserted schemas falsified at an existing transition
    /// frame. Direct write-index equalities precede tracked-index ite formulas.
    pub(crate) fn violated_guarded_read_updates(
        &mut self,
        smt: &dyn ProblemContext,
        depth: u16,
        limit: usize,
    ) -> Vec<Term> {
        let Some(guarded) = &self.guarded else {
            return Vec::new();
        };
        if depth == 0 || limit == 0 || guarded.updates.is_empty() {
            return Vec::new();
        }
        let known = smt
            .get_instantiations()
            .iter()
            .map(canonical_instantiation_key)
            .collect::<HashSet<_>>();
        let mut violated = Vec::new();
        for schema in &guarded.updates {
            let Some(frame_zero) = smt.frame_transition_formula(schema.clone(), 0) else {
                continue;
            };
            let Some(instance) = smt.make_unquantified_instance(frame_zero) else {
                continue;
            };
            let key = canonical_instantiation_key(instance.get_term());
            if known.contains(&key) || self.installed_guarded.contains(&key) {
                continue;
            }
            for frame in 0..depth {
                let Some(framed) = smt.frame_transition_formula(schema.clone(), frame) else {
                    continue;
                };
                self.guarded_model_evaluations += 1;
                if matches!(smt.eval_to_string(&framed).as_deref(), Ok("false")) {
                    self.guarded_model_violations += 1;
                    violated.push(schema.clone());
                    break;
                }
            }
        }
        violated.sort_by_key(|term| {
            let rendered = term.to_string();
            (rendered.contains("(ite "), rendered.len(), rendered)
        });
        violated.truncate(limit);
        self.guarded_max_batch = self.guarded_max_batch.max(violated.len() as u64);
        violated
    }

    /// Install selected schemas through the existing unrolling/deduplication
    /// policy. No solver assertions are made directly by the encoding.
    pub(crate) fn install_guarded_read_updates(
        &mut self,
        schemas: Vec<Term>,
        smt: &mut dyn ProblemContext,
    ) {
        for schema in schemas {
            let Some(frame_zero) = smt.frame_transition_formula(schema, 0) else {
                continue;
            };
            let Some(instance) = smt.make_unquantified_instance(frame_zero) else {
                continue;
            };
            let key = canonical_instantiation_key(instance.get_term());
            let result = smt.add_instantiation(InstantiationRequest::untracked(instance));
            self.installed_guarded.insert(key);
            if result.abstract_instance_added {
                self.guarded_schemas_installed += 1;
            }
        }
    }

    pub(crate) fn add_statistics(&self, statistics: &mut SolverStatistics) {
        if let Some(guarded) = &self.guarded {
            for (name, value) in [
                ("writes", guarded.writes_detected as u64),
                (
                    "nonlinear rejected",
                    guarded.writes_rejected_nonlinear as u64,
                ),
                ("expensive values", guarded.writes_rejected_expensive as u64),
                (
                    "eager read composites",
                    guarded.eager_read_composite_writes as u64,
                ),
                ("schemas planned", guarded.updates.len() as u64),
                ("eager schemas", guarded.eager_updates.len() as u64),
                ("model evaluations", self.guarded_model_evaluations),
                ("model violations", self.guarded_model_violations),
                ("schemas installed", self.guarded_schemas_installed),
                ("max batch", self.guarded_max_batch),
            ] {
                statistics.add_count(&format!("yardbird encoding guarded {name}"), value);
            }
        }

        statistics.add_count(
            "yardbird encoding recurrent candidates",
            self.recurrent_products.stable_factor_candidates as u64,
        );
        statistics.add_count(
            "yardbird encoding recurrent applied",
            self.recurrent_products.products_abstracted as u64,
        );
        statistics.add_count(
            "yardbird encoding recurrent rejected",
            self.recurrent_products.rejected_unproven_recurrence as u64,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn abstract_model(path: &str) -> (VMTModel, Vec<(String, String)>) {
        VMTModel::from_path(path)
            .unwrap()
            .abstract_array_theory_with_preprocessing(false)
    }

    #[test]
    fn default_options_leave_the_model_unchanged() {
        let (model, array_types) = abstract_model("examples/array/array_equiv_2.vmt");
        let transition = model.get_trans_condition_for_yardbird();

        let (planned_model, plan) =
            EncodingPlan::apply(model, &array_types, EncodingOptions::default());

        assert_eq!(planned_model.get_trans_condition_for_yardbird(), transition);
        assert_eq!(plan.recurrent_products.products_abstracted, 0);
        assert!(plan.guarded.is_none());
    }

    #[test]
    fn recurrent_products_are_independently_enabled() {
        let (model, array_types) = abstract_model("examples/array/array_equiv_2.vmt");

        let (planned_model, plan) = EncodingPlan::apply(
            model,
            &array_types,
            EncodingOptions {
                recurrent_products: true,
                ..EncodingOptions::default()
            },
        );

        assert_eq!(plan.recurrent_products.products_abstracted, 1);
        assert!(planned_model
            .get_trans_condition_for_yardbird()
            .to_string()
            .contains("yb_mul_table_i_c"));
    }
}
