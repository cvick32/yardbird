//! Optional problem-derived array encodings.
//!
//! This module is the single seam between the array strategy and individual
//! encodings. Every transformation is disabled unless its explicit option is
//! enabled.

mod recurrent_products;
mod stability;

use log::info;
use smt2parser::vmt::VMTModel;

use crate::utils::SolverStatistics;

use self::recurrent_products::{abstract_proven_recurrent_products, RecurrentProductReport};

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct EncodingOptions {
    pub(crate) recurrent_products: bool,
}

#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct EncodingPlan {
    recurrent_products: RecurrentProductReport,
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

        info!(
            "Array encodings: recurrent_products={} recurrent_candidates={} recurrent_applied={} recurrent_rejected={}",
            options.recurrent_products,
            plan.recurrent_products.stable_factor_candidates,
            plan.recurrent_products.products_abstracted,
            plan.recurrent_products.rejected_unproven_recurrence,
        );

        (model, plan)
    }

    pub(crate) fn add_statistics(&self, statistics: &mut SolverStatistics) {
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
    }

    #[test]
    fn recurrent_products_are_independently_enabled() {
        let (model, array_types) = abstract_model("examples/array/array_equiv_2.vmt");

        let (planned_model, plan) = EncodingPlan::apply(
            model,
            &array_types,
            EncodingOptions {
                recurrent_products: true,
            },
        );

        assert_eq!(plan.recurrent_products.products_abstracted, 1);
        assert!(planned_model
            .get_trans_condition_for_yardbird()
            .to_string()
            .contains("yb_mul_table_i_c"));
    }
}
