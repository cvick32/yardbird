//! Bounded cross-theory support over original source vocabulary. A satisfied
//! instance stays available across models, including its array support. Only
//! independently validated, violated instances are sent to installation.
use super::{
    candidate::InstantiationBatch, search_context::SearchContext, source_terms::SourceTerms,
    symbolic_pool::SymbolicCandidatePool,
};
use crate::{
    policy::{effort::WorkReport, term_selection::TermCostFactory},
    theories::{
        array::read_support::ArrayReadSupport, quantifiers::read_support::QuantifierReadSupport,
    },
};

#[derive(Default)]
pub(crate) struct ReadSupport {
    depth: Option<u16>,
    arrays: ArrayReadSupport,
    quantifiers: QuantifierReadSupport,
    pool: SymbolicCandidatePool,
    next_array: bool,
}
impl ReadSupport {
    pub fn candidates<F: TermCostFactory>(
        &mut self,
        context: &SearchContext<'_, F>,
    ) -> anyhow::Result<(WorkReport, InstantiationBatch)> {
        if self.depth != Some(context.depth) {
            let source = SourceTerms::new(
                context.smt.get_source_subterms(),
                &context.formulas.quantifiers.signatures,
            );
            *self = Self {
                depth: Some(context.depth),
                arrays: ArrayReadSupport::new(&context.smt.get_array_types(), &source),
                quantifiers: QuantifierReadSupport::new(
                    context.formulas.quantifiers,
                    &source,
                    &context.smt.get_array_types(),
                ),
                pool: Default::default(),
                next_array: false,
            };
        }
        let mut generated = [0usize; 2];
        while generated.iter().sum::<usize>() < context.allowance.dependency_work
            && (self.arrays.pending() || self.quantifiers.pending())
        {
            let array = if self.next_array {
                self.arrays.pending()
            } else {
                !self.quantifiers.pending()
            };
            let instance = if array {
                self.arrays.next()
            } else {
                self.quantifiers.next(context.formulas.quantifiers)
            };
            self.next_array = !array;
            if let Some(instance) = instance {
                if !array {
                    self.arrays.remember(&instance.term);
                }
                generated[usize::from(array)] += 1;
                self.pool.remember([instance]);
            }
        }
        let batch = self.pool.candidates(context)?;
        let mut report = WorkReport::from_batch(&batch);
        report.dependency_work = generated.iter().sum();
        report.continuable |= self.arrays.pending() || self.quantifiers.pending();
        report.budget_exhausted |= report.continuable;
        if let Some(profile) = &context.profiling {
            let mut p = profile.borrow_mut();
            p.add_counter(
                "read_support_quantifier_instances_generated",
                generated[0] as u64,
            );
            p.add_counter(
                "read_support_array_instances_generated",
                generated[1] as u64,
            );
            p.add_counter("read_support_instances_selected", report.selected as u64);
        }
        Ok((report, batch))
    }
}
