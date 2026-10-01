//! Read-only inputs shared by refinement searches. Installation and history
//! updates remain with the coordinator.
use crate::instance_installation::assertion_tracker::canonical_instantiation_key;
use crate::policy::effort::WorkAllowance;
use crate::policy::instance_selection::InstantiationRanker;
use crate::policy::term_selection::TermCostFactory;
use crate::problem_context::ProblemContext;
use crate::profiling::RefinementProfilingCollector;
use crate::rule_matching::candidate_builder::ArtifactCapture;
use crate::terms::language::{expr_to_term, TermExpr};
use rustc_hash::FxHashMap;
use smt2parser::concrete::Term;
use std::{cell::RefCell, rc::Rc};

/// Shared source formulas. Copies borrow the same immutable plan and index;
/// model-dependent activation, matching cursors and queues belong to searches.
#[derive(Clone, Copy)]
pub(crate) struct SearchFormulas<'a> {
    /// VMT formulas and framing. Stateless SMT-LIB inputs have no VMT index.
    pub index: Option<&'a crate::transition_index::TransitionIndex>,
    pub quantifiers: &'a crate::theories::quantifiers::QuantifierPlan,
}

pub(crate) struct SearchContext<'a, F: TermCostFactory> {
    pub formulas: SearchFormulas<'a>,
    pub model_version: u64,
    pub graph: &'a crate::refinement_graph::RefinementGraph,
    pub graph_version: u64,
    pub smt: &'a dyn ProblemContext,
    pub term_config: &'a F::Config,
    pub ranker: &'a dyn InstantiationRanker,
    pub allowance: WorkAllowance,
    pub operation_id: Option<crate::policy::effort::OperationId>,
    pub pending_instances: &'a std::collections::HashSet<Term>,
    pub selection_counts: &'a FxHashMap<String, u32>,
    pub artifact_capture: ArtifactCapture,
    pub depth: u16,
    pub refinement_step: u32,
    pub profiling: Option<Rc<RefCell<RefinementProfilingCollector>>>,
}

impl<F: TermCostFactory> SearchContext<'_, F> {
    pub fn term_cost(
        &self,
        context: &crate::policy::term_selection::context::TermCostContext,
        depth: u32,
    ) -> F {
        F::from_context(context, depth, self.term_config)
    }
    pub fn installable_expression(&self, expression: &TermExpr) -> Option<Term> {
        let term = expr_to_term(expression.clone());
        self.smt
            .make_unquantified_instance(term)
            .map(|instance| canonical_instantiation_key(instance.get_term()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theories::quantifiers::{
        equations::{EquationCompiler, EquationCursor},
        refinement::QuantifierRefinement,
    };
    use crate::transition_index::TransitionIndex;

    /// `SearchFormulas` exists so a shared `index`/`quantifiers` pair can be
    /// copied to independent searches; this exercises the equation matcher
    /// against real (not hand-built) indexed formulas at both an initial and
    /// a transition frame, through one `SearchFormulas` view of them.
    #[test]
    fn indexed_formulas_supply_guarded_equations_at_initial_and_transition_frames() {
        let input = r#"
            (declare-fun a () (Array Int Int))
            (declare-fun an () (Array Int Int))
            (define-fun .a () (Array Int Int) (! a :next an))
            (declare-fun tick () Bool)
            (define-fun .tick () Bool (! tick :action 0))
            (declare-fun mark (Int) Bool)
            (assert (forall ((i Int)) (mark i)))
            (define-fun initialized () Bool
              (forall ((i Int)) (= (select a i) i)))
            (define-fun updated () Bool
              (forall ((i Int)) (= (select an i) (+ (select a i) 1))))
            (define-fun init () Bool (! initialized :init true))
            (define-fun trans () Bool (! (and tick (=> tick updated)) :trans true))
            (define-fun prop () Bool (! (= (select a 4) 4) :invar-property 0))
        "#;
        let commands = smt2parser::CommandStream::new(
            input.as_bytes(),
            smt2parser::concrete::SyntaxBuilder,
            None,
        )
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
        let model = smt2parser::vmt::VMTModel::checked_from(commands).unwrap();
        let mut quantifiers = QuantifierRefinement::default();
        let model = quantifiers.configure_model(model, false);
        let (model, _) = model.abstract_array_theory();
        let index = TransitionIndex::from_model(
            &model,
            &quantifiers
                .plan
                .rules
                .iter()
                .map(|r| r.name.clone())
                .collect(),
        );
        let formulas = SearchFormulas {
            index: Some(&index),
            quantifiers: &quantifiers.plan,
        };
        let transition = &index.actions()["tick"].requirements[0];
        assert_eq!(transition.guards.len(), 1);
        assert_eq!(transition.guards[0].expression.to_string(), "tick");
        assert!(
            !transition.binders.is_empty(),
            "quantified updates must retain their helper links"
        );
        assert!(!index.axioms().is_empty());
        assert_eq!(
            index.transition(),
            &model.get_trans_condition_for_yardbird()
        );

        // Retains the full helper implication and the actual array frames at
        // both an initial-frame root and a transition-frame (action-guarded) root.
        for (root, demand, expected) in [
            (
                index.index_term(index.initial(), 0),
                "(Read_Int_Int a@0 4)",
                "4",
            ),
            (
                index.index_term(&transition.body, 1),
                "(Read_Int_Int a@2 4)",
                "(+ (Read_Int_Int a@1 4) 1)",
            ),
        ] {
            let mut compiler = EquationCompiler::new(root);
            while compiler.pending() {
                compiler.step_with_definitions(formulas.quantifiers, formulas.index);
            }
            let equations = compiler.finish();
            let mut cursor = EquationCursor::default();
            let mut instances = Vec::new();
            let mut replacements = Vec::new();
            while cursor.pending() {
                if let Some(term) = cursor.step(
                    &equations,
                    &demand.parse().unwrap(),
                    formulas.quantifiers,
                    &mut instances,
                ) {
                    replacements.push(term.to_string());
                }
            }
            assert!(
                replacements.contains(&expected.to_owned()),
                "{replacements:?}"
            );
            assert!(!instances.is_empty());
            assert!(instances.iter().all(|i| i
                .term
                .to_string()
                .starts_with("(=> (__yardbird_quantifier_")));
            assert!(instances
                .iter()
                .any(|i| i.term.to_string().contains(demand)));
        }
    }
}
