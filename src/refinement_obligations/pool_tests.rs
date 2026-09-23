use super::*;
use crate::{
    instance_installation::request::{InstantiationInstallResult, InstantiationRequest},
    policy::{
        effort::OperationId, instance_selection::TermCostInstantiationRanker,
        term_selection::array::ArrayAstSize,
    },
    refinement_graph::RefinementGraph,
    rule_matching::rule::QuantifiedRule,
    utils::SolverStatistics,
};
use smt2parser::vmt::{
    quantified_instantiator::{Instance, UnquantifiedInstantiator},
    variable::Variable,
    ReadsAndWrites,
};
use std::cell::{Cell, RefCell};

#[derive(Default)]
struct CountingModel {
    values: HashMap<Term, String>,
    installed: Vec<Term>,
    evaluations: RefCell<Vec<Term>>,
    normalizations: Cell<usize>,
}

impl ProblemContext for CountingModel {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn has_model(&self) -> bool {
        true
    }
    fn eval_to_string(&self, term: &Term) -> anyhow::Result<String> {
        self.evaluations.borrow_mut().push(term.clone());
        self.values
            .get(term)
            .cloned()
            .ok_or_else(|| anyhow::anyhow!("missing model value: {term}"))
    }
    fn make_unquantified_instance(&self, term: Term) -> Option<Instance> {
        self.normalizations.set(self.normalizations.get() + 1);
        UnquantifiedInstantiator::rewrite_unquantified(term, vec![])
    }
    fn model_to_string(&self) -> anyhow::Result<String> {
        Ok(String::new())
    }
    fn get_all_subterms(&self) -> Vec<&Term> {
        vec![]
    }
    fn get_solver_statistics(&self) -> SolverStatistics {
        SolverStatistics::default()
    }
    fn get_reason_unknown(&self) -> Option<String> {
        None
    }
    fn add_instantiation(&mut self, _: InstantiationRequest) -> InstantiationInstallResult {
        Default::default()
    }
    fn get_instantiations(&self) -> Vec<Term> {
        self.installed.clone()
    }
    fn get_variables(&self) -> &[Variable] {
        &[]
    }
    fn get_number_instantiations_added(&self) -> u64 {
        self.installed.len() as u64
    }
    fn get_number_instantiation_assertions_added(&self) -> u64 {
        self.installed.len() as u64
    }
    fn get_init_and_transition_subterms(&self) -> Vec<String> {
        vec![]
    }
    fn get_property_subterms(&self) -> Vec<String> {
        vec![]
    }
    fn get_reads_and_writes(&self) -> ReadsAndWrites {
        ReadsAndWrites::default()
    }
    fn get_array_types(&self) -> Vec<(String, String)> {
        vec![]
    }
}

fn instance(i: usize) -> SymbolicInstance {
    SymbolicInstance {
        term: format!("(= (f {i}) 0)").parse().unwrap(),
        rule: QuantifiedRule::input_binder("test-binder"),
        bindings: vec![],
    }
}

fn offer(
    pool: &mut RefinementObligations,
    smt: &CountingModel,
    model: u64,
    depth: u16,
    pending: &HashSet<Term>,
    winners: usize,
) -> anyhow::Result<InstantiationBatch> {
    pool.candidates(&SearchContext::<ArrayAstSize> {
        graph: &RefinementGraph::default(),
        graph_version: 0,
        smt,
        term_config: &(),
        ranker: &TermCostInstantiationRanker,
        allowance: WorkAllowance {
            winners,
            ..Default::default()
        },
        operation_id: Some(OperationId {
            model,
            offer: 0,
            index: 0,
        }),
        pending_instances: pending,
        selection_counts: &Default::default(),
        artifact_capture: Default::default(),
        depth,
        refinement_step: 0,
        profiling: None,
    })
}

#[test]
fn unchanged_model_only_evaluates_new_pool_entries() {
    let mut pool = RefinementObligations::default();
    let mut smt = CountingModel::default();
    for i in 0..64 {
        smt.values
            .insert(instance(i).term.clone(), (i != 0).to_string());
        pool.remember([instance(i)]);
    }
    let pending = HashSet::new();
    assert_eq!(
        offer(&mut pool, &smt, 1, 0, &pending, 10)
            .unwrap()
            .selected()
            .count(),
        1
    );
    let normalized = smt.normalizations.get();
    assert_eq!(smt.evaluations.borrow().len(), 64);
    assert_eq!(
        offer(&mut pool, &smt, 1, 0, &pending, 10)
            .unwrap()
            .selected()
            .count(),
        1
    );
    assert_eq!(
        smt.evaluations.borrow().len(),
        64,
        "same-model slices must reuse evaluations"
    );
    assert_eq!(
        smt.normalizations.get(),
        normalized,
        "same-model slices must reuse normalization"
    );

    smt.values.insert(instance(64).term.clone(), "false".into());
    pool.remember([instance(64), instance(0)]);
    assert_eq!(
        offer(&mut pool, &smt, 1, 0, &pending, 10)
            .unwrap()
            .selected()
            .count(),
        2
    );
    assert_eq!(
        smt.evaluations.borrow().len(),
        65,
        "only the new unique entry is evaluated"
    );
    let normalized = smt.normalizations.get();

    smt.values.insert(instance(0).term.clone(), "true".into());
    smt.values.insert(instance(1).term.clone(), "false".into());
    let batch = offer(&mut pool, &smt, 2, 0, &pending, 10).unwrap();
    assert_eq!(batch.selected().count(), 2);
    assert_eq!(
        smt.evaluations.borrow().len(),
        130,
        "every entry is reconsidered on a new model"
    );
    let terms = batch
        .selected()
        .map(|c| crate::terms::language::expr_to_term(c.expression.clone()))
        .collect::<HashSet<_>>();
    assert_eq!(terms, HashSet::from([instance(1).term, instance(64).term]));
    assert_eq!(
        smt.normalizations.get(),
        normalized,
        "normalization survives a model change"
    );
    offer(&mut pool, &smt, 1, 0, &pending, 10).unwrap();
    assert_eq!(
        smt.evaluations.borrow().len(),
        195,
        "returning to an old model ID still invalidates the current cache"
    );
    offer(&mut pool, &smt, 1, 1, &pending, 10).unwrap();
    assert_eq!(smt.evaluations.borrow().len(), 260);
    assert!(
        smt.normalizations.get() > normalized,
        "a new depth discards normalization too"
    );
}

#[test]
fn cached_pool_rechecks_pending_installed_and_winner_limits() {
    let mut pool = RefinementObligations::default();
    pool.remember((0..3).map(instance));
    let mut smt = CountingModel::default();
    let key = |i| canonical_instantiation_key(&instance(i).term);
    smt.installed.push(instance(1).term);
    smt.values.insert(instance(2).term, "false".into());
    let mut pending = HashSet::from([key(0)]);
    assert_eq!(
        offer(&mut pool, &smt, 1, 0, &pending, 10)
            .unwrap()
            .selected()
            .count(),
        1
    );
    assert_eq!(
        *smt.evaluations.borrow(),
        vec![instance(2).term],
        "known entries need no evaluation"
    );
    let normalized = smt.normalizations.get();

    // A temporarily pending entry must remain available if the pending batch
    // changes without a new solver model.
    pending.clear();
    smt.values.insert(instance(0).term, "false".into());
    assert_eq!(
        offer(&mut pool, &smt, 1, 0, &pending, 10)
            .unwrap()
            .selected()
            .count(),
        2
    );
    smt.installed.clear();
    smt.values.insert(instance(1).term, "false".into());
    assert_eq!(
        offer(&mut pool, &smt, 1, 0, &pending, 10)
            .unwrap()
            .selected()
            .count(),
        3
    );
    let batch = offer(&mut pool, &smt, 1, 0, &pending, 1).unwrap();
    assert_eq!(
        batch.selected().count(),
        1,
        "winner allowance is applied afresh"
    );
    let chosen = canonical_instantiation_key(&expr_to_term(
        batch.selected().next().unwrap().expression.clone(),
    ));
    pending.insert(chosen.clone());
    let next = offer(&mut pool, &smt, 1, 0, &pending, 10).unwrap();
    assert_eq!(next.selected().count(), 2);
    assert!(next
        .selected()
        .all(|c| canonical_instantiation_key(&expr_to_term(c.expression.clone())) != chosen));
    smt.installed = (0..3).map(|i| instance(i).term).collect();
    assert_eq!(
        offer(&mut pool, &smt, 1, 0, &pending, 10)
            .unwrap()
            .selected()
            .count(),
        0
    );
    assert_eq!(smt.evaluations.borrow().len(), 3);
    assert_eq!(smt.normalizations.get(), normalized);
}

#[test]
fn failed_evaluation_does_not_drop_unprocessed_pool_entries() {
    let mut pool = RefinementObligations::default();
    pool.remember((0..3).map(instance));
    let mut smt = CountingModel::default();
    smt.values.insert(instance(0).term, "true".into());
    smt.values.insert(instance(2).term, "false".into());
    let pending = HashSet::new();
    assert!(offer(&mut pool, &smt, 1, 0, &pending, 10).is_err());
    smt.values.insert(instance(1).term, "false".into());
    assert_eq!(
        offer(&mut pool, &smt, 1, 0, &pending, 10)
            .unwrap()
            .selected()
            .count(),
        2
    );
    assert_eq!(
        *smt.evaluations.borrow(),
        vec![
            instance(0).term,
            instance(1).term,
            instance(1).term,
            instance(2).term
        ]
    );
    assert_eq!(
        offer(&mut pool, &smt, 1, 0, &pending, 10)
            .unwrap()
            .selected()
            .count(),
        2
    );
    assert_eq!(smt.evaluations.borrow().len(), 4);
}

#[test]
fn cached_pool_preserves_frame_normalization_and_provenance() {
    let mut pool = RefinementObligations::default();
    let mut smt = CountingModel::default();
    let instances = (2..4)
        .map(|frame| SymbolicInstance {
            rule: QuantifiedRule::input_binder("test-binder"),
            term: format!("(= (f x@{frame}) x@{frame})").parse().unwrap(),
            bindings: vec![("x".into(), format!("x@{frame}").parse().unwrap())],
        })
        .collect::<Vec<_>>();
    for instance in &instances {
        smt.values.insert(instance.term.clone(), "false".into());
    }
    pool.remember(instances.clone());
    let pending = HashSet::new();
    let signature = |batch: InstantiationBatch| {
        batch
            .into_selected()
            .map(|c| (c.expression, c.cost, c.provenance))
            .collect::<Vec<_>>()
    };
    let first = signature(offer(&mut pool, &smt, 1, 3, &pending, 10).unwrap());
    assert_eq!(first.len(), 1, "equal normalized schemas must deduplicate");
    assert_eq!(
        first[0].2.relative_bindings(),
        &[("x".into(), "x+0".parse().unwrap())]
    );
    let normalized = smt.normalizations.get();
    assert_eq!(
        signature(offer(&mut pool, &smt, 1, 3, &pending, 10).unwrap()),
        first
    );
    assert_eq!(smt.normalizations.get(), normalized);
    let mut fresh = RefinementObligations::default();
    fresh.remember(instances);
    assert_eq!(
        signature(offer(&mut fresh, &smt, 1, 3, &pending, 10).unwrap()),
        first
    );
}
