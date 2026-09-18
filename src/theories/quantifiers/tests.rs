use super::*;
use crate::theories::array::search::generate_quantified_candidates;
use crate::{Driver, SolverBackend, Strategy, YardbirdOptions};

fn model(source: &str) -> VMTModel {
    let commands = smt2parser::CommandStream::new(
        std::io::Cursor::new(source.as_bytes()),
        smt2parser::concrete::SyntaxBuilder,
        None,
    )
    .collect::<Result<Vec<_>, _>>()
    .unwrap();
    VMTModel::checked_from(commands).unwrap()
}

fn formula_model(init: &str, property: &str) -> VMTModel {
    model(&format!(
        "(declare-fun a () (Array Bool Bool))
            (define-fun init () Bool (! {init} :init true))
            (define-fun trans () Bool (! true :trans true))
            (define-fun prop () Bool (! {property} :invar-property 0))"
    ))
}

fn check(init: &str, property: &str) -> crate::Result<crate::ProofLoopResult> {
    check_model(formula_model(init, property))
}

fn check_model(model: VMTModel) -> crate::Result<crate::ProofLoopResult> {
    check_model_with_timeout(model, None)
}

fn check_model_with_timeout(
    model: VMTModel,
    timeout: Option<std::time::Duration>,
) -> crate::Result<crate::ProofLoopResult> {
    let mut options = YardbirdOptions::from_filename("unused.vmt".into());
    options.strategy = Strategy::Abstract;
    let mut driver = Driver::new(
        model,
        options.build_instantiation_strategy(),
        SolverBackend::Z3,
    );
    driver = driver.with_wall_timeout(timeout);
    driver.check_strategy(1, options.build_array_strategy())
}

#[test]
fn provenance_preserves_nested_shadowing_and_lowered_bindings() {
    let input = formula_model("(forall ((x Int)) (exists ((x Int)) (= x 0)))", "false");
    let (scoped, mut provenance) =
        crate::theories::quantifiers::provenance::scope_model(input.clone(), true).unwrap();
    let (without_profile, empty) =
        crate::theories::quantifiers::provenance::scope_model(input, false).unwrap();
    assert_eq!(scoped.as_commands(), without_profile.as_commands());
    assert!(empty.sources.is_empty());
    assert_eq!(provenance.sources.len(), 2);
    let child = provenance
        .sources
        .values()
        .find(|s| s.kind == "exists")
        .unwrap();
    let parent = &provenance.sources[child.parent_source_id.as_ref().unwrap()];
    assert_eq!(parent.kind, "forall");
    assert_eq!(child.variables[0].name, "x");
    assert_eq!(parent.variables[0].name, "x");
    assert_ne!(
        child.variables[0].scoped_name,
        parent.variables[0].scoped_name
    );
    assert_eq!(child.formula, "(exists ((x Int)) (= x 0))");
    let (lowered, plan) = lower_model_with_provenance(scoped.clone(), &mut provenance).unwrap();
    let (untracked, _) = lower_model(scoped).unwrap();
    assert_eq!(lowered.as_commands(), untracked.as_commands());
    assert_eq!(provenance.rules.len(), plan.rules.len());
    for (name, rule) in &provenance.rules {
        assert_eq!(name, QuantifiedRule::input_binder(&rule.helper).name());
        assert_eq!(rule.witnesses.len(), rule.variables.len());
        let source = &provenance.sources[&rule.source_id];
        assert_eq!(
            rule.variables[0].scoped_name,
            source.variables[0].scoped_name
        );
        assert!(rule.variables[0]
            .lowered_name
            .starts_with("__yardbird_bound_"));
    }
}

#[test]
fn provenance_tracks_property_witnesses_without_binder_rules() {
    let input = formula_model("true", "(forall ((i Int)) (= i i))");
    let (scoped, mut provenance) =
        crate::theories::quantifiers::provenance::scope_model(input, true).unwrap();
    let (rewritten, bindings) = scoped.herbrandize_universal_property_with_bindings();
    provenance.record_property_witnesses(&bindings);
    let (_, plan) = lower_model_with_provenance(rewritten, &mut provenance).unwrap();
    assert_eq!(bindings.len(), 1);
    assert!(plan.rules.is_empty());
    assert!(provenance.rules.is_empty());
    let source = provenance.sources.values().next().unwrap();
    assert_eq!(source.formula, "(forall ((i Int)) (= i i))");
    assert_eq!(
        source.property_witnesses[0].scoped_variable,
        source.variables[0].scoped_name
    );
    assert_eq!(source.property_witnesses[0].witness, bindings[0].1 .0);
}

#[test]
fn provenance_keeps_one_source_for_let_copies_and_constant_lambdas() {
    let input = formula_model("(let ((p (forall ((x Int)) (= x 0)))) (and p p))", "false");
    let (scoped, mut provenance) =
        crate::theories::quantifiers::provenance::scope_model(input, true).unwrap();
    lower_model_with_provenance(scoped, &mut provenance).unwrap();
    assert_eq!(provenance.sources.len(), 1);
    assert_eq!(provenance.rules.len(), 2);
    assert!(provenance
        .rules
        .values()
        .all(|r| provenance.sources.contains_key(&r.source_id)));
    let input = formula_model("(= (select (lambda ((i Int)) 0) 0) 0)", "true");
    let (scoped, mut provenance) =
        crate::theories::quantifiers::provenance::scope_model(input, true).unwrap();
    lower_model_with_provenance(scoped, &mut provenance).unwrap();
    assert!(provenance.rules.is_empty());
    assert!(
        provenance
            .sources
            .values()
            .next()
            .unwrap()
            .eliminated_as_constant_array
    );
}

#[test]
fn provenance_and_work_are_retained_on_timeout() {
    for timeout in [
        std::time::Duration::ZERO,
        std::time::Duration::from_millis(200),
    ] {
        let input = formula_model(
            "(forall ((i Int)) (= (select a true) (select a true)))",
            "false",
        );
        let mut options = YardbirdOptions::from_filename("provenance.vmt".into());
        options.profile = true;
        let mut driver = Driver::new(
            input,
            options.build_instantiation_strategy(),
            SolverBackend::Z3,
        )
        .with_profiler(options.build_profiler())
        .with_wall_timeout(Some(timeout));
        let result = match driver.check_strategy(1, options.build_array_strategy()) {
            Ok(result) => result,
            Err(_) => driver.take_failed_result().unwrap(),
        };
        assert!(!result.profiling.quantifier_provenance.sources.is_empty());
        assert!(!result.profiling.quantifier_provenance.rules.is_empty());
        let serialized = serde_json::to_value(&result.profiling).unwrap();
        let roundtrip: crate::profiling::ProfilingRunRecord =
            serde_json::from_value(serialized).unwrap();
        assert_eq!(roundtrip.quantifier_provenance.sources.len(), 1);
        assert_eq!(
            result.run_progress.as_ref().unwrap().termination_reason,
            "timeout"
        );
        if !timeout.is_zero() {
            assert!(result
                .profiling
                .cost_records
                .iter()
                .any(|r| !r.quantifier_work.is_empty()));
        }
    }
    let legacy: crate::profiling::ProfilingRunRecord = serde_json::from_str("{}").unwrap();
    assert!(legacy.quantifier_provenance.sources.is_empty());
}

#[test]
fn provenance_joins_successful_rule_work_and_actual_installations() {
    let input = formula_model("(forall ((x Bool)) (select a x))", "(select a true)");
    let mut options = YardbirdOptions::from_filename("provenance.vmt".into());
    options.profile = true;
    let mut driver = Driver::new(
        input,
        options.build_instantiation_strategy(),
        SolverBackend::Z3,
    )
    .with_profiler(options.build_profiler());
    let result = driver
        .check_strategy(1, options.build_array_strategy())
        .unwrap();
    let mut installed = 0;
    let mut examined = 0;
    for record in &result.profiling.cost_records {
        for (rule, phases) in &record.quantifier_work {
            let source_id = &result.profiling.quantifier_provenance.rules[rule].source_id;
            assert!(result
                .profiling
                .quantifier_provenance
                .sources
                .contains_key(source_id));
            for work in phases.values() {
                examined += work.counters.get("matches_examined").copied().unwrap_or(0);
                installed += work
                    .counters
                    .get("abstract_instances_added")
                    .copied()
                    .unwrap_or(0);
            }
        }
    }
    assert!(examined > 0);
    assert!(installed > 0);
    let old_record = r#"{"scope":"legacy","bmc_depth":0,"refinement_step":0,"array_types":[],"timing_secs":{},"counters":{},"cost_rec":{"total_calls":0,"total_secs":0.0,"total_expr_nodes":0,"max_expr_nodes":0,"by_site":{}},"egraph":{},"rule_instantiation":{"rule_search_calls":0,"rule_instantiation_calls":0,"skipped_instantiation_calls":0,"matches_total":0,"substitutions_total":0,"substitutions_explored":0,"candidates_generated":0,"candidates_selected":0,"by_rule":{}}}"#;
    let legacy: crate::profiling::ProfilingRecord = serde_json::from_str(old_record).unwrap();
    assert!(legacy.quantifier_work.is_empty());
}

#[derive(Clone)]
pub(super) struct PreferLongName;

impl egg::CostFunction<TermLanguage> for PreferLongName {
    type Cost = u32;
    fn cost<C>(&mut self, node: &TermLanguage, mut child: C) -> u32
    where
        C: FnMut(egg::Id) -> u32,
    {
        use egg::Language;
        let own = match node {
            TermLanguage::Symbol(symbol) if symbol.as_str() == "long_preferred_term" => 1,
            TermLanguage::Symbol(symbol) if symbol.as_str() == "a" => 100,
            _ => 2,
        };
        node.fold(own, |sum, id| sum + child(id))
    }
}
impl crate::policy::term_selection::YardbirdCostFunction<TermLanguage> for PreferLongName {
    fn get_string_terms(&self) -> Vec<String> {
        vec![]
    }
    fn get_reads_and_writes(&self) -> smt2parser::vmt::ReadsAndWrites {
        Default::default()
    }
}

#[derive(Clone, Default)]
struct CountCosts(std::rc::Rc<std::cell::RefCell<Vec<String>>>);

impl egg::CostFunction<TermLanguage> for CountCosts {
    type Cost = u32;
    fn cost<C>(&mut self, node: &TermLanguage, children: C) -> u32
    where
        C: FnMut(egg::Id) -> u32,
    {
        self.0.borrow_mut().push(node.to_string());
        PreferLongName.cost(node, children)
    }
}

impl crate::policy::term_selection::YardbirdCostFunction<TermLanguage> for CountCosts {
    fn get_string_terms(&self) -> Vec<String> {
        vec![]
    }
    fn get_reads_and_writes(&self) -> smt2parser::vmt::ReadsAndWrites {
        Default::default()
    }
}

pub(crate) struct PreparedFixture {
    pub(crate) egraph: egg::EGraph<TermLanguage, ()>,
    pub(crate) search: PreparedQuantifierSearch,
}
impl std::ops::Deref for PreparedFixture {
    type Target = PreparedQuantifierSearch;
    fn deref(&self) -> &Self::Target {
        &self.search
    }
}
impl std::ops::DerefMut for PreparedFixture {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.search
    }
}
impl PreparedFixture {
    pub(crate) fn candidates<'a, CF>(
        &mut self,
        evaluate: impl FnMut(&Term) -> anyhow::Result<String>,
        search: impl Into<BinderSearch<'a>>,
        make_cost: impl FnOnce(&crate::policy::term_selection::context::TermCostContext) -> CF,
        options: InstantiationOptions,
    ) -> anyhow::Result<InstantiationBatch>
    where
        CF: crate::policy::term_selection::YardbirdCostFunction<TermLanguage> + 'static,
    {
        self.search
            .candidates(&self.egraph, evaluate, search, make_cost, options)
    }
}

pub(super) fn prepared_fixture(variable_count: usize, value_count: usize) -> PreparedFixture {
    let variables = (0..variable_count)
        .map(|i| (Symbol(format!("x{i}")), string_to_sort("Int")))
        .collect::<Vec<_>>();
    let rule = BinderRule {
        name: "q".into(),
        kind: BinderKind::Forall,
        captures: vec![(Symbol("unit".into()), string_to_sort("Bool"))],
        body: app(
            "p",
            variables
                .iter()
                .map(|(symbol, _)| app(&symbol.0, vec![]))
                .collect(),
        ),
        witnesses: (0..variable_count).map(|i| format!("witness{i}")).collect(),
        variables,
        result_sort: string_to_sort("Bool"),
        unit_capture: true,
    };
    let plan = QuantifierPlan {
        rules: vec![rule],
        signatures: (0..value_count)
            .map(|i| (format!("v{i}"), (vec![], string_to_sort("Int"))))
            .collect(),
        ..Default::default()
    };
    let mut graph = egg::EGraph::<TermLanguage, ()>::default();
    let mut terms = vec![];
    for term in ["(q true)".to_string(), "true".into(), "false".into()]
        .into_iter()
        .chain((0..value_count).map(|i| format!("v{i}")))
    {
        let expression = translate_term_with_array_types(term.parse().unwrap(), &[]).unwrap();
        graph.add_expr(&expression);
        terms.push(expression);
    }
    let proxy = graph.lookup_expr(&terms[0]).unwrap();
    let truth = graph.lookup_expr(&terms[1]).unwrap();
    graph.union(proxy, truth);
    let sort = graph.add(TermLanguage::SortTag("Int".into()));
    for expression in &terms[3..] {
        let value = graph.lookup_expr(expression).unwrap();
        graph.add(TermLanguage::Domain([sort, value]));
    }
    graph.rebuild();
    let mut representatives = HashMap::new();
    for expression in &terms {
        representatives
            .entry(graph.find(graph.lookup_expr(expression).unwrap()))
            .or_insert(expression.clone());
    }
    PreparedFixture {
        egraph: graph,
        search: PreparedQuantifierSearch {
            graph_version: 0,
            additional_terms: terms,
            representatives,
            evaluations: HashMap::new(),
            compiled: plan.compiled(&[]).unwrap(),
            cursors: HashMap::new(),
            requests: HashMap::new(),
            obligations: HashMap::new(),
            catalog: Default::default(),
            cost_context: Default::default(),
        },
    }
}

pub(super) fn prepared_options() -> InstantiationOptions {
    InstantiationOptions {
        search_allowance: crate::policy::effort::WorkAllowance::default(),
        candidate_catalog: Default::default(),
        additional_terms: vec![],
        candidate_scope: crate::rule_matching::scope::CandidateScope::AllCandidates,
        refinement_step: 0,
        selection_counts: Default::default(),
        depth: 0,
        instrumentation: crate::rule_matching::candidate_builder::InstantiationInstrumentation {
            artifact_capture: Default::default(),
            profiling: None,
        },
    }
}

#[test]
fn satisfied_matches_do_not_invoke_costs_or_extraction() {
    let mut prepared = prepared_fixture(1, 5);
    let cost = CountCosts::default();
    let factories = std::cell::Cell::new(0);
    let batch = prepared
        .candidates(
            |_| Ok("true".into()),
            SearchPhase::Conflicts,
            |_| {
                factories.set(factories.get() + 1);
                cost.clone()
            },
            prepared_options(),
        )
        .unwrap();
    assert!(batch.candidates.is_empty());
    assert_eq!(
        factories.get(),
        0,
        "even heuristic construction must wait for a violation"
    );
    assert!(
        cost.0.borrow().is_empty(),
        "satisfied matches must not initialize ranked extraction"
    );
}

#[test]
fn a_surviving_match_does_not_score_rejected_binding_classes() {
    let mut prepared = prepared_fixture(1, 5);
    let cost = CountCosts::default();
    let batch = prepared
        .candidates(
            |term| {
                Ok(if term.to_string().contains("(p v4)") {
                    "false"
                } else {
                    "true"
                }
                .into())
            },
            SearchPhase::Conflicts,
            |_| cost.clone(),
            prepared_options(),
        )
        .unwrap();
    assert_eq!(batch.candidates.len(), 1);
    assert!(batch.candidates[0].model_violation_verified);
    let calls = cost.0.borrow();
    assert!(calls.iter().any(|symbol| symbol == "v4"));
    assert!(!calls
        .iter()
        .any(|symbol| ["v0", "v1", "v2", "v3"].contains(&symbol.as_str())));
}

#[test]
fn fallback_optimizes_surviving_bindings_without_costing_unrelated_classes() {
    let mut prepared = prepared_fixture(1, 2);
    prepared.additional_terms.clear(); // Exercise the shared e-graph fallback.
    let preferred =
        translate_term_with_array_types("long_preferred_term".parse().unwrap(), &[]).unwrap();
    let preferred_id = prepared.egraph.add_expr(&preferred);
    let original = prepared.egraph.lookup_expr(&"v0".parse().unwrap()).unwrap();
    prepared.egraph.union(original, preferred_id);
    prepared.egraph.rebuild();
    let cost = CountCosts::default();
    let batch = prepared
        .candidates(
            |term| {
                Ok(if term.to_string().contains("v1") {
                    "true"
                } else {
                    "false"
                }
                .into())
            },
            SearchPhase::Conflicts,
            |_| cost.clone(),
            prepared_options(),
        )
        .unwrap();
    assert_eq!(batch.candidates.len(), 1);
    assert!(batch.candidates[0]
        .expression
        .to_string()
        .contains("long_preferred_term"));
    assert!(!cost.0.borrow().iter().any(|symbol| symbol == "v1"));
}

#[test]
fn triggered_and_domain_search_share_model_obligation_results() {
    let mut prepared = prepared_fixture(1, 2);
    // Keep this test focused on sharing evaluations across the historical
    // trigger and domain paths; signed-plan matching is tested separately.
    let legacy = prepared.compiled.sources[0]
        .compile(SearchPhase::TriggeredConflicts, &[])
        .unwrap()
        .unwrap();
    std::rc::Rc::get_mut(&mut prepared.compiled)
        .unwrap()
        .phases
        .insert(SearchPhase::TriggeredConflicts, vec![legacy]);
    for atom in ["(p v0)", "(p v1)"] {
        prepared
            .egraph
            .add_expr(&translate_term_with_array_types(atom.parse().unwrap(), &[]).unwrap());
    }
    prepared.egraph.rebuild();
    let mut checks = 0;
    prepared
        .candidates(
            |_| {
                checks += 1;
                Ok("true".into())
            },
            SearchPhase::TriggeredConflicts,
            |_| CountCosts::default(),
            prepared_options(),
        )
        .unwrap();
    assert_eq!(checks, 2);
    let batch = prepared
        .candidates(
            |_| panic!("the same model obligation was already evaluated"),
            SearchPhase::Conflicts,
            |_| CountCosts::default(),
            prepared_options(),
        )
        .unwrap();
    assert!(batch.candidates.is_empty());
}

#[test]
fn optimized_binding_preserves_the_cheap_obligations_value() {
    let mut prepared = prepared_fixture(1, 1);
    let preferred =
        translate_term_with_array_types("long_preferred_term".parse().unwrap(), &[]).unwrap();
    let preferred_id = prepared.egraph.add_expr(&preferred);
    let original = prepared.egraph.lookup_expr(&"v0".parse().unwrap()).unwrap();
    prepared.egraph.union(original, preferred_id);
    prepared.egraph.rebuild();
    prepared.additional_terms.push(preferred);
    let batch = prepared
        .candidates(
            |term| {
                assert_eq!(
                    term.to_string().replace("long_preferred_term", "v0"),
                    "(=> (q true) (p v0))"
                );
                Ok("false".into())
            },
            SearchPhase::Conflicts,
            |_| CountCosts::default(),
            prepared_options(),
        )
        .unwrap();
    assert_eq!(batch.candidates.len(), 1);
    assert!(batch.candidates[0]
        .expression
        .to_string()
        .contains("long_preferred_term"));
    assert!(batch.candidates[0].model_violation_verified);
}

#[test]
fn a_new_phase_pass_reconsiders_bindings_after_history_changes() {
    let mut prepared = prepared_fixture(1, 1);
    let preferred =
        translate_term_with_array_types("long_preferred_term".parse().unwrap(), &[]).unwrap();
    let preferred_id = prepared.egraph.add_expr(&preferred);
    let original = prepared.egraph.lookup_expr(&"v0".parse().unwrap()).unwrap();
    prepared.egraph.union(original, preferred_id);
    prepared.egraph.rebuild();
    prepared.additional_terms.push(preferred.clone());
    let first = prepared
        .candidates(
            |_| unreachable!(),
            SearchPhase::Expand,
            |_| CountCosts::default(),
            prepared_options(),
        )
        .unwrap();
    assert!(first.candidates[0]
        .expression
        .to_string()
        .contains("long_preferred_term"));
    let mut options = prepared_options();
    options
        .selection_counts
        .insert(crate::training::canonical_term_hash(&preferred), 100);
    prepared.start_phase(SearchPhase::Expand, 0);
    let second = prepared
        .candidates(
            |_| unreachable!(),
            SearchPhase::Expand,
            |_| CountCosts::default(),
            options,
        )
        .unwrap();
    assert_eq!(second.candidates.len(), 1);
    assert!(second.candidates[0].expression.to_string().contains("v0"));
    assert!(!second.candidates[0]
        .expression
        .to_string()
        .contains("long_preferred_term"));
}

#[test]
fn binder_profiling_separates_matching_from_grounding() {
    for violated in [false, true] {
        let profiling = std::rc::Rc::new(std::cell::RefCell::new(
            crate::profiling::RefinementProfilingCollector::new("test", None, None, vec![]),
        ));
        let mut prepared = prepared_fixture(1, 2);
        let mut options = prepared_options();
        options.instrumentation.profiling = Some(profiling.clone());
        prepared
            .candidates(
                |_| Ok(if violated { "false" } else { "true" }.into()),
                SearchPhase::Conflicts,
                |_| CountCosts::default(),
                options,
            )
            .unwrap();
        let record = std::rc::Rc::try_unwrap(profiling)
            .ok()
            .unwrap()
            .into_inner()
            .finish();
        assert!(record.timing_secs.contains_key("rule_matching_total"));
        assert_eq!(
            record.timing_secs.contains_key("rule_grounding_total"),
            violated
        );
        assert!(!record.timing_secs.contains_key("rule_search_total"));
    }
}

#[test]
fn binder_continuation_finds_a_violation_after_a_satisfied_prefix() {
    use crate::rule_matching::grounding::instantiate_with_bindings;
    use crate::terms::language::expr_to_term;
    use crate::theories::quantifiers::search::{search_binder_page, BinderSearchCursor};
    let mut prepared = prepared_fixture(2, 11); // 121 typed substitutions.
    let rules = &prepared.compiled.phases[&SearchPhase::Conflicts];
    let mut cursor = BinderSearchCursor::default();
    let first = search_binder_page(&prepared.egraph, rules, &mut cursor, &None);
    assert_eq!(first.matches.len(), 100);
    assert_eq!(first.report.continuable_rules.len(), 1);
    assert!(first.report.budget_exhausted_rules.is_empty());
    let second = search_binder_page(&prepared.egraph, rules, &mut cursor, &None);
    assert_eq!(second.matches.len(), 21);
    assert!(second.report.continuable_rules.is_empty());
    assert!(second.report.budget_exhausted_rules.is_empty());
    let last = second.matches.last().unwrap();
    let target = expr_to_term(
        instantiate_with_bindings(rules[0].formula(), |variable| {
            Ok(&prepared.representatives[&prepared.egraph.find(last.substitution[variable])])
        })
        .unwrap(),
    );
    let evaluate = |term: &Term| Ok(if *term == target { "false" } else { "true" }.into());
    let cost = CountCosts::default();
    let profiling = std::rc::Rc::new(std::cell::RefCell::new(
        crate::profiling::RefinementProfilingCollector::new("test", None, None, vec![]),
    ));
    let mut options = prepared_options();
    options.instrumentation.profiling = Some(profiling.clone());
    let first = prepared
        .candidates(evaluate, SearchPhase::Conflicts, |_| cost.clone(), options)
        .unwrap();
    assert!(first.candidates.is_empty());
    assert!(prepared.can_continue(SearchPhase::Conflicts));
    assert!(cost.0.borrow().is_empty());
    let record = std::rc::Rc::try_unwrap(profiling)
        .ok()
        .unwrap()
        .into_inner()
        .finish();
    assert_eq!(
        record
            .counters
            .get("rule_search_truncated")
            .copied()
            .unwrap_or(0),
        0
    );
    assert_eq!(record.counters["rule_search_continuations_available"], 1);
    assert_eq!(record.counters["rule_search_budget_exhausted"], 0);
    let second = prepared
        .candidates(
            evaluate,
            SearchPhase::Conflicts,
            |_| cost,
            prepared_options(),
        )
        .unwrap();
    assert_eq!(second.candidates.len(), 1);
    assert_eq!(
        expr_to_term(second.candidates[0].expression.clone()),
        target
    );
    assert!(!prepared.can_continue(SearchPhase::Conflicts));
}

#[test]
fn expansion_can_materialize_a_satisfied_obligation() {
    let mut prepared = prepared_fixture(1, 1);
    let batch = prepared
        .candidates(
            |_| panic!("expansion must not require a violation"),
            SearchPhase::Expand,
            |_| CountCosts::default(),
            prepared_options(),
        )
        .unwrap();
    assert_eq!(batch.candidates.len(), 1);
    assert!(!batch.candidates[0].model_violation_verified);
}

#[test]
fn compiled_rules_are_reused_until_array_types_change() {
    let plan = QuantifierPlan::default();
    let first = plan.compiled(&[]).unwrap();
    assert!(std::rc::Rc::ptr_eq(&first, &plan.compiled(&[]).unwrap()));
    let changed = plan.compiled(&[("Int".into(), "Bool".into())]).unwrap();
    assert!(!std::rc::Rc::ptr_eq(&first, &changed));
}

#[test]
fn binder_work_limit_is_reported_as_budget_exhaustion_not_continuation() {
    use crate::theories::quantifiers::search::{search_binder_page, BinderSearchCursor};
    let prepared = prepared_fixture(2, 257); // 66,049 > the 65,536 work window.
    let rules = &prepared.compiled.phases[&SearchPhase::Conflicts];
    let mut cursor = BinderSearchCursor::default();
    let mut count = 0;
    let mut examined = 0;
    loop {
        let page = search_binder_page(&prepared.egraph, rules, &mut cursor, &None);
        count += page.matches.len();
        assert_eq!(page.report.returned_substitutions, page.matches.len());
        examined += page.report.examined_substitutions;
        assert_eq!(
            page.report.continuable_rules.len(),
            usize::from(cursor.can_continue())
        );
        assert_eq!(
            page.report.budget_exhausted_rules.len(),
            usize::from(!cursor.can_continue())
        );
        if !cursor.can_continue() {
            break;
        }
    }
    assert_eq!(count, 65_536);
    assert_eq!(
        examined, 21_550_192,
        "prefix re-examination must also be bounded"
    );
    let exhausted = search_binder_page(&prepared.egraph, rules, &mut cursor, &None);
    assert!(exhausted.matches.is_empty());
    assert_eq!(exhausted.report.examined_substitutions, 0);
    assert!(exhausted.report.continuable_rules.is_empty());
    assert_eq!(exhausted.report.budget_exhausted_rules.len(), 1);
}

#[test]
fn binder_exact_work_limit_completes_without_budget_exhaustion() {
    use crate::theories::quantifiers::search::{search_binder_page, BinderSearchCursor};
    let prepared = prepared_fixture(2, 256); // Exactly 65,536 substitutions.
    let rules = &prepared.compiled.phases[&SearchPhase::Conflicts];
    let mut cursor = BinderSearchCursor::default();
    let mut count = 0;
    loop {
        let page = search_binder_page(&prepared.egraph, rules, &mut cursor, &None);
        count += page.matches.len();
        assert!(page.report.budget_exhausted_rules.is_empty());
        assert_eq!(
            page.report.continuable_rules.len(),
            usize::from(cursor.can_continue())
        );
        if !cursor.can_continue() {
            break;
        }
    }
    assert_eq!(count, 65_536);
}

#[test]
fn nested_binder_search_prepares_once_per_model_and_refreshes_after_checks() {
    let mut options = YardbirdOptions::from_filename("unused.vmt".into());
    options.profile = true;
    let mut driver = Driver::new(
        formula_model("(exists ((x Bool)) (forall ((y Bool)) (= x y)))", "false"),
        options.build_instantiation_strategy(),
        SolverBackend::Z3,
    )
    .with_profiler(options.build_profiler());
    let result = driver
        .check_strategy(1, options.build_array_strategy())
        .unwrap();
    let sat_models = result
        .profiling
        .solver_checks
        .iter()
        .filter(|check| check.result == crate::solver::SolverCheckResult::Sat)
        .count();
    let preparations: u64 = result
        .profiling
        .cost_records
        .iter()
        .map(|record| {
            record
                .counters
                .get("input_binder_model_preparations")
                .copied()
                .unwrap_or(0)
        })
        .sum();
    assert!(
        sat_models > 1,
        "the fixture must require fresh counterexample models"
    );
    assert_eq!(preparations, sat_models as u64);
    assert!(result.profiling.cost_records.iter().any(|record| record
        .timing_secs
        .contains_key("input_binder_triggered_conflicts")));
    assert!(!result.counterexample);
}

fn ranked_binder_fixture(phase: SearchPhase) -> InstantiationBatch {
    use crate::rule_matching::candidate_builder::InstantiationInstrumentation;
    use crate::rule_matching::scope::CandidateScope;
    let rule = BinderRule {
        name: "q".into(),
        kind: BinderKind::Forall,
        captures: vec![(Symbol("unit".into()), string_to_sort("Bool"))],
        variables: vec![(Symbol("x".into()), string_to_sort("Int"))],
        body: "(p x)".parse().unwrap(),
        witnesses: vec!["witness".into()],
        result_sort: string_to_sort("Bool"),
        unit_capture: true,
    };
    let mut graph = egg::EGraph::<TermLanguage, ()>::default();
    let mut catalog = crate::problem_context::ArrayCandidateCatalog::default();
    let mut add = |text: &str| {
        catalog.source_grounded.terms.push(text.to_string());
        graph.add_expr(&translate_term_with_array_types(text.parse().unwrap(), &[]).unwrap())
    };
    if phase == SearchPhase::TriggeredConflicts {
        add("(p b)");
    }
    let proxy = add("(q true)");
    let truth = add("true");
    let falsity = add("false");
    let a = add("a");
    let preferred = add("long_preferred_term");
    let b = add("b");
    // A Bool term with a different typed domain must never bind the Int slot.
    let boolean = add("flag");
    // Sort names can also be term names; equal values for those terms
    // must not merge the typed domains.
    let named_int = add("Int");
    let named_bool = add("Bool");
    graph.union(named_int, named_bool);
    graph.union(a, preferred);
    graph.union(truth, boolean);
    graph.union(
        proxy,
        if phase == SearchPhase::Witnesses {
            falsity
        } else {
            truth
        },
    );
    let int_sort = graph.add(TermLanguage::SortTag("Int".into()));
    let bool_sort = graph.add(TermLanguage::SortTag("Bool".into()));
    graph.add(TermLanguage::Domain([int_sort, a]));
    graph.add(TermLanguage::Domain([int_sort, b]));
    graph.add(TermLanguage::Domain([bool_sort, boolean]));
    graph.rebuild();
    generate_quantified_candidates(
        &graph,
        PreferLongName,
        &[rule.compile(phase, &[]).unwrap().unwrap()],
        InstantiationOptions {
            search_allowance: crate::policy::effort::WorkAllowance::default(),
            additional_terms: catalog
                .source_grounded
                .terms
                .iter()
                .map(|term| translate_term_with_array_types(term.parse().unwrap(), &[]).unwrap())
                .collect(),
            candidate_catalog: catalog,
            candidate_scope: CandidateScope::AllCandidates,
            refinement_step: 0,
            selection_counts: Default::default(),
            depth: 0,
            instrumentation: InstantiationInstrumentation {
                artifact_capture: crate::rule_matching::candidate_builder::ArtifactCapture {
                    decisions: true,
                    instantiation_provenance: true,
                    conflicts: true,
                },
                profiling: None,
            },
        },
        None,
    )
    .unwrap()
}

#[test]
fn input_binders_use_costed_typed_egg_grounding_and_record_decisions() {
    use egg::CostFunction;
    let batch = ranked_binder_fixture(SearchPhase::Conflicts);
    assert_eq!(batch.candidates.len(), 2);
    let rendered = batch
        .candidates
        .iter()
        .map(|candidate| {
            assert_eq!(
                candidate.cost,
                PreferLongName.cost_rec(&candidate.expression)
            );
            assert!(!candidate.selected, "generation must not bypass selection");
            assert!(!candidate.decisions.is_empty());
            assert!(!candidate.selection_history.is_empty());
            assert!(candidate.abstract_instantiation.is_some());
            assert!(
                candidate.conflict.is_none(),
                "input binders are not auxiliary array conflicts"
            );
            crate::terms::language::expr_to_term(candidate.expression.clone()).to_string()
        })
        .collect::<Vec<_>>();
    assert!(rendered
        .iter()
        .any(|text| text.contains("(p long_preferred_term)")));
    assert!(rendered.iter().any(|text| text.contains("(p b)")));
    assert!(rendered
        .iter()
        .all(|text| !text.contains("flag") && !text.contains("(p a)")));
}

#[test]
fn input_binders_match_existing_body_atoms_before_domain_fallback() {
    let triggered = ranked_binder_fixture(SearchPhase::TriggeredConflicts);
    assert_eq!(triggered.candidates.len(), 1);
    let term = crate::terms::language::expr_to_term(triggered.candidates[0].expression.clone());
    assert!(term.to_string().contains("(p b)"));
    assert_eq!(
        ranked_binder_fixture(SearchPhase::Conflicts)
            .candidates
            .len(),
        2
    );
}

#[test]
fn input_binder_batches_obey_rankers_budgets_and_novelty() {
    use crate::policy::instance_selection::{InstantiationRanker, TermCostInstantiationRanker};
    use crate::rule_matching::scope::CandidateScope;
    #[derive(Clone, Debug)]
    struct Reverse;
    impl InstantiationRanker for Reverse {
        fn clone_box(&self) -> Box<dyn InstantiationRanker> {
            Box::new(self.clone())
        }
        fn compare(
            &self,
            left: &crate::rule_matching::candidate::InstantiationCandidate,
            right: &crate::rule_matching::candidate::InstantiationCandidate,
        ) -> std::cmp::Ordering {
            TermCostInstantiationRanker.compare(right, left)
        }
    }
    let prepare = |batch: &mut InstantiationBatch,
                   ranker: &dyn InstantiationRanker,
                   budget,
                   known: &HashSet<String>| {
        batch
            .prepare_with_ranker(
                CandidateScope::AllCandidates,
                known,
                budget,
                ranker,
                |_| panic!("expansion need not violate the model"),
                |candidate| Some(candidate.expression.to_string()),
            )
            .unwrap()
    };
    let mut batch = ranked_binder_fixture(SearchPhase::Expand);
    assert_eq!(
        prepare(&mut batch, &TermCostInstantiationRanker, 1, &HashSet::new()).selected_count(),
        1
    );
    let first = batch.selected().next().unwrap().expression.to_string();
    assert_eq!(
        prepare(&mut batch, &Reverse, 1, &HashSet::new()).selected_count(),
        1
    );
    assert_ne!(
        first,
        batch.selected().next().unwrap().expression.to_string()
    );
    assert_eq!(
        prepare(&mut batch, &Reverse, 40, &HashSet::new()).selected_count(),
        2
    );
    assert_eq!(
        prepare(
            &mut batch,
            &TermCostInstantiationRanker,
            1,
            &HashSet::from([first.clone()])
        )
        .selected_count(),
        1
    );
    assert_ne!(
        first,
        batch.selected().next().unwrap().expression.to_string()
    );

    let mut witnesses = ranked_binder_fixture(SearchPhase::Witnesses);
    assert_eq!(witnesses.candidates.len(), 1);
    assert!(witnesses.candidates[0]
        .expression
        .to_string()
        .contains("witness"));
    assert_eq!(
        prepare(
            &mut witnesses,
            &TermCostInstantiationRanker,
            1,
            &HashSet::new()
        )
        .selected_count(),
        1
    );
}

#[test]
fn let_aliases_are_not_captured_by_quantifiers_or_property_witnesses() {
    let source = |init: &str, property: &str| {
        model(&format!(
            "(declare-fun a () (Array Bool Bool))
            (declare-fun x () Bool)
            (define-fun init () Bool (! {init} :init true))
            (define-fun trans () Bool (! true :trans true))
            (define-fun prop () Bool (! {property} :invar-property 0))"
        ))
    };
    let alias = "(let ((alias x)) (forall ((x Bool)) alias))";
    assert!(check_model(source("x", alias)).is_ok());
    let result = check_model_with_timeout(
        source(&format!("(and x {alias})"), "false"),
        Some(std::time::Duration::from_millis(100)),
    )
    .unwrap();
    assert_eq!(result.run_progress.unwrap().termination_reason, "timeout");
    assert!(!result.found_proof && !result.counterexample);
}

#[test]
fn arrays_that_only_occur_in_binder_expressions_are_declared() {
    let result = check_model(model("(define-fun init () Bool (! true :init true))
            (define-fun trans () Bool (! true :trans true))
            (define-fun prop () Bool (! (forall ((x Bool)) (select (lambda ((y Bool)) true) x)) :invar-property 0))")).unwrap();
    assert!(!result.counterexample);
}

#[test]
fn arithmetic_hidden_in_a_quantifier_selects_a_sufficient_logic() {
    assert!(check("(forall ((x Int)) (< (* x x) 0))", "false").is_ok());
}

#[test]
fn every_protocol_lowers_to_quantifier_free_commands_and_rules() {
    let root =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/distributed_protocols");
    let mut files = Vec::new();
    for directory in std::fs::read_dir(root).unwrap().flatten() {
        if !directory.path().is_dir() {
            continue;
        }
        for entry in std::fs::read_dir(directory.path()).unwrap().flatten() {
            if entry
                .path()
                .extension()
                .is_some_and(|extension| extension == "vmt")
            {
                files.push(entry.path());
            }
        }
    }
    assert!(files.len() >= 30, "protocol inventory unexpectedly shrank");
    files.sort();
    for file in files {
        let (lowered, plan) = lower_model(VMTModel::from_path(&file).unwrap())
            .unwrap_or_else(|error| panic!("{}: {error}", file.display()));
        let (abstracted, _) = lowered.abstract_array_theory();
        for command in abstracted.as_commands() {
            if let Command::Assert { term } | Command::DefineFun { term, .. } = command {
                assert!(!contains_binders(&term), "{} leaked {term}", file.display());
            }
        }
        for rule in plan.rules {
            assert!(
                !contains_binders(&rule.body),
                "{} leaked binder in rule {}",
                file.display(),
                rule.name
            );
        }
    }
}

#[test]
fn existential_witness_depends_on_the_enclosing_universal() {
    let (_, plan) = lower_model(formula_model(
        "(forall ((x Bool)) (exists ((y Bool)) (= x y)))",
        "false",
    ))
    .unwrap();
    let exists = plan
        .rules
        .iter()
        .find(|rule| rule.kind == BinderKind::Exists)
        .unwrap();
    assert_eq!(exists.captures.len(), 1);
    let witness = exists.witness_instance(&[app("true", vec![])]).unwrap();
    assert!(witness
        .to_string()
        .contains(&format!("({} true)", exists.witnesses[0])));
    assert!(!contains_binders(&witness));
}

#[test]
fn shadowed_binders_have_distinct_capture_free_names() {
    let (_, plan) = lower_model(formula_model(
        "(forall ((x Bool)) (and x (exists ((x Bool)) (not x))))",
        "false",
    ))
    .unwrap();
    let outer = plan
        .rules
        .iter()
        .find(|rule| rule.kind == BinderKind::Forall)
        .unwrap();
    let inner = plan
        .rules
        .iter()
        .find(|rule| rule.kind == BinderKind::Exists)
        .unwrap();
    assert_ne!(outer.variables[0].0, inner.variables[0].0);
    assert!(!inner
        .captures
        .iter()
        .any(|(symbol, _)| symbol == &outer.variables[0].0));
}

#[test]
fn nested_constant_lambdas_use_nested_constant_arrays() {
    let source = model("(declare-fun a () (Array Bool (Array Bool Bool)))
            (define-fun init () Bool (! (= a (lambda ((x Bool)) (lambda ((y Bool)) false))) :init true))
            (define-fun trans () Bool (! true :trans true))
            (define-fun prop () Bool (! true :invar-property 0))");
    let (lowered, plan) = lower_model(source).unwrap();
    assert!(plan.rules.is_empty());
    let (abstracted, types) = lowered.abstract_array_theory();
    assert!(types.contains(&("Bool".into(), "Bool".into())));
    assert!(types.contains(&("Bool".into(), "Array_Bool_Bool".into())));
    assert!(abstracted
        .as_vmt_string()
        .contains("(ConstArr_Bool_Array_Bool_Bool (ConstArr_Bool_Bool false))"));
}

#[test]
fn quantifier_polarities_and_alternation_are_sound_over_booleans() {
    // These formulas are unsatisfiable; either polarity can require
    // universal instances as well as existential witnesses.
    for init in [
        "(forall ((x Bool)) x)",
        "(not (exists ((x Bool)) x))",
        "(exists ((x Bool)) (forall ((y Bool)) (= x y)))",
        "(not (forall ((x Bool)) (exists ((y Bool)) (= x y))))",
        "(= false (exists ((x Bool) (y Bool)) (distinct x y)))",
    ] {
        let result = check(init, "false").unwrap_or_else(|error| panic!("{init}: {error}"));
        assert!(!result.counterexample);
        assert_eq!(
            result
                .solver_statistics
                .get_f64("concrete_validation_checks"),
            Some(0.0)
        );
    }
    // Continued search is inconclusive until externally interrupted. Never
    // prove these satisfiable formulas inconsistent or delegate them to Z3.
    for init in [
        "(exists ((x Bool)) x)",
        "(not (forall ((x Bool)) x))",
        "(forall ((x Bool)) (exists ((y Bool)) (= x y)))",
        "(exists ((x Bool)) (and x (forall ((x Bool)) (= x x))))",
    ] {
        let result = check_model_with_timeout(
            formula_model(init, "false"),
            Some(std::time::Duration::from_millis(100)),
        )
        .unwrap();
        assert_eq!(
            result.run_progress.unwrap().termination_reason,
            "timeout",
            "{init}"
        );
        assert!(!result.found_proof && !result.counterexample);
        assert_eq!(
            result
                .solver_statistics
                .get_f64("concrete_validation_checks"),
            Some(0.0)
        );
    }
}

#[test]
fn binder_page_rotate_and_preserve_each_rules_position() {
    use crate::theories::quantifiers::search::{search_binder_page, BinderSearchCursor};

    let prepared = prepared_fixture(2, 11);
    let other = prepared_fixture(2, 11);

    let mut first_compiled = std::rc::Rc::try_unwrap(prepared.search.compiled)
        .ok()
        .unwrap();
    let mut second_comiled = std::rc::Rc::try_unwrap(other.search.compiled).ok().unwrap();

    let mut rules = first_compiled
        .phases
        .remove(&SearchPhase::Conflicts)
        .unwrap();
    rules.extend(
        second_comiled
            .phases
            .remove(&SearchPhase::Conflicts)
            .unwrap(),
    );

    assert_eq!(rules.len(), 2);

    let mut cursor = BinderSearchCursor::default();
    let mut seen = [
        HashSet::<Vec<egg::Id>>::new(),
        HashSet::<Vec<egg::Id>>::new(),
    ];

    for (rule_index, count, pending) in [(0, 100, 2), (1, 100, 2), (0, 21, 1), (1, 21, 0)] {
        let page = search_binder_page(&prepared.egraph, &rules, &mut cursor, &None);

        assert_eq!(page.matches.len(), count);
        assert_eq!(page.report.rounds, 1);
        assert_eq!(page.report.continuable_rules.len(), pending);
        assert_eq!(cursor.can_continue(), pending > 0);
        assert!(page.report.budget_exhausted_rules.is_empty());

        for matched in page.matches {
            assert_eq!(matched.rule_index, rule_index);
            let bindings = rules[rule_index]
                .formula_variables()
                .iter()
                .map(|var| prepared.egraph.find(matched.substitution[*var]))
                .collect::<Vec<_>>();

            assert!(
                seen[rule_index].insert(bindings),
                "a binding was returned more than once for rule {rule_index}"
            );
        }
    }

    assert_eq!(seen[0].len(), 121);
    assert_eq!(seen[1].len(), 121);

    let finished = search_binder_page(&prepared.egraph, &rules, &mut cursor, &None);

    assert!(finished.matches.is_empty());
    assert_eq!(finished.report.rounds, 0);
    assert_eq!(finished.report.examined_substitutions, 0);
    assert!(finished.report.continuable_rules.is_empty());
    assert!(finished.report.budget_exhausted_rules.is_empty());
}

#[test]
fn binder_pages_skip_completed_rules() {
    use crate::theories::quantifiers::search::{search_binder_page, BinderSearchCursor};

    // Both rules use the same domain of 11 values.
    // One variable gives 11 matches; two give 121.
    let short = prepared_fixture(1, 11);
    let long = prepared_fixture(2, 11);

    let mut short_compiled = std::rc::Rc::try_unwrap(short.search.compiled).ok().unwrap();
    let mut long_compiled = std::rc::Rc::try_unwrap(long.search.compiled).ok().unwrap();

    let mut rules = short_compiled
        .phases
        .remove(&SearchPhase::Conflicts)
        .unwrap();
    rules.extend(
        long_compiled
            .phases
            .remove(&SearchPhase::Conflicts)
            .unwrap(),
    );
    assert_eq!(rules.len(), 2);

    let mut cursor = BinderSearchCursor::default();

    for (rule_index, count, more) in [(0, 11, true), (1, 100, true), (1, 21, false)] {
        let page = search_binder_page(&long.egraph, &rules, &mut cursor, &None);

        assert_eq!(page.matches.len(), count);
        assert!(page
            .matches
            .iter()
            .all(|matched| matched.rule_index == rule_index));
        assert_eq!(page.report.rounds, 1);
        assert_eq!(page.report.continuable_rules.len(), usize::from(more));
        assert!(page.report.budget_exhausted_rules.is_empty());
        assert_eq!(cursor.can_continue(), more);
    }

    let finished = search_binder_page(&long.egraph, &rules, &mut cursor, &None);
    assert!(finished.matches.is_empty());
    assert_eq!(finished.report.examined_substitutions, 0);
    assert_eq!(finished.report.rounds, 0);
    assert!(!cursor.can_continue());
}
