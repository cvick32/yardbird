use super::*;
use smt2parser::{concrete::SyntaxBuilder, vmt::VMTModel, CommandStream};
use std::collections::HashSet;

fn model(text: &str) -> VMTModel {
    VMTModel::checked_from(
        CommandStream::new(text.as_bytes(), SyntaxBuilder, None)
            .collect::<Result<Vec<_>, _>>()
            .unwrap(),
    )
    .unwrap()
}
fn fixture() -> (TransitionIndex, Vec<(String, String)>) {
    let input = std::fs::read_to_string("tests/fixtures/array_dataflow_actions.vmt")
        .unwrap()
        .replace(
            "(= (select b 0) 0)",
            "(and (= (select a (witness a)) 0) (= (select b 0) 0))",
        );
    let (model, types) = model(&input).abstract_array_theory();
    (TransitionIndex::from_model(&model, &HashSet::new()), types)
}

fn observation(term: &Term, choose: bool, violate_axiom: bool) -> anyhow::Result<ModelEvaluation> {
    let text = term.to_string();
    Ok(
        if text.starts_with("(and ") || text.starts_with("(= (Read_Int_Int a@2") {
            "false"
        } else if text.starts_with("(=>") {
            if violate_axiom {
                "false"
            } else {
                "true"
            }
        } else if text == "choose@1" || text == "choose@0" {
            if choose {
                "true"
            } else {
                "false"
            }
        } else if text.starts_with("send@") || text == "(= (Read_Int_Int b@2 0) 0)" {
            "true"
        } else if text.starts_with("idle@")
            || text.starts_with("(= 1 ")
            || text.starts_with("(= 2 ")
        {
            "false"
        } else if text.starts_with("(Read_Int_Int ") {
            "7"
        } else if text == "0" {
            "0"
        } else {
            anyhow::bail!("unexpected query {text}")
        }
        .into(),
    )
}

#[test]
fn follows_only_violated_branch_selected_updates_and_preserves_witness_frames() {
    let (index, types) = fixture();
    let trace = trace_violation(&index, &types, 2, 9, 200, |t| observation(t, false, false));
    assert!(!trace.budget_exhausted);
    assert!(!trace
        .nodes
        .iter()
        .any(|n| matches!(n.status, TraceStatus::EvaluationFailed { .. })));
    assert!(trace.nodes.iter().any(|n| n.status
        == TraceStatus::InitialState {
            array: "a@0".into()
        }));
    assert!(
        trace
            .nodes
            .iter()
            .filter(|n| matches!(n.reason, TraceReason::Transition { .. }))
            .count()
            == 2
    );
    assert!(!trace
        .nodes
        .iter()
        .any(|n| n.expression.to_string().starts_with("(Read_Int_Int b")
            || n.expression.to_string().starts_with("(= (Read_Int_Int b")));
    let array_nodes = trace
        .nodes
        .iter()
        .filter(|n| n.expression.to_string().starts_with("(Read_Int_Int"));
    for n in array_nodes {
        assert!(n.expression.to_string().contains("(witness a@2)"));
        assert!(!n.expression.to_string().contains("(witness a@1)"));
    }
    assert!(trace.nodes.iter().any(|n| n
        .conditions
        .iter()
        .any(|c| c.expression.to_string() == "choose@1" && c.value == "false")));
    let changed = trace_violation(&index, &types, 2, 10, 200, |t| observation(t, true, false));
    assert!(changed
        .nodes
        .iter()
        .any(|n| n.expression.to_string().contains("Write_Int_Int a@1 1 10")));
    assert!(!changed
        .nodes
        .iter()
        .any(|n| n.expression.to_string().contains("Write_Int_Int a@1 2 20")));
    let json = serde_json::to_string(&trace).unwrap();
    let restored: CountermodelTrace = serde_json::from_str(&json).unwrap();
    assert_eq!(
        restored.nodes.last().unwrap().expression,
        trace.nodes.last().unwrap().expression
    );
}

#[test]
fn stops_at_the_actual_violated_array_axiom_and_reports_its_formula() {
    let (index, types) = fixture();
    let trace = trace_violation(&index, &types, 2, 1, 200, |t| observation(t, false, true));
    let blocked = trace
        .nodes
        .iter()
        .find(|n| n.status == TraceStatus::ViolatedArrayAxiom)
        .unwrap();
    let lemma = blocked.lemma.as_ref().unwrap();
    assert_eq!(lemma.model_value.as_deref(), Some("false"));
    assert!(lemma
        .formula
        .to_string()
        .contains("(not (= 2 (witness a@2)))"));
    assert!(!trace
        .nodes
        .iter()
        .any(|n| matches!(n.status, TraceStatus::InitialState { .. })));
}

#[test]
fn budgets_and_evaluation_errors_are_explicit_not_proofs() {
    let (index, types) = fixture();
    for limit in 0..30 {
        let mut queries = 0;
        let trace = trace_violation(&index, &types, 2, 1, limit, |t| {
            queries += 1;
            observation(t, false, false)
        });
        assert!(trace.work <= limit);
        assert!(queries <= limit);
        assert!(trace.budget_exhausted);
        assert!(trace
            .nodes
            .iter()
            .any(|n| n.status == TraceStatus::BudgetExhausted));
    }
    let trace = trace_violation(&index, &types, 2, 1, 200, |_| {
        anyhow::bail!("model unavailable")
    });
    assert!(matches!(
        trace.nodes[0].status,
        TraceStatus::EvaluationFailed { .. }
    ));
}

#[test]
fn normal_driver_exposes_model_local_traces_without_changing_installed_instances() {
    use crate::{policy::term_selection::array::ArrayAstSize, SolverBackend, YardbirdOptions};
    let input = r#"
        (declare-fun a () (Array Int Int))
        (declare-fun an () (Array Int Int))
        (define-fun .a () (Array Int Int) (! a :next an))
        (define-fun init () Bool (! (= a ((as const (Array Int Int)) 0)) :init true))
        (define-fun trans () Bool (! (= an (store a 1 10)) :trans true))
        (define-fun prop () Bool (! (= (select a 2) 0) :invar-property 0))
    "#;
    let mut results = vec![];
    for trace_work in [0, 200] {
        let mut options = YardbirdOptions::from_filename("trace.vmt".into());
        options.countermodel_trace_work = trace_work;
        options.profile = true;
        let strategy = crate::strategies::Abstract::<ArrayAstSize>::new(
            3,
            false,
            crate::YardbirdPolicy::new(()),
            true,
        )
        .with_countermodel_trace_work(trace_work);
        let mut driver = crate::Driver::new(
            model(input),
            options.build_instantiation_strategy(),
            SolverBackend::Z3,
        )
        .with_profiler(options.build_profiler())
        .with_wall_timeout(Some(std::time::Duration::from_secs(10)));
        let result = driver.check_strategy(3, Box::new(strategy)).unwrap();
        assert!(!result.counterexample);
        if trace_work > 0 {
            let traces = result
                .profiling
                .cost_records
                .iter()
                .filter_map(|r| r.countermodel_trace.as_ref())
                .collect::<Vec<_>>();
            assert!(!traces.is_empty());
            assert!(traces.iter().any(|t| t.depth > 0
                && t.nodes
                    .iter()
                    .any(|n| matches!(n.reason, TraceReason::Transition { .. }))));
            assert!(traces.iter().all(|t| !t.budget_exhausted));
        }
        let mut installed = result
            .profiling
            .cost_records
            .iter()
            .flat_map(|record| record.installations.iter().map(|i| i.term.clone()))
            .collect::<Vec<_>>();
        installed.sort();
        results.push((result.total_instantiations_added, installed));
    }
    assert_eq!(results[0], results[1]);
}

#[test]
fn direct_store_hit_and_constant_array_expose_sound_blocking_lemmas() {
    for expression in [
        "(select (store a 2 5) 2)",
        "(select ((as const (Array Int Int)) 5) 2)",
    ] {
        let input = format!("(declare-fun a () (Array Int Int)) (define-fun init () Bool (! true :init true)) (define-fun trans () Bool (! true :trans true)) (define-fun prop () Bool (! (= {expression} 5) :invar-property 0))");
        let (model, types) = model(&input).abstract_array_theory();
        let index = TransitionIndex::from_model(&model, &HashSet::new());
        let trace = trace_violation(&index, &types, 0, 1, 100, |t| {
            let text = t.to_string();
            Ok(if text == "(= 2 2)" {
                "true"
            } else if text.starts_with("(=") {
                "false"
            } else if text.starts_with("(Read_") {
                "7"
            } else {
                "5"
            }
            .into())
        });
        let blocked = trace
            .nodes
            .iter()
            .find(|n| n.status == TraceStatus::ViolatedArrayAxiom)
            .unwrap();
        let formula = blocked
            .lemma
            .as_ref()
            .unwrap()
            .formula
            .to_string()
            .replace("Read_Int_Int", "select")
            .replace("Write_Int_Int", "store")
            .replace("ConstArr_Int_Int", "(as const (Array Int Int))");
        let solver = z3::Solver::new();
        solver.from_string(format!(
            "(declare-const a@0 (Array Int Int)) (assert (not {formula}))"
        ));
        assert_eq!(solver.check(), z3::SatResult::Unsat);
    }
}

fn initial_equality_fixture(initial: &str) -> (TransitionIndex, Vec<(String, String)>) {
    let text = format!(
        "(declare-fun a () (Array Int (Array Int Int)))
         (declare-fun an () (Array Int (Array Int Int)))
         (declare-fun b () (Array Int (Array Int Int)))
         (declare-fun bn () (Array Int (Array Int Int)))
         (declare-fun c () (Array Int (Array Int Int)))
         (declare-fun cn () (Array Int (Array Int Int)))
         (declare-fun gate () Bool) (declare-fun gaten () Bool)
         (declare-fun witness ((Array Int (Array Int Int))) Int)
         (define-fun .a () (Array Int (Array Int Int)) (! a :next an))
         (define-fun .b () (Array Int (Array Int Int)) (! b :next bn))
         (define-fun .c () (Array Int (Array Int Int)) (! c :next cn))
         (define-fun .gate () Bool (! gate :next gaten))
         (define-fun empty () (Array Int (Array Int Int))
           ((as const (Array Int (Array Int Int))) ((as const (Array Int Int)) 0)))
         (define-fun start () Bool {initial})
         (define-fun init () Bool (! start :init true))
         (define-fun trans () Bool
           (! (and (= an a) (= bn b) (= cn c) (= gaten gate)) :trans true))
         (define-fun prop () Bool
           (! (= (select (select a (witness a)) 0) 0) :invar-property 0))"
    );
    let (model, types) = model(&text).abstract_array_theory();
    (TransitionIndex::from_model(&model, &HashSet::new()), types)
}

fn initial_equality_observation(
    term: &Term,
    gate: ModelEvaluation,
    equality: ModelEvaluation,
) -> anyhow::Result<ModelEvaluation> {
    let text = term.to_string();
    Ok(if text == "gate@0" {
        gate
    } else if text.starts_with("(= (Read_") {
        // A spurious property read and the constant-array instance blocking it.
        "false".into()
    } else if text.starts_with("(=") {
        equality
    } else if text.starts_with("(Read_") {
        "7".into()
    } else if text == "0" {
        "0".into()
    } else {
        anyhow::bail!("unexpected query {text}")
    })
}

#[test]
fn initial_equalities_follow_reversed_definitions_and_alias_cycles_preserving_indices() {
    for initial in ["(= empty a)", "(and (= a b) (= b c) (= c a) (= empty c))"] {
        let (index, types) = initial_equality_fixture(initial);
        let trace = trace_violation(&index, &types, 2, 1, 256, |term| {
            initial_equality_observation(term, "true".into(), "true".into())
        });
        assert!(!trace.budget_exhausted);
        let initial = trace
            .nodes
            .iter()
            .find(|node| matches!(node.reason, TraceReason::Initialization { .. }))
            .expect("source equalities should expose the nested constant array");
        assert!(initial.lemma.is_none());
        assert!(initial.conditions.iter().all(|c| c.value == "true"));
        let blocked = trace
            .nodes
            .iter()
            .find(|node| node.status == TraceStatus::ViolatedArrayAxiom)
            .expect("the existing array rule must supply the blocking lemma");
        let formula = blocked.lemma.as_ref().unwrap().formula.to_string();
        assert!(formula.contains("(witness a@2)"), "{formula}");
        assert!(!formula.contains("(witness a@0)"));
        assert!(formula.contains("ConstArr_Int_Array_Int_Int"));
        assert!(trace.nodes.iter().all(|node| !matches!(
            node.status,
            TraceStatus::InconsistentStep | TraceStatus::EvaluationFailed { .. }
        )));
    }
}

#[test]
fn initial_equality_branches_keep_unknown_frontiers_without_hiding_known_paths() {
    for initial in [
        "(and (=> gate (= a b)) (= empty a))",
        "(and (= empty a) (=> gate (= a b)))",
        "(and (=> gate (= a b)) (= a b) (= b empty))",
        "(and (= a b) (=> gate (= a b)) (= b empty))",
        "(and (= a b) (= empty a))",
    ] {
        let (index, types) = initial_equality_fixture(initial);
        let unknown_equality = initial == "(and (= a b) (= empty a))";
        for limit in [0, 5, 20, 40, 80, 512] {
            let mut queries = 0;
            let trace = trace_violation(&index, &types, 2, 1, limit, |term| {
                queries += 1;
                if unknown_equality && term.to_string() == "(= a@0 b@0)" {
                    return Ok(ModelEvaluation::Undetermined);
                }
                initial_equality_observation(term, ModelEvaluation::Undetermined, "true".into())
            });
            assert!(trace.work <= limit && queries <= limit);
            if limit != 512 {
                continue;
            }
            assert!(!trace.budget_exhausted, "{initial}");
            assert!(
                trace.nodes.iter().any(|node| matches!(
                    &node.status,
                    TraceStatus::Undetermined { expression }
                        if expression == if unknown_equality { "(= a@0 b@0)" } else { "gate@0" }
                )),
                "the unknown branch must remain visible: {initial}"
            );
            assert!(
                trace
                    .nodes
                    .iter()
                    .any(|node| node.status == TraceStatus::ViolatedArrayAxiom),
                "an unknown sibling must not hide the constant initializer: {initial}"
            );
            assert!(trace
                .nodes
                .iter()
                .filter(|node| matches!(node.reason, TraceReason::Initialization { .. }))
                .all(|node| node.lemma.is_none()));
        }
    }
}

#[test]
fn initial_equality_branches_explore_each_known_initializer() {
    let (index, types) = initial_equality_fixture(
        "(and (= a empty) (= a (store empty 1 ((as const (Array Int Int)) 0))))",
    );
    let trace = trace_violation(&index, &types, 2, 1, 512, |term| {
        initial_equality_observation(term, "true".into(), "true".into())
    });
    assert!(!trace.budget_exhausted);
    let blocking = trace
        .nodes
        .iter()
        .filter(|node| node.status == TraceStatus::ViolatedArrayAxiom)
        .map(|node| node.lemma.as_ref().unwrap().formula.to_string())
        .collect::<Vec<_>>();
    assert!(
        blocking
            .iter()
            .any(|formula| formula.contains("Write_Int_Array_Int_Int")),
        "{blocking:?}"
    );
    assert!(
        blocking
            .iter()
            .any(|formula| !formula.contains("Write_Int_Array_Int_Int")),
        "{blocking:?}"
    );
}

#[test]
fn initial_equalities_respect_guards_and_partial_evaluation_across_models() {
    let (index, types) = initial_equality_fixture("(=> gate (= a empty))");
    for (version, gate, equality, blocked, undetermined) in [
        (1, "true".into(), "true".into(), true, false),
        (2, "false".into(), "true".into(), false, false),
        (3, ModelEvaluation::Undetermined, "true".into(), false, true),
        (4, "true".into(), ModelEvaluation::Undetermined, false, true),
    ] {
        let trace = trace_violation(&index, &types, 2, version, 256, |term| {
            initial_equality_observation(term, gate.clone(), equality.clone())
        });
        assert_eq!(
            trace
                .nodes
                .iter()
                .any(|node| node.status == TraceStatus::ViolatedArrayAxiom),
            blocked
        );
        assert_eq!(
            trace
                .nodes
                .iter()
                .any(|node| matches!(node.status, TraceStatus::Undetermined { .. })),
            undetermined
        );
        if blocked {
            let initial = trace
                .nodes
                .iter()
                .find(|node| matches!(node.reason, TraceReason::Initialization { .. }))
                .unwrap();
            assert!(initial
                .conditions
                .iter()
                .any(|c| c.expression.to_string() == "gate@0" && c.value == "true"));
        }
    }
}

#[test]
fn initial_equalities_do_not_follow_negation_or_loop_without_a_value() {
    for initial in ["(not (= a empty))", "(and (= a b) (= b c) (= c a))"] {
        let (index, types) = initial_equality_fixture(initial);
        for limit in [0, 5, 20, 256] {
            let mut queries = 0;
            let trace = trace_violation(&index, &types, 2, 1, limit, |term| {
                queries += 1;
                initial_equality_observation(term, "true".into(), "true".into())
            });
            assert!(trace.work <= limit);
            assert!(queries <= limit);
            assert!(!trace.nodes.iter().any(|node| node.lemma.is_some()));
            if limit == 256 {
                assert!(!trace.budget_exhausted);
                assert!(trace
                    .nodes
                    .iter()
                    .any(|node| matches!(node.status, TraceStatus::InitialState { .. })));
            }
        }
    }
}

#[test]
fn initial_equalities_retain_the_false_ite_branch_guard() {
    let (index, types) = initial_equality_fixture("(ite gate (= a b) (= empty a))");
    let trace = trace_violation(&index, &types, 2, 1, 256, |term| {
        initial_equality_observation(term, "false".into(), "true".into())
    });
    let initial = trace
        .nodes
        .iter()
        .find(|node| matches!(node.reason, TraceReason::Initialization { .. }))
        .unwrap();
    assert!(initial
        .conditions
        .iter()
        .any(|c| { c.expression.to_string() == "gate@0" && c.value == "false" }));
    assert!(trace
        .nodes
        .iter()
        .any(|node| node.status == TraceStatus::ViolatedArrayAxiom));
}

#[test]
fn trace_options_enable_serialization_and_reject_unsupported_modes() {
    use clap::Parser;
    let options = crate::YardbirdOptions::parse_from([
        "yardbird",
        "-f",
        "test.vmt",
        "--countermodel-trace-work",
        "80",
    ]);
    assert!(options.build_profiler().is_some());
    options.validate_countermodel_trace_options().unwrap();
    let mut options = options;
    options.strategy = crate::Strategy::Concrete;
    assert!(options.validate_countermodel_trace_options().is_err());
    options.strategy = crate::Strategy::Abstract;
    options.filename = Some("test.smt2".into());
    assert!(options.validate_countermodel_trace_options().is_err());
    options.filename = Some("test.vmt".into());
    options.strategy = crate::Strategy::Concrete;
    assert!(options.validate_countermodel_trace_options().is_err());
    options.strategy = crate::Strategy::Abstract;
    // cvc5's `eval_partial` only answers from an already-captured value and
    // never issues a fresh query, so guidance would silently find almost
    // nothing rather than fail; reject the combination instead.
    options.solver = crate::SolverBackend::Cvc5;
    assert!(options.validate_countermodel_trace_options().is_err());
}

#[derive(Clone, Debug)]
struct RejectTracedInstances;
impl crate::policy::instance_selection::InstantiationRanker for RejectTracedInstances {
    fn clone_box(&self) -> Box<dyn crate::policy::instance_selection::InstantiationRanker> {
        Box::new(self.clone())
    }
    fn compare(
        &self,
        left: &crate::rule_matching::candidate::InstantiationCandidate,
        right: &crate::rule_matching::candidate::InstantiationCandidate,
    ) -> std::cmp::Ordering {
        left.cost.cmp(&right.cost)
    }
    fn is_eligible(
        &self,
        candidate: &crate::rule_matching::candidate::InstantiationCandidate,
        _: crate::rule_matching::scope::CandidateScope,
    ) -> bool {
        candidate.provenance.countermodel_origin().is_none()
    }
}

// DefaultEffort deliberately fixes guided work independently of its ordinary
// allowance. Override the actual operation to test small guided budgets.
struct GuidanceBudget {
    inner: crate::policy::DefaultEffort,
    work: usize,
}
impl crate::policy::effort::ProofEffort for GuidanceBudget {
    fn uses_countermodel_refinement(&self) -> bool {
        true
    }
    fn choose(
        &mut self,
        context: &crate::policy::effort::EffortContext<'_>,
    ) -> crate::policy::effort::EffortDecision {
        use crate::policy::effort::{EffortDecision, OperationKind};
        let mut decision = self.inner.choose(context);
        if let EffortDecision::Execute {
            operation,
            allowance,
        } = &mut decision
        {
            if context
                .operations
                .iter()
                .any(|op| op.id == *operation && op.kind == OperationKind::CountermodelCandidates)
            {
                allowance.dependency_work = self.work;
            }
        }
        decision
    }
    fn choose_binder_rule(
        &mut self,
        context: &crate::policy::effort::BinderEffortContext<'_>,
    ) -> Option<usize> {
        self.inner.choose_binder_rule(context)
    }
    fn observe(&mut self, event: &crate::policy::effort::EffortEvent<'_>) {
        self.inner.observe(event);
    }
    fn egraph_builder(
        &self,
    ) -> Box<dyn crate::theories::array::array_egraph_builder::ArrayEGraphBuilder> {
        self.inner.egraph_builder()
    }
    fn requires_property_cone(&self) -> bool {
        self.inner.requires_property_cone()
    }
}

#[test]
fn traced_axioms_reach_shared_ranking_and_installation_without_requiring_profiling() {
    use crate::{policy::term_selection::array::ArrayAstSize, SolverBackend, YardbirdOptions};
    // Two distinct instances of the same axiom exercise the ordinary winner
    // budget, then retracing under the new model after installation.
    let input = r#"
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)
        (declare-fun v () Int)
        (define-fun init () Bool (! true :init true))
        (define-fun trans () Bool (! true :trans true))
        (define-fun prop () Bool (!
          (and
            (=> (not (= i j)) (= (select (store a i v) j) (select a j)))
            (=> (not (= (+ i 1) j)) (= (select (store a (+ i 1) v) j) (select a j))))
          :invar-property 0))
    "#;
    let mut accepted = None;
    for (profile, reject, work) in [
        (true, false, 512),
        (false, false, 512),
        (true, true, 512),
        (true, false, 1),
    ] {
        let mut options = YardbirdOptions::from_filename("trace.vmt".into());
        options.profile = profile;
        let mut policy =
            crate::YardbirdPolicy::<ArrayAstSize>::new(()).with_effort(GuidanceBudget {
                inner: crate::policy::DefaultEffort::default().with_countermodel_refinement(true),
                work,
            });
        if reject {
            policy = policy.with_instantiation_ranker(Box::new(RejectTracedInstances));
        }
        let strategy = crate::strategies::Abstract::new(1, false, policy, profile)
            .with_exact_read_after_write_preprocessing(false);
        let mut driver = crate::Driver::new(
            model(input),
            options.build_instantiation_strategy(),
            SolverBackend::Z3,
        )
        .with_profiler(options.build_profiler())
        .with_wall_timeout(Some(std::time::Duration::from_secs(10)));
        let result = driver.check_strategy(1, Box::new(strategy)).unwrap();
        assert!(!result.counterexample);
        assert!(result.total_instantiations_added > 0);
        if !profile {
            assert_eq!(Some(result.total_instantiations_added), accepted);
            continue;
        }
        let mut traced = 0;
        let mut selected = 0;
        let mut models = HashSet::new();
        for record in &result.profiling.cost_records {
            for effort in &record.effort {
                if effort.operation != "CountermodelCandidates" {
                    continue;
                }
                let trace = record.countermodel_trace.as_ref().unwrap();
                models.insert(trace.model_version);
                assert_eq!(trace.budget_exhausted, work == 1);
                assert!(effort.report.selected <= 1);
                for candidate in &effort.candidates {
                    let origin = candidate.countermodel_origin.as_ref().unwrap();
                    assert_eq!(origin.model_version, trace.model_version);
                    let node = &trace.nodes[origin.node];
                    assert_eq!(node.status, TraceStatus::ViolatedArrayAxiom);
                    assert_eq!(
                        node.lemma.as_ref().unwrap().model_value.as_deref(),
                        Some("false")
                    );
                    traced += 1;
                    selected += usize::from(candidate.selected);
                    if candidate.selected {
                        assert!(record
                            .installations
                            .iter()
                            .any(|i| i.abstract_instantiation_id.as_deref()
                                == Some(candidate.abstract_instantiation_id.as_str())));
                    }
                }
            }
        }
        if work == 1 {
            assert_eq!(traced, 0);
            assert!(!models.is_empty());
            continue;
        }
        assert!(traced > 0);
        if reject {
            assert_eq!(
                selected, 0,
                "ranker must be able to reject traced candidates"
            );
        } else {
            assert!(selected >= 2);
            assert!(
                models.len() >= 2,
                "fresh models must get fresh explanations"
            );
            accepted = Some(result.total_instantiations_added);
        }
    }
}

#[test]
fn countermodel_policy_needs_no_numeric_switch_or_profiling() {
    use clap::Parser;
    let options = crate::YardbirdOptions::parse_from([
        "yardbird",
        "-f",
        "test.vmt",
        "--policy",
        "countermodel-guided",
    ]);
    assert_eq!(options.countermodel_trace_work, 0);
    assert!(!options.profiling_enabled());
    options.validate_countermodel_trace_options().unwrap();
    let mut options = options;
    options.filename = Some("test.smt2".into());
    assert!(options.validate_countermodel_trace_options().is_err());
    options.filename = Some("test.vmt".into());
    options.strategy = crate::Strategy::Concrete;
    options.validate_countermodel_trace_options().unwrap();
    options.policy = None;
    options.countermodel_trace_work = 1;
    assert!(options.validate_countermodel_trace_options().is_err());
}

#[test]
fn quantified_initializers_are_installed_from_the_read_trace() {
    use crate::{policy::term_selection::array::ArrayAstSize, SolverBackend, YardbirdOptions};
    let input = r#"
        (declare-fun a () (Array Int (Array Int Int)))
        (declare-fun an () (Array Int (Array Int Int)))
        (define-fun .a () (Array Int (Array Int Int)) (! a :next an))
        (define-fun initialized () Bool
          (forall ((x Int)) (forall ((y Int)) (= (select (select a x) y) (+ x y)))))
        (define-fun init () Bool (! initialized :init true))
        (define-fun trans () Bool (! (= an a) :trans true))
        (define-fun prop () Bool (! (= (select (select a 4) 9) 13) :invar-property 0))
    "#;
    for (profile, reject) in [(true, false), (false, false), (true, true)] {
        let mut options = YardbirdOptions::from_filename("initializer.vmt".into());
        options.profile = profile;
        let mut policy = crate::YardbirdPolicy::<ArrayAstSize>::new(()).with_effort(
            crate::policy::DefaultEffort::default().with_countermodel_refinement(true),
        );
        if reject {
            policy = policy.with_instantiation_ranker(Box::new(RejectTracedInstances));
        }
        let strategy = crate::strategies::Abstract::new(3, false, policy, profile);
        let mut driver = crate::Driver::new(
            model(input),
            options.build_instantiation_strategy(),
            SolverBackend::Z3,
        )
        .with_profiler(options.build_profiler())
        .with_wall_timeout(Some(std::time::Duration::from_secs(10)));
        let result = driver.check_strategy(3, Box::new(strategy)).unwrap();
        assert_eq!(
            result
                .run_progress
                .as_ref()
                .unwrap()
                .deepest_completed_depth,
            Some(2)
        );
        assert!(!result.counterexample);
        if !profile {
            continue;
        }
        let mut selected = 0;
        let mut candidates = 0;
        let mut handed_off = 0;
        for record in &result.profiling.cost_records {
            let Some(trace) = &record.countermodel_trace else {
                continue;
            };
            assert!(!trace.budget_exhausted);
            assert!(!trace.nodes.iter().any(|node| matches!(
                node.status,
                TraceStatus::EvaluationFailed { .. } | TraceStatus::InconsistentStep
            )));
            for effort in &record.effort {
                if effort.operation == "DiscoverDependencies" {
                    for candidate in &effort.candidates {
                        let Some(origin) = &candidate.countermodel_origin else {
                            continue;
                        };
                        if origin.model_version != trace.model_version {
                            continue;
                        }
                        let node = &trace.nodes[origin.node];
                        if !matches!(node.reason, TraceReason::UnresolvedInitialization { .. }) {
                            continue;
                        }
                        assert!(matches!(node.status, TraceStatus::Undetermined { .. }));
                        assert!(node.lemma.as_ref().unwrap().model_value.is_none());
                        assert_eq!(candidate.selected, !reject);
                        if candidate.selected {
                            handed_off += 1;
                            assert!(record.installations.iter().any(|i| i
                                .abstract_instantiation_id
                                .as_deref()
                                == Some(&candidate.abstract_instantiation_id)
                                && i.result
                                    .as_ref()
                                    .is_some_and(|r| r.solver_assertions_added() > 0)));
                        }
                    }
                }
                if effort.operation != "CountermodelCandidates" {
                    continue;
                }
                for candidate in &effort.candidates {
                    let node = &trace.nodes[candidate.countermodel_origin.as_ref().unwrap().node];
                    if node.status != TraceStatus::ViolatedQuantifierInstance {
                        continue;
                    }
                    candidates += 1;
                    assert!(matches!(node.reason, TraceReason::Initialization { .. }));
                    assert_eq!(
                        node.lemma.as_ref().unwrap().model_value.as_deref(),
                        Some("false")
                    );
                    if candidate.selected {
                        selected += 1;
                        assert!(record.installations.iter().any(|i| i
                            .abstract_instantiation_id
                            .as_deref()
                            == Some(&candidate.abstract_instantiation_id)
                            && i.result
                                .as_ref()
                                .is_some_and(|r| r.solver_assertions_added() > 0)));
                    }
                }
            }
        }
        assert!(candidates > 0);
        if reject {
            assert_eq!(selected, 0);
        } else {
            assert!(selected > 0);
            assert!(handed_off > 0);
        }
    }
}

#[test]
fn initializer_matching_preserves_captures_and_finds_each_broken_binder_link() {
    use crate::theories::quantifiers::{
        countermodel::InitializerSearch, BinderKind, BinderRule, QuantifierPlan,
    };
    use smt2parser::{concrete::Symbol, vmt::array_abstractor::string_to_sort};
    let input = r#"
        (declare-fun a () (Array Int (Array Int Int)))
        (declare-fun an () (Array Int (Array Int Int)))
        (declare-fun zero () Int)
        (declare-fun w ((Array Int (Array Int Int))) Int)
        (define-fun .a () (Array Int (Array Int Int)) (! a :next an))
        (define-fun init () Bool (! true :init true))
        (define-fun trans () Bool (! (= an a) :trans true))
        (define-fun prop () Bool (! true :invar-property 0))
    "#;
    let (model, types) = model(input).abstract_array_theory();
    let index = TransitionIndex::from_model(&model, &HashSet::new());
    let arr = string_to_sort("Array_Int_Array_Int_Int");
    let int = string_to_sort("Int");
    let fields = |names: &[&str]| {
        names
            .iter()
            .map(|name| {
                (
                    Symbol((*name).into()),
                    if *name == "a" {
                        arr.clone()
                    } else {
                        int.clone()
                    },
                )
            })
            .collect()
    };
    let mut plan = QuantifierPlan::default();
    plan.rules = vec![
        BinderRule {
            name: "outer".into(),
            kind: BinderKind::Forall,
            captures: fields(&["a", "z"]),
            variables: fields(&["x"]),
            body: "(inner a z x)".parse().unwrap(),
            witnesses: vec![],
            result_sort: string_to_sort("Bool"),
            unit_capture: false,
        },
        BinderRule {
            name: "inner".into(),
            kind: BinderKind::Forall,
            captures: fields(&["a", "z", "x"]),
            variables: fields(&["y"]),
            body: "(= (Read_Int_Int (Read_Int_Array_Int_Int a x) y) (+ z x y))"
                .parse()
                .unwrap(),
            witnesses: vec![],
            result_sort: string_to_sort("Bool"),
            unit_capture: false,
        },
    ];
    plan.signatures
        .insert("w".into(), (vec![arr.clone()], int.clone()));
    plan.signatures.insert("a".into(), (vec![], arr));
    plan.signatures.insert("zero".into(), (vec![], int));
    let root: Term = "(outer a@0 zero)".parse().unwrap();
    let read: Term = "(Read_Int_Int (Read_Int_Array_Int_Int a@0 (w a@2)) 9)"
        .parse()
        .unwrap();
    for broken in 0..3 {
        let mut search = InitializerSearch::new(&plan, root.clone());
        let mut evaluate = |term: &Term| {
            let s = term.to_string();
            Ok(if s.starts_with("(=> (outer") {
                if broken == 0 {
                    "false"
                } else {
                    "true"
                }
            } else if s.starts_with("(=> (inner") {
                if broken == 1 {
                    "false"
                } else {
                    "true"
                }
            } else {
                "true"
            }
            .into())
        };
        let mut cx = TraceContext {
            index: &index,
            types: &types,
            evaluate: &mut evaluate,
            remaining: 200,
            initializers: None,
            transitions: None,
        };
        let steps = search
            .steps(&read, &mut cx)
            .unwrap_or_else(|_| panic!("initializer search failed"));
        assert_eq!(steps.len(), 1);
        let step = &steps[0];
        let TraceReason::Initialization { path } = &step.reason else {
            panic!("missing initialization path")
        };
        assert_eq!(path.len(), broken);
        for lemma in path.iter().chain(step.lemma.iter()) {
            let text = lemma.formula.to_string();
            assert!(text.contains("a@0 zero (w a@2)"));
            assert!(!text.contains("(w a@0)"));
            assert!(lemma
                .instance
                .as_ref()
                .unwrap()
                .bindings
                .iter()
                .any(|(_, term)| term.to_string() == "zero"));
        }
        if broken < 2 {
            assert_eq!(
                step.lemma.as_ref().unwrap().rule,
                if broken == 0 {
                    "input-binder-outer"
                } else {
                    "input-binder-inner"
                }
            );
        } else {
            assert!(step.lemma.is_none());
            assert_eq!(step.term.to_string(), "(+ zero (w a@2) 9)");
        }
    }
    // An unknown helper or full implication preserves the exact guarded
    // instance, but never authorizes following its initializer equation.
    for (unknown, expected_path) in [("(=> (outer", 0), ("(inner", 1), ("(=> (inner", 1)] {
        let mut search = InitializerSearch::new(&plan, root.clone());
        let mut evaluate = |term: &Term| {
            Ok(if term.to_string().starts_with(unknown) && term != &root {
                ModelEvaluation::Undetermined
            } else {
                "true".into()
            })
        };
        let mut cx = TraceContext {
            index: &index,
            types: &types,
            evaluate: &mut evaluate,
            remaining: 200,
            initializers: None,
            transitions: None,
        };
        let steps = search
            .steps(&read, &mut cx)
            .unwrap_or_else(|_| panic!("matching failed"));
        let step = &steps[0];
        let TraceReason::UnresolvedInitialization { path, expression } = &step.reason else {
            panic!("missing unresolved initializer");
        };
        assert_eq!(path.len(), expected_path);
        assert!(expression.starts_with(unknown));
        let lemma = step.lemma.as_ref().unwrap();
        assert!(lemma.model_value.is_none());
        assert_eq!(step.term, lemma.instance.as_ref().unwrap().term);
        assert!(step.term.to_string().contains("a@0 zero (w a@2)"));
        assert_ne!(step.term.to_string(), "(+ zero (w a@2) 9)");
    }
    // Initializer bodies hidden under disjunction are not unconditional.
    let mut conditional =
        InitializerSearch::new(&plan, "(or (outer a@0 zero) unrelated)".parse().unwrap());
    let mut evaluate = |_: &Term| Ok("true".into());
    let mut cx = TraceContext {
        index: &index,
        types: &types,
        evaluate: &mut evaluate,
        remaining: 200,
        initializers: None,
        transitions: None,
    };
    assert!(conditional
        .steps(&read, &mut cx)
        .unwrap_or_else(|_| panic!("conditional matching failed"))
        .is_empty());
    for budget in 0..4 {
        let mut search = InitializerSearch::new(&plan, root.clone());
        let mut cx = TraceContext {
            index: &index,
            types: &types,
            evaluate: &mut evaluate,
            remaining: budget,
            initializers: None,
            transitions: None,
        };
        assert!(matches!(
            search.steps(&read, &mut cx),
            Err(TraceError::Budget)
        ));
    }
    // A different captured array is not interchangeable, even if a model
    // might equate it with a@0. A frame-zero initializer also cannot match a@1.
    for other in ["b@0", "a@1"] {
        let mut search = InitializerSearch::new(&plan, root.clone());
        let mut evaluate = |_: &Term| Ok("true".into());
        let mut cx = TraceContext {
            index: &index,
            types: &types,
            evaluate: &mut evaluate,
            remaining: 200,
            initializers: None,
            transitions: None,
        };
        let other_read = read.to_string().replace("a@0", other).parse().unwrap();
        assert!(search
            .steps(&other_read, &mut cx)
            .unwrap_or_else(|_| panic!("matching failed"))
            .is_empty());
    }
}

#[test]
fn opaque_relations_join_traced_atoms_through_shared_ranking() {
    use crate::{policy::term_selection::array::ArrayAstSize, SolverBackend, YardbirdOptions};
    let input = r#"
        (declare-sort item 0)
        (declare-fun rel (item item) Bool)
        (declare-fun a () item)
        (declare-fun b () item)
        (declare-fun c () item)
        (assert (forall ((x item) (y item) (z item))
          (=> (and (rel x y) (rel y z)) (rel x z))))
        (define-fun init () Bool (! true :init true))
        (define-fun trans () Bool (! true :trans true))
        (define-fun prop () Bool
          (! (and (=> (and (rel a b) (rel b c)) (rel a c))
                  (=> (and (rel c b) (rel b a)) (rel c a))) :invar-property 0))
    "#;
    let mut profiled_count = None;
    for (profile, reject) in [(true, false), (false, false), (true, true)] {
        let mut options = YardbirdOptions::from_filename("relations.vmt".into());
        options.profile = profile;
        let mut policy = crate::YardbirdPolicy::<ArrayAstSize>::new(()).with_effort(
            crate::policy::DefaultEffort::default().with_countermodel_refinement(true),
        );
        if reject {
            policy = policy.with_instantiation_ranker(Box::new(RejectTracedInstances));
        }
        let strategy = crate::strategies::Abstract::new(1, false, policy, profile);
        let mut driver = crate::Driver::new(
            model(input),
            options.build_instantiation_strategy(),
            SolverBackend::Z3,
        )
        .with_profiler(options.build_profiler())
        .with_wall_timeout(Some(std::time::Duration::from_secs(10)));
        let result = driver.check_strategy(1, Box::new(strategy)).unwrap();
        assert_eq!(
            result
                .run_progress
                .as_ref()
                .unwrap()
                .deepest_completed_depth,
            Some(0)
        );
        assert!(!result.counterexample);
        if !profile {
            assert_eq!(profiled_count, Some(result.total_instantiations_added));
            continue;
        }
        let mut produced = 0;
        let mut models = HashSet::new();
        let mut selected = 0;
        for record in &result.profiling.cost_records {
            let Some(trace) = &record.countermodel_trace else {
                continue;
            };
            assert!(!trace.budget_exhausted);
            for effort in &record.effort {
                if effort.operation != "CountermodelCandidates" {
                    continue;
                }
                for candidate in &effort.candidates {
                    let node = &trace.nodes[candidate.countermodel_origin.as_ref().unwrap().node];
                    let TraceReason::QuantifierMatch { anchors } = &node.reason else {
                        continue;
                    };
                    produced += 1;
                    models.insert(trace.model_version);
                    assert_eq!(node.status, TraceStatus::ViolatedQuantifierInstance);
                    assert_eq!(
                        node.lemma.as_ref().unwrap().model_value.as_deref(),
                        Some("false")
                    );
                    assert!(anchors.len() >= 2, "transitivity needs joined trace terms");
                    assert!(anchors.iter().all(|i| matches!(
                        trace.nodes[*i].status,
                        TraceStatus::Unsupported { .. }
                    )));
                    if candidate.selected {
                        selected += 1;
                        assert!(record
                            .installations
                            .iter()
                            .any(|i| i.abstract_instantiation_id.as_deref()
                                == Some(&candidate.abstract_instantiation_id)));
                    }
                }
            }
        }
        assert!(produced > 0);
        if reject {
            assert_eq!(selected, 0);
        } else {
            assert!(selected >= 2);
            assert!(models.len() >= 2);
            profiled_count = Some(result.total_instantiations_added);
        }
    }
}

#[test]
fn undetermined_property_sibling_does_not_hide_a_known_violated_read() {
    let (index, types) = fixture();
    let trace = trace_violation(&index, &types, 2, 1, 200, |term| {
        if term.to_string() == "(= (Read_Int_Int b@2 0) 0)" {
            Ok(ModelEvaluation::Undetermined)
        } else {
            observation(term, false, true)
        }
    });
    assert!(trace
        .nodes
        .iter()
        .any(|n| n.status == TraceStatus::ViolatedArrayAxiom));
    assert!(trace.nodes.iter().any(|n| matches!(&n.status, TraceStatus::Undetermined { expression } if expression == "(= (Read_Int_Int b@2 0) 0)")));
    assert!(!trace
        .nodes
        .iter()
        .any(|n| n.expression.to_string().starts_with("(Read_Int_Int b@")));
    assert!(!trace
        .nodes
        .iter()
        .any(|n| matches!(n.status, TraceStatus::EvaluationFailed { .. })));
}

#[test]
fn unresolved_index_equality_stops_only_the_guided_read_branch() {
    let (index, types) = fixture();
    let trace = trace_violation(&index, &types, 2, 1, 200, |term| {
        if term.to_string().starts_with("(= 2 ") {
            Ok(ModelEvaluation::Undetermined)
        } else {
            observation(term, false, true)
        }
    });
    assert!(trace.nodes.iter().any(|n| matches!(&n.status, TraceStatus::Undetermined { expression } if expression.starts_with("(= 2 "))));
    assert!(trace.candidate_pool().instances().is_empty());
    assert!(!trace
        .nodes
        .iter()
        .any(|n| matches!(n.status, TraceStatus::EvaluationFailed { .. })));
}

#[test]
fn guided_and_standard_candidates_can_be_installed_in_one_pass() {
    use crate::{
        policy::{effort::WorkAllowance, term_selection::array::ArrayBMCCost},
        SolverBackend, YardbirdOptions,
    };
    let input = std::fs::read_to_string(
        "examples/distributed_protocols/multi_paxos/multi_paxos.encoding.vmt",
    )
    .unwrap();
    let mut options = YardbirdOptions::from_filename("supplement.vmt".into());
    options.profile = true;
    let policy = crate::YardbirdPolicy::<ArrayBMCCost>::new(()).with_effort(
        crate::policy::DefaultEffort::default()
            .with_countermodel_refinement(true)
            .with_guidance_followup(Some(WorkAllowance {
                dependency_work: 128,
                ..Default::default()
            })),
    );
    let strategy = crate::strategies::Abstract::new(2, false, policy, true)
        .with_exact_read_after_write_preprocessing(false);
    let mut driver = crate::Driver::new(
        model(&input),
        options.build_instantiation_strategy(),
        SolverBackend::Z3,
    )
    .with_profiler(options.build_profiler())
    .with_wall_timeout(Some(std::time::Duration::from_secs(60)));
    let result = driver.check_strategy(2, Box::new(strategy)).unwrap();
    assert_eq!(
        result
            .run_progress
            .as_ref()
            .unwrap()
            .deepest_completed_depth,
        Some(1)
    );
    assert!(result.profiling.cost_records.iter().any(|record| {
        let operations: Vec<_> = record
            .effort
            .iter()
            .filter(|e| {
                e.operation == "CountermodelCandidates" || e.operation == "DiscoverDependencies"
            })
            .collect();
        operations.windows(2).any(|pair| {
            pair[0].operation == "CountermodelCandidates"
                && pair[0].report.selected > 0
                && pair[1].operation == "DiscoverDependencies"
                && pair[1].allowance.unwrap().dependency_work == 128
                && pair[1].report.selected > 0
                && record.installations.len() == pair[0].report.selected + pair[1].report.selected
        })
    }));
}

#[test]
fn action_requirements_obey_effort_and_ranking_without_profiling() {
    use crate::{
        policy::{
            effort::{ActionRequirementGuidance, WorkAllowance},
            term_selection::array::ArrayAstSize,
        },
        SolverBackend, YardbirdOptions,
    };
    let input = include_str!("../../tests/fixtures/action_requirement_trace.vmt");
    let mut profiled_count = None;
    for (profile, mode, reject, work) in [
        (
            true,
            ActionRequirementGuidance::WhenUnproductive,
            false,
            1024,
        ),
        (
            false,
            ActionRequirementGuidance::WhenUnproductive,
            false,
            1024,
        ),
        (true, ActionRequirementGuidance::Always, false, 1024),
        (true, ActionRequirementGuidance::Disabled, false, 1024),
        (true, ActionRequirementGuidance::Always, true, 1024),
        (true, ActionRequirementGuidance::Always, false, 32),
    ] {
        let mut options = YardbirdOptions::from_filename("requirements.vmt".into());
        options.profile = profile;
        let mut policy =
            crate::YardbirdPolicy::<ArrayAstSize>::new(()).with_effort(GuidanceBudget {
                inner: crate::policy::DefaultEffort::default()
                    .with_countermodel_refinement(true)
                    .with_allowance(WorkAllowance {
                        guidance_action_requirements: mode,
                        ..Default::default()
                    }),
                work,
            });
        if reject {
            policy = policy.with_instantiation_ranker(Box::new(RejectTracedInstances));
        }
        let strategy = crate::strategies::Abstract::new(3, false, policy, profile);
        let mut driver = crate::Driver::new(
            model(input),
            options.build_instantiation_strategy(),
            SolverBackend::Z3,
        )
        .with_profiler(options.build_profiler())
        .with_wall_timeout(Some(std::time::Duration::from_secs(10)));
        let result = driver.check_strategy(3, Box::new(strategy)).unwrap();
        assert_eq!(
            result
                .run_progress
                .as_ref()
                .unwrap()
                .deepest_completed_depth,
            Some(2)
        );
        assert!(!result.counterexample);
        if !profile {
            assert_eq!(profiled_count, Some(result.total_instantiations_added));
            continue;
        }
        let mut reached = 0;
        let mut exhausted = 0;
        let mut selected = 0;
        for record in &result.profiling.cost_records {
            let Some(trace) = &record.countermodel_trace else {
                continue;
            };
            assert!(trace.work <= work);
            exhausted += usize::from(trace.budget_exhausted);
            assert!(!trace.nodes.iter().any(|node| matches!(
                node.status,
                TraceStatus::InconsistentStep | TraceStatus::EvaluationFailed { .. }
            )));
            for effort in &record.effort {
                if effort.operation != "CountermodelCandidates" {
                    continue;
                }
                for candidate in &effort.candidates {
                    let Some(origin) = &candidate.countermodel_origin else {
                        continue;
                    };
                    assert_eq!(origin.model_version, trace.model_version);
                    let mut cursor = Some(origin.node);
                    while let Some(id) = cursor {
                        let node = &trace.nodes[id];
                        if matches!(&node.reason, TraceReason::ActionRequirement { action, .. } if action == "decide")
                        {
                            reached += 1;
                            selected += usize::from(candidate.selected);
                            break;
                        }
                        cursor = node.parent;
                    }
                }
            }
        }
        if work == 32 {
            assert!(exhausted > 0);
        } else if mode == ActionRequirementGuidance::Disabled {
            assert_eq!(reached, 0);
        } else {
            assert!(reached > 0);
            assert_eq!(selected == 0, reject);
        }
        if mode == ActionRequirementGuidance::WhenUnproductive {
            profiled_count = Some(result.total_instantiations_added);
        }
    }
}

#[test]
fn same_frame_equations_obey_assertion_bounds_guards_and_capture_frames() {
    use crate::theories::quantifiers::refinement::QuantifierRefinement;
    let input = r#"
      (declare-fun scratch () (Array Int Int))
      (declare-fun sn () (Array Int Int))
      (declare-fun votes () (Array Int Int))
      (declare-fun vn () (Array Int Int))
      (declare-fun w ((Array Int Int)) Int)
      (declare-fun tick () Bool)
      (define-fun .scratch () (Array Int Int) (! scratch :next sn))
      (define-fun .votes () (Array Int Int) (! votes :next vn))
      (define-fun .tick () Bool (! tick :action 0))
      (define-fun init () Bool (! true :init true))
      (define-fun trans () Bool (! (=> tick (forall ((i Int)) (= (select scratch i) (select votes i)))) :trans true))
      (define-fun prop () Bool (! true :invar-property 0))
    "#;
    let mut quantifiers = QuantifierRefinement::default();
    let lowered = quantifiers.configure_model(model(input), false);
    let (lowered, types) = lowered.abstract_array_theory();
    let index = TransitionIndex::from_model(
        &lowered,
        &quantifiers
            .plan
            .rules
            .iter()
            .map(|r| r.name.clone())
            .collect(),
    );
    let read: Term = "(Read_Int_Int scratch@0 (w votes@1))".parse().unwrap();
    for (depth, mode, guard, expected) in [
        (1, GuidanceTransitionOrder::CurrentFirst, "true", 1),
        (1, GuidanceTransitionOrder::PredecessorFirst, "true", 1),
        (1, GuidanceTransitionOrder::PredecessorOnly, "true", 0),
        (0, GuidanceTransitionOrder::CurrentFirst, "true", 0),
        (1, GuidanceTransitionOrder::CurrentFirst, "false", 0),
    ] {
        let mut search = TransitionSearch::new(&quantifiers.plan, depth, mode);
        let mut queries = 0;
        let mut evaluate = |term: &Term| {
            queries += 1;
            let text = term.to_string();
            Ok(if text == "tick@0" {
                guard
            } else if text.starts_with("(=>") {
                "false"
            } else {
                "true"
            }
            .into())
        };
        let mut cx = TraceContext {
            index: &index,
            types: &types,
            evaluate: &mut evaluate,
            remaining: 512,
            initializers: None,
            transitions: None,
        };
        let steps = search
            .steps(&read, &mut cx, true)
            .unwrap_or_else(|_| panic!("same-frame search failed"));
        assert_eq!(steps.len(), expected);
        for step in steps {
            assert!(matches!(
                step.reason,
                TraceReason::QuantifiedTransition { frame: 0, .. }
            ));
            let formula = step.lemma.unwrap().formula.to_string();
            assert!(formula.contains("scratch@0") && formula.contains("(w votes@1)"));
            assert!(!formula.contains("scratch@1") && !formula.contains("(w votes@0)"));
        }
        if depth == 0 || mode == GuidanceTransitionOrder::PredecessorOnly {
            assert_eq!(queries, 0);
        }
    }
    // The final state has no outgoing transition asserted, even if evaluating
    // its fresh action flag could accidentally return true in the model.
    let mut search =
        TransitionSearch::new(&quantifiers.plan, 1, GuidanceTransitionOrder::CurrentFirst);
    let mut evaluate = |_: &Term| -> anyhow::Result<ModelEvaluation> {
        panic!("must not query the unasserted frame")
    };
    let mut cx = TraceContext {
        index: &index,
        types: &types,
        evaluate: &mut evaluate,
        remaining: 512,
        initializers: None,
        transitions: None,
    };
    assert!(search
        .steps(
            &"(Read_Int_Int scratch@1 0)".parse().unwrap(),
            &mut cx,
            true
        )
        .unwrap_or_else(|_| panic!("search failed"))
        .is_empty());
    let mut search =
        TransitionSearch::new(&quantifiers.plan, 1, GuidanceTransitionOrder::CurrentFirst);
    let mut evaluate = |_: &Term| Ok(ModelEvaluation::Undetermined);
    let mut cx = TraceContext {
        index: &index,
        types: &types,
        evaluate: &mut evaluate,
        remaining: 512,
        initializers: None,
        transitions: None,
    };
    assert!(matches!(
        search.steps(&read, &mut cx, true),
        Err(TraceError::Undetermined(_))
    ));
}

#[test]
fn same_frame_instances_use_shared_ranking_and_work_without_profiling() {
    use crate::{
        policy::{
            effort::{ActionRequirementGuidance, WorkAllowance},
            term_selection::array::ArrayAstSize,
        },
        SolverBackend, YardbirdOptions,
    };
    let mut counts = None;
    for (mode, profile, reject) in [
        (GuidanceTransitionOrder::CurrentFirst, true, false),
        (GuidanceTransitionOrder::CurrentFirst, false, false),
        (GuidanceTransitionOrder::PredecessorFirst, true, false),
        (GuidanceTransitionOrder::PredecessorOnly, true, false),
        (GuidanceTransitionOrder::CurrentFirst, true, true),
    ] {
        let mut options = YardbirdOptions::from_filename("same-frame.vmt".into());
        options.profile = profile;
        let mut policy = crate::YardbirdPolicy::<ArrayAstSize>::new(()).with_effort(
            crate::policy::DefaultEffort::default()
                .with_countermodel_refinement(true)
                .with_allowance(WorkAllowance {
                    guidance_action_requirements: ActionRequirementGuidance::WhenUnproductive,
                    guidance_transition_order: mode,
                    ..Default::default()
                }),
        );
        if reject {
            policy = policy.with_instantiation_ranker(Box::new(RejectTracedInstances));
        }
        let strategy = crate::strategies::Abstract::new(3, false, policy, profile);
        let mut driver = crate::Driver::new(
            model(include_str!(
                "../../tests/fixtures/same_frame_requirement.vmt"
            )),
            options.build_instantiation_strategy(),
            SolverBackend::Z3,
        )
        .with_profiler(options.build_profiler())
        .with_wall_timeout(Some(std::time::Duration::from_secs(10)));
        let result = driver.check_strategy(3, Box::new(strategy)).unwrap();
        assert_eq!(
            result.run_progress.unwrap().deepest_completed_depth,
            Some(2)
        );
        if !profile {
            assert_eq!(counts, Some(result.total_instantiations_added));
            continue;
        }
        let mut selected = 0;
        for record in &result.profiling.cost_records {
            let Some(trace) = &record.countermodel_trace else {
                continue;
            };
            assert!(trace.work <= 1024);
            for effort in &record.effort {
                if effort.operation != "CountermodelCandidates" {
                    continue;
                }
                for candidate in &effort.candidates {
                    let Some(origin) = &candidate.countermodel_origin else {
                        continue;
                    };
                    let node = &trace.nodes[origin.node];
                    if matches!(
                        node.reason,
                        TraceReason::QuantifiedTransition { frame: 0, .. }
                    ) && node
                        .lemma
                        .as_ref()
                        .is_some_and(|l| l.formula.to_string().contains("scratch@0"))
                    {
                        assert_eq!(origin.model_version, trace.model_version);
                        selected += usize::from(candidate.selected);
                    }
                }
            }
        }
        assert_eq!(
            selected > 0,
            !reject && mode != GuidanceTransitionOrder::PredecessorOnly
        );
        if mode == GuidanceTransitionOrder::CurrentFirst && !reject {
            counts = Some(result.total_instantiations_added);
        }
    }
}
