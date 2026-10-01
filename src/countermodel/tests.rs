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
        let mut policy = crate::YardbirdPolicy::<ArrayAstSize>::new(()).with_effort(
            crate::policy::DefaultEffort::default()
                .with_countermodel_refinement(true)
                .with_allowance(crate::policy::effort::WorkAllowance {
                    dependency_work: work,
                    ..Default::default()
                }),
        );
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
    assert!(options.validate_countermodel_trace_options().is_err());
}
