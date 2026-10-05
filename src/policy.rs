//! Composed policy for the abstract array/binder strategy.
//!
//! Cost construction, complete-instance selection and effort settings have one owner.
//! The effort policy chooses work; the engine validates and executes it.

pub mod eager;
pub mod effort;
pub mod instance_selection;
pub mod term_selection;
use crate::auxiliary_synthesis::ConditionalHistory;
use crate::instance_installation::full_unroll::FullUnrollStrategy;
use crate::policy::instance_selection::{InstantiationRanker, PreferSourceInstantiationRanker};
use crate::policy::term_selection::array::ArrayBMCCost;
use crate::policy::term_selection::context::TermCostContext;
use crate::policy::term_selection::TermCostFactory;
use crate::solver::PropertyCheckMode;
use crate::strategies::{Abstract, ProofStrategyExt, RefinementState};
use crate::theories::array::array_egraph_builder::SourceThenFullEGraphBuilder;
use crate::{ArrayProofPlan, SolverBackend};
pub use effort::{DefaultEffort, ProofEffort};

/// Executable policies selected by name. Each constructs its own proof plan.
#[derive(
    clap::ValueEnum, Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize,
)]
pub enum NamedPolicy {
    /// German's BMC-cost policy with batched winners and property assumptions.
    GermanFast,
    /// Try property-connected array axiom instances before general search.
    CountermodelGuided,
}

impl NamedPolicy {
    pub fn build_plan(self, run: &crate::YardbirdOptions) -> crate::ArrayProofPlan {
        match self {
            Self::GermanFast => run_german_fast(run),
            Self::CountermodelGuided => run_countermodel_guided(run),
        }
    }
}

fn run_german_fast(run: &crate::YardbirdOptions) -> crate::ArrayProofPlan {
    let policy = YardbirdPolicy::<ArrayBMCCost>::new(())
        .with_instantiation_ranker(Box::new(PreferSourceInstantiationRanker))
        .with_effort(
            DefaultEffort::default()
                .with_egraph_builder(Box::<SourceThenFullEGraphBuilder>::default())
                .with_winners_per_group(20),
        );
    let policy = run.configure_eager_policy(policy);
    let strategy = Abstract::new(run.depth, run.run_ic3ia, policy, run.profiling_enabled())
        .with_countermodel_trace_work(run.countermodel_trace_work)
        .with_artifact_capture(run.build_array_artifact_capture())
        .with_theory_selection(run.theory.clone())
        .with_property_check_mode(PropertyCheckMode::Assumptions);
    let synthesis = run.build_aux_synthesis_config();
    let conditional_history = (!synthesis.is_off()).then(|| {
        Box::new(ConditionalHistory::<ArrayBMCCost>::new(synthesis, ()))
            as Box<dyn ProofStrategyExt<RefinementState>>
    });
    ArrayProofPlan {
        solver: SolverBackend::Z3,
        instantiation_strategy: Box::new(FullUnrollStrategy::new()),
        strategy: Box::new(strategy),
        conditional_history,
    }
}

fn run_countermodel_guided(run: &crate::YardbirdOptions) -> crate::ArrayProofPlan {
    let followup = (run.guidance_schedule == effort::GuidanceSchedule::Supplement).then_some(
        effort::WorkAllowance {
            winners: 20,
            dependency_work: 128,
            dependency_demands: 16,
            dependency_paths: 4,
            dependency_links: 4,
            dependency_helpers: 32,
            ..Default::default()
        },
    );
    let policy = YardbirdPolicy::<ArrayBMCCost>::new(())
        .with_instantiation_ranker(Box::new(PreferSourceInstantiationRanker))
        .with_effort(
            DefaultEffort::default()
                .with_countermodel_refinement(true)
                .with_guidance_work(run.guidance_work.unwrap_or(1024))
                .with_allowance(effort::WorkAllowance {
                    guidance_action_requirements:
                        effort::ActionRequirementGuidance::WhenUnproductive,
                    guidance_transition_order: effort::GuidanceTransitionOrder::PredecessorFirst,
                    ..Default::default()
                })
                .with_guidance_followup(followup)
                .with_egraph_builder(Box::<SourceThenFullEGraphBuilder>::default())
                .with_winners_per_group(20),
        );
    let policy = run.configure_eager_policy(policy);
    let strategy = Abstract::new(run.depth, run.run_ic3ia, policy, run.profiling_enabled())
        .with_countermodel_trace_work(run.countermodel_trace_work)
        .with_artifact_capture(run.build_array_artifact_capture())
        .with_theory_selection(run.theory.clone())
        .with_property_check_mode(PropertyCheckMode::Assumptions);
    let synthesis = run.build_aux_synthesis_config();
    let conditional_history = (!synthesis.is_off()).then(|| {
        Box::new(ConditionalHistory::<ArrayBMCCost>::new(synthesis, ()))
            as Box<dyn ProofStrategyExt<RefinementState>>
    });
    ArrayProofPlan {
        solver: SolverBackend::Z3,
        instantiation_strategy: Box::new(FullUnrollStrategy::new()),
        strategy: Box::new(strategy),
        conditional_history,
    }
}

/// One policy configuration, retaining the existing term and ranker seams.
pub struct YardbirdPolicy<F: TermCostFactory> {
    term_config: F::Config,
    instances: Box<dyn InstantiationRanker>,
    effort: Box<dyn ProofEffort>,
    eager: Option<eager::EagerInstantiation>,
}

impl<F: TermCostFactory> YardbirdPolicy<F> {
    pub fn new(term_config: F::Config) -> Self {
        Self {
            term_config,
            instances: Box::new(PreferSourceInstantiationRanker),
            effort: Box::<DefaultEffort>::default(),
            eager: None,
        }
    }

    pub fn with_term_config(mut self, config: F::Config) -> Self {
        self.term_config = config;
        self
    }

    pub fn with_eager_instantiation(mut self, config: eager::EagerInstantiation) -> Self {
        self.eager = Some(config);
        self
    }

    pub(crate) fn eager_seeder(&self) -> Option<Box<dyn crate::strategies::eager::InstanceSeeder>>
    where
        F: 'static,
    {
        self.eager.map(|config| {
            Box::new(crate::strategies::eager::CostGuidedSeeder::<F>::new(
                self.term_config.clone(),
                config,
            )) as Box<dyn crate::strategies::eager::InstanceSeeder>
        })
    }

    pub fn with_instantiation_ranker(mut self, ranker: Box<dyn InstantiationRanker>) -> Self {
        self.instances = ranker;
        self
    }

    pub fn with_effort(mut self, effort: impl ProofEffort + 'static) -> Self {
        self.effort = Box::new(effort);
        self
    }

    pub fn term_cost(&self, context: &TermCostContext, depth: u32) -> F {
        F::from_context(context, depth, &self.term_config)
    }

    pub fn instantiation_ranker(&self) -> &dyn InstantiationRanker {
        self.instances.as_ref()
    }

    pub fn effort(&self) -> &dyn ProofEffort {
        self.effort.as_ref()
    }
    pub fn effort_mut(&mut self) -> &mut dyn ProofEffort {
        self.effort.as_mut()
    }
    pub(crate) fn parts(&mut self) -> (&F::Config, &dyn InstantiationRanker, &mut dyn ProofEffort) {
        (
            &self.term_config,
            self.instances.as_ref(),
            self.effort.as_mut(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::policy::term_selection::array::ArrayAstSize;

    #[test]
    fn countermodel_plan_runs_guidance_and_configures_the_supplement_directly() {
        use smt2parser::{concrete::SyntaxBuilder, vmt::VMTModel, CommandStream};

        let input = r#"
            (declare-fun a () (Array Int Int))
            (define-fun init () Bool (!
              (forall ((i Int)) (= (select a i) 0)) :init true))
            (define-fun trans () Bool (! true :trans true))
            (define-fun prop () Bool (!
              (= (select (store a 1 7) 1) 7) :invar-property 0))
        "#;
        for schedule in [
            effort::GuidanceSchedule::Immediate,
            effort::GuidanceSchedule::Supplement,
        ] {
            let mut run = crate::YardbirdOptions::from_filename("guided.vmt".into());
            run.depth = 1;
            run.profile = true;
            run.guidance_schedule = schedule;
            run.guidance_work = (schedule == effort::GuidanceSchedule::Supplement).then_some(4096);
            // Direct dispatch must work even without run.policy set.
            let plan = NamedPolicy::CountermodelGuided.build_plan(&run);
            let model = VMTModel::checked_from(
                CommandStream::new(input.as_bytes(), SyntaxBuilder, None)
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap(),
            )
            .unwrap();
            let mut driver = crate::Driver::new(model, plan.instantiation_strategy, plan.solver)
                .with_profiler(run.build_profiler())
                .with_wall_timeout(Some(std::time::Duration::from_secs(10)));
            let result = driver.check_strategy(run.depth, plan.strategy).unwrap();
            assert!(!result.counterexample);
            let record = result
                .profiling
                .cost_records
                .iter()
                .find(|record| {
                    record.effort.iter().any(|operation| {
                        operation.operation == "CountermodelCandidates"
                            && operation.report.selected > 0
                    })
                })
                .expect("the named plan must select guided instances");
            let guided = record
                .effort
                .iter()
                .position(|operation| {
                    operation.operation == "CountermodelCandidates" && operation.report.selected > 0
                })
                .unwrap();
            assert_eq!(record.effort[guided].allowance.unwrap().winners, 20);
            assert_eq!(
                record.effort[guided].allowance.unwrap().dependency_work,
                run.guidance_work.unwrap_or(1024)
            );
            let followup = record.effort.get(guided + 1);
            if schedule == effort::GuidanceSchedule::Supplement {
                let followup =
                    followup.expect("supplement must run before returning to the driver");
                assert_eq!(followup.operation, "DiscoverDependencies");
                let allowance = followup.allowance.unwrap();
                assert_eq!(allowance.winners, 20);
                assert_eq!(allowance.dependency_work, 128);
                assert_eq!(allowance.dependency_demands, 16);
                assert_eq!(allowance.dependency_paths, 4);
                assert_eq!(allowance.dependency_links, 4);
                assert_eq!(allowance.dependency_helpers, 32);
            } else {
                assert_eq!(followup.unwrap().operation, "ReturnToDriver");
            }
        }
    }

    #[test]
    #[should_panic(expected = "candidate groups need a winner")]
    fn zero_winner_allowance_is_invalid() {
        let _ = YardbirdPolicy::<ArrayAstSize>::new(())
            .with_effort(DefaultEffort::default().with_winners_per_group(0));
    }
}
