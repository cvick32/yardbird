//! Agent interaction with Yardbird through stdio, native refinement, and batch verification.
mod native;
pub mod one_shot;
pub use native::NativeAgent;
pub(crate) use options::migrate_saved_options;
pub use options::{AgentMode, AgentTrigger};
pub(crate) mod observations;
mod options;
mod protocol;
pub(crate) mod records;
pub use options::AgentOptions;

use crate::{
    instance_installation::{
        full_unroll::FullUnrollStrategy,
        request::{InstantiationInstallResult, InstantiationRequest},
        InstantiationContext, InstantiationStrategy,
    },
    policy::{
        discovery::{DiscoveryContext, InstanceDiscovery},
        effort::{
            BinderEffortContext, DefaultEffort, EffortContext, EffortDecision, EffortEvent,
            OperationKind, ProofEffort, WorkAllowance, WorkReport,
        },
        instance_selection::TermCostInstantiationRanker,
        term_selection::array::ArrayBMCCost,
        YardbirdPolicy,
    },
    problem_context::ProblemContext,
    rule_matching::candidate::SymbolicInstance,
    solver::{PropertyCheckMode, SolverCheckResult},
    strategies::{Abstract, ProofAction, ProofStrategy, RefinementState},
    vmt_bmc_session::VmtBmcSession,
    YardbirdOptions,
};
use protocol::Session;
use std::sync::{Arc, Mutex};

type SharedSession = Arc<Mutex<Session>>;
struct Producer(SharedSession);
impl InstanceDiscovery for Producer {
    fn candidate_limit(&self) -> Option<usize> {
        Some(self.0.lock().unwrap().candidate_capacity())
    }
    fn observe_formulas(&mut self, index: Option<&crate::transition_index::TransitionIndex>) {
        self.0.lock().unwrap().index = index.cloned();
    }
    fn take_admitted_terms(&mut self) -> Vec<smt2parser::concrete::Term> {
        std::mem::take(&mut self.0.lock().unwrap().admitted)
    }
    fn observe_operation(
        &mut self,
        kind: OperationKind,
        report: &WorkReport,
        candidates: &[crate::rule_matching::candidate::InstantiationCandidate],
        smt: &dyn ProblemContext,
    ) -> anyhow::Result<()> {
        self.0
            .lock()
            .unwrap()
            .observe_search(kind, report, candidates, smt)
    }

    fn supports_input_binders(&self) -> bool {
        true
    }
    fn discover(
        &mut self,
        context: &DiscoveryContext<'_>,
    ) -> anyhow::Result<Vec<SymbolicInstance>> {
        self.0.lock().unwrap().interact(context)
    }
}

struct Effort {
    start: u16,
    ordinary: DefaultEffort,
    session: SharedSession,
}
impl ProofEffort for Effort {
    fn allows_concrete_validation(&self) -> bool {
        false
    }
    fn choose(&mut self, c: &EffortContext<'_>) -> EffortDecision {
        if c.depth < self.start {
            return self.ordinary.choose(c);
        }
        {
            let session = self.session.lock().unwrap();
            if session.is_advancing() {
                return EffortDecision::ReturnToDriver;
            }
        }
        let searching = self.session.lock().unwrap().search_remaining() > 0;
        if searching {
            // Pending agent choices must not suppress the explicitly requested search.
            let context = EffortContext {
                pending_instances: 0,
                ..*c
            };
            match self.ordinary.choose(&context) {
                EffortDecision::Execute { operation, .. } => {
                    return EffortDecision::Execute {
                        operation,
                        allowance: WorkAllowance {
                            winners: 64,
                            ..WorkAllowance::default()
                        },
                    }
                }
                EffortDecision::Stop => self.session.lock().unwrap().end_search("exhausted"),
                EffortDecision::ReturnToDriver => {
                    self.session.lock().unwrap().end_search("policy_yield")
                }
            }
        }
        let op = c
            .operations
            .iter()
            .find(|o| o.kind == OperationKind::PolicyCandidates)
            .expect("agent producer offered");
        EffortDecision::Execute {
            operation: op.id,
            allowance: WorkAllowance {
                winners: 64,
                discovery_calls: 1,
                ..WorkAllowance::default()
            },
        }
    }
    fn choose_binder_rule(&mut self, c: &BinderEffortContext<'_>) -> Option<usize> {
        self.ordinary.choose_binder_rule(c)
    }
    fn observe(&mut self, e: &EffortEvent<'_>) {
        self.ordinary.observe(e);
    }
    fn egraph_builder(
        &self,
    ) -> Box<dyn crate::theories::array::array_egraph_builder::ArrayEGraphBuilder> {
        self.ordinary.egraph_builder()
    }
    fn requires_property_cone(&self) -> bool {
        self.ordinary.requires_property_cone()
    }
}

#[derive(Clone)]
struct RecordingInstallation(SharedSession);
impl std::fmt::Debug for RecordingInstallation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("AgentFullUnroll")
    }
}
impl InstantiationStrategy for RecordingInstallation {
    fn clone_box(&self) -> Box<dyn InstantiationStrategy> {
        Box::new(self.clone())
    }
    fn on_generate(
        &mut self,
        request: InstantiationRequest,
        context: &mut InstantiationContext<'_>,
    ) -> InstantiationInstallResult {
        let key = crate::instance_installation::assertion_tracker::canonical_instantiation_key(
            request.inst.get_term(),
        )
        .to_string();
        let result = context.install_new(request);
        self.0.lock().unwrap().installed(&key, result);
        result
    }
    fn on_loop(&mut self, depth: u16, context: &mut InstantiationContext<'_>) {
        FullUnrollStrategy::new().on_loop(depth, context);
    }
}

/// Run the stdio protocol without constructing any external inference client.
pub fn run_stdio(options: &YardbirdOptions) -> anyhow::Result<()> {
    options.agent.validate(options)?;
    options.validate_theory_selection()?;
    let shared = Arc::new(Mutex::new(Session::stdio(options)?));
    let result = run_session(options, shared.clone());
    let mut session = shared.lock().unwrap();
    if !session.terminated {
        let reason = match &result {
            Ok(()) if session.ever_paused => "bounded_complete",
            Ok(()) => "target_not_reached",
            Err(_) => "internal_error",
        };
        session.terminate(reason)?;
    }
    result
}

fn run_session(options: &YardbirdOptions, shared: SharedSession) -> anyhow::Result<()> {
    let policy = YardbirdPolicy::<ArrayBMCCost>::new(())
        .with_instantiation_ranker(Box::new(TermCostInstantiationRanker))
        .with_boxed_effort(Box::new(Effort {
            start: options.agent.agent_pause_depth,
            ordinary: DefaultEffort::default(),
            session: shared.clone(),
        }))
        .with_discovery(Producer(shared.clone()));
    let mut strategy: Box<dyn ProofStrategy<'static, RefinementState>> = Box::new(
        Abstract::new(options.depth, false, policy, false)
            .with_theory_selection(options.theory.clone())
            .with_property_check_mode(PropertyCheckMode::Assumptions),
    );
    let model = strategy.configure_model(crate::model_from_options(options));
    if let Some(error) = strategy.configuration_error() {
        anyhow::bail!("{error}");
    }
    let mut smt = VmtBmcSession::new(
        &model,
        &strategy,
        crate::SolverBackend::Z3,
        false,
        Box::new(RecordingInstallation(shared.clone())),
        false,
        None,
    )?;
    let mut needs_check = true;
    for depth in 0..options.depth {
        for step in 0..u32::MAX {
            {
                let mut s = shared.lock().unwrap();
                if s.expired() {
                    s.terminate("timeout")?;
                    return Ok(());
                }
            }
            smt.unroll(depth);
            let mut state = strategy.setup(&smt, depth)?;
            if needs_check {
                let timeout = shared.lock().unwrap().check_timeout_ms();
                smt.set_timeout_millis(timeout)?;
                let result = smt.check_property();
                eprintln!("agent check depth={depth} step={step} result={result:?}");
                shared
                    .lock()
                    .unwrap()
                    .record_assertions(&smt.smt2_string_with_property_check());
                shared.lock().unwrap().checked(&smt);
                if shared.lock().unwrap().expired() {
                    shared.lock().unwrap().terminate("timeout")?;
                    return Ok(());
                }
                match result {
                    SolverCheckResult::Unsat => {
                        strategy.unsat(&mut state, &smt)?;
                        shared.lock().unwrap().depth_closed(depth);
                        break;
                    }
                    SolverCheckResult::Unknown => {
                        let reason = smt.get_reason_unknown().unwrap_or_default();
                        shared.lock().unwrap().terminate(
                            if reason.contains("timeout") || reason.contains("canceled") {
                                "timeout"
                            } else {
                                "unknown"
                            },
                        )?;
                        return Ok(());
                    }
                    SolverCheckResult::Sat => {}
                }
            }
            // A stopped/expired controller deliberately exits through the ordinary
            // error channel of discovery; it never becomes a proof/counterexample.
            let action = strategy.sat(&mut state, &smt, step);
            if shared.lock().unwrap().terminated {
                return Ok(());
            }
            anyhow::ensure!(
                matches!(action?, ProofAction::Continue),
                "ordinary prelude exhausted without a refinement"
            );
            let before = smt.get_number_instantiation_assertions_added();
            strategy.finish(state, &mut smt)?;
            needs_check = smt.get_number_instantiation_assertions_added() > before;
            if !needs_check {
                let mut session = shared.lock().unwrap();
                if session.ever_paused {
                    session.no_progress()?;
                } else {
                    anyhow::bail!("ordinary prelude made no progress");
                }
            }
        }
        needs_check = true;
    }
    Ok(())
}
