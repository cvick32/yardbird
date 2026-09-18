//! Scheduling decisions, separate from matching and logical validity.
pub use crate::quantifiers::SearchPhase;
use crate::theories::array::array_egraph_builder::{
    ArrayEGraphBuilder, SourceThenFullEGraphBuilder,
};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorkAllowance {
    pub winners: usize,
    /// Maximum term-construction attempts in one vocabulary-growth operation.
    pub vocabulary_work: usize,
    pub binder_page_size: usize,
    pub binder_search_limit: usize,
    pub array_initial_limit: usize,
    pub array_rounds: usize,
    pub dependency_demands: usize,
    pub dependency_paths: usize,
    pub dependency_links: usize,
    pub dependency_work: usize,
    pub dependency_helpers: usize,
}
impl Default for WorkAllowance {
    fn default() -> Self {
        Self {
            winners: 1,
            vocabulary_work: 64,
            binder_page_size: 100,
            binder_search_limit: 65_536,
            array_initial_limit: 1_000,
            array_rounds: 15,
            dependency_demands: 64,
            dependency_paths: 16,
            dependency_links: 8,
            dependency_work: 512,
            dependency_helpers: 128,
        }
    }
}
impl WorkAllowance {
    fn widen(&mut self) {
        self.winners = self.winners.saturating_mul(2);
        self.binder_search_limit = self
            .binder_search_limit
            .saturating_mul(2)
            .min(usize::MAX - 1);
        self.array_initial_limit = self
            .array_initial_limit
            .saturating_mul(2)
            .min((usize::MAX - 1) >> (self.array_rounds - 1));
        self.dependency_demands = self.dependency_demands.saturating_mul(2);
        self.dependency_paths = self.dependency_paths.saturating_mul(2);
        self.dependency_links = self.dependency_links.saturating_mul(2);
        self.dependency_work = self.dependency_work.saturating_mul(2);
        self.dependency_helpers = self.dependency_helpers.saturating_mul(2);
    }

    pub(crate) fn validate(&self) -> anyhow::Result<()> {
        anyhow::ensure!(
            self.vocabulary_work > 0,
            "vocabulary growth needs a positive allowance"
        );
        anyhow::ensure!(self.winners > 0, "candidate groups need a winner");
        anyhow::ensure!(
            self.binder_page_size > 0
                && self.binder_search_limit > 0
                && self.binder_search_limit < usize::MAX,
            "invalid binder allowance"
        );
        anyhow::ensure!(
            self.array_initial_limit > 0
                && self.array_rounds > 0
                && self.array_rounds <= usize::BITS as usize
                && self.array_initial_limit <= (usize::MAX - 1) >> (self.array_rounds - 1),
            "invalid array allowance"
        );
        anyhow::ensure!(
            [
                self.dependency_demands,
                self.dependency_paths,
                self.dependency_links,
                self.dependency_work,
                self.dependency_helpers
            ]
            .into_iter()
            .all(|n| n > 0),
            "invalid dependency allowance"
        );
        Ok(())
    }
}

/// Handles are scoped to one offer. The engine rejects a retained/stale handle.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OperationId {
    pub(crate) model: u64,
    pub(crate) offer: u64,
    pub(crate) index: usize,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum OperationKind {
    DiscoverDependencies,
    DependencyRequest(usize),
    Binder(SearchPhase),
    GuardedReads,
    ExpandArray,
    GrowVocabulary,
    ArrayCandidates,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EffortOperation {
    pub id: OperationId,
    pub kind: OperationKind,
    /// Symbolic helper/bindings for dependency requests; never an e-class ID.
    pub description: String,
}
pub struct EffortContext<'a> {
    pub model: u64,
    pub graph_version: u64,
    pub depth: u16,
    pub refinement_step: u32,
    pub pending_instances: usize,
    pub operations: &'a [EffortOperation],
}
pub enum EffortDecision {
    Execute {
        operation: OperationId,
        allowance: WorkAllowance,
    },
    ReturnToDriver,
}
/// A phase has multiple independently resumable compiled rule pages. Only the
/// policy chooses among the pending rules; the matcher executes that choice.
pub struct BinderEffortContext<'a> {
    pub phase: SearchPhase,
    pub pending_rules: &'a [(usize, String)],
    pub rule_count: usize,
}
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct WorkReport {
    pub candidates_returned: usize,
    pub selected: usize,
    pub examined_substitutions: usize,
    pub dependency_work: usize,
    pub vocabulary_work: usize,
    pub terms_added: usize,
    pub budget_exhausted: bool,
    pub continuable: bool,
    pub array_exhausted: bool,
    pub selected_instances: Vec<String>,
}
pub enum EffortEvent<'a> {
    NewProblem,
    BeginPass {
        model: u64,
        depth: u16,
        refinement_step: u32,
    },
    Completed {
        operation: OperationKind,
        report: &'a WorkReport,
    },
    BinderPage {
        phase: SearchPhase,
        rule: usize,
        rule_count: usize,
        report: &'a WorkReport,
    },
    Installed {
        abstract_id: &'a str,
        assertions_added: u64,
    },
    SolverResult {
        depth: u16,
        result: &'a str,
    },
}

pub trait ProofEffort {
    fn choose(&mut self, context: &EffortContext<'_>) -> EffortDecision;
    fn choose_binder_rule(&mut self, context: &BinderEffortContext<'_>) -> Option<usize>;
    fn observe(&mut self, _event: &EffortEvent<'_>) {}
    fn egraph_builder(&self) -> Box<dyn ArrayEGraphBuilder>;
    fn requires_property_cone(&self) -> bool;
}

#[derive(Clone, Copy)]
enum Stage {
    Dependencies,
    Grow,
    Witnesses,
    Guards,
    Build,
    Arrays,
    Triggered,
    Conflicts,
    Expand,
    Return,
}
/// Default ordering and scheduling. After exhausting the initial staged search,
/// alternate wider search/selection allowances with bounded vocabulary growth.
/// Return after each pass so the driver can enforce external limits.
pub struct DefaultEffort {
    allowance: WorkAllowance,
    initial_allowance: WorkAllowance,
    retry: bool,
    grow_next: bool,
    retrying: bool,
    array_exhausted: bool,
    egraph_builder: Box<dyn ArrayEGraphBuilder>,
    stage: Stage,
    model: u64,
    step: u32,
    dependency_model: Option<u64>,
    discovered_this_pass: bool,
    requests: HashSet<usize>,
    next_rule: HashMap<SearchPhase, usize>,
}
impl Default for DefaultEffort {
    fn default() -> Self {
        Self {
            allowance: WorkAllowance::default(),
            initial_allowance: WorkAllowance::default(),
            retry: false,
            grow_next: false,
            retrying: false,
            array_exhausted: false,
            egraph_builder: Box::<SourceThenFullEGraphBuilder>::default(),
            stage: Stage::Dependencies,
            model: 0,
            step: 0,
            dependency_model: None,
            discovered_this_pass: false,
            requests: HashSet::new(),
            next_rule: HashMap::new(),
        }
    }
}
impl DefaultEffort {
    pub fn with_winners_per_group(mut self, winners: usize) -> Self {
        assert!(winners > 0, "candidate groups need a winner");
        self.allowance.winners = winners;
        self.initial_allowance = self.allowance;
        self
    }
    pub fn with_allowance(mut self, allowance: WorkAllowance) -> Self {
        allowance.validate().expect("valid effort allowance");
        self.allowance = allowance;
        self.initial_allowance = allowance;
        self
    }
    pub fn with_egraph_builder(mut self, builder: Box<dyn ArrayEGraphBuilder>) -> Self {
        self.egraph_builder = builder;
        self
    }
}
impl ProofEffort for DefaultEffort {
    fn choose(&mut self, context: &EffortContext<'_>) -> EffortDecision {
        loop {
            let find = |kind| context.operations.iter().find(|op| op.kind == kind);
            let operation = match self.stage {
                Stage::Dependencies => {
                    if self.step % 8 == 7
                        || (self.dependency_model == Some(self.model) && !self.discovered_this_pass)
                    {
                        self.stage = Stage::Witnesses;
                        continue;
                    }
                    if !self.discovered_this_pass {
                        find(OperationKind::DiscoverDependencies)
                    } else if self.requests.len() < 32 {
                        context.operations.iter().find(|op| matches!(op.kind, OperationKind::DependencyRequest(i) if !self.requests.contains(&i)))
                    } else {
                        None
                    }
                }
                Stage::Grow => find(OperationKind::GrowVocabulary),
                Stage::Witnesses => find(OperationKind::Binder(SearchPhase::Witnesses)),
                Stage::Guards => find(OperationKind::GuardedReads),
                Stage::Build if self.retrying => find(OperationKind::ArrayCandidates),
                Stage::Build => find(OperationKind::ExpandArray),
                Stage::Arrays => find(OperationKind::ArrayCandidates),
                Stage::Triggered => find(OperationKind::Binder(SearchPhase::TriggeredConflicts)),
                Stage::Conflicts => find(OperationKind::Binder(SearchPhase::Conflicts)),
                Stage::Expand => find(OperationKind::Binder(SearchPhase::Expand)),
                Stage::Return => return EffortDecision::ReturnToDriver,
            };
            if let Some(operation) = operation {
                return EffortDecision::Execute {
                    operation: operation.id,
                    allowance: self.allowance,
                };
            }
            self.stage = match self.stage {
                Stage::Grow => Stage::Dependencies,
                Stage::Dependencies => Stage::Witnesses,
                Stage::Witnesses => Stage::Guards,
                Stage::Guards => Stage::Build,
                Stage::Build if self.retrying => Stage::Triggered,
                Stage::Build => Stage::Expand,
                Stage::Arrays => Stage::Triggered,
                Stage::Triggered => Stage::Conflicts,
                Stage::Conflicts if self.retrying => Stage::Expand,
                Stage::Conflicts | Stage::Expand | Stage::Return => {
                    if self.array_exhausted {
                        self.retry = true;
                    }
                    Stage::Return
                }
            };
        }
    }
    fn choose_binder_rule(&mut self, context: &BinderEffortContext<'_>) -> Option<usize> {
        let next = self.next_rule.get(&context.phase).copied().unwrap_or(0);
        context
            .pending_rules
            .iter()
            .min_by_key(|(i, _)| {
                (i + context.rule_count - next % context.rule_count) % context.rule_count
            })
            .map(|(i, _)| *i)
    }
    fn observe(&mut self, event: &EffortEvent<'_>) {
        match event {
            EffortEvent::NewProblem => {
                self.next_rule.clear();
                self.dependency_model = None;
                self.model = 0;
                self.allowance = self.initial_allowance;
                self.retry = false;
                self.retrying = false;
                self.grow_next = false;
                self.array_exhausted = false;
            }
            EffortEvent::BeginPass {
                model,
                refinement_step,
                ..
            } => {
                if self.model != *model {
                    self.allowance = self.initial_allowance;
                    self.retry = false;
                    self.grow_next = false;
                    self.retrying = false;
                    self.array_exhausted = false;
                }
                self.model = *model;
                self.step = *refinement_step;
                self.stage = Stage::Dependencies;
                if self.retry {
                    self.retrying = true;
                    self.dependency_model = None;
                    if self.grow_next {
                        self.stage = Stage::Grow;
                    } else {
                        self.allowance.widen();
                    }
                    self.grow_next = !self.grow_next;
                    self.retry = false;
                }
                self.discovered_this_pass = false;
                self.requests.clear();
            }
            EffortEvent::BinderPage {
                phase,
                rule,
                rule_count,
                ..
            } => {
                self.next_rule.insert(*phase, (rule + 1) % rule_count);
            }
            EffortEvent::Completed { operation, report } => {
                if report.selected > 0 {
                    self.retry = false;
                    self.stage = Stage::Return;
                    return;
                }
                self.stage = match operation {
                    OperationKind::GrowVocabulary => Stage::Dependencies,
                    OperationKind::DiscoverDependencies => {
                        self.dependency_model = Some(self.model);
                        self.discovered_this_pass = true;
                        Stage::Dependencies
                    }
                    OperationKind::DependencyRequest(i) => {
                        self.requests.insert(*i);
                        Stage::Dependencies
                    }
                    OperationKind::Binder(SearchPhase::Witnesses) => Stage::Guards,
                    OperationKind::GuardedReads => Stage::Build,
                    OperationKind::ExpandArray if report.array_exhausted => {
                        self.array_exhausted = true;
                        Stage::Expand
                    }
                    OperationKind::ExpandArray => Stage::Arrays,
                    OperationKind::ArrayCandidates => Stage::Triggered,
                    OperationKind::Binder(SearchPhase::TriggeredConflicts) => Stage::Conflicts,
                    OperationKind::Binder(SearchPhase::Conflicts) if self.retrying => Stage::Expand,
                    OperationKind::Binder(SearchPhase::Conflicts | SearchPhase::Expand) => {
                        if self.array_exhausted {
                            self.retry = true;
                        }
                        Stage::Return
                    }
                };
            }
            _ => {}
        }
    }
    fn egraph_builder(&self) -> Box<dyn ArrayEGraphBuilder> {
        self.egraph_builder.clone_box()
    }
    fn requires_property_cone(&self) -> bool {
        self.egraph_builder.requires_property_cone()
    }
}

impl WorkReport {
    pub(crate) fn from_batch(batch: &crate::instantiation::candidate::InstantiationBatch) -> Self {
        Self {
            candidates_returned: batch.candidates.len(),
            selected: batch.selected().count(),
            examined_substitutions: batch.search.examined_substitutions,
            budget_exhausted: !batch.search.budget_exhausted_rules.is_empty(),
            continuable: !batch.search.continuable_rules.is_empty(),
            selected_instances: batch
                .selected()
                .map(|c| c.provenance.abstract_instantiation_id().to_owned())
                .collect(),
            ..Self::default()
        }
    }
}

/// Execution observations use the existing profiling output, linked to selected
/// abstract instances. They describe observed work, not causal proof credit.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EffortRecord {
    pub graph_version: u64,
    pub operation_id: Option<OperationId>,
    pub operation: String,
    pub offered: Vec<String>,
    pub allowance: WorkAllowance,
    pub report: WorkReport,
    pub elapsed_secs: f64,
}
