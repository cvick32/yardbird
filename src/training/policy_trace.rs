//! Versioned policy observations, built from the existing runtime profiling hooks.
//! Indices and model/graph versions are run-local links, never cross-run identities.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::{
    policy::effort::{EffortCandidate, EffortRecordKind, WorkAllowance, WorkReport},
    profiling::{InstallationRecord, SolverCheckProfilingRecord},
    ProofLoopResult,
};

pub const POLICY_TRACE_VERSION: u32 = 1;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EffortDecisionRecord {
    pub schema_version: u32,
    pub decision_index: u64,
    pub parent_decision_index: Option<u64>,
    pub depth: Option<u16>,
    pub refinement_step: Option<u32>,
    pub preceding_check_id: Option<u64>,
    /// Next observed check, not a claim that this action caused its outcome.
    pub subsequent_check_id: Option<u64>,
    pub model_version: u64,
    pub graph_version_before: u64,
    pub graph_version_after: u64,
    pub pending_instances: usize,
    pub kind: EffortRecordKind,
    pub chosen: String,
    pub offered: Vec<String>,
    pub allowance: Option<WorkAllowance>,
    pub report: WorkReport,
    pub stop_reason: String,
    pub candidates: Vec<EffortCandidate>,
    pub choice_elapsed_secs: f64,
    /// Enclosing operation times include their nested page work and choices.
    pub elapsed_secs: f64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PolicyInstallationRecord {
    pub installation_index: u64,
    pub preceding_check_id: Option<u64>,
    pub subsequent_check_id: Option<u64>,
    pub depth: Option<u16>,
    pub refinement_step: Option<u32>,
    pub installation: InstallationRecord,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PolicyRunOutcome {
    pub schema_version: u32,
    pub progress: Option<crate::driver::RunProgress>,
    pub counterexample: bool,
    pub found_proof: bool,
    pub total_refinement_steps: u32,
    pub total_instantiations_added: u64,
    pub quantifier_provenance: crate::quantifiers::provenance::QuantifierProvenance,
}

/// Observations of a run, including runs which terminate without a proof.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PolicyTrace {
    pub decisions: Vec<EffortDecisionRecord>,
    pub checks: Vec<SolverCheckProfilingRecord>,
    pub installations: Vec<PolicyInstallationRecord>,
    pub outcome: PolicyRunOutcome,
}

impl PolicyTrace {
    pub fn from_result(result: &ProofLoopResult) -> Self {
        let checks = &result.profiling.solver_checks;
        let check_positions = checks
            .iter()
            .enumerate()
            .map(|(position, check)| ((Some(check.depth), Some(check.refinement_step)), position))
            .collect::<HashMap<_, _>>();
        let mut decisions = Vec::new();
        let mut installations = Vec::new();
        for pass in &result.profiling.cost_records {
            let position = check_positions.get(&(pass.bmc_depth, pass.refinement_step));
            let preceding_check_id = position.map(|&i| checks[i].check_id);
            let subsequent_check_id = position
                .and_then(|&i| checks.get(i + 1))
                .map(|c| c.check_id);
            // Runtime reports arrive at completion. Put each enclosing decision
            // before its pages to recover decision order, keeping page order.
            let mut ordered = pass.effort.iter().enumerate().collect::<Vec<_>>();
            ordered.sort_by_key(|(index, record)| {
                (
                    record.operation_id.map(|id| id.offer).unwrap_or(u64::MAX),
                    u8::from(record.kind == EffortRecordKind::BinderPage),
                    *index,
                )
            });
            let mut parents = HashMap::new();
            for (_, record) in ordered {
                let decision_index = decisions.len() as u64;
                let operation_key = record.operation_id.map(|id| (id.model, id.offer, id.index));
                let parent_decision_index = if record.kind == EffortRecordKind::BinderPage {
                    operation_key.and_then(|key| parents.get(&key).copied())
                } else {
                    if let Some(key) = operation_key {
                        parents.insert(key, decision_index);
                    }
                    None
                };
                decisions.push(EffortDecisionRecord {
                    schema_version: POLICY_TRACE_VERSION,
                    decision_index,
                    parent_decision_index,
                    depth: pass.bmc_depth,
                    refinement_step: pass.refinement_step,
                    preceding_check_id,
                    subsequent_check_id,
                    model_version: record.model_version,
                    graph_version_before: record.graph_version_before,
                    graph_version_after: record.graph_version,
                    pending_instances: record.pending_instances,
                    kind: record.kind,
                    chosen: record.chosen.clone(),
                    offered: record.offered.clone(),
                    allowance: record.allowance,
                    report: record.report.clone(),
                    stop_reason: if record.allowance.is_none() {
                        "policy_handoff"
                    } else if record.report.cache_hit {
                        "cached_empty_pass"
                    } else if record.report.selected > 0 {
                        "selected_candidates"
                    } else if record.report.budget_exhausted {
                        "budget_exhausted"
                    } else if record.report.continuable {
                        "page_available"
                    } else {
                        "operation_completed"
                    }
                    .into(),
                    candidates: record.candidates.clone(),
                    choice_elapsed_secs: record.choice_elapsed_secs,
                    elapsed_secs: record.elapsed_secs,
                });
            }
            for installation in &pass.installations {
                installations.push(PolicyInstallationRecord {
                    installation_index: installations.len() as u64,
                    preceding_check_id,
                    subsequent_check_id,
                    depth: pass.bmc_depth,
                    refinement_step: pass.refinement_step,
                    installation: installation.clone(),
                });
            }
        }
        Self {
            decisions,
            checks: checks.clone(),
            installations,
            outcome: PolicyRunOutcome {
                schema_version: POLICY_TRACE_VERSION,
                progress: result.run_progress.clone(),
                counterexample: result.counterexample,
                found_proof: result.found_proof,
                total_refinement_steps: result.total_refinement_steps,
                total_instantiations_added: result.total_instantiations_added,
                quantifier_provenance: result.profiling.quantifier_provenance.clone(),
            },
        }
    }
}
