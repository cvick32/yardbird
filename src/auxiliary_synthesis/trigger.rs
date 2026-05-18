use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::auxiliary_synthesis::{
    ArrayConflictRecord, AuxSynthesisConfig, ConflictClassification, SynthesisTrigger,
};

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct TriggerDecision {
    pub fired: bool,
    pub reason: String,
    pub selected_conflict_id: Option<String>,
    pub detected_conflicts: Vec<String>,
}

#[derive(Clone, Debug, Default)]
pub struct AuxTriggerState {
    normalized_counts: BTreeMap<String, u32>,
}

impl AuxTriggerState {
    pub fn decide(
        &mut self,
        config: &AuxSynthesisConfig,
        conflicts: &[ArrayConflictRecord],
        refinement_step: u32,
        n_refines: u32,
    ) -> TriggerDecision {
        if config.trigger == SynthesisTrigger::Off {
            return TriggerDecision {
                fired: false,
                reason: "synthesis disabled".to_string(),
                selected_conflict_id: None,
                detected_conflicts: vec![],
            };
        }

        let detected_conflicts = conflicts
            .iter()
            .filter(|conflict| conflict.is_non_local)
            .map(|conflict| conflict.conflict_id.clone())
            .collect::<Vec<_>>();

        if config.trigger == SynthesisTrigger::Detect {
            return TriggerDecision {
                fired: false,
                reason: format!("detected {} non-local conflicts", detected_conflicts.len()),
                selected_conflict_id: None,
                detected_conflicts,
            };
        }

        let selected = select_non_local_conflict(conflicts);
        let Some(selected) = selected else {
            return TriggerDecision {
                fired: false,
                reason: "no non-local conflict available".to_string(),
                selected_conflict_id: None,
                detected_conflicts,
            };
        };

        match config.trigger {
            SynthesisTrigger::Off | SynthesisTrigger::Detect => unreachable!(),
            SynthesisTrigger::NonLocal => TriggerDecision {
                fired: true,
                reason: "selected non-local conflict".to_string(),
                selected_conflict_id: Some(selected.conflict_id.clone()),
                detected_conflicts,
            },
            SynthesisTrigger::ManualAfterN => {
                let threshold = config.manual_after.unwrap_or(u32::MAX);
                let fired = refinement_step >= threshold;
                TriggerDecision {
                    fired,
                    reason: if fired {
                        format!("refinement step {refinement_step} reached manual threshold {threshold}")
                    } else {
                        format!(
                            "refinement step {refinement_step} below manual threshold {threshold}"
                        )
                    },
                    selected_conflict_id: fired.then(|| selected.conflict_id.clone()),
                    detected_conflicts,
                }
            }
            SynthesisTrigger::RefinementLimit => {
                let window = config.refinement_limit_window.unwrap_or(0);
                let remaining = n_refines.saturating_sub(refinement_step + 1);
                let fired = remaining <= window;
                TriggerDecision {
                    fired,
                    reason: if fired {
                        format!("remaining refinement budget {remaining} within window {window}")
                    } else {
                        format!("remaining refinement budget {remaining} outside window {window}")
                    },
                    selected_conflict_id: fired.then(|| selected.conflict_id.clone()),
                    detected_conflicts,
                }
            }
            SynthesisTrigger::RepeatedPattern => {
                let threshold = config.repeated_pattern_threshold.unwrap_or(u32::MAX);
                let key = normalize_conflict_pattern(selected);
                let count = self.normalized_counts.entry(key).or_insert(0);
                *count += 1;
                let fired = *count >= threshold;
                TriggerDecision {
                    fired,
                    reason: if fired {
                        format!("normalized conflict pattern reached threshold {threshold}")
                    } else {
                        format!(
                            "normalized conflict pattern count {count} below threshold {threshold}"
                        )
                    },
                    selected_conflict_id: fired.then(|| selected.conflict_id.clone()),
                    detected_conflicts,
                }
            }
        }
    }
}

fn select_non_local_conflict(conflicts: &[ArrayConflictRecord]) -> Option<&ArrayConflictRecord> {
    conflicts
        .iter()
        .find(|conflict| {
            conflict.is_non_local && conflict.classification == ConflictClassification::Regular
        })
        .or_else(|| conflicts.iter().find(|conflict| conflict.is_non_local))
}

fn normalize_conflict_pattern(conflict: &ArrayConflictRecord) -> String {
    let min_frame = conflict.frame_span.min_frame.unwrap_or(0);
    conflict
        .term
        .to_string()
        .split_whitespace()
        .map(|part| normalize_frame_token(part, min_frame))
        .collect::<Vec<_>>()
        .join(" ")
}

fn normalize_frame_token(token: &str, min_frame: i64) -> String {
    let Some((prefix, suffix)) = token.rsplit_once('@') else {
        return token.to_string();
    };
    let frame_digits = suffix
        .chars()
        .take_while(|ch| ch.is_ascii_digit())
        .collect::<String>();
    if frame_digits.is_empty() {
        return token.to_string();
    }
    let Ok(frame) = frame_digits.parse::<i64>() else {
        return token.to_string();
    };
    let rest = &suffix[frame_digits.len()..];
    format!("{prefix}@+{}{rest}", frame - min_frame)
}
