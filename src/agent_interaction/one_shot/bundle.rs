use crate::{
    policy::instantiation::{terms, InstantiationSnapshot},
    problem_context::ProblemContext,
    strategies::{ProofStrategyExt, RefinementState},
};
use serde::{Deserialize, Serialize};
use smt2parser::concrete::Term;
use std::{
    collections::BTreeMap,
    sync::{Arc, Mutex},
};

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Proposal {
    pub schema_id: String,
    /// Inline, ground SMT terms. No model IDs, declarations, or arbitrary asserted formulas.
    pub bindings: BTreeMap<String, String>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Batch {
    pub rationale: String,
    pub instantiations: Vec<Proposal>,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Replay {
    pub version: u32,
    pub source: String,
    pub target_depth: u16,
    pub native_progress: Option<crate::driver::RunProgress>,
    pub formulas: Vec<String>,
}

/// Passive native observer. Captures only installed theory formulas, not assumptions,
/// transitions, the negated property, or previously proved properties.
#[derive(Default, Clone)]
pub struct Recorder(Arc<Mutex<Vec<Term>>>);
impl ProofStrategyExt<RefinementState> for Recorder {
    fn unsat(&mut self, _: &mut RefinementState, smt: &dyn ProblemContext) -> anyhow::Result<()> {
        let mut saved = self.0.lock().unwrap();
        let previous = saved.len();
        saved.extend(
            smt.get_asserted_instantiation_terms()
                .into_iter()
                .skip(previous)
                .cloned(),
        );
        Ok(())
    }
}
impl Recorder {
    pub fn save(
        &self,
        options: &crate::YardbirdOptions,
        result: &crate::ProofLoopResult,
    ) -> anyhow::Result<()> {
        let path = options.one_shot.export_instantiations.as_ref().unwrap();
        anyhow::ensure!(
            result
                .run_progress
                .as_ref()
                .is_some_and(|p| p.deepest_completed_depth == Some(options.depth - 1)),
            "export requires a completed native run through every requested bound"
        );
        let formulas = self
            .0
            .lock()
            .unwrap()
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        let count = formulas.len();
        let artifact = Replay {
            version: 1,
            source: std::fs::read_to_string(options.require_filename()?)?,
            target_depth: options.depth,
            native_progress: result.run_progress.clone(),
            formulas,
        };
        let file = std::fs::File::options()
            .write(true)
            .create_new(true)
            .open(path)?;
        serde_json::to_writer(file, &artifact)?;
        log::info!(
            "REPLAY EXPORTED {} exact ground instances to {}",
            count,
            path.display()
        );
        Ok(())
    }
}

/// Recover a substitution, then reconstruct through the trusted schema constructor.
/// Matching alone is never accepted as a proof of validity.
pub(super) fn validate_replay(
    snapshot: &InstantiationSnapshot,
    formula: &str,
) -> anyhow::Result<Term> {
    let term = terms::parse(formula)?;
    for schema in &snapshot.schemas {
        let pattern = terms::parse(&schema.formula)?;
        let mut bindings = BTreeMap::new();
        if matches(&pattern, &term, &schema.slots, &mut bindings) {
            let text = bindings
                .iter()
                .map(|(k, v)| (k.clone(), v.to_string()))
                .collect();
            let resolved = snapshot.resolve_text(&schema.id, &text)?;
            let canonical =
                crate::instance_installation::assertion_tracker::canonical_instantiation_key;
            anyhow::ensure!(
                canonical(&resolved.term) == canonical(&term),
                "replay schema reconstruction differs"
            );
            return Ok(term);
        }
    }
    anyhow::bail!("replay formula is not an instance of a trusted schema: {formula}")
}

fn matches(
    pattern: &Term,
    value: &Term,
    slots: &BTreeMap<String, String>,
    bindings: &mut BTreeMap<String, Term>,
) -> bool {
    if let Term::QualIdentifier(id) = pattern {
        let name = id.to_string();
        if slots.contains_key(&name) {
            return match bindings.get(&name) {
                Some(previous) => previous == value,
                None => {
                    bindings.insert(name, value.clone());
                    true
                }
            };
        }
    }
    match (pattern, value) {
        (
            Term::Application {
                qual_identifier: a,
                arguments: aa,
            },
            Term::Application {
                qual_identifier: b,
                arguments: ba,
            },
        ) => {
            if a != b || aa.len() != ba.len() {
                return false;
            }
            let original = bindings.clone();
            // Consequents bind structural slots before commutative guards.
            if aa
                .iter()
                .zip(ba)
                .rev()
                .all(|(a, b)| matches(a, b, slots, bindings))
            {
                return true;
            }
            *bindings = original.clone();
            if a.to_string() == "="
                && aa.len() == 2
                && matches(&aa[0], &ba[1], slots, bindings)
                && matches(&aa[1], &ba[0], slots, bindings)
            {
                return true;
            }
            *bindings = original;
            false
        }
        _ => pattern == value,
    }
}

pub(super) fn last_frame(term: &Term) -> anyhow::Result<u16> {
    match term {
        Term::QualIdentifier(id) => {
            let name = id.to_string();
            let name = name.trim_matches('|');
            smt2parser::vmt::split_framed_symbol(name)
                .map(|(_, n)| u16::try_from(n).map_err(Into::into))
                .unwrap_or(Ok(0))
        }
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            let own = last_frame(&Term::QualIdentifier(qual_identifier.clone()))?;
            arguments
                .iter()
                .map(last_frame)
                .try_fold(own, |max, n| Ok(max.max(n?)))
        }
        Term::Constant(_) => Ok(0),
        _ => anyhow::bail!("batch instances must be ground"),
    }
}
