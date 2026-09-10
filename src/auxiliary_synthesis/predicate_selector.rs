use std::collections::{BTreeMap, BTreeSet};

use anyhow::{anyhow, Context};
use log::{debug, info};
use serde::{Deserialize, Serialize};
use smt2parser::{
    concrete::{QualIdentifier, Term},
    vmt::{array_abstractor::ArrayAbstractor, split_framed_symbol, variable::Variable},
};

use crate::{
    auxiliary_synthesis::{AuxiliarySynthesisCandidate, PredicateRelevancePolicy},
    interpolant::{PredicateCandidate, SequenceInterpolants},
    problem_context::ProblemContext,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Occurrence {
    First,
    Last,
}

impl Occurrence {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::First => "first_occurrence",
            Self::Last => "last_occurrence",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Derivation {
    Predicate,
    Exit,
}

impl Derivation {
    fn as_str(self) -> &'static str {
        match self {
            Self::Predicate => "predicate",
            Self::Exit => "predicate_exit",
        }
    }
}

#[derive(Clone, Debug)]
struct GuardCandidate {
    predicate_index: usize,
    source_interpolants: Vec<usize>,
    source_frames: Vec<u16>,
    ranking_term: Term,
    capture_guard: Term,
    occurrence: Occurrence,
    derivation: Derivation,
    exact_capture_match: bool,
}

#[derive(Clone, Debug)]
struct Rejection {
    predicate_index: usize,
    derivation: Derivation,
    reason: String,
}

impl std::fmt::Display for Rejection {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "candidate={} derivation={}: {}",
            self.predicate_index,
            self.derivation.as_str(),
            self.reason
        )
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct InterpolantGuardSelectionRecord {
    pub predicate_index: usize,
    pub predicate: String,
    pub capture_guard: String,
    pub source_interpolants: Vec<usize>,
    pub source_frames: Vec<u16>,
    pub derivation: String,
    pub capture_mode: String,
    pub exact_capture_match: bool,
    pub ranker: String,
    pub cost: u32,
    pub structurally_scored: bool,
    #[serde(default)]
    pub property_overlap: bool,
    #[serde(default)]
    pub relevance: String,
    pub eligible_count: usize,
    pub control_guard: Option<String>,
    pub rejected: Vec<String>,
}

#[derive(Clone, Debug, Default)]
struct Classification {
    eligible: Vec<GuardCandidate>,
    rejected: Vec<Rejection>,
    control_guard: Option<Term>,
}

#[derive(Clone, Debug)]
struct GuardScore {
    cost: u32,
    structurally_scored: bool,
    property_overlap: bool,
    relevance: GuardRelevance,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum GuardRelevance {
    ExactProperty,
    CaptureScalar,
    CaptureIndexedArray,
}

impl GuardRelevance {
    fn as_str(self) -> &'static str {
        match self {
            Self::ExactProperty => "exact_property",
            Self::CaptureScalar => "capture_scalar",
            Self::CaptureIndexedArray => "capture_indexed_array",
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct SelectedGuard {
    pub(crate) capture_guard: Term,
    pub(crate) occurrence: Occurrence,
    pub(crate) record: InterpolantGuardSelectionRecord,
}

fn has_recent_interpolant_provenance(source_frames: &[u16], capture_frame: u16) -> bool {
    let provenance_floor = capture_frame.saturating_sub(1);
    source_frames.iter().any(|frame| *frame >= provenance_floor)
}

fn classify_interpolant_guards(
    synthesis_candidate: &AuxiliarySynthesisCandidate,
    sequence: &SequenceInterpolants,
    abstract_problem: &dyn ProblemContext,
) -> anyhow::Result<Classification> {
    let target_frame = u16::try_from(synthesis_candidate.capture_target.frame)
        .context("capture frame is negative or exceeds the BMC frame range")?;
    if target_frame >= sequence.depth {
        return Err(anyhow!(
            "capture frame {target_frame} cannot update history before the property at depth {}",
            sequence.depth
        ));
    }
    if !abstract_problem.has_model() {
        return Err(anyhow!(
            "abstract counterexample model is unavailable for guard classification"
        ));
    }

    let declarations = variable_declarations(abstract_problem.get_variables());
    let source_frame_by_interpolant = sequence
        .partitions
        .iter()
        .map(|partition| (partition.interpolant.interpolant_number, partition.frame))
        .collect::<BTreeMap<_, _>>();
    let capture_frame = target_frame;
    let control_guard = control_location_guard(
        abstract_problem,
        abstract_problem.get_variables(),
        capture_frame,
    )?;
    let mut report = Classification {
        control_guard,
        ..Classification::default()
    };

    for (predicate_index, predicate) in sequence.predicates.candidates().iter().enumerate() {
        let source_frames = predicate
            .interpolant_numbers
            .iter()
            .filter_map(|number| source_frame_by_interpolant.get(number).copied())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        if !has_recent_interpolant_provenance(&source_frames, capture_frame) {
            report.rejected.push(Rejection {
                predicate_index,
                derivation: Derivation::Predicate,
                reason: format!(
                    "predicate comes only from interpolation boundaries {source_frames:?} before the eligible suffix at frame {} for capture frame {capture_frame}",
                    capture_frame.saturating_sub(1),
                ),
            });
            continue;
        }
        if contains_smtinterpol_array_diff(&predicate.term) {
            report.rejected.push(Rejection {
                predicate_index,
                derivation: Derivation::Predicate,
                reason: "predicate uses SMTInterpol-internal array witness @diff".to_string(),
            });
            continue;
        }

        let local_predicate = match localize_predicate(predicate, &declarations) {
            Ok(term) => term,
            Err(error) => {
                report.rejected.push(Rejection {
                    predicate_index,
                    derivation: Derivation::Predicate,
                    reason: error.to_string(),
                });
                continue;
            }
        };
        let exact_capture_match = predicate.variables.iter().any(|variable| {
            variable.name == synthesis_candidate.capture_target.current_name
                && matches!(
                    variable.frame,
                    Some(frame)
                        if frame == i64::from(capture_frame)
                            || frame == i64::from(capture_frame + 1)
                )
        });

        classify_variant(
            &mut report,
            abstract_problem,
            predicate_index,
            predicate,
            &source_frames,
            local_predicate.clone(),
            local_predicate.clone(),
            ClassifiedModes::Both,
            Derivation::Predicate,
            exact_capture_match,
            capture_frame,
            sequence.depth,
        );

        match shift_current_to_next(&local_predicate, &declarations) {
            Some(shifted) => {
                let shifted = not_term(shifted);
                classify_variant(
                    &mut report,
                    abstract_problem,
                    predicate_index,
                    predicate,
                    &source_frames,
                    shifted.clone(),
                    shifted,
                    ClassifiedModes::FirstOnly,
                    Derivation::Exit,
                    exact_capture_match,
                    capture_frame,
                    sequence.depth,
                );
            }
            None => report.rejected.push(Rejection {
                predicate_index,
                derivation: Derivation::Exit,
                reason: "predicate already uses a next-state symbol".to_string(),
            }),
        }
    }

    Ok(report)
}

#[allow(clippy::too_many_arguments)]
fn classify_variant(
    report: &mut Classification,
    abstract_problem: &dyn ProblemContext,
    predicate_index: usize,
    predicate: &PredicateCandidate,
    source_frames: &[u16],
    local_ranking_term: Term,
    local_guard: Term,
    allowed_modes: ClassifiedModes,
    derivation: Derivation,
    exact_capture_match: bool,
    capture_frame: u16,
    depth: u16,
) {
    let local_guard = conjoin_control_guard(local_guard, report.control_guard.as_ref());
    let abstract_ranking_term = match abstract_native_arrays(local_ranking_term) {
        Ok(term) => term,
        Err(error) => {
            report.rejected.push(Rejection {
                predicate_index,
                derivation,
                reason: format!("array abstraction failed: {error}"),
            });
            return;
        }
    };
    let abstract_guard = match abstract_native_arrays(local_guard) {
        Ok(term) => term,
        Err(error) => {
            report.rejected.push(Rejection {
                predicate_index,
                derivation,
                reason: format!("array abstraction failed: {error}"),
            });
            return;
        }
    };
    let values = match evaluate_transition_guard(abstract_problem, &abstract_guard, depth) {
        Ok(values) => values,
        Err(error) => {
            report.rejected.push(Rejection {
                predicate_index,
                derivation,
                reason: format!("model evaluation failed: {error}"),
            });
            return;
        }
    };
    let (first_occurrence, last_occurrence) = classify_trace_values(&values, capture_frame);
    let mut added = false;
    if allowed_modes.allows_last() && last_occurrence {
        report.eligible.push(GuardCandidate {
            predicate_index,
            source_interpolants: predicate.interpolant_numbers.iter().copied().collect(),
            source_frames: source_frames.to_vec(),
            ranking_term: abstract_ranking_term.clone(),
            capture_guard: abstract_guard.clone(),
            occurrence: Occurrence::Last,
            derivation,
            exact_capture_match,
        });
        added = true;
    }
    if allowed_modes.allows_first() && first_occurrence {
        report.eligible.push(GuardCandidate {
            predicate_index,
            source_interpolants: predicate.interpolant_numbers.iter().copied().collect(),
            source_frames: source_frames.to_vec(),
            ranking_term: abstract_ranking_term,
            capture_guard: abstract_guard,
            occurrence: Occurrence::First,
            derivation,
            exact_capture_match,
        });
        added = true;
    }
    if !added {
        report.rejected.push(Rejection {
            predicate_index,
            derivation,
            reason: format!(
                "trace values {values:?} do not classify at capture frame {capture_frame}"
            ),
        });
    }
}

pub(crate) fn select_interpolant_guard(
    synthesis_candidate: &AuxiliarySynthesisCandidate,
    sequence: &SequenceInterpolants,
    abstract_problem: &dyn ProblemContext,
    ranker: &str,
    relevance_policy: PredicateRelevancePolicy,
    mut score: impl FnMut(&Term) -> (u32, bool),
) -> anyhow::Result<Option<SelectedGuard>> {
    let report = classify_interpolant_guards(synthesis_candidate, sequence, abstract_problem)?;
    info!(
        "AUX-SYNTH classified {} eligible interpolant guards and rejected {} derivations{}",
        report.eligible.len(),
        report.rejected.len(),
        report
            .control_guard
            .as_ref()
            .map(|guard| format!(" with control guard {guard}"))
            .unwrap_or_default(),
    );
    for rejection in &report.rejected {
        debug!("AUX-SYNTH rejected interpolant guard {rejection}");
    }
    let property_terms = normalized_property_terms(abstract_problem);
    let Some((guard, guard_score)) = rank_candidates(
        &report,
        &property_terms,
        &synthesis_candidate.capture_target.current_name,
        &synthesis_candidate.capture_target.next_name,
        relevance_policy,
        &mut score,
    ) else {
        if !report.eligible.is_empty() {
            info!(
                "AUX-SYNTH rejected all {} eligible interpolant guards under predicate relevance policy {}",
                report.eligible.len(),
                relevance_policy,
            );
        }
        return Ok(None);
    };
    let record = InterpolantGuardSelectionRecord {
        predicate_index: guard.predicate_index,
        predicate: guard.ranking_term.to_string(),
        capture_guard: guard.capture_guard.to_string(),
        source_interpolants: guard.source_interpolants,
        source_frames: guard.source_frames,
        derivation: guard.derivation.as_str().to_string(),
        capture_mode: guard.occurrence.as_str().to_string(),
        exact_capture_match: guard.exact_capture_match,
        ranker: ranker.to_string(),
        cost: guard_score.cost,
        structurally_scored: guard_score.structurally_scored,
        property_overlap: guard_score.property_overlap,
        relevance: guard_score.relevance.as_str().to_string(),
        eligible_count: report.eligible.len(),
        control_guard: report.control_guard.as_ref().map(ToString::to_string),
        rejected: report.rejected.iter().map(ToString::to_string).collect(),
    };
    Ok(Some(SelectedGuard {
        capture_guard: guard.capture_guard,
        occurrence: guard.occurrence,
        record,
    }))
}

fn normalized_property_terms(problem: &dyn ProblemContext) -> BTreeSet<String> {
    problem
        .get_property_subterms()
        .into_iter()
        .filter_map(|term| term.parse::<Term>().ok())
        .filter_map(|term| normalized_property_term(&term))
        .collect()
}

fn normalized_property_term(term: &Term) -> Option<String> {
    let unframed = rewrite_simple_term(term, &mut |identifier| {
        let name = identifier.get_name();
        Ok(split_framed_symbol(&name)
            .map(|(base, _)| QualIdentifier::simple(base))
            .unwrap_or_else(|| identifier.clone()))
    })
    .ok()?;
    Some(canonicalize_order_relation(unframed).to_string())
}

fn canonicalize_order_relation(term: Term) -> Term {
    match term {
        Term::Constant(_) | Term::QualIdentifier(_) => term,
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            let mut arguments = arguments
                .into_iter()
                .map(canonicalize_order_relation)
                .collect::<Vec<_>>();
            let reversed_operator = match qual_identifier.get_name().as_str() {
                ">=" => Some("<="),
                ">" => Some("<"),
                _ => None,
            };
            let qual_identifier = match reversed_operator {
                Some(operator) if arguments.len() == 2 => {
                    arguments.swap(0, 1);
                    QualIdentifier::simple(operator)
                }
                _ => qual_identifier,
            };
            Term::Application {
                qual_identifier,
                arguments,
            }
        }
        Term::Let { var_bindings, term } => Term::Let {
            var_bindings: var_bindings
                .into_iter()
                .map(|(name, binding)| (name, canonicalize_order_relation(binding)))
                .collect(),
            term: Box::new(canonicalize_order_relation(*term)),
        },
        Term::Lambda { vars, term } => Term::Lambda {
            vars,
            term: Box::new(canonicalize_order_relation(*term)),
        },
        Term::Forall { vars, term } => Term::Forall {
            vars,
            term: Box::new(canonicalize_order_relation(*term)),
        },
        Term::Exists { vars, term } => Term::Exists {
            vars,
            term: Box::new(canonicalize_order_relation(*term)),
        },
        Term::Match { term, cases } => Term::Match {
            term: Box::new(canonicalize_order_relation(*term)),
            cases: cases
                .into_iter()
                .map(|(pattern, term)| (pattern, canonicalize_order_relation(term)))
                .collect(),
        },
        Term::Attributes { term, attributes } => Term::Attributes {
            term: Box::new(canonicalize_order_relation(*term)),
            attributes,
        },
    }
}

fn rank_candidates(
    report: &Classification,
    property_terms: &BTreeSet<String>,
    capture_current: &str,
    capture_next: &str,
    relevance_policy: PredicateRelevancePolicy,
    score: &mut impl FnMut(&Term) -> (u32, bool),
) -> Option<(GuardCandidate, GuardScore)> {
    let mut ranked = report
        .eligible
        .iter()
        .cloned()
        .filter_map(|guard| {
            let property_overlap = normalized_property_term(&guard.ranking_term)
                .is_some_and(|term| property_terms.contains(&term));
            let relevance = guard_relevance(
                &guard,
                property_overlap,
                capture_current,
                capture_next,
                relevance_policy,
            )?;
            let (cost, structurally_scored) = score(&guard.ranking_term);
            Some((
                guard,
                GuardScore {
                    cost,
                    structurally_scored,
                    property_overlap,
                    relevance,
                },
            ))
        })
        .collect::<Vec<_>>();
    ranked.sort_by(|(left_guard, left_score), (right_guard, right_score)| {
        left_score
            .relevance
            .cmp(&right_score.relevance)
            .then_with(|| left_score.cost.cmp(&right_score.cost))
            .then_with(|| {
                right_guard
                    .exact_capture_match
                    .cmp(&left_guard.exact_capture_match)
            })
            .then_with(|| {
                occurrence_rank(left_guard.occurrence).cmp(&occurrence_rank(right_guard.occurrence))
            })
            .then_with(|| left_guard.predicate_index.cmp(&right_guard.predicate_index))
            .then_with(|| {
                left_guard
                    .capture_guard
                    .to_string()
                    .cmp(&right_guard.capture_guard.to_string())
            })
    });
    ranked.into_iter().next()
}

fn guard_relevance(
    guard: &GuardCandidate,
    property_overlap: bool,
    capture_current: &str,
    capture_next: &str,
    relevance_policy: PredicateRelevancePolicy,
) -> Option<GuardRelevance> {
    if property_overlap {
        return Some(GuardRelevance::ExactProperty);
    }
    if relevance_policy == PredicateRelevancePolicy::ExactProperty {
        return None;
    }
    if !guard.exact_capture_match {
        return None;
    }
    if !contains_array_operation(&guard.ranking_term) {
        return Some(GuardRelevance::CaptureScalar);
    }
    array_indices_align_with_capture(&guard.ranking_term, capture_current, capture_next)
        .then_some(GuardRelevance::CaptureIndexedArray)
}

fn contains_array_operation(term: &Term) -> bool {
    match term {
        Term::Constant(_) | Term::QualIdentifier(_) => false,
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            let name = qual_identifier.get_name();
            matches!(name.as_str(), "select" | "store")
                || name.starts_with("Read_")
                || name.starts_with("Write_")
                || arguments.iter().any(contains_array_operation)
        }
        Term::Let { var_bindings, term } => {
            var_bindings
                .iter()
                .any(|(_, binding)| contains_array_operation(binding))
                || contains_array_operation(term)
        }
        Term::Lambda { term, .. }
        | Term::Forall { term, .. }
        | Term::Exists { term, .. }
        | Term::Attributes { term, .. } => contains_array_operation(term),
        Term::Match { term, cases } => {
            contains_array_operation(term)
                || cases.iter().any(|(_, case)| contains_array_operation(case))
        }
    }
}

fn array_indices_align_with_capture(
    term: &Term,
    capture_current: &str,
    capture_next: &str,
) -> bool {
    fn visit(term: &Term, capture_current: &str, capture_next: &str, saw: &mut bool) -> bool {
        match term {
            Term::Constant(_) | Term::QualIdentifier(_) => true,
            Term::Application {
                qual_identifier,
                arguments,
            } => {
                let name = qual_identifier.get_name();
                let is_array_access = matches!(name.as_str(), "select" | "store")
                    || name.starts_with("Read_")
                    || name.starts_with("Write_");
                if is_array_access {
                    *saw = true;
                    let Some(index) = arguments.get(1) else {
                        return false;
                    };
                    if !term_contains_symbol(index, capture_current)
                        && !term_contains_symbol(index, capture_next)
                    {
                        return false;
                    }
                }
                arguments
                    .iter()
                    .all(|argument| visit(argument, capture_current, capture_next, saw))
            }
            Term::Let { var_bindings, term } => {
                var_bindings
                    .iter()
                    .all(|(_, binding)| visit(binding, capture_current, capture_next, saw))
                    && visit(term, capture_current, capture_next, saw)
            }
            Term::Lambda { term, .. }
            | Term::Forall { term, .. }
            | Term::Exists { term, .. }
            | Term::Attributes { term, .. } => visit(term, capture_current, capture_next, saw),
            Term::Match { term, cases } => {
                visit(term, capture_current, capture_next, saw)
                    && cases
                        .iter()
                        .all(|(_, case)| visit(case, capture_current, capture_next, saw))
            }
        }
    }

    let mut saw_array_access = false;
    visit(term, capture_current, capture_next, &mut saw_array_access) && saw_array_access
}

fn term_contains_symbol(term: &Term, expected: &str) -> bool {
    match term {
        Term::Constant(_) => false,
        Term::QualIdentifier(identifier) => identifier.get_name() == expected,
        Term::Application { arguments, .. } => arguments
            .iter()
            .any(|argument| term_contains_symbol(argument, expected)),
        Term::Let { var_bindings, term } => {
            var_bindings
                .iter()
                .any(|(_, binding)| term_contains_symbol(binding, expected))
                || term_contains_symbol(term, expected)
        }
        Term::Lambda { term, .. }
        | Term::Forall { term, .. }
        | Term::Exists { term, .. }
        | Term::Attributes { term, .. } => term_contains_symbol(term, expected),
        Term::Match { term, cases } => {
            term_contains_symbol(term, expected)
                || cases
                    .iter()
                    .any(|(_, case)| term_contains_symbol(case, expected))
        }
    }
}

fn occurrence_rank(mode: Occurrence) -> u8 {
    match mode {
        Occurrence::Last => 0,
        Occurrence::First => 1,
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum ClassifiedModes {
    Both,
    FirstOnly,
}

impl ClassifiedModes {
    fn allows_first(self) -> bool {
        true
    }

    fn allows_last(self) -> bool {
        self == Self::Both
    }
}

fn classify_trace_values(values: &[bool], capture_frame: u16) -> (bool, bool) {
    let target_index = usize::from(capture_frame);
    let Some(target_value) = values.get(target_index).copied() else {
        return (false, false);
    };
    if !target_value {
        return (false, false);
    }
    let first = values[..target_index].iter().all(|value| !value);
    let last = values[target_index + 1..].iter().all(|value| !value);
    (first, last)
}

fn evaluate_transition_guard(
    problem: &dyn ProblemContext,
    local_guard: &Term,
    depth: u16,
) -> anyhow::Result<Vec<bool>> {
    (0..depth)
        .map(|source_frame| {
            let indexed = problem
                .frame_transition_formula(local_guard.clone(), source_frame)
                .ok_or_else(|| anyhow!("problem cannot frame transition guards"))?;
            match problem.eval_to_string(&indexed)?.trim() {
                "true" => Ok(true),
                "false" => Ok(false),
                value => Err(anyhow!("guard evaluated to non-Boolean value {value}")),
            }
        })
        .collect()
}

fn localize_predicate(
    predicate: &PredicateCandidate,
    declarations: &BTreeMap<String, String>,
) -> anyhow::Result<Term> {
    let frames = predicate
        .variables
        .iter()
        .filter_map(|variable| variable.frame)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let roles = match frames.as_slice() {
        [frame] => BTreeMap::from([(*frame, LocalFrame::Current)]),
        [current, next] if *next == *current + 1 => {
            BTreeMap::from([(*current, LocalFrame::Current), (*next, LocalFrame::Next)])
        }
        [] => return Err(anyhow!("predicate has no framed state variables")),
        _ => return Err(anyhow!("predicate spans non-local frames {frames:?}")),
    };
    rewrite_simple_term(&predicate.term, &mut |identifier| {
        let name = identifier.get_name();
        let Some((base, frame)) = split_framed_symbol(&name) else {
            return Ok(identifier.clone());
        };
        let next = declarations
            .get(&base)
            .ok_or_else(|| anyhow!("framed symbol {name} has no VMT state declaration"))?;
        Ok(match roles.get(&frame) {
            Some(LocalFrame::Current) => QualIdentifier::simple(&base),
            Some(LocalFrame::Next) => QualIdentifier::simple(next),
            None => {
                return Err(anyhow!(
                    "framed symbol {name} is outside predicate locality"
                ))
            }
        })
    })
}

fn shift_current_to_next(term: &Term, declarations: &BTreeMap<String, String>) -> Option<Term> {
    let next_names = declarations.values().collect::<BTreeSet<_>>();
    rewrite_simple_term(term, &mut |identifier| {
        let name = identifier.get_name();
        if next_names.contains(&name) {
            return Err(anyhow!("already next-state"));
        }
        Ok(declarations
            .get(&name)
            .map(QualIdentifier::simple)
            .unwrap_or_else(|| identifier.clone()))
    })
    .ok()
}

fn rewrite_simple_term(
    term: &Term,
    rewrite_identifier: &mut impl FnMut(&QualIdentifier) -> anyhow::Result<QualIdentifier>,
) -> anyhow::Result<Term> {
    match term {
        Term::Constant(_) => Ok(term.clone()),
        Term::QualIdentifier(identifier) => {
            Ok(Term::QualIdentifier(rewrite_identifier(identifier)?))
        }
        Term::Application {
            qual_identifier,
            arguments,
        } => Ok(Term::Application {
            qual_identifier: rewrite_identifier(qual_identifier)?,
            arguments: arguments
                .iter()
                .map(|argument| rewrite_simple_term(argument, rewrite_identifier))
                .collect::<anyhow::Result<_>>()?,
        }),
        Term::Attributes { term, attributes } => Ok(Term::Attributes {
            term: Box::new(rewrite_simple_term(term, rewrite_identifier)?),
            attributes: attributes.clone(),
        }),
        Term::Let { .. }
        | Term::Lambda { .. }
        | Term::Forall { .. }
        | Term::Exists { .. }
        | Term::Match { .. } => Err(anyhow!(
            "predicate contains a binder or match after candidate normalization"
        )),
    }
}

fn variable_declarations(variables: &[Variable]) -> BTreeMap<String, String> {
    variables
        .iter()
        .map(|variable| {
            (
                variable.get_current_variable_name().clone(),
                variable.get_next_variable_name().clone(),
            )
        })
        .collect()
}

fn control_location_guard(
    problem: &dyn ProblemContext,
    variables: &[Variable],
    target_source_frame: u16,
) -> anyhow::Result<Option<Term>> {
    let Some(pc) = variables
        .iter()
        .find(|variable| variable.get_current_variable_name() == "pc")
    else {
        return Ok(None);
    };
    let pc_term = symbol_term(pc.get_current_variable_name());
    let indexed = problem
        .frame_transition_formula(pc_term.clone(), target_source_frame)
        .ok_or_else(|| anyhow!("problem cannot frame the pc control guard"))?;
    let value = problem
        .eval_to_string(&indexed)
        .context("failed to evaluate pc at the capture transition")?
        .parse::<Term>()
        .context("pc model value is not an SMT term")?;
    Ok(Some(eq_term(pc_term, value)))
}

fn conjoin_control_guard(predicate: Term, control: Option<&Term>) -> Term {
    match control {
        Some(control) => Term::Application {
            qual_identifier: QualIdentifier::simple("and"),
            arguments: vec![control.clone(), predicate],
        },
        None => predicate,
    }
}

fn abstract_native_arrays(term: Term) -> anyhow::Result<Term> {
    let mut abstractor = ArrayAbstractor::default();
    term.accept(&mut abstractor)
        .map_err(|error| anyhow!("{error:?}"))
}

fn contains_smtinterpol_array_diff(term: &Term) -> bool {
    match term {
        Term::Constant(_) => false,
        Term::QualIdentifier(identifier) => identifier.get_name() == "@diff",
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            qual_identifier.get_name() == "@diff"
                || arguments.iter().any(contains_smtinterpol_array_diff)
        }
        Term::Let { var_bindings, term } => {
            var_bindings
                .iter()
                .any(|(_, binding)| contains_smtinterpol_array_diff(binding))
                || contains_smtinterpol_array_diff(term)
        }
        Term::Lambda { term, .. }
        | Term::Forall { term, .. }
        | Term::Exists { term, .. }
        | Term::Attributes { term, .. } => contains_smtinterpol_array_diff(term),
        Term::Match { term, cases } => {
            contains_smtinterpol_array_diff(term)
                || cases
                    .iter()
                    .any(|(_, case)| contains_smtinterpol_array_diff(case))
        }
    }
}

fn symbol_term(name: &str) -> Term {
    Term::QualIdentifier(QualIdentifier::simple(name))
}

fn eq_term(lhs: Term, rhs: Term) -> Term {
    Term::Application {
        qual_identifier: QualIdentifier::simple("="),
        arguments: vec![lhs, rhs],
    }
}

fn not_term(term: Term) -> Term {
    Term::Application {
        qual_identifier: QualIdentifier::simple("not"),
        arguments: vec![term],
    }
}

#[derive(Clone, Copy)]
enum LocalFrame {
    Current,
    Next,
}

pub(crate) fn predicate_ast_size(term: &Term) -> u32 {
    match term {
        Term::Constant(_) | Term::QualIdentifier(_) => 1,
        Term::Application { arguments, .. } => {
            1 + arguments.iter().map(predicate_ast_size).sum::<u32>()
        }
        Term::Let { var_bindings, term } => {
            1 + var_bindings
                .iter()
                .map(|(_, binding)| predicate_ast_size(binding))
                .sum::<u32>()
                + predicate_ast_size(term)
        }
        Term::Lambda { term, .. }
        | Term::Forall { term, .. }
        | Term::Exists { term, .. }
        | Term::Attributes { term, .. } => 1 + predicate_ast_size(term),
        Term::Match { term, cases } => {
            1 + predicate_ast_size(term)
                + cases
                    .iter()
                    .map(|(_, case)| predicate_ast_size(case))
                    .sum::<u32>()
        }
    }
}

/// Whether every application is represented structurally in `ArrayLanguage`
/// with an arity accepted by `translate_term`.
pub(crate) fn predicate_supports_structural_cost(term: &Term) -> bool {
    match term {
        Term::Constant(_) | Term::QualIdentifier(_) => true,
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            let name = qual_identifier.get_name();
            let arity_ok = if name.starts_with("ConstArr_") {
                arguments.len() == 1
            } else if name.starts_with("Read_") {
                arguments.len() == 2
            } else if name.starts_with("Write_") {
                arguments.len() == 3
            } else {
                match name.as_str() {
                    "and" | "or" | "+" | "-" | "*" => true,
                    "not" | "to_real" => arguments.len() == 1,
                    "=>" | "=" | ">=" | ">" | "<=" | "<" | "mod" | "/" | "bvcomp" => {
                        arguments.len() == 2
                    }
                    "ite" => arguments.len() == 3,
                    _ => false,
                }
            };
            arity_ok && arguments.iter().all(predicate_supports_structural_cost)
        }
        Term::Attributes { term, .. } => predicate_supports_structural_cost(term),
        Term::Let { .. }
        | Term::Lambda { .. }
        | Term::Forall { .. }
        | Term::Exists { .. }
        | Term::Match { .. } => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpolant::Interpolant;
    use smt2parser::concrete::{Command, FunctionDec, Identifier, Sort, Symbol};

    fn variable(name: &str) -> Variable {
        let next = format!("{name}_next");
        let sort = Sort::Simple {
            identifier: Identifier::Simple {
                symbol: Symbol("Int".to_string()),
            },
        };
        Variable {
            current: Command::DeclareFun {
                symbol: Symbol(name.to_string()),
                parameters: vec![],
                sort: sort.clone(),
            },
            next: Command::DeclareFun {
                symbol: Symbol(next.clone()),
                parameters: vec![],
                sort: sort.clone(),
            },
            relationship: Command::DefineFun {
                sig: FunctionDec {
                    name: Symbol(format!(".{name}")),
                    parameters: vec![],
                    result: sort,
                },
                term: name.parse().unwrap(),
            },
        }
    }

    #[test]
    fn provenance_includes_the_boundary_before_capture() {
        assert!(has_recent_interpolant_provenance(&[4], 5));
        assert!(!has_recent_interpolant_provenance(&[3], 5));
        assert!(has_recent_interpolant_provenance(&[0], 0));
    }

    #[test]
    fn classifies_first_and_last_occurrence_from_transition_values() {
        assert_eq!(
            classify_trace_values(&[false, false, true, true], 2),
            (true, false)
        );
        assert_eq!(
            classify_trace_values(&[true, true, true, false], 2),
            (false, true)
        );
        assert_eq!(
            classify_trace_values(&[false, true, false], 1),
            (true, true)
        );
        assert_eq!(
            classify_trace_values(&[false, false, false], 1),
            (false, false)
        );
    }

    #[test]
    fn localizes_one_frame_to_current_and_two_frames_to_current_next() {
        let declarations = variable_declarations(&[variable("i"), variable("j")]);
        let one = Interpolant::new("(< i@3 j@3)".parse().unwrap(), 0)
            .predicates()
            .candidates()[0]
            .clone();
        let two = Interpolant::new("(= i@3 j@4)".parse().unwrap(), 0)
            .predicates()
            .candidates()[0]
            .clone();

        assert_eq!(
            localize_predicate(&one, &declarations).unwrap().to_string(),
            "(< i j)"
        );
        assert_eq!(
            localize_predicate(&two, &declarations).unwrap().to_string(),
            "(= i j_next)"
        );
    }

    #[test]
    fn next_shift_rejects_transition_predicates_and_shifts_state_predicates() {
        let declarations = variable_declarations(&[variable("i"), variable("j")]);
        let state: Term = "(< i j)".parse().unwrap();
        let transition: Term = "(< i j_next)".parse().unwrap();

        assert_eq!(
            shift_current_to_next(&state, &declarations)
                .unwrap()
                .to_string(),
            "(< i_next j_next)"
        );
        assert!(shift_current_to_next(&transition, &declarations).is_none());
    }

    #[test]
    fn selection_uses_cost_then_capture_relevance_and_mode() {
        let guard = |predicate_index, occurrence, exact_capture_match, term: &str| GuardCandidate {
            predicate_index,
            source_interpolants: vec![3],
            source_frames: vec![3],
            ranking_term: term.parse().unwrap(),
            capture_guard: term.parse().unwrap(),
            occurrence,
            derivation: Derivation::Predicate,
            exact_capture_match,
        };
        let mut report = Classification {
            eligible: vec![
                guard(0, Occurrence::First, false, "(< i 4)"),
                guard(1, Occurrence::First, true, "(< i 5)"),
                guard(2, Occurrence::Last, true, "(< i 6)"),
            ],
            ..Classification::default()
        };
        let property_terms = report
            .eligible
            .iter()
            .filter_map(|guard| normalized_property_term(&guard.ranking_term))
            .collect();
        let selected = rank_candidates(
            &report,
            &property_terms,
            "i",
            "i_next",
            PredicateRelevancePolicy::ExactProperty,
            &mut |term| {
                let cost = if term.to_string() == "(< i 4)" { 1 } else { 2 };
                (cost, true)
            },
        )
        .unwrap();
        assert_eq!(selected.0.predicate_index, 0);

        report.eligible.remove(0);
        let selected = rank_candidates(
            &report,
            &property_terms,
            "i",
            "i_next",
            PredicateRelevancePolicy::ExactProperty,
            &mut |_| (2, true),
        )
        .unwrap();
        assert_eq!(selected.0.occurrence, Occurrence::Last);
    }

    #[test]
    fn selection_excludes_non_property_overlapping_candidates() {
        let guard = |predicate_index, term: &str| GuardCandidate {
            predicate_index,
            source_interpolants: vec![3],
            source_frames: vec![3],
            ranking_term: term.parse().unwrap(),
            capture_guard: term.parse().unwrap(),
            occurrence: Occurrence::Last,
            derivation: Derivation::Predicate,
            exact_capture_match: false,
        };
        let report = Classification {
            eligible: vec![guard(0, "(= j 0)"), guard(1, "(<= 0 j)")],
            ..Classification::default()
        };
        let property_term: Term = "(>= j@5 0)".parse().unwrap();
        let property_terms = BTreeSet::from([normalized_property_term(&property_term).unwrap()]);

        let selected = rank_candidates(
            &report,
            &property_terms,
            "i",
            "i_next",
            PredicateRelevancePolicy::ExactProperty,
            &mut |_| (102, true),
        )
        .unwrap();

        assert_eq!(selected.0.predicate_index, 1);
        assert!(selected.1.property_overlap);
    }

    #[test]
    fn selection_admits_capture_scalar_without_property_overlap() {
        let report = Classification {
            eligible: vec![GuardCandidate {
                predicate_index: 0,
                source_interpolants: vec![3],
                source_frames: vec![3],
                ranking_term: "(= j 0)".parse().unwrap(),
                capture_guard: "(= j 0)".parse().unwrap(),
                occurrence: Occurrence::Last,
                derivation: Derivation::Predicate,
                exact_capture_match: true,
            }],
            ..Classification::default()
        };
        let property_term: Term = "(>= i@5 0)".parse().unwrap();
        let property_terms = BTreeSet::from([normalized_property_term(&property_term).unwrap()]);

        let selected = rank_candidates(
            &report,
            &property_terms,
            "j",
            "j_next",
            PredicateRelevancePolicy::CaptureAligned,
            &mut |_| (1, true),
        )
        .unwrap();

        assert_eq!(selected.0.predicate_index, 0);
        assert!(!selected.1.property_overlap);
        assert_eq!(selected.1.relevance, GuardRelevance::CaptureScalar);
    }

    #[test]
    fn selection_rejects_concrete_array_index_for_symbolic_capture() {
        let report = Classification {
            eligible: vec![GuardCandidate {
                predicate_index: 0,
                source_interpolants: vec![3],
                source_frames: vec![3],
                ranking_term: "(= (Read_Int_Int a 0) 1)".parse().unwrap(),
                capture_guard: "(= (Read_Int_Int a 0) 1)".parse().unwrap(),
                occurrence: Occurrence::Last,
                derivation: Derivation::Predicate,
                exact_capture_match: false,
            }],
            ..Classification::default()
        };
        let property_term: Term = "(= (Read_Int_Int a Z) 1)".parse().unwrap();
        let property_terms = BTreeSet::from([normalized_property_term(&property_term).unwrap()]);

        assert!(rank_candidates(
            &report,
            &property_terms,
            "i",
            "i_next",
            PredicateRelevancePolicy::CaptureAligned,
            &mut |_| (1, true),
        )
        .is_none());
    }

    #[test]
    fn selection_admits_array_predicate_indexed_by_capture_target() {
        let report = Classification {
            eligible: vec![GuardCandidate {
                predicate_index: 0,
                source_interpolants: vec![3],
                source_frames: vec![3],
                ranking_term: "(= 0 (Read_Int_Int a i))".parse().unwrap(),
                capture_guard: "(= 0 (Read_Int_Int a i))".parse().unwrap(),
                occurrence: Occurrence::Last,
                derivation: Derivation::Predicate,
                exact_capture_match: true,
            }],
            ..Classification::default()
        };
        let property_term: Term = "(= (Read_Int_Int a Z) 1)".parse().unwrap();
        let property_terms = BTreeSet::from([normalized_property_term(&property_term).unwrap()]);

        let selected = rank_candidates(
            &report,
            &property_terms,
            "i",
            "i_next",
            PredicateRelevancePolicy::CaptureAligned,
            &mut |_| (1, true),
        )
        .unwrap();

        assert_eq!(selected.1.relevance, GuardRelevance::CaptureIndexedArray);
    }

    #[test]
    fn selection_prefers_capture_scalar_over_capture_indexed_array() {
        let guard = |predicate_index, term: &str| GuardCandidate {
            predicate_index,
            source_interpolants: vec![3],
            source_frames: vec![3],
            ranking_term: term.parse().unwrap(),
            capture_guard: term.parse().unwrap(),
            occurrence: Occurrence::Last,
            derivation: Derivation::Predicate,
            exact_capture_match: true,
        };
        let report = Classification {
            eligible: vec![guard(0, "(= 0 (Read_Int_Int a i))"), guard(1, "(= 1 i)")],
            ..Classification::default()
        };

        let selected = rank_candidates(
            &report,
            &BTreeSet::new(),
            "i",
            "i_next",
            PredicateRelevancePolicy::CaptureAligned,
            &mut |term| {
                if contains_array_operation(term) {
                    (1, true)
                } else {
                    (100, true)
                }
            },
        )
        .unwrap();

        assert_eq!(selected.0.predicate_index, 1);
        assert_eq!(selected.1.relevance, GuardRelevance::CaptureScalar);
    }

    #[test]
    fn structural_cost_support_rejects_opaque_or_invalid_arity_terms() {
        assert!(predicate_supports_structural_cost(
            &"(= (Read_Int_Int a i) x)".parse().unwrap()
        ));
        assert!(!predicate_supports_structural_cost(
            &"(custom-predicate i)".parse().unwrap()
        ));
        assert!(!predicate_supports_structural_cost(
            &"(= i j k)".parse().unwrap()
        ));
    }

    #[test]
    fn identifies_smtinterpol_array_diff_witnesses() {
        assert!(contains_smtinterpol_array_diff(
            &"(= (@diff a b) i)".parse().unwrap()
        ));
        assert!(!contains_smtinterpol_array_diff(
            &"(= (Read_Int_Int a i) value)".parse().unwrap()
        ));
    }
}
