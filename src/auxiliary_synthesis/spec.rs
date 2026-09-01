use std::collections::{BTreeMap, BTreeSet};

use anyhow::{anyhow, Context};
use serde::{Deserialize, Serialize};
use smt2parser::concrete::{
    AttributeValue, Command, FunctionDec, Identifier, Keyword, QualIdentifier, Sort, Symbol, Term,
};
use smt2parser::vmt::{
    split_framed_symbol, variable::var_is_immutable, variable::Variable, VMTModel,
};

use crate::auxiliary_synthesis::{ArrayConflictRecord, FrameSpan, GuardPolicy, SynthesisTrigger};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HistorySpec {
    pub name: String,
    pub next_name: String,
    pub sort: Sort,
    pub capture_term: Term,
    pub capture_guard: Term,
    #[serde(default)]
    pub capture_mode: HistoryCaptureMode,
    pub initial_value: Option<Term>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
#[serde(tag = "mode", rename_all = "snake_case")]
pub enum HistoryCaptureMode {
    FirstOccurrence {
        latch_name: String,
        latch_next_name: String,
    },
    #[default]
    LastOccurrence,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProphecySpec {
    pub name: String,
    pub next_name: String,
    pub sort: Sort,
    pub initial_value: Option<Term>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AuxiliarySpec {
    pub aux_id: String,
    pub source_conflict_id: String,
    pub source_term_hash: String,
    pub depth_created: u16,
    pub refinement_step_created: u32,
    pub history: HistorySpec,
    pub prophecy: Option<ProphecySpec>,
    pub localized_axiom: Option<Term>,
    pub property_constraint: Option<Term>,
    pub guard_policy: GuardPolicy,
    pub trigger: SynthesisTrigger,
    pub non_monotonicity_check: NonMonotonicityCheckRecord,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AuxiliaryRecord {
    pub aux_id: String,
    pub source_conflict_id: String,
    pub source_term_hash: String,
    pub depth_created: u16,
    pub refinement_step_created: u32,
    pub installed_at_depth: u16,
    pub trigger: SynthesisTrigger,
    pub guard_policy: GuardPolicy,
    pub history_name: String,
    pub prophecy_name: Option<String>,
    pub capture_term: String,
    pub capture_guard: String,
    #[serde(default)]
    pub capture_mode: HistoryCaptureMode,
    pub source_instantiation: String,
    pub localized_axiom: Option<String>,
    #[serde(default)]
    pub property_constraint: Option<String>,
    pub source_frame_span: FrameSpan,
    pub localized_frame_span: Option<FrameSpan>,
    pub non_monotonicity_check: NonMonotonicityCheckRecord,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NonMonotonicityCheckRecord {
    pub status: NonMonotonicityStatus,
    pub source_term: String,
    pub localized_term: Option<String>,
    pub source_frame_span: FrameSpan,
    pub localized_frame_span: Option<FrameSpan>,
    pub note: String,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum NonMonotonicityStatus {
    Pending,
    Skipped,
}

impl AuxiliarySpec {
    pub fn from_conflict(
        conflict: &ArrayConflictRecord,
        variables: &[Variable],
        trigger: SynthesisTrigger,
        guard_policy: GuardPolicy,
    ) -> anyhow::Result<Self> {
        if guard_policy != GuardPolicy::True {
            return Err(anyhow!(
                "guard policy {guard_policy} requires a synthesized and validated guard"
            ));
        }
        let capture = select_capture_variable(conflict, variables)
            .with_context(|| format!("no capture variable found for {}", conflict.conflict_id))?;
        let safe_id = sanitize_symbol_fragment(&conflict.conflict_id);
        let aux_id = format!("aux_{safe_id}");
        let history_name = format!("yb_hist_{safe_id}");
        let prophecy_name = format!("yb_prop_{safe_id}");
        // The highest-framed value is observed in the post-state of the
        // transition that reaches it, so capture the declared next symbol.
        let capture_term = symbol_term(&capture.next_name);
        let capture_guard = true_term();
        let localized_axiom =
            localize_conflict_term(&conflict.term, &capture, &prophecy_name, variables)?;
        let localized_frame_span = FrameSpan::from_term(&localized_axiom);
        let non_monotonicity_check = NonMonotonicityCheckRecord {
            status: NonMonotonicityStatus::Pending,
            source_term: conflict.term.to_string(),
            localized_term: Some(localized_axiom.to_string()),
            source_frame_span: conflict.frame_span.clone(),
            localized_frame_span: Some(localized_frame_span),
            note: "localized axiom replaces a framed term with a stuttering prophecy variable; semantic monotonicity not checked yet".to_string(),
        };

        Ok(Self {
            aux_id,
            source_conflict_id: conflict.conflict_id.clone(),
            source_term_hash: conflict.term_hash.clone(),
            depth_created: conflict.depth,
            refinement_step_created: conflict.refinement_step,
            history: HistorySpec {
                name: history_name.clone(),
                next_name: format!("{history_name}_next"),
                sort: capture.sort.clone(),
                capture_term,
                capture_guard,
                capture_mode: HistoryCaptureMode::LastOccurrence,
                initial_value: None,
            },
            prophecy: Some(ProphecySpec {
                name: prophecy_name.clone(),
                next_name: format!("{prophecy_name}_next"),
                sort: capture.sort,
                initial_value: None,
            }),
            localized_axiom: Some(localized_axiom),
            property_constraint: Some(eq_term(
                symbol_term(&prophecy_name),
                symbol_term(&history_name),
            )),
            guard_policy,
            trigger,
            non_monotonicity_check,
        })
    }

    pub fn variables(&self) -> Vec<Variable> {
        let mut variables = vec![history_spec_to_variable(&self.history)];
        if let HistoryCaptureMode::FirstOccurrence {
            latch_name,
            latch_next_name,
        } = &self.history.capture_mode
        {
            variables.push(auxiliary_variable(
                latch_name,
                latch_next_name,
                &bool_sort(),
            ));
        }
        if let Some(prophecy) = &self.prophecy {
            variables.push(prophecy_spec_to_variable(prophecy));
        }
        variables
    }

    pub fn transition_terms(&self) -> Vec<Term> {
        let mut terms = vec![];
        let capture_condition = match &self.history.capture_mode {
            HistoryCaptureMode::FirstOccurrence {
                latch_name,
                latch_next_name,
            } => {
                let latch = symbol_term(latch_name);
                terms.push(eq_term(
                    symbol_term(latch_next_name),
                    or_term(vec![latch.clone(), self.history.capture_guard.clone()]),
                ));
                and_term(vec![self.history.capture_guard.clone(), not_term(latch)])
            }
            HistoryCaptureMode::LastOccurrence => self.history.capture_guard.clone(),
        };
        terms.insert(
            0,
            eq_term(
                symbol_term(&self.history.next_name),
                ite_term(
                    capture_condition,
                    self.history.capture_term.clone(),
                    symbol_term(&self.history.name),
                ),
            ),
        );
        if let Some(prophecy) = &self.prophecy {
            terms.push(eq_term(
                symbol_term(&prophecy.next_name),
                symbol_term(&prophecy.name),
            ));
        }
        if let Some(localized_axiom) = &self.localized_axiom {
            terms.push(localized_axiom.clone());
        }
        terms
    }

    pub fn init_terms(&self) -> Vec<Term> {
        let mut terms = vec![];
        if let Some(initial_value) = &self.history.initial_value {
            terms.push(eq_term(
                symbol_term(&self.history.name),
                initial_value.clone(),
            ));
        }
        if let HistoryCaptureMode::FirstOccurrence { latch_name, .. } = &self.history.capture_mode {
            terms.push(not_term(symbol_term(latch_name)));
        }
        if let Some(prophecy) = &self.prophecy {
            if let Some(initial_value) = &prophecy.initial_value {
                terms.push(eq_term(symbol_term(&prophecy.name), initial_value.clone()));
            }
        }
        terms
    }

    pub fn record(&self, installed_at_depth: u16) -> AuxiliaryRecord {
        AuxiliaryRecord {
            aux_id: self.aux_id.clone(),
            source_conflict_id: self.source_conflict_id.clone(),
            source_term_hash: self.source_term_hash.clone(),
            depth_created: self.depth_created,
            refinement_step_created: self.refinement_step_created,
            installed_at_depth,
            trigger: self.trigger,
            guard_policy: self.guard_policy,
            history_name: self.history.name.clone(),
            prophecy_name: self.prophecy.as_ref().map(|prophecy| prophecy.name.clone()),
            capture_term: self.history.capture_term.to_string(),
            capture_guard: self.history.capture_guard.to_string(),
            capture_mode: self.history.capture_mode.clone(),
            source_instantiation: self.non_monotonicity_check.source_term.clone(),
            localized_axiom: self.localized_axiom.as_ref().map(ToString::to_string),
            property_constraint: self.property_constraint.as_ref().map(ToString::to_string),
            source_frame_span: self.non_monotonicity_check.source_frame_span.clone(),
            localized_frame_span: self.non_monotonicity_check.localized_frame_span.clone(),
            non_monotonicity_check: self.non_monotonicity_check.clone(),
        }
    }

    /// Reflect this runtime auxiliary transformation in a VMT model so
    /// downstream proof engines see the same system as bounded checking.
    pub fn apply_to_model(&self, model: &mut VMTModel) {
        for variable in self.variables() {
            model.add_state_variable(variable);
        }
        for init_term in self.init_terms() {
            model.add_initial_constraint(init_term);
        }
        for transition_term in self.transition_terms() {
            model.add_transition_constraint(transition_term);
        }
        if let Some(property_constraint) = &self.property_constraint {
            model.guard_property(property_constraint.clone());
        }
    }
}

fn history_spec_to_variable(spec: &HistorySpec) -> Variable {
    auxiliary_variable(&spec.name, &spec.next_name, &spec.sort)
}

fn prophecy_spec_to_variable(spec: &ProphecySpec) -> Variable {
    auxiliary_variable(&spec.name, &spec.next_name, &spec.sort)
}

fn auxiliary_variable(name: &str, next_name: &str, sort: &Sort) -> Variable {
    Variable {
        current: Command::DeclareFun {
            symbol: Symbol(name.to_string()),
            parameters: vec![],
            sort: sort.clone(),
        },
        next: Command::DeclareFun {
            symbol: Symbol(next_name.to_string()),
            parameters: vec![],
            sort: sort.clone(),
        },
        relationship: Command::DefineFun {
            sig: FunctionDec {
                name: Symbol(format!("{name}_relationship")),
                parameters: vec![],
                result: bool_sort(),
            },
            term: Term::Attributes {
                term: Box::new(symbol_term(name)),
                attributes: vec![(
                    Keyword("next".to_string()),
                    AttributeValue::Symbol(Symbol(next_name.to_string())),
                )],
            },
        },
    }
}

#[derive(Clone, Debug)]
struct CaptureVariable {
    base_name: String,
    next_name: String,
    frame: i64,
    sort: Sort,
}

fn select_capture_variable(
    conflict: &ArrayConflictRecord,
    variables: &[Variable],
) -> anyhow::Result<CaptureVariable> {
    let variable_declarations = variables
        .iter()
        .filter_map(|variable| match &variable.current {
            Command::DeclareFun {
                symbol,
                parameters,
                sort,
            } if parameters.is_empty() => Some((
                symbol.0.clone(),
                (variable.get_next_variable_name().clone(), sort.clone()),
            )),
            _ => None,
        })
        .collect::<std::collections::BTreeMap<_, _>>();
    let target_frame = conflict
        .frame_span
        .max_frame
        .or(conflict.frame_span.min_frame)
        .ok_or_else(|| anyhow!("conflict has no framed symbols"))?;

    let mut symbols = vec![];
    collect_framed_symbols(&conflict.term, &mut symbols);
    symbols
        .into_iter()
        .filter(|(_, frame)| *frame == target_frame)
        .filter(|(base, _)| !var_is_immutable(base))
        .find_map(|(base_name, _)| {
            variable_declarations
                .get(&base_name)
                .and_then(|(next_name, sort)| {
                    (!sort_is_array(sort)).then(|| CaptureVariable {
                        base_name,
                        next_name: next_name.clone(),
                        frame: target_frame,
                        sort: sort.clone(),
                    })
                })
        })
        .ok_or_else(|| anyhow!("no declared scalar state variable found at frame {target_frame}"))
}

fn sort_is_array(sort: &Sort) -> bool {
    match sort {
        Sort::Simple { identifier } => identifier_name(identifier).starts_with("Array"),
        Sort::Parameterized {
            identifier,
            parameters: _,
        } => identifier_name(identifier) == "Array",
    }
}

fn identifier_name(identifier: &Identifier) -> &str {
    match identifier {
        Identifier::Simple { symbol } | Identifier::Indexed { symbol, indices: _ } => &symbol.0,
    }
}

fn localize_conflict_term(
    term: &Term,
    capture: &CaptureVariable,
    prophecy_name: &str,
    variables: &[Variable],
) -> anyhow::Result<Term> {
    let declarations = variables
        .iter()
        .map(|variable| {
            (
                variable.get_current_variable_name().clone(),
                variable.get_next_variable_name().clone(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut symbols = vec![];
    collect_framed_symbols(term, &mut symbols);
    let remaining_frames = symbols
        .iter()
        .filter(|(base, frame)| !(base == &capture.base_name && *frame == capture.frame))
        .filter(|(base, _)| !var_is_immutable(base))
        .map(|(_, frame)| *frame)
        .collect::<BTreeSet<_>>();
    let frame_roles = match remaining_frames
        .iter()
        .copied()
        .collect::<Vec<_>>()
        .as_slice()
    {
        [] => BTreeMap::new(),
        [frame] => BTreeMap::from([(*frame, LocalFrame::Current)]),
        [current, next] if *next == *current + 1 => {
            BTreeMap::from([(*current, LocalFrame::Current), (*next, LocalFrame::Next)])
        }
        frames => {
            return Err(anyhow!(
                "cannot localize remaining non-adjacent frames {frames:?} with one prophecy"
            ))
        }
    };

    rewrite_localized_term(term, capture, prophecy_name, &declarations, &frame_roles)
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum LocalFrame {
    Current,
    Next,
}

fn rewrite_localized_term(
    term: &Term,
    capture: &CaptureVariable,
    prophecy_name: &str,
    declarations: &BTreeMap<String, String>,
    frame_roles: &BTreeMap<i64, LocalFrame>,
) -> anyhow::Result<Term> {
    match term {
        Term::Constant(_) => Ok(term.clone()),
        Term::QualIdentifier(qi) => Ok(Term::QualIdentifier(localize_qual_identifier(
            qi,
            capture,
            prophecy_name,
            declarations,
            frame_roles,
        )?)),
        Term::Application {
            qual_identifier,
            arguments,
        } => Ok(Term::Application {
            qual_identifier: localize_qual_identifier(
                qual_identifier,
                capture,
                prophecy_name,
                declarations,
                frame_roles,
            )?,
            arguments: arguments
                .iter()
                .map(|argument| {
                    rewrite_localized_term(
                        argument,
                        capture,
                        prophecy_name,
                        declarations,
                        frame_roles,
                    )
                })
                .collect::<anyhow::Result<Vec<_>>>()?,
        }),
        Term::Let { var_bindings, term } => Ok(Term::Let {
            var_bindings: var_bindings
                .iter()
                .map(|(symbol, binding)| {
                    Ok((
                        symbol.clone(),
                        rewrite_localized_term(
                            binding,
                            capture,
                            prophecy_name,
                            declarations,
                            frame_roles,
                        )?,
                    ))
                })
                .collect::<anyhow::Result<Vec<_>>>()?,
            term: Box::new(rewrite_localized_term(
                term,
                capture,
                prophecy_name,
                declarations,
                frame_roles,
            )?),
        }),
        Term::Lambda { vars, term } => Ok(Term::Lambda {
            vars: vars.clone(),
            term: Box::new(rewrite_localized_term(
                term,
                capture,
                prophecy_name,
                declarations,
                frame_roles,
            )?),
        }),
        Term::Forall { vars, term } => Ok(Term::Forall {
            vars: vars.clone(),
            term: Box::new(rewrite_localized_term(
                term,
                capture,
                prophecy_name,
                declarations,
                frame_roles,
            )?),
        }),
        Term::Exists { vars, term } => Ok(Term::Exists {
            vars: vars.clone(),
            term: Box::new(rewrite_localized_term(
                term,
                capture,
                prophecy_name,
                declarations,
                frame_roles,
            )?),
        }),
        Term::Match { term, cases } => Ok(Term::Match {
            term: Box::new(rewrite_localized_term(
                term,
                capture,
                prophecy_name,
                declarations,
                frame_roles,
            )?),
            cases: cases
                .iter()
                .map(|(symbols, case_term)| {
                    Ok((
                        symbols.clone(),
                        rewrite_localized_term(
                            case_term,
                            capture,
                            prophecy_name,
                            declarations,
                            frame_roles,
                        )?,
                    ))
                })
                .collect::<anyhow::Result<Vec<_>>>()?,
        }),
        Term::Attributes { term, attributes } => Ok(Term::Attributes {
            term: Box::new(rewrite_localized_term(
                term,
                capture,
                prophecy_name,
                declarations,
                frame_roles,
            )?),
            attributes: attributes.clone(),
        }),
    }
}

fn localize_qual_identifier(
    qi: &QualIdentifier,
    capture: &CaptureVariable,
    prophecy_name: &str,
    declarations: &BTreeMap<String, String>,
    frame_roles: &BTreeMap<i64, LocalFrame>,
) -> anyhow::Result<QualIdentifier> {
    let name = qi.get_name();
    let Some((base, frame)) = split_framed_symbol(&name) else {
        return Ok(qi.clone());
    };
    if base == capture.base_name && frame == capture.frame {
        return Ok(QualIdentifier::simple(prophecy_name));
    }
    if var_is_immutable(&base) {
        return Ok(QualIdentifier::simple(base));
    }
    let next_name = declarations
        .get(&base)
        .ok_or_else(|| anyhow!("cannot localize undeclared framed symbol {name}"))?;
    match frame_roles.get(&frame) {
        Some(LocalFrame::Current) => Ok(QualIdentifier::simple(base)),
        Some(LocalFrame::Next) => Ok(QualIdentifier::simple(next_name)),
        None => Err(anyhow!("no local frame mapping for {name}")),
    }
}

pub fn term_contains_auxiliary_symbol(term: &Term) -> bool {
    match term {
        Term::Constant(_) => false,
        Term::QualIdentifier(qi) => is_auxiliary_symbol_name(&qi.get_name()),
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            is_auxiliary_symbol_name(&qual_identifier.get_name())
                || arguments.iter().any(term_contains_auxiliary_symbol)
        }
        Term::Let { var_bindings, term } => {
            var_bindings
                .iter()
                .any(|(_, binding)| term_contains_auxiliary_symbol(binding))
                || term_contains_auxiliary_symbol(term)
        }
        Term::Lambda { term, .. } | Term::Forall { term, .. } | Term::Exists { term, .. } => {
            term_contains_auxiliary_symbol(term)
        }
        Term::Match { term, cases } => {
            term_contains_auxiliary_symbol(term)
                || cases
                    .iter()
                    .any(|(_, case_term)| term_contains_auxiliary_symbol(case_term))
        }
        Term::Attributes { term, .. } => term_contains_auxiliary_symbol(term),
    }
}

fn is_auxiliary_symbol_name(name: &str) -> bool {
    name.starts_with("yb_hist_") || name.starts_with("yb_prop_") || name.starts_with("yb_capture_")
}

fn collect_framed_symbols(term: &Term, symbols: &mut Vec<(String, i64)>) {
    match term {
        Term::Constant(_) => {}
        Term::QualIdentifier(qi) => collect_qual_identifier(qi, symbols),
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            collect_qual_identifier(qual_identifier, symbols);
            for argument in arguments {
                collect_framed_symbols(argument, symbols);
            }
        }
        Term::Let { var_bindings, term } => {
            for (_, binding) in var_bindings {
                collect_framed_symbols(binding, symbols);
            }
            collect_framed_symbols(term, symbols);
        }
        Term::Lambda { term, .. } | Term::Forall { term, .. } | Term::Exists { term, .. } => {
            collect_framed_symbols(term, symbols);
        }
        Term::Match { term, cases } => {
            collect_framed_symbols(term, symbols);
            for (_, case_term) in cases {
                collect_framed_symbols(case_term, symbols);
            }
        }
        Term::Attributes { term, .. } => {
            collect_framed_symbols(term, symbols);
        }
    }
}

fn collect_qual_identifier(qi: &QualIdentifier, symbols: &mut Vec<(String, i64)>) {
    if let Some((base, frame)) = split_framed_symbol(&qi.get_name()) {
        symbols.push((base, frame));
    }
}

fn sanitize_symbol_fragment(fragment: &str) -> String {
    fragment
        .chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                ch
            } else {
                '_'
            }
        })
        .collect()
}

fn app(name: &str, arguments: Vec<Term>) -> Term {
    Term::Application {
        qual_identifier: QualIdentifier::simple(name),
        arguments,
    }
}

fn eq_term(left: Term, right: Term) -> Term {
    app("=", vec![left, right])
}

fn ite_term(condition: Term, then_term: Term, else_term: Term) -> Term {
    app("ite", vec![condition, then_term, else_term])
}

fn and_term(arguments: Vec<Term>) -> Term {
    app("and", arguments)
}

fn or_term(arguments: Vec<Term>) -> Term {
    app("or", arguments)
}

fn not_term(term: Term) -> Term {
    app("not", vec![term])
}

fn symbol_term(name: &str) -> Term {
    Term::QualIdentifier(QualIdentifier::simple(name))
}

fn true_term() -> Term {
    symbol_term("true")
}

fn bool_sort() -> Sort {
    Sort::Simple {
        identifier: Identifier::Simple {
            symbol: Symbol("Bool".to_string()),
        },
    }
}

#[cfg(test)]
mod tests {
    use smt2parser::{get_term_from_term_string, Numeral};

    use super::*;

    fn int_sort() -> Sort {
        Sort::Simple {
            identifier: Identifier::Simple {
                symbol: Symbol("Int".to_string()),
            },
        }
    }

    fn variable(name: &str) -> Variable {
        Variable {
            current: Command::DeclareFun {
                symbol: Symbol(name.to_string()),
                parameters: vec![],
                sort: int_sort(),
            },
            next: Command::DeclareFun {
                symbol: Symbol(format!("{name}_next")),
                parameters: vec![],
                sort: int_sort(),
            },
            relationship: Command::DeclareSort {
                symbol: Symbol("Unused".to_string()),
                arity: Numeral::from(0_u32),
            },
        }
    }

    #[test]
    fn builds_last_occurrence_history_prophecy_and_local_schema() {
        let term = get_term_from_term_string("(= x@0 y@2)");
        let conflict = ArrayConflictRecord::new(
            0,
            "abstract-instantiation-0",
            "test",
            "(= x@0 y@2)".parse().unwrap(),
            term,
            2,
            3,
            1,
            vec![],
        );
        let spec = AuxiliarySpec::from_conflict(
            &conflict,
            &[variable("x"), variable("y")],
            SynthesisTrigger::NonLocal,
            GuardPolicy::True,
        )
        .unwrap();
        assert_eq!(spec.history.capture_term.to_string(), "y_next");
        assert_eq!(
            spec.history.capture_mode,
            HistoryCaptureMode::LastOccurrence
        );
        assert_eq!(
            spec.localized_axiom.as_ref().unwrap().to_string(),
            "(= x yb_prop_conflict_2_3_0)"
        );
        assert_eq!(
            spec.property_constraint.as_ref().unwrap().to_string(),
            "(= yb_prop_conflict_2_3_0 yb_hist_conflict_2_3_0)"
        );
        assert_eq!(spec.transition_terms().len(), 3);
        assert!(FrameSpan::from_term(spec.localized_axiom.as_ref().unwrap())
            .frames
            .is_empty());
        assert_eq!(
            spec.non_monotonicity_check.status,
            NonMonotonicityStatus::Pending
        );
    }

    #[test]
    fn first_occurrence_capture_adds_a_monotone_latch() {
        let history = HistorySpec {
            name: "h".to_string(),
            next_name: "h_next".to_string(),
            sort: int_sort(),
            capture_term: symbol_term("x_next"),
            capture_guard: symbol_term("g"),
            capture_mode: HistoryCaptureMode::FirstOccurrence {
                latch_name: "yb_capture_h".to_string(),
                latch_next_name: "yb_capture_h_next".to_string(),
            },
            initial_value: None,
        };
        let spec = AuxiliarySpec {
            aux_id: "aux_test".to_string(),
            source_conflict_id: "conflict-test".to_string(),
            source_term_hash: "hash-test".to_string(),
            depth_created: 2,
            refinement_step_created: 0,
            history,
            prophecy: None,
            localized_axiom: None,
            property_constraint: None,
            guard_policy: GuardPolicy::Interpolant,
            trigger: SynthesisTrigger::NonLocal,
            non_monotonicity_check: NonMonotonicityCheckRecord {
                status: NonMonotonicityStatus::Pending,
                source_term: "true".to_string(),
                localized_term: None,
                source_frame_span: FrameSpan::default(),
                localized_frame_span: None,
                note: "test".to_string(),
            },
        };

        assert_eq!(spec.variables().len(), 2);
        assert_eq!(spec.init_terms()[0].to_string(), "(not yb_capture_h)");
        assert_eq!(
            spec.transition_terms()
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>(),
            vec![
                "(= h_next (ite (and g (not yb_capture_h)) x_next h))",
                "(= yb_capture_h_next (or yb_capture_h g))",
            ]
        );
    }

    #[test]
    fn localization_maps_adjacent_remaining_frames_to_current_and_next() {
        let term = get_term_from_term_string("(= (f x@1 x@2) y@4)");
        let conflict = ArrayConflictRecord::new(
            0,
            "abstract-instantiation-0",
            "test",
            "(= x@1 y@4)".parse().unwrap(),
            term,
            4,
            0,
            1,
            vec![],
        );
        let spec = AuxiliarySpec::from_conflict(
            &conflict,
            &[variable("x"), variable("y")],
            SynthesisTrigger::NonLocal,
            GuardPolicy::True,
        )
        .unwrap();

        assert_eq!(
            spec.localized_axiom.unwrap().to_string(),
            "(= (f x x_next) yb_prop_conflict_4_0_0)"
        );
    }

    #[test]
    fn localization_rejects_non_adjacent_remaining_frames() {
        let term = get_term_from_term_string("(= (+ x@0 x@2) y@4)");
        let conflict = ArrayConflictRecord::new(
            0,
            "abstract-instantiation-0",
            "test",
            "(= x@0 y@4)".parse().unwrap(),
            term,
            4,
            0,
            1,
            vec![],
        );

        let error = AuxiliarySpec::from_conflict(
            &conflict,
            &[variable("x"), variable("y")],
            SynthesisTrigger::NonLocal,
            GuardPolicy::True,
        )
        .unwrap_err();
        assert!(error.to_string().contains("non-adjacent frames"));
    }

    #[test]
    fn conflict_constructor_never_falls_back_to_a_true_guard() {
        let term = get_term_from_term_string("(= x@0 y@2)");
        let conflict = ArrayConflictRecord::new(
            0,
            "abstract-instantiation-0",
            "test",
            "(= x@0 y@2)".parse().unwrap(),
            term,
            2,
            0,
            1,
            vec![],
        );

        let error = AuxiliarySpec::from_conflict(
            &conflict,
            &[variable("x"), variable("y")],
            SynthesisTrigger::NonLocal,
            GuardPolicy::Interpolant,
        )
        .unwrap_err();
        assert!(error.to_string().contains("requires a synthesized"));
    }

    #[test]
    fn applying_a_spec_exports_the_complete_auxiliary_system() {
        let mut model = VMTModel::from_path("./examples/array/array_copy.vmt").unwrap();
        let spec = AuxiliarySpec {
            aux_id: "aux_export".to_string(),
            source_conflict_id: "conflict-export".to_string(),
            source_term_hash: "hash-export".to_string(),
            depth_created: 2,
            refinement_step_created: 0,
            history: HistorySpec {
                name: "yb_hist_export".to_string(),
                next_name: "yb_hist_export_next".to_string(),
                sort: int_sort(),
                capture_term: "0".parse().unwrap(),
                capture_guard: true_term(),
                capture_mode: HistoryCaptureMode::FirstOccurrence {
                    latch_name: "yb_capture_export".to_string(),
                    latch_next_name: "yb_capture_export_next".to_string(),
                },
                initial_value: None,
            },
            prophecy: Some(ProphecySpec {
                name: "yb_prop_export".to_string(),
                next_name: "yb_prop_export_next".to_string(),
                sort: int_sort(),
                initial_value: None,
            }),
            localized_axiom: Some("(= yb_prop_export yb_hist_export)".parse().unwrap()),
            property_constraint: Some("(= yb_prop_export yb_hist_export)".parse().unwrap()),
            guard_policy: GuardPolicy::Interpolant,
            trigger: SynthesisTrigger::NonLocal,
            non_monotonicity_check: NonMonotonicityCheckRecord {
                status: NonMonotonicityStatus::Pending,
                source_term: "true".to_string(),
                localized_term: Some("(= yb_prop_export yb_hist_export)".to_string()),
                source_frame_span: FrameSpan::default(),
                localized_frame_span: Some(FrameSpan::default()),
                note: "test".to_string(),
            },
        };

        let original_property = model.get_property_for_yardbird();
        spec.apply_to_model(&mut model);

        let variable_names = model
            .get_state_variables()
            .into_iter()
            .map(|variable| variable.get_current_variable_name().clone())
            .collect::<Vec<_>>();
        assert!(variable_names.contains(&"yb_hist_export".to_string()));
        assert!(variable_names.contains(&"yb_capture_export".to_string()));
        assert!(variable_names.contains(&"yb_prop_export".to_string()));
        assert!(model
            .get_initial_condition_for_yardbird()
            .to_string()
            .contains("(not yb_capture_export)"));
        assert!(model
            .get_trans_condition_for_yardbird()
            .to_string()
            .contains("(= yb_prop_export_next yb_prop_export)"));
        assert_eq!(
            model.get_property_for_yardbird().to_string(),
            format!("(=> (= yb_prop_export yb_hist_export) {original_property})")
        );
    }

    #[test]
    fn detects_auxiliary_symbols_in_terms() {
        let original: Term = "(= (Read_Int_Int a@0 i@0) (Read_Int_Int a@0 i@1))"
            .parse()
            .unwrap();
        let auxiliary: Term =
            "(= (Read_Int_Int a@0 yb_prop_conflict_2_0_0@0) (Read_Int_Int a@0 i@1))"
                .parse()
                .unwrap();

        assert!(!term_contains_auxiliary_symbol(&original));
        assert!(term_contains_auxiliary_symbol(&auxiliary));
    }
}
