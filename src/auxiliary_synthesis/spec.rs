use anyhow::{anyhow, Context};
use serde::{Deserialize, Serialize};
use smt2parser::concrete::{
    AttributeValue, Command, FunctionDec, Identifier, Keyword, QualIdentifier, Sort, Symbol, Term,
};
use smt2parser::vmt::{variable::var_is_immutable, variable::Variable, VARIABLE_FRAME_DELIMITER};

use crate::auxiliary_synthesis::{ArrayConflictRecord, FrameSpan, GuardPolicy, SynthesisTrigger};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HistorySpec {
    pub name: String,
    pub next_name: String,
    pub sort: Sort,
    pub capture_term: Term,
    pub capture_guard: Term,
    pub initial_value: Option<Term>,
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
    pub source_instantiation: String,
    pub localized_axiom: Option<String>,
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
        let capture = select_capture_variable(conflict, variables)
            .with_context(|| format!("no capture variable found for {}", conflict.conflict_id))?;
        let safe_id = sanitize_symbol_fragment(&conflict.conflict_id);
        let aux_id = format!("aux_{safe_id}");
        let history_name = format!("yb_hist_{safe_id}");
        let prophecy_name = format!("yb_prop_{safe_id}");
        let capture_term = Term::QualIdentifier(QualIdentifier::simple(&capture.base_name));
        let capture_guard = true_term();
        let localized_axiom = replace_framed_symbol(
            &conflict.term,
            &capture.base_name,
            capture.frame,
            &prophecy_name,
        );
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
                initial_value: None,
            },
            prophecy: Some(ProphecySpec {
                name: prophecy_name.clone(),
                next_name: format!("{prophecy_name}_next"),
                sort: capture.sort,
                initial_value: None,
            }),
            localized_axiom: Some(localized_axiom),
            property_constraint: None,
            guard_policy,
            trigger,
            non_monotonicity_check,
        })
    }

    pub fn variables(&self) -> Vec<Variable> {
        let mut variables = vec![history_spec_to_variable(&self.history)];
        if let Some(prophecy) = &self.prophecy {
            variables.push(prophecy_spec_to_variable(prophecy));
        }
        variables
    }

    pub fn transition_terms(&self) -> Vec<Term> {
        let mut terms = vec![eq_term(
            symbol_term(&self.history.next_name),
            ite_term(
                self.history.capture_guard.clone(),
                self.history.capture_term.clone(),
                symbol_term(&self.history.name),
            ),
        )];
        if let Some(prophecy) = &self.prophecy {
            terms.push(eq_term(
                symbol_term(&prophecy.next_name),
                symbol_term(&prophecy.name),
            ));
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
            source_instantiation: self.non_monotonicity_check.source_term.clone(),
            localized_axiom: self.localized_axiom.as_ref().map(ToString::to_string),
            source_frame_span: self.non_monotonicity_check.source_frame_span.clone(),
            localized_frame_span: self.non_monotonicity_check.localized_frame_span.clone(),
            non_monotonicity_check: self.non_monotonicity_check.clone(),
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
    frame: i64,
    sort: Sort,
}

fn select_capture_variable(
    conflict: &ArrayConflictRecord,
    variables: &[Variable],
) -> anyhow::Result<CaptureVariable> {
    let variable_sorts = variables
        .iter()
        .filter_map(|variable| match &variable.current {
            Command::DeclareFun {
                symbol,
                parameters,
                sort,
            } if parameters.is_empty() => Some((symbol.0.clone(), sort.clone())),
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
            variable_sorts.get(&base_name).and_then(|sort| {
                (!sort_is_array(sort)).then(|| CaptureVariable {
                    base_name,
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

fn replace_framed_symbol(term: &Term, base_name: &str, frame: i64, replacement: &str) -> Term {
    match term {
        Term::Constant(_) => term.clone(),
        Term::QualIdentifier(qi) => {
            let name = qi.get_name();
            if split_framed_symbol(&name) == Some((base_name.to_string(), frame)) {
                symbol_term(replacement)
            } else {
                term.clone()
            }
        }
        Term::Application {
            qual_identifier,
            arguments,
        } => Term::Application {
            qual_identifier: qual_identifier.clone(),
            arguments: arguments
                .iter()
                .map(|argument| replace_framed_symbol(argument, base_name, frame, replacement))
                .collect(),
        },
        Term::Let { var_bindings, term } => Term::Let {
            var_bindings: var_bindings
                .iter()
                .map(|(symbol, binding)| {
                    (
                        symbol.clone(),
                        replace_framed_symbol(binding, base_name, frame, replacement),
                    )
                })
                .collect(),
            term: Box::new(replace_framed_symbol(term, base_name, frame, replacement)),
        },
        Term::Forall { vars, term } => Term::Forall {
            vars: vars.clone(),
            term: Box::new(replace_framed_symbol(term, base_name, frame, replacement)),
        },
        Term::Exists { vars, term } => Term::Exists {
            vars: vars.clone(),
            term: Box::new(replace_framed_symbol(term, base_name, frame, replacement)),
        },
        Term::Match { term, cases } => Term::Match {
            term: Box::new(replace_framed_symbol(term, base_name, frame, replacement)),
            cases: cases
                .iter()
                .map(|(symbols, case_term)| {
                    (
                        symbols.clone(),
                        replace_framed_symbol(case_term, base_name, frame, replacement),
                    )
                })
                .collect(),
        },
        Term::Attributes { term, attributes } => Term::Attributes {
            term: Box::new(replace_framed_symbol(term, base_name, frame, replacement)),
            attributes: attributes.clone(),
        },
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
        Term::Forall { term, .. } | Term::Exists { term, .. } => {
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
    name.starts_with("yb_hist_") || name.starts_with("yb_prop_")
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
        Term::Forall { term, .. } | Term::Exists { term, .. } => {
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

fn split_framed_symbol(symbol: &str) -> Option<(String, i64)> {
    let (base, frame) = symbol.rsplit_once(VARIABLE_FRAME_DELIMITER)?;
    let frame = frame.parse::<i64>().ok()?;
    Some((base.to_string(), frame))
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
    fn builds_true_guard_history_and_prophecy_from_conflict() {
        let term = get_term_from_term_string("(= x@0 y@2)");
        let conflict = ArrayConflictRecord::new(
            0,
            "test",
            "(= x@0 y@2)".parse().unwrap(),
            term,
            2,
            3,
            1,
            crate::auxiliary_synthesis::ConflictClassification::Regular,
            vec![],
        );
        let spec = AuxiliarySpec::from_conflict(
            &conflict,
            &[variable("x"), variable("y")],
            SynthesisTrigger::NonLocal,
            GuardPolicy::True,
        )
        .unwrap();
        assert_eq!(spec.history.capture_term.to_string(), "y");
        assert_eq!(
            spec.localized_axiom.as_ref().unwrap().to_string(),
            "(= x@0 yb_prop_conflict_2_3_0)"
        );
        assert_eq!(spec.transition_terms().len(), 2);
        assert_eq!(
            spec.non_monotonicity_check.status,
            NonMonotonicityStatus::Pending
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
