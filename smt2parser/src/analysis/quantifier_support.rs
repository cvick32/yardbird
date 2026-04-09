use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use crate::{
    analysis::nnf::to_nnf,
    concrete::{Command, FunctionDec, Sort, Term},
    let_extract::LetExtract,
    visitors::AttributeValue,
};

#[derive(Clone, Debug, Serialize, Deserialize, Eq, PartialEq)]
pub enum FileReason {
    QuantifierFree,
    ForallOnly,
    ExistsEliminatedByNnf,
    UnsupportedExistsPositivePolarity,
    UnsupportedAlternation,
    ParseError,
}

impl FileReason {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::QuantifierFree => "quantifier_free",
            Self::ForallOnly => "forall_only",
            Self::ExistsEliminatedByNnf => "exists_eliminated_by_nnf",
            Self::UnsupportedExistsPositivePolarity => "unsupported_exists_positive_polarity",
            Self::UnsupportedAlternation => "unsupported_alternation",
            Self::ParseError => "parse_error",
        }
    }

    pub fn severity(&self) -> u8 {
        match self {
            Self::ParseError => 0,
            Self::UnsupportedAlternation => 1,
            Self::UnsupportedExistsPositivePolarity => 2,
            Self::ExistsEliminatedByNnf => 3,
            Self::ForallOnly => 4,
            Self::QuantifierFree => 5,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FileAnalysis {
    pub relative_path: PathBuf,
    pub family: String,
    pub incrementality: String,
    pub has_arrays: bool,
    pub has_quantifiers: bool,
    pub has_forall: bool,
    pub has_exists: bool,
    pub fully_supported: bool,
    pub reason: String,
    pub n_asserts: usize,
    pub n_forall: usize,
    pub n_exists: usize,
    pub n_exists_after_nnf: usize,
    pub uses_push_pop: bool,
    pub uses_check_sat_assuming: bool,
    pub parse_error: Option<String>,
}

impl FileAnalysis {
    pub fn parse_error(relative_path: PathBuf, error: String) -> Self {
        let (incrementality, family) = infer_path_metadata(&relative_path);
        Self {
            relative_path,
            family,
            incrementality,
            has_arrays: false,
            has_quantifiers: false,
            has_forall: false,
            has_exists: false,
            fully_supported: false,
            reason: FileReason::ParseError.as_str().to_string(),
            n_asserts: 0,
            n_forall: 0,
            n_exists: 0,
            n_exists_after_nnf: 0,
            uses_push_pop: false,
            uses_check_sat_assuming: false,
            parse_error: Some(error),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, Default)]
pub struct AssertionAnalysis {
    pub index: usize,
    pub n_forall_before: usize,
    pub n_exists_before: usize,
    pub n_exists_after_nnf: usize,
    pub reason: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub original: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub let_eliminated: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub nnf: Option<String>,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct AnalysisOptions {
    pub include_assertion_text: bool,
}

#[derive(Default)]
pub struct FileAnalysisAccumulator {
    has_arrays: bool,
    asserts: usize,
    forall: usize,
    exists: usize,
    exists_after_nnf: usize,
    uses_push_pop: bool,
    uses_check_sat_assuming: bool,
    worst_reason: Option<FileReason>,
}

impl FileAnalysisAccumulator {
    pub fn observe_command(&mut self, command: &Command) {
        match command {
            Command::DeclareConst { sort, .. } => self.has_arrays |= sort_has_array(sort),
            Command::DeclareFun {
                parameters, sort, ..
            } => {
                self.has_arrays |= parameters.iter().any(sort_has_array) || sort_has_array(sort);
            }
            Command::DefineFun { sig, .. } | Command::DefineFunRec { sig, .. } => {
                self.has_arrays |= function_sig_has_array(sig);
            }
            Command::DefineFunsRec { funs } => {
                self.has_arrays |= funs.iter().any(|(sig, _)| function_sig_has_array(sig));
            }
            Command::DefineSort { sort, .. } => self.has_arrays |= sort_has_array(sort),
            Command::Push { .. } | Command::Pop { .. } => self.uses_push_pop = true,
            Command::CheckSatAssuming { .. } => self.uses_check_sat_assuming = true,
            _ => {}
        }
    }

    pub fn observe_assertion(&mut self, analysis: &AssertionAnalysis) {
        self.asserts += 1;
        self.forall += analysis.n_forall_before;
        self.exists += analysis.n_exists_before;
        self.exists_after_nnf += analysis.n_exists_after_nnf;
        let reason = parse_reason(&analysis.reason);
        match &self.worst_reason {
            Some(current) if current.severity() <= reason.severity() => {}
            _ => self.worst_reason = Some(reason),
        }
    }

    pub fn finish(self, relative_path: &Path) -> FileAnalysis {
        let (incrementality, family) = infer_path_metadata(relative_path);
        let aggregated_reason = self.worst_reason.unwrap_or(FileReason::QuantifierFree);
        FileAnalysis {
            relative_path: relative_path.to_path_buf(),
            family: family.clone(),
            incrementality,
            has_arrays: self.has_arrays,
            has_quantifiers: self.forall + self.exists > 0,
            has_forall: self.forall > 0,
            has_exists: self.exists > 0,
            fully_supported: matches!(
                aggregated_reason,
                FileReason::QuantifierFree
                    | FileReason::ForallOnly
                    | FileReason::ExistsEliminatedByNnf
            ),
            reason: aggregated_reason.as_str().to_string(),
            n_asserts: self.asserts,
            n_forall: self.forall,
            n_exists: self.exists,
            n_exists_after_nnf: self.exists_after_nnf,
            uses_push_pop: self.uses_push_pop,
            uses_check_sat_assuming: self.uses_check_sat_assuming,
            parse_error: None,
        }
    }
}

pub struct ProcessedAssertion {
    pub let_command: Command,
    pub nnf_command: Command,
    pub analysis: AssertionAnalysis,
}

pub fn analyze_assertion(index: usize, term: Term, options: AnalysisOptions) -> ProcessedAssertion {
    let original_text = options.include_assertion_text.then(|| term.to_string());
    let let_term = LetExtract::substitute(term);
    let before = count_quantifiers(&let_term);
    let let_text = options.include_assertion_text.then(|| let_term.to_string());

    let let_command = Command::Assert {
        term: let_term.clone(),
    };

    match to_nnf(let_term.clone()) {
        Ok(nnf_term) => {
            let after = count_quantifiers(&nnf_term);
            let reason = classify_reason(before, after);
            let analysis = AssertionAnalysis {
                index,
                n_forall_before: before.forall,
                n_exists_before: before.exists,
                n_exists_after_nnf: after.exists,
                reason: reason.as_str().to_string(),
                original: original_text,
                let_eliminated: let_text,
                nnf: options.include_assertion_text.then(|| nnf_term.to_string()),
            };
            ProcessedAssertion {
                let_command,
                nnf_command: Command::Assert { term: nnf_term },
                analysis,
            }
        }
        Err(_) => {
            let analysis = AssertionAnalysis {
                index,
                n_forall_before: before.forall,
                n_exists_before: before.exists,
                n_exists_after_nnf: before.exists,
                reason: FileReason::ParseError.as_str().to_string(),
                original: original_text,
                let_eliminated: let_text,
                nnf: None,
            };
            ProcessedAssertion {
                let_command,
                nnf_command: Command::Assert { term: let_term },
                analysis,
            }
        }
    }
}

pub fn array_family_allowlist() -> &'static [&'static str] {
    &[
        "ABV",
        "ABVFP",
        "ABVFPLRA",
        "AUFBV",
        "AUFBVFP",
        "QF_ABV",
        "QF_ABVFP",
        "QF_ABVFPLRA",
        "QF_AUFBV",
        "QF_AUFBVFP",
    ]
}

#[derive(Default)]
pub struct SummaryAccumulator {
    total_files: usize,
    counts_by_family: std::collections::BTreeMap<String, usize>,
    counts_by_reason: std::collections::BTreeMap<String, usize>,
    counts_by_incrementality: std::collections::BTreeMap<String, usize>,
    grouped_counts: std::collections::BTreeMap<String, usize>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SummaryReport {
    pub total_files: usize,
    pub counts_by_family: std::collections::BTreeMap<String, usize>,
    pub counts_by_reason: std::collections::BTreeMap<String, usize>,
    pub counts_by_incrementality: std::collections::BTreeMap<String, usize>,
    pub grouped_counts:
        std::collections::BTreeMap<String, std::collections::BTreeMap<String, usize>>,
}

impl SummaryAccumulator {
    pub fn observe(&mut self, file: &FileAnalysis) {
        self.total_files += 1;
        *self
            .counts_by_family
            .entry(file.family.clone())
            .or_insert(0) += 1;
        *self
            .counts_by_reason
            .entry(file.reason.clone())
            .or_insert(0) += 1;
        *self
            .counts_by_incrementality
            .entry(file.incrementality.clone())
            .or_insert(0) += 1;
        for key in [
            format!("family={}", file.family),
            format!("incrementality={}", file.incrementality),
            format!("fully_supported={}", file.fully_supported),
            format!("reason={}", file.reason),
        ] {
            *self.grouped_counts.entry(key).or_insert(0) += 1;
        }
    }

    pub fn to_report(&self) -> SummaryReport {
        SummaryReport {
            total_files: self.total_files,
            counts_by_family: self.counts_by_family.clone(),
            counts_by_reason: self.counts_by_reason.clone(),
            counts_by_incrementality: self.counts_by_incrementality.clone(),
            grouped_counts: self
                .grouped_counts
                .iter()
                .map(|(k, v)| {
                    (
                        k.clone(),
                        std::collections::BTreeMap::from([(String::from("count"), *v)]),
                    )
                })
                .collect(),
        }
    }
}

#[derive(Clone, Copy)]
struct QuantifierCounts {
    forall: usize,
    exists: usize,
}

fn sort_has_array(sort: &Sort) -> bool {
    match sort {
        Sort::Simple { .. } => false,
        Sort::Parameterized {
            identifier,
            parameters,
        } => identifier.to_string() == "Array" || parameters.iter().any(sort_has_array),
    }
}

fn function_sig_has_array(sig: &FunctionDec) -> bool {
    sig.parameters.iter().any(|(_, sort)| sort_has_array(sort)) || sort_has_array(&sig.result)
}

fn count_quantifiers(term: &Term) -> QuantifierCounts {
    match term {
        Term::Forall { term, .. } => {
            let counts = count_quantifiers(term);
            QuantifierCounts {
                forall: counts.forall + 1,
                exists: counts.exists,
            }
        }
        Term::Exists { term, .. } => {
            let counts = count_quantifiers(term);
            QuantifierCounts {
                forall: counts.forall,
                exists: counts.exists + 1,
            }
        }
        Term::Application { arguments, .. } => arguments.iter().fold(
            QuantifierCounts {
                forall: 0,
                exists: 0,
            },
            |acc, arg| {
                let next = count_quantifiers(arg);
                QuantifierCounts {
                    forall: acc.forall + next.forall,
                    exists: acc.exists + next.exists,
                }
            },
        ),
        Term::Let { var_bindings, term } => {
            let binding_counts = var_bindings.iter().fold(
                QuantifierCounts {
                    forall: 0,
                    exists: 0,
                },
                |acc, (_, value)| {
                    let next = count_quantifiers(value);
                    QuantifierCounts {
                        forall: acc.forall + next.forall,
                        exists: acc.exists + next.exists,
                    }
                },
            );
            let inner = count_quantifiers(term);
            QuantifierCounts {
                forall: binding_counts.forall + inner.forall,
                exists: binding_counts.exists + inner.exists,
            }
        }
        Term::Match { term, cases } => {
            let inner = count_quantifiers(term);
            cases.iter().fold(inner, |acc, (_, value)| {
                let next = count_quantifiers(value);
                QuantifierCounts {
                    forall: acc.forall + next.forall,
                    exists: acc.exists + next.exists,
                }
            })
        }
        Term::Attributes { term, attributes } => {
            let inner = count_quantifiers(term);
            attributes.iter().fold(inner, |acc, (_, value)| {
                let next = count_quantifiers_in_attribute(value);
                QuantifierCounts {
                    forall: acc.forall + next.forall,
                    exists: acc.exists + next.exists,
                }
            })
        }
        Term::Constant(_) | Term::QualIdentifier(_) => QuantifierCounts {
            forall: 0,
            exists: 0,
        },
    }
}

fn count_quantifiers_in_attribute(value: &AttributeValue) -> QuantifierCounts {
    match value {
        AttributeValue::None | AttributeValue::Constant(_) | AttributeValue::Symbol(_) => {
            QuantifierCounts {
                forall: 0,
                exists: 0,
            }
        }
        AttributeValue::SExpr(_) => QuantifierCounts {
            forall: 0,
            exists: 0,
        },
    }
}

fn classify_reason(before: QuantifierCounts, after: QuantifierCounts) -> FileReason {
    if before.forall + before.exists == 0 {
        return FileReason::QuantifierFree;
    }
    if after.exists == 0 {
        return if before.exists == 0 {
            FileReason::ForallOnly
        } else {
            FileReason::ExistsEliminatedByNnf
        };
    }
    if after.forall > 0 {
        FileReason::UnsupportedAlternation
    } else {
        FileReason::UnsupportedExistsPositivePolarity
    }
}

fn parse_reason(reason: &str) -> FileReason {
    match reason {
        "quantifier_free" => FileReason::QuantifierFree,
        "forall_only" => FileReason::ForallOnly,
        "exists_eliminated_by_nnf" => FileReason::ExistsEliminatedByNnf,
        "unsupported_exists_positive_polarity" => FileReason::UnsupportedExistsPositivePolarity,
        "unsupported_alternation" => FileReason::UnsupportedAlternation,
        _ => FileReason::ParseError,
    }
}

pub fn infer_path_metadata(path: &Path) -> (String, String) {
    let components = path
        .components()
        .map(|component| component.as_os_str().to_string_lossy().to_string())
        .collect::<Vec<_>>();
    let family = components
        .iter()
        .find(|component| array_family_allowlist().contains(&component.as_str()))
        .cloned();
    let incrementality = components
        .iter()
        .find(|component| matches!(component.as_str(), "incremental" | "non-incremental"))
        .cloned();

    match (incrementality, family) {
        (Some(incrementality), Some(family)) => (incrementality, family),
        (Some(incrementality), None) => (incrementality, "unknown".to_string()),
        (None, Some(family)) => ("unknown".to_string(), family),
        (None, None) => {
            if components.len() >= 2 {
                (components[0].clone(), components[1].clone())
            } else {
                ("unknown".to_string(), "unknown".to_string())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        analyze_assertion, infer_path_metadata, AnalysisOptions, FileAnalysis,
        FileAnalysisAccumulator,
    };
    use crate::{concrete::Command, get_command_from_command_string};

    fn analyze(assertions: &[&[u8]]) -> (super::FileAnalysis, Vec<super::AssertionAnalysis>) {
        let commands = assertions
            .iter()
            .map(|command| get_command_from_command_string(command))
            .collect::<Vec<_>>();
        let mut acc = FileAnalysisAccumulator::default();
        let mut out = Vec::new();
        for (i, command) in commands.into_iter().enumerate() {
            match command {
                Command::Assert { term } => {
                    let processed = analyze_assertion(i, term, AnalysisOptions::default());
                    acc.observe_assertion(&processed.analysis);
                    out.push(processed.analysis);
                }
                other => acc.observe_command(&other),
            }
        }
        (
            acc.finish(std::path::Path::new("non-incremental/AUFBV/test.smt2")),
            out,
        )
    }

    #[test]
    fn classifies_quantifier_free_assertion() {
        let (file, _) = analyze(&[b"(assert (> x 0))"]);
        assert!(file.fully_supported);
        assert_eq!(file.reason, "quantifier_free");
    }

    #[test]
    fn detects_arrays_from_declare_fun_sort() {
        let commands = [
            get_command_from_command_string(b"(declare-fun a () (Array Int Int))"),
            get_command_from_command_string(b"(assert true)"),
        ];
        let mut acc = FileAnalysisAccumulator::default();
        for command in commands {
            match command {
                Command::Assert { term } => {
                    let processed = analyze_assertion(0, term, AnalysisOptions::default());
                    acc.observe_assertion(&processed.analysis);
                }
                other => acc.observe_command(&other),
            }
        }
        let file = acc.finish(std::path::Path::new("non-incremental/ABV/test.smt2"));
        assert!(file.has_arrays);
    }

    #[test]
    fn detects_arrays_from_declare_fun_parameter_sort() {
        let commands = [
            get_command_from_command_string(b"(declare-fun f ((Array Int Int) Int) Bool)"),
            get_command_from_command_string(b"(assert true)"),
        ];
        let mut acc = FileAnalysisAccumulator::default();
        for command in commands {
            match command {
                Command::Assert { term } => {
                    let processed = analyze_assertion(0, term, AnalysisOptions::default());
                    acc.observe_assertion(&processed.analysis);
                }
                other => acc.observe_command(&other),
            }
        }
        let file = acc.finish(std::path::Path::new("non-incremental/ABV/test.smt2"));
        assert!(file.has_arrays);
    }

    #[test]
    fn classifies_exists_eliminated_by_nnf() {
        let (file, _) = analyze(&[b"(assert (not (exists ((x Int)) (> x 0))))"]);
        assert!(file.fully_supported);
        assert_eq!(file.reason, "exists_eliminated_by_nnf");
        assert_eq!(file.n_exists_after_nnf, 0);
    }

    #[test]
    fn classifies_unsupported_alternation() {
        let (file, _) = analyze(&[b"(assert (forall ((x Int)) (exists ((y Int)) (> y x))))"]);
        assert!(!file.fully_supported);
        assert_eq!(file.reason, "unsupported_alternation");
    }

    #[test]
    fn parse_error_row_is_conservative() {
        let row = FileAnalysis::parse_error(
            std::path::PathBuf::from("non-incremental/ABV/bad.smt2"),
            "boom".to_string(),
        );
        assert!(!row.fully_supported);
        assert_eq!(row.reason, "parse_error");
    }

    #[test]
    fn shallow_paths_fall_back_to_unknown_metadata() {
        let (incrementality, family) =
            infer_path_metadata(std::path::Path::new("non-incremental/AUFBV/test.smt2"));
        assert_eq!(incrementality, "non-incremental");
        assert_eq!(family, "AUFBV");

        let (incrementality, family) = infer_path_metadata(std::path::Path::new(
            "20190429-UltimateAutomizerSvcomp2019/example.smt2",
        ));
        assert_eq!(incrementality, "20190429-UltimateAutomizerSvcomp2019");
        assert_eq!(family, "example.smt2");

        let (incrementality, family) = infer_path_metadata(std::path::Path::new(
            "incremental/QF_ABV/2019-Mann/example.smt2",
        ));
        assert_eq!(incrementality, "incremental");
        assert_eq!(family, "QF_ABV");

        let (incrementality, family) = infer_path_metadata(std::path::Path::new("flat.smt2"));
        assert_eq!(incrementality, "unknown");
        assert_eq!(family, "unknown");
    }
}
