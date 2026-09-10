use clap::ValueEnum;
use serde::{Deserialize, Serialize};

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, ValueEnum, Serialize, Deserialize)]
#[clap(rename_all = "kebab_case")]
#[serde(rename_all = "kebab-case")]
pub enum SynthesisTrigger {
    #[default]
    Off,
    Detect,
    NonLocal,
    ManualAfterN,
    RefinementLimit,
    RepeatedPattern,
}

impl std::fmt::Display for SynthesisTrigger {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SynthesisTrigger::Off => write!(f, "off"),
            SynthesisTrigger::Detect => write!(f, "detect"),
            SynthesisTrigger::NonLocal => write!(f, "non-local"),
            SynthesisTrigger::ManualAfterN => write!(f, "manual-after-n"),
            SynthesisTrigger::RefinementLimit => write!(f, "refinement-limit"),
            SynthesisTrigger::RepeatedPattern => write!(f, "repeated-pattern"),
        }
    }
}

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, ValueEnum, Serialize, Deserialize)]
#[clap(rename_all = "kebab_case")]
#[serde(rename_all = "kebab-case")]
pub enum GuardPolicy {
    #[default]
    True,
    AxiomLocal,
    Interpolant,
    Llm,
}

impl std::fmt::Display for GuardPolicy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GuardPolicy::True => write!(f, "true"),
            GuardPolicy::AxiomLocal => write!(f, "axiom-local"),
            GuardPolicy::Interpolant => write!(f, "interpolant"),
            GuardPolicy::Llm => write!(f, "llm"),
        }
    }
}

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, ValueEnum, Serialize, Deserialize)]
#[clap(rename_all = "kebab_case")]
#[serde(rename_all = "kebab-case")]
pub enum AuxRefinementRetention {
    #[default]
    KeepAll,
    DropSource,
}

impl std::fmt::Display for AuxRefinementRetention {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AuxRefinementRetention::KeepAll => write!(f, "keep-all"),
            AuxRefinementRetention::DropSource => write!(f, "drop-source"),
        }
    }
}

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, ValueEnum, Serialize, Deserialize)]
#[clap(rename_all = "kebab_case")]
#[serde(rename_all = "kebab-case")]
pub enum PredicateRelevancePolicy {
    #[default]
    ExactProperty,
    CaptureAligned,
}

impl std::fmt::Display for PredicateRelevancePolicy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ExactProperty => write!(f, "exact-property"),
            Self::CaptureAligned => write!(f, "capture-aligned"),
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct AuxSynthesisConfig {
    pub trigger: SynthesisTrigger,
    pub guard_policy: GuardPolicy,
    #[serde(default)]
    pub refinement_retention: AuxRefinementRetention,
    #[serde(default)]
    pub predicate_relevance: PredicateRelevancePolicy,
    pub manual_after: Option<u32>,
    pub refinement_limit_window: Option<u32>,
    pub repeated_pattern_threshold: Option<u32>,
}

impl AuxSynthesisConfig {
    pub fn is_off(&self) -> bool {
        self.trigger == SynthesisTrigger::Off
    }
}
