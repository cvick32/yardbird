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

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct AuxSynthesisConfig {
    pub trigger: SynthesisTrigger,
    pub guard_policy: GuardPolicy,
    pub manual_after: Option<u32>,
    pub refinement_limit_window: Option<u32>,
    pub repeated_pattern_threshold: Option<u32>,
}

impl AuxSynthesisConfig {
    pub fn is_off(&self) -> bool {
        self.trigger == SynthesisTrigger::Off
    }
}
