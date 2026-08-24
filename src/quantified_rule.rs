//! Identity and provenance shared by quantified rules, independent of how a
//! particular rule is matched or instantiated.

use smt2parser::{concrete::Term, vmt::TransitionGuard};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum QuantifiedRuleCategory {
    ArrayAxiom,
    TransitionGuard,
    Other,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ArrayAxiomKind {
    WriteDoesNotOverwrite,
    ReadAfterWrite,
    ConstantArray,
}

impl ArrayAxiomKind {
    fn stable_name(self) -> &'static str {
        match self {
            Self::WriteDoesNotOverwrite => "write-does-not-overwrite",
            Self::ReadAfterWrite => "read-after-write",
            Self::ConstantArray => "constant-array",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum QuantifiedRuleKind {
    ArrayAxiom(ArrayAxiomKind),
    TransitionGuard,
    Other,
}

impl QuantifiedRuleKind {
    pub fn category(self) -> QuantifiedRuleCategory {
        match self {
            Self::ArrayAxiom(_) => QuantifiedRuleCategory::ArrayAxiom,
            Self::TransitionGuard => QuantifiedRuleCategory::TransitionGuard,
            Self::Other => QuantifiedRuleCategory::Other,
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum QuantifiedRuleProvenance {
    BuiltInArrayTheory {
        index_sort: String,
        value_sort: String,
    },
    TransitionGuard {
        action: String,
        ordinal: usize,
    },
}

/// Stable rule metadata carried beside the rule's current executable form.
///
/// Array rules and transition guards can share this identity without teaching
/// cost functions about their executable egg searchers.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct QuantifiedRule {
    name: String,
    kind: QuantifiedRuleKind,
    provenance: QuantifiedRuleProvenance,
}

impl QuantifiedRule {
    pub fn array_axiom(
        kind: ArrayAxiomKind,
        index_sort: impl Into<String>,
        value_sort: impl Into<String>,
    ) -> Self {
        let index_sort = index_sort.into();
        let value_sort = value_sort.into();
        Self {
            name: format!("{}-{index_sort}-{value_sort}", kind.stable_name()),
            kind: QuantifiedRuleKind::ArrayAxiom(kind),
            provenance: QuantifiedRuleProvenance::BuiltInArrayTheory {
                index_sort,
                value_sort,
            },
        }
    }

    pub fn transition_guard(action: impl Into<String>, ordinal: usize) -> Self {
        let action = action.into();
        Self {
            name: format!("transition-guard-{action}-{ordinal}"),
            kind: QuantifiedRuleKind::TransitionGuard,
            provenance: QuantifiedRuleProvenance::TransitionGuard { action, ordinal },
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn kind(&self) -> QuantifiedRuleKind {
        self.kind
    }

    pub fn category(&self) -> QuantifiedRuleCategory {
        self.kind.category()
    }

    pub fn provenance(&self) -> &QuantifiedRuleProvenance {
        &self.provenance
    }
}

/// A positive universal guard found in the consequent of one transition action.
///
/// This first representation deliberately retains the original quantifier. A
/// later phase will compile it to an egg searcher and remove it from the
/// transition relation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TransitionGuardRule {
    metadata: QuantifiedRule,
    parsed: TransitionGuard,
}

impl TransitionGuardRule {
    pub fn from_parsed(parsed: TransitionGuard, ordinal: usize) -> Self {
        Self {
            metadata: QuantifiedRule::transition_guard(parsed.action(), ordinal),
            parsed,
        }
    }

    pub fn metadata(&self) -> &QuantifiedRule {
        &self.metadata
    }

    pub fn quantified_formula(&self) -> &Term {
        self.parsed.quantified_formula()
    }
}
