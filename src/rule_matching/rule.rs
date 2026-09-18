//! Identity and provenance shared by quantified rules, independent of how a
//! particular rule is matched or instantiated.
use crate::theories::array::rule::ArrayAxiomKind;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum QuantifiedRuleCategory {
    ArrayAxiom,
    TransitionGuard,
    InputBinder,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum QuantifiedRuleKind {
    ArrayAxiom(ArrayAxiomKind),
    TransitionGuard,
    InputBinder,
}

impl QuantifiedRuleKind {
    pub fn category(self) -> QuantifiedRuleCategory {
        match self {
            Self::ArrayAxiom(_) => QuantifiedRuleCategory::ArrayAxiom,
            Self::TransitionGuard => QuantifiedRuleCategory::TransitionGuard,
            Self::InputBinder => QuantifiedRuleCategory::InputBinder,
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
    InputBinder {
        helper: String,
    },
}

/// Stable rule metadata carried beside the rule's current executable form.
///
/// Array rules and transition guards can share this identity without teaching
/// cost functions about their executable egg searchers.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct QuantifiedRule {
    pub(crate) name: String,
    pub(crate) kind: QuantifiedRuleKind,
    pub(crate) provenance: QuantifiedRuleProvenance,
}

impl QuantifiedRule {
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
