//! Identity of built-in array axioms.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ArrayAxiomKind {
    WriteDoesNotOverwrite,
    ReadAfterWrite,
    ConstantArray,
}

impl ArrayAxiomKind {
    pub(crate) fn stable_name(self) -> &'static str {
        match self {
            Self::WriteDoesNotOverwrite => "write-does-not-overwrite",
            Self::ReadAfterWrite => "read-after-write",
            Self::ConstantArray => "constant-array",
        }
    }
}

use crate::rule_matching::rule::{QuantifiedRule, QuantifiedRuleKind, QuantifiedRuleProvenance};

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
}
