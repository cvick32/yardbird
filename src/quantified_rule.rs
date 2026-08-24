//! Identity and provenance shared by quantified rules, independent of how a
//! particular rule is matched or instantiated.

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
}

/// Stable rule metadata carried beside the rule's current executable form.
///
/// Array rules are currently executed as `egg::Rewrite`s. Transition guards
/// will eventually have a different executable form, but both can share this
/// identity and provenance without teaching cost functions about egg types.
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
