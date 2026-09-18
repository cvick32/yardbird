//! Quantified transition conditions and syntax-level substitution.
use smt2parser::{
    concrete::{QualIdentifier, Sort, Symbol, Term},
    let_extract::LetExtract,
    vmt::TransitionGuard,
};

/// A positive universal guard found in the consequent of one transition action.
///
/// The parser retains this source formula after removing it from the transition
/// relation so Yardbird can compile and instantiate the corresponding rule.
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

    pub fn action(&self) -> &str {
        self.parsed.action()
    }

    pub fn bound_variables(&self) -> &[(Symbol, Sort)] {
        self.parsed.bound_variables()
    }

    pub fn body(&self) -> &Term {
        self.parsed.body()
    }

    pub fn parsed(&self) -> &TransitionGuard {
        &self.parsed
    }

    /// Ground the currently supported single-binder transition guard while
    /// retaining its action condition. Solver-specific BMC framing happens
    /// after this syntax-level substitution.
    pub fn ground_formula(&self, candidate: Term) -> Option<Term> {
        let [(binder, _)] = self.bound_variables() else {
            return None;
        };
        let body = LetExtract::substitute(Term::Let {
            var_bindings: vec![(binder.clone(), candidate)],
            term: Box::new(self.body().clone()),
        });
        Some(Term::Application {
            qual_identifier: QualIdentifier::simple("=>"),
            arguments: vec![
                Term::QualIdentifier(QualIdentifier::simple(self.action())),
                body,
            ],
        })
    }
}

use crate::rule_matching::rule::{QuantifiedRule, QuantifiedRuleKind, QuantifiedRuleProvenance};

impl QuantifiedRule {
    pub fn transition_guard(action: impl Into<String>, ordinal: usize) -> Self {
        let action = action.into();
        Self {
            name: format!("transition-guard-{action}-{ordinal}"),
            kind: QuantifiedRuleKind::TransitionGuard,
            provenance: QuantifiedRuleProvenance::TransitionGuard { action, ordinal },
        }
    }
}
