//! Rule identities for lowered input binders.

use crate::rule_matching::rule::{QuantifiedRule, QuantifiedRuleKind, QuantifiedRuleProvenance};

impl QuantifiedRule {
    pub fn input_binder(helper: impl Into<String>) -> Self {
        let helper = helper.into();
        Self {
            name: format!("input-binder-{helper}"),
            kind: QuantifiedRuleKind::InputBinder,
            provenance: QuantifiedRuleProvenance::InputBinder { helper },
        }
    }
}
