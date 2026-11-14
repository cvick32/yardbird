//! Exact instances of registered source binders. No provider-supplied formulas.
use super::{app, provenance::QuantifierProvenance, BinderKind, BinderRule};
use crate::{
    rule_matching::{candidate::SymbolicInstance, rule::QuantifiedRule},
    terms::language::TermLanguage,
};
use serde_json::{json, Value};
use smt2parser::concrete::Term;
use std::collections::BTreeMap;

pub(crate) struct BinderInstantiationSchema {
    pub slots: BTreeMap<String, String>,
    pub formula: String,
    pub provenance: Value,
    rule: BinderRule,
    witness: bool,
}

impl BinderInstantiationSchema {
    pub fn new(
        rule: &BinderRule,
        provenance: &QuantifierProvenance,
        witness: bool,
    ) -> anyhow::Result<Self> {
        anyhow::ensure!(
            rule.kind != BinderKind::Lambda,
            "LLM binder guidance requires lambda-free input; use the .encoding.vmt companion"
        );
        let lowered = provenance
            .rules
            .get(QuantifiedRule::input_binder(&rule.name).name())
            .ok_or_else(|| anyhow::anyhow!("missing source provenance for binder {}", rule.name))?;
        let _source = provenance
            .sources
            .get(&lowered.source_id)
            .ok_or_else(|| anyhow::anyhow!("missing input source {}", lowered.source_id))?;
        let mut slots = BTreeMap::new();
        if !rule.unit_capture {
            for (i, (_, sort)) in rule.captures.iter().enumerate() {
                slots.insert(format!("capture_{i}"), TermLanguage::sort_to_name(sort));
            }
        }
        if !witness {
            for (i, (_, sort)) in rule.variables.iter().enumerate() {
                slots.insert(format!("variable_{i}"), TermLanguage::sort_to_name(sort));
            }
        }
        let mut schema = Self {
            slots,
            formula: String::new(),
            rule: rule.clone(),
            witness,
            provenance: json!({"kind":"input_binder", "direction":if witness {"witness"} else {"instance"},
                "source_id":lowered.source_id,"lowered":lowered,
                "capture_slots":if rule.unit_capture {vec![]} else {rule.captures.iter().enumerate().map(|(i,(name,_))|json!({"slot":format!("capture_{i}"),"name":name.0})).collect::<Vec<_>>()},
                "variable_slots":if witness {vec![]} else {rule.variables.iter().enumerate().map(|(i,(name,_))|json!({"slot":format!("variable_{i}"),"name":name.0})).collect::<Vec<_>>()}}),
        };
        let placeholders = schema
            .slots
            .keys()
            .map(|s| (s.clone(), app(s, vec![])))
            .collect();
        schema.formula = schema.instantiate(&placeholders)?.term.to_string();
        Ok(schema)
    }

    pub fn name(&self) -> &str {
        &self.rule.name
    }

    pub fn instantiate(
        &self,
        bindings: &BTreeMap<String, Term>,
    ) -> anyhow::Result<SymbolicInstance> {
        anyhow::ensure!(
            bindings.keys().eq(self.slots.keys()),
            "substitution must bind exactly the schema's slots"
        );
        let captures = if self.rule.unit_capture {
            vec![app("true", vec![])]
        } else {
            (0..self.rule.captures.len())
                .map(|i| bindings[&format!("capture_{i}")].clone())
                .collect()
        };
        let term = if self.witness {
            self.rule
                .witness_instance(&captures)
                .expect("quantified binder has witness direction")
        } else {
            let values = (0..self.rule.variables.len())
                .map(|i| bindings[&format!("variable_{i}")].clone())
                .collect::<Vec<_>>();
            self.rule.instantiate(&captures, &values)
        };
        Ok(SymbolicInstance {
            rule: QuantifiedRule::input_binder(&self.rule.name),
            term,
            bindings: bindings
                .iter()
                .map(|(s, t)| (format!("?{s}"), t.clone()))
                .collect(),
        })
    }
}
