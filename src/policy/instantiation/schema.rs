//! Provider-neutral catalogue entries backed by exact theory constructors.
use crate::{
    rule_matching::candidate::SymbolicInstance,
    theories::{
        array::instantiation_schema::ArrayInstantiationSchema,
        quantifiers::instantiation_schema::BinderInstantiationSchema,
    },
};
use serde_json::{json, Value};
use smt2parser::concrete::Term;
use std::collections::BTreeMap;

pub(crate) struct InstantiationSchema {
    pub id: String,
    pub slots: BTreeMap<String, String>,
    pub formula: String,
    pub provenance: Value,
    constructor: Constructor,
}
enum Constructor {
    Array(Box<ArrayInstantiationSchema>),
    Binder(Box<BinderInstantiationSchema>),
}
impl InstantiationSchema {
    pub fn array(schema: ArrayInstantiationSchema) -> Self {
        Self {
            id: schema.id.clone(),
            slots: schema.slots.clone(),
            formula: schema.formula.clone(),
            provenance: json!({"kind":"array_axiom"}),
            constructor: Constructor::Array(Box::new(schema)),
        }
    }
    pub fn binder(id: String, schema: BinderInstantiationSchema) -> Self {
        Self {
            id,
            slots: schema.slots.clone(),
            formula: schema.formula.clone(),
            provenance: schema.provenance.clone(),
            constructor: Constructor::Binder(Box::new(schema)),
        }
    }
    pub fn name(&self) -> &str {
        match &self.constructor {
            Constructor::Array(s) => s.name(),
            Constructor::Binder(s) => s.name(),
        }
    }
    pub fn instantiate(
        &self,
        bindings: &BTreeMap<String, Term>,
    ) -> anyhow::Result<SymbolicInstance> {
        match &self.constructor {
            Constructor::Array(s) => s.instantiate(bindings),
            Constructor::Binder(s) => s.instantiate(bindings),
        }
    }
}

pub(crate) fn match_schema_slots(
    pattern: &Term,
    value: &Term,
    slots: &BTreeMap<String, String>,
    bindings: &mut BTreeMap<String, Term>,
) -> bool {
    if let Term::QualIdentifier(id) = pattern {
        let name = id.to_string();
        if slots.contains_key(&name) {
            return match bindings.get(&name) {
                Some(previous) => previous == value,
                None => {
                    bindings.insert(name, value.clone());
                    true
                }
            };
        }
    }
    match (pattern, value) {
        (
            Term::Application {
                qual_identifier: a,
                arguments: aa,
            },
            Term::Application {
                qual_identifier: b,
                arguments: ba,
            },
        ) => {
            if a != b || aa.len() != ba.len() {
                return false;
            }
            let original = bindings.clone();
            // Consequents bind structural slots before commutative guards.
            if aa
                .iter()
                .zip(ba)
                .rev()
                .all(|(a, b)| match_schema_slots(a, b, slots, bindings))
            {
                return true;
            }
            *bindings = original.clone();
            if a.to_string() == "="
                && aa.len() == 2
                && match_schema_slots(&aa[0], &ba[1], slots, bindings)
                && match_schema_slots(&aa[1], &ba[0], slots, bindings)
            {
                return true;
            }
            *bindings = original;
            false
        }
        _ => pattern == value,
    }
}
