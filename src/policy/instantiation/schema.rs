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
