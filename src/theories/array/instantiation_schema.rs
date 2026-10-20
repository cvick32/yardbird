//! Typed, exact instantiation of the same axiom patterns used by matching.
use std::collections::BTreeMap;

use smt2parser::concrete::Term;

use super::{array_axioms::array_rules_for_type, rule::ArrayAxiomKind};
use crate::{
    rule_matching::{
        candidate::SymbolicInstance, compiled_rule::CompiledQuantifiedRule,
        grounding::instantiate_with_bindings, rule::QuantifiedRuleKind,
    },
    terms::language::{expr_to_term, translate_term_with_array_types, TermExpr},
};

pub(crate) struct ArrayInstantiationSchema {
    pub id: String,
    pub slots: BTreeMap<String, String>,
    pub formula: String,
    compiled: CompiledQuantifiedRule<()>,
    types: Vec<(String, String)>,
}

impl ArrayInstantiationSchema {
    pub fn all(types: &[(String, String)]) -> anyhow::Result<Vec<Self>> {
        let mut schemas = vec![];
        let mut types = types.to_vec();
        types.sort();
        types.dedup();
        for (index, value) in &types {
            for compiled in array_rules_for_type::<()>(index, value) {
                let QuantifiedRuleKind::ArrayAxiom(kind) = compiled.metadata.kind() else {
                    unreachable!()
                };
                let slots: BTreeMap<String, String> = match kind {
                    ArrayAxiomKind::ConstantArray => {
                        BTreeMap::from([("a".into(), value.clone()), ("b".into(), index.clone())])
                    }
                    kind => {
                        let mut slots = BTreeMap::from([
                            ("a".into(), format!("Array_{index}_{value}")),
                            ("idx".into(), index.clone()),
                            ("val".into(), value.clone()),
                        ]);
                        if kind == ArrayAxiomKind::WriteDoesNotOverwrite {
                            slots.insert("c".into(), index.clone());
                        }
                        slots
                    }
                };
                let placeholders = slots
                    .keys()
                    .map(|name| {
                        Ok((
                            format!("?{name}").parse::<egg::Var>()?,
                            name.parse::<TermExpr>()?,
                        ))
                    })
                    .collect::<anyhow::Result<std::collections::HashMap<_, _>>>()?;
                let formula = expr_to_term(instantiate_with_bindings(&compiled.formula, |v| {
                    Ok(&placeholders[&v])
                })?)
                .to_string();
                schemas.push(Self {
                    id: format!("q{}", schemas.len()),
                    slots,
                    formula,
                    compiled,
                    types: types.clone(),
                });
            }
        }
        Ok(schemas)
    }

    pub fn name(&self) -> &str {
        self.compiled.metadata.name()
    }

    /// The caller resolves IDs to catalogue terms and checks their slot sorts.
    pub fn instantiate(
        &self,
        bindings: &BTreeMap<String, Term>,
    ) -> anyhow::Result<SymbolicInstance> {
        anyhow::ensure!(
            bindings.keys().eq(self.slots.keys()),
            "substitution must bind exactly the schema's slots"
        );
        let expressions = bindings
            .iter()
            .map(|(name, term)| {
                Ok((
                    format!("?{name}").parse::<egg::Var>()?,
                    translate_term_with_array_types(term.clone(), &self.types).ok_or_else(
                        || anyhow::anyhow!("cannot represent binding {name}: {term}"),
                    )?,
                ))
            })
            .collect::<anyhow::Result<std::collections::HashMap<_, _>>>()?;
        let expression = instantiate_with_bindings(&self.compiled.formula, |v| {
            expressions
                .get(&v)
                .ok_or_else(|| anyhow::anyhow!("missing binding {v}"))
        })?;
        Ok(SymbolicInstance {
            rule: self.compiled.metadata.clone(),
            term: expr_to_term(expression),
            bindings: bindings
                .iter()
                .map(|(name, term)| (format!("?{name}"), term.clone()))
                .collect(),
        })
    }
}
