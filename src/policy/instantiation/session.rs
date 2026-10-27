//! Run-scoped identity and immutable vocabulary blocks shared by all providers.
//! Only the vocabulary is retained: every capture replaces the complete model.
use std::collections::{BTreeMap, BTreeSet};

use serde_json::{json, Value};

use super::InstantiationSnapshot;
use crate::policy::discovery::DiscoveryContext;

#[derive(Default)]
pub(crate) struct InstantiationSession {
    ids: BTreeMap<(String, String), usize>,
    active_ids: BTreeSet<String>,
    declarations: BTreeSet<String>,
    prefix: Vec<Value>,
}

impl InstantiationSession {
    pub fn capture(
        &mut self,
        context: &DiscoveryContext<'_>,
        problem_source: &str,
    ) -> anyhow::Result<InstantiationSnapshot> {
        // A failed capture must not advance identity or vocabulary history.
        let mut snapshot = InstantiationSnapshot::capture(context, problem_source)?;
        self.prepare(&mut snapshot);
        Ok(snapshot)
    }

    fn prepare(&mut self, snapshot: &mut InstantiationSnapshot) {
        for term in &mut snapshot.terms {
            let next = self.ids.len();
            let id = self
                .ids
                .entry((term.expression.clone(), term.sort.clone()))
                .or_insert(next);
            term.id = format!("t{id}");
        }
        snapshot
            .terms
            .sort_by_key(|t| self.ids[&(t.expression.clone(), t.sort.clone())]);
        let mut fixed = snapshot.state();
        for field in [
            "terms",
            "declarations",
            "model",
            "depth",
            "refinement_step",
            "model_version",
            "successful_instantiations",
        ] {
            fixed.as_object_mut().unwrap().remove(field);
        }
        let active_ids: BTreeSet<_> = snapshot.terms.iter().map(|t| t.id.clone()).collect();
        let declarations: BTreeSet<_> = snapshot.declarations.iter().cloned().collect();
        // Shrinkage or changed source/schema invalidates the serialized prefix,
        // but IDs are never reassigned, including when removed terms return.
        if self.prefix.first() != Some(&fixed)
            || !self.active_ids.is_subset(&active_ids)
            || !self.declarations.is_subset(&declarations)
        {
            self.prefix = vec![fixed];
            self.active_ids.clear();
            self.declarations.clear();
        }
        let added_terms: Vec<_> = snapshot
            .terms
            .iter()
            .filter(|t| !self.active_ids.contains(&t.id))
            .collect();
        let added_declarations: Vec<_> = declarations.difference(&self.declarations).collect();
        if !added_terms.is_empty() || !added_declarations.is_empty() {
            // Interleave additions in one block. Separate growing declarations
            // before growing terms would invalidate the old catalogue prefix.
            self.prefix
                .push(json!({"declarations":added_declarations,"terms":added_terms}));
        }
        self.active_ids = active_ids;
        self.declarations = declarations;
        // Flat and blocked representations have identical order and contents.
        snapshot.declarations = self
            .prefix
            .iter()
            .skip(1)
            .flat_map(|v| {
                v["declarations"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|d| d.as_str().unwrap().to_owned())
            })
            .collect();
        let positions: BTreeMap<_, _> = self
            .prefix
            .iter()
            .skip(1)
            .flat_map(|v| v["terms"].as_array().unwrap())
            .enumerate()
            .map(|(index, t)| (t["id"].as_str().unwrap(), index))
            .collect();
        snapshot.terms.sort_by_key(|t| positions[t.id.as_str()]);
        snapshot.prefix = self.prefix.clone();
    }
}

#[cfg(test)]
mod tests;
