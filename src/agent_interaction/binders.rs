//! Source and substitution evidence for the async binder-context experiment.
use super::{InstantiationSnapshot, SnapshotInput, TransitionIndex};
use crate::{
    policy::instantiation::match_schema_slots,
    theories::quantifiers::{app, BinderRule},
};
use anyhow::Context;
use serde_json::{json, Value};
use smt2parser::concrete::{Symbol, Term};
use std::collections::{BTreeMap, BTreeSet, HashMap};

pub(super) type BinderActions = BTreeMap<String, BTreeSet<String>>;

pub(super) fn action_names(index: Option<&TransitionIndex>) -> BinderActions {
    let mut actions = BinderActions::new();
    if let Some(index) = index {
        for (action, entry) in index.actions() {
            for binder in entry.requirements.iter().flat_map(|r| &r.binders) {
                actions
                    .entry(binder.helper.clone())
                    .or_default()
                    .insert(action.clone());
            }
        }
    }
    actions
}

struct Binder {
    source: Value,
    capture_count: usize,
    capture_tuples: BTreeSet<Vec<String>>,
}

pub(super) struct BinderContext(BTreeMap<String, Binder>);

impl BinderContext {
    pub(super) fn new(input: &SnapshotInput, actions: BinderActions) -> anyhow::Result<Self> {
        let mut binders = BTreeMap::new();
        let Some((rules, provenance)) = &input.quantifiers else {
            return Ok(Self(binders));
        };
        // Join by lexical identity: nested binders can reuse the same source spelling.
        let scoped: HashMap<_, _> = provenance
            .sources
            .values()
            .flat_map(|s| &s.variables)
            .map(|v| (v.scoped_name.as_str(), v.name.as_str()))
            .collect();
        let mut names = HashMap::new();
        for lowered in provenance.rules.values() {
            for var in &lowered.variables {
                names.insert(
                    var.lowered_name.as_str(),
                    *scoped
                        .get(var.scoped_name.as_str())
                        .context("missing source binder variable")?,
                );
            }
        }
        for source in provenance.sources.values() {
            for witness in &source.property_witnesses {
                names.insert(
                    witness.witness.as_str(),
                    *scoped
                        .get(witness.scoped_variable.as_str())
                        .context("missing source witness variable")?,
                );
            }
        }
        let source_name = |symbol: &Symbol| {
            Symbol(
                names
                    .get(symbol.0.as_str())
                    .copied()
                    .unwrap_or(&symbol.0)
                    .to_owned(),
            )
            .to_string()
        };

        let history = installed_by_helper(&input.installed);
        for rule in rules {
            let rule_id = crate::rule_matching::rule::QuantifiedRule::input_binder(&rule.name);
            let lowered = provenance
                .rules
                .get(rule_id.name())
                .context("missing binder provenance")?;
            let source = provenance
                .sources
                .get(&lowered.source_id)
                .context("missing quantifier source")?;
            let captures: Vec<_> = rule
                .captures
                .iter()
                .filter(|_| !rule.unit_capture)
                .map(|(symbol, _)| source_name(symbol))
                .collect();
            let variables: Vec<_> = rule
                .variables
                .iter()
                .map(|(symbol, _)| source_name(symbol))
                .collect();
            let capture_count = captures.len();
            let mut details = json!({"source_ref":lowered.source_id,"formula":source.formula,
                "capture_slot_names":captures, "variable_slot_names":variables});
            if let Some(action) = actions.get(&rule.name) {
                details["actions"] = json!(action);
            }

            if let Some(formulas) = history.get(&rule.name) {
                add_installed_tuples(&mut details, rule, capture_count, formulas);
            }
            binders.insert(
                rule.name.clone(),
                Binder {
                    source: details,
                    capture_count,
                    capture_tuples: BTreeSet::new(),
                },
            );
        }
        Ok(Self(binders))
    }

    pub(super) fn annotate(mut self, snapshot: &InstantiationSnapshot, axioms: &mut Value) {
        for t in &snapshot.terms {
            if let Term::Application {
                qual_identifier,
                arguments,
            } = &t.term
            {
                if let Some(binder) = self.0.get_mut(&qual_identifier.get_name()) {
                    if binder.capture_count > 0 && binder.capture_count == arguments.len() {
                        binder
                            .capture_tuples
                            .insert(arguments.iter().map(ToString::to_string).collect());
                    }
                }
            }
        }
        for (entry, schema) in axioms
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .zip(&snapshot.schemas)
        {
            let Some(binder) = self.0.get_mut(schema.name()) else {
                continue;
            };
            if schema.provenance["direction"] == "witness" {
                entry["binder_context_ref"] = json!(format!("binder:{}:instance", schema.name()));
            } else {
                binder.source["ground_capture_tuples"] = json!(binder.capture_tuples);
                entry["binder_context"] = binder.source.take();
            }
        }
    }
}

/// A binder instance contains its proxy on one side of an implication, possibly
/// negated in the witness direction. The index only shortlists formulas.
fn installed_by_helper(installed: &[Term]) -> HashMap<String, Vec<&Term>> {
    let mut history: HashMap<String, Vec<&Term>> = HashMap::new();
    for term in installed {
        let Term::Application {
            qual_identifier,
            arguments,
        } = term
        else {
            continue;
        };
        if qual_identifier.get_name() != "=>" {
            continue;
        }
        for side in arguments {
            let proxy = match side {
                Term::Application {
                    qual_identifier,
                    arguments,
                } if qual_identifier.get_name() == "not" && arguments.len() == 1 => &arguments[0],
                other => other,
            };
            if let Term::Application {
                qual_identifier, ..
            } = proxy
            {
                history
                    .entry(qual_identifier.get_name())
                    .or_default()
                    .push(term);
            }
        }
    }
    history
}

fn add_installed_tuples(
    context: &mut Value,
    rule: &BinderRule,
    capture_count: usize,
    formulas: &[&Term],
) {
    // The native constructor supplies both patterns. Matching recovers syntax
    // from installed formulas without completing a model or introducing a lemma.
    let captures: Vec<_> = rule
        .captures
        .iter()
        .map(|(s, _)| app(&s.0, vec![]))
        .collect();
    let variables: Vec<_> = rule
        .variables
        .iter()
        .map(|(s, _)| app(&s.0, vec![]))
        .collect();
    let ordered: Vec<_> = rule
        .captures
        .iter()
        .take(capture_count)
        .chain(&rule.variables)
        .map(|(s, sort)| (s.to_string(), sort.to_string()))
        .collect();
    let slots = ordered.iter().cloned().collect();
    let captures = if rule.unit_capture {
        vec![app("true", vec![])]
    } else {
        captures
    };
    let ordinary = rule.instantiate(&captures, &variables);
    let Some(witness) = rule.witness_instance(&captures) else {
        return;
    };
    let mut instances = BTreeSet::new();
    let mut witnesses = BTreeSet::new();
    for formula in formulas {
        let mut bindings = BTreeMap::new();
        if match_schema_slots(&ordinary, formula, &slots, &mut bindings) {
            instances.insert(
                ordered
                    .iter()
                    .map(|(s, _)| bindings.get(s).map(ToString::to_string))
                    .collect::<Vec<_>>(),
            );
        } else {
            // The proxy contains every capture. Recover the actual correlated
            // arguments and construct the same witness terms as the binder rule.
            bindings.clear();
            if match_schema_slots(&witness, formula, &slots, &mut bindings) {
                let mut terms: Vec<_> = ordered[..capture_count]
                    .iter()
                    .map(|(s, _)| bindings[s].clone())
                    .collect();
                let arguments = if rule.unit_capture {
                    vec![app("true", vec![])]
                } else {
                    terms.clone()
                };
                terms.extend(rule.witnesses.iter().map(|w| app(w, arguments.clone())));
                witnesses.insert(terms.iter().map(ToString::to_string).collect::<Vec<_>>());
            }
        }
    }
    if !instances.is_empty() {
        context["installed_relative_tuples"] = json!(instances);
    }
    if !witnesses.is_empty() {
        context["installed_witness_relative_tuples"] = json!(witnesses);
    }
}
