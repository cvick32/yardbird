//! Static backward dependency cone rooted at the checked property.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use smt2parser::{
    concrete::Term,
    vmt::{definition_graph::DefinitionGraph, VMTModel},
};

#[derive(Clone, Debug, Default)]
pub struct PropertyCone {
    pub state_distances: BTreeMap<String, u32>,
    pub array_distances: BTreeMap<String, u32>,
}

pub fn build_property_cone(model: &VMTModel) -> PropertyCone {
    let current_variables = model
        .get_all_current_variable_names()
        .into_iter()
        .collect::<BTreeSet<_>>();
    let next_to_current = model.get_next_to_current_varible_names();
    let current_to_next = next_to_current
        .iter()
        .map(|(next, current)| (current.clone(), next.clone()))
        .collect::<BTreeMap<_, _>>();
    let array_variables = model
        .get_state_variables()
        .into_iter()
        .filter(|variable| variable.get_sort_name().contains("Array"))
        .map(|variable| variable.get_current_variable_name().clone())
        .collect::<BTreeSet<_>>();
    let graph = model.get_helper_definitions();
    let transition = model.get_trans_condition_for_yardbird();
    let property = model.get_property_for_yardbird();
    let mut builder = ConeBuilder {
        graph,
        current_variables,
        next_to_current,
        cone: PropertyCone::default(),
    };

    builder.collect_dependencies(&property, 0, &mut HashSet::new());
    let mut queue = builder
        .cone
        .state_distances
        .iter()
        .map(|(state, distance)| (state.clone(), *distance))
        .collect::<VecDeque<_>>();
    let mut expanded_at = BTreeMap::<String, u32>::new();

    while let Some((state, distance)) = queue.pop_front() {
        if expanded_at
            .get(&state)
            .is_some_and(|known| *known <= distance)
        {
            continue;
        }
        expanded_at.insert(state.clone(), distance);
        let Some(next) = current_to_next.get(&state) else {
            continue;
        };

        let mut contains_cache = HashMap::new();
        let mut slices = Vec::new();
        builder.collect_update_slices(
            &transition,
            next,
            &[],
            &mut contains_cache,
            &mut HashSet::new(),
            &mut slices,
        );
        for slice in slices {
            builder.collect_guard_slice(&slice, next, distance.saturating_add(1));
        }

        for (dependency, dependency_distance) in &builder.cone.state_distances {
            if expanded_at
                .get(dependency)
                .is_none_or(|known| dependency_distance < known)
                && !queue.iter().any(|(queued, queued_distance)| {
                    queued == dependency && queued_distance <= dependency_distance
                })
            {
                queue.push_back((dependency.clone(), *dependency_distance));
            }
        }
    }

    builder.cone.array_distances = builder
        .cone
        .state_distances
        .iter()
        .filter(|(state, _)| array_variables.contains(*state))
        .map(|(state, distance)| (state.clone(), *distance))
        .collect();
    builder.cone
}

struct ConeBuilder<'a> {
    graph: &'a DefinitionGraph,
    current_variables: BTreeSet<String>,
    next_to_current: HashMap<String, String>,
    cone: PropertyCone,
}

impl ConeBuilder<'_> {
    fn collect_dependencies(
        &mut self,
        term: &Term,
        distance: u32,
        active_helpers: &mut HashSet<String>,
    ) {
        if let Some(symbol) = leaf_symbol(term) {
            if let Some(definition) = self.graph.get(&symbol) {
                if active_helpers.insert(symbol.clone()) {
                    self.collect_dependencies(definition.body(), distance, active_helpers);
                    active_helpers.remove(&symbol);
                }
            } else if self.current_variables.contains(&symbol) {
                insert_min(&mut self.cone.state_distances, symbol, distance);
            }
            return;
        }

        match term {
            Term::Application { arguments, .. } => {
                for argument in arguments {
                    self.collect_dependencies(argument, distance, active_helpers);
                }
            }
            Term::Let { var_bindings, term } => {
                for (_, value) in var_bindings {
                    self.collect_dependencies(value, distance, active_helpers);
                }
                self.collect_dependencies(term, distance, active_helpers);
            }
            Term::Forall { term, .. }
            | Term::Exists { term, .. }
            | Term::Attributes { term, .. } => {
                self.collect_dependencies(term, distance, active_helpers);
            }
            Term::Match { term, cases } => {
                self.collect_dependencies(term, distance, active_helpers);
                for (_, case) in cases {
                    self.collect_dependencies(case, distance, active_helpers);
                }
            }
            Term::Constant(_) | Term::QualIdentifier(_) => {}
        }
    }

    fn collect_guard_slice(&mut self, term: &Term, target_next: &str, distance: u32) {
        if let Some(symbol) = leaf_symbol(term) {
            if let Some(definition) = self.graph.get(&symbol) {
                self.collect_guard_slice(definition.body(), target_next, distance);
            } else if symbol == target_next || !self.next_to_current.contains_key(&symbol) {
                self.collect_dependencies(term, distance, &mut HashSet::new());
            }
            return;
        }

        let Term::Application {
            qual_identifier,
            arguments,
        } = term
        else {
            self.collect_dependencies(term, distance, &mut HashSet::new());
            return;
        };
        if matches!(
            qual_identifier.get_name().as_str(),
            "and" | "or" | "not" | "=>"
        ) {
            for argument in arguments {
                self.collect_guard_slice(argument, target_next, distance);
            }
            return;
        }

        let next_symbols = self.next_symbols(term, &mut HashSet::new());
        if next_symbols.is_empty() || next_symbols.contains(target_next) {
            self.collect_dependencies(term, distance, &mut HashSet::new());
        }
    }

    fn collect_update_slices(
        &self,
        term: &Term,
        target: &str,
        guards: &[Term],
        contains_cache: &mut HashMap<String, bool>,
        active_helpers: &mut HashSet<String>,
        slices: &mut Vec<Term>,
    ) {
        if let Some(symbol) = leaf_symbol(term) {
            if symbol == target {
                slices.extend(guards.iter().cloned());
                slices.push(term.clone());
            } else if let Some(definition) = self.graph.get(&symbol) {
                if active_helpers.insert(symbol.clone()) {
                    self.collect_update_slices(
                        definition.body(),
                        target,
                        guards,
                        contains_cache,
                        active_helpers,
                        slices,
                    );
                    active_helpers.remove(&symbol);
                }
            }
            return;
        }

        let Term::Application {
            qual_identifier,
            arguments,
        } = term
        else {
            return;
        };
        match qual_identifier.get_name().as_str() {
            "or" => {
                for argument in arguments {
                    if self.contains_symbol(argument, target, contains_cache, &mut HashSet::new()) {
                        self.collect_update_slices(
                            argument,
                            target,
                            guards,
                            contains_cache,
                            active_helpers,
                            slices,
                        );
                    }
                }
            }
            "and" => {
                for (index, argument) in arguments.iter().enumerate() {
                    if !self.contains_symbol(argument, target, contains_cache, &mut HashSet::new())
                    {
                        continue;
                    }
                    let mut nested_guards = guards.to_vec();
                    nested_guards.extend(
                        arguments
                            .iter()
                            .enumerate()
                            .filter(|(other, _)| *other != index)
                            .map(|(_, sibling)| sibling.clone()),
                    );
                    self.collect_update_slices(
                        argument,
                        target,
                        &nested_guards,
                        contains_cache,
                        active_helpers,
                        slices,
                    );
                }
            }
            "=>" if arguments.len() == 2 => {
                if self.contains_symbol(&arguments[1], target, contains_cache, &mut HashSet::new())
                {
                    let mut nested_guards = guards.to_vec();
                    nested_guards.push(arguments[0].clone());
                    self.collect_update_slices(
                        &arguments[1],
                        target,
                        &nested_guards,
                        contains_cache,
                        active_helpers,
                        slices,
                    );
                }
            }
            "not" if arguments.len() == 1 => self.collect_update_slices(
                &arguments[0],
                target,
                guards,
                contains_cache,
                active_helpers,
                slices,
            ),
            _ => {
                if self.contains_symbol(term, target, contains_cache, &mut HashSet::new()) {
                    slices.extend(guards.iter().cloned());
                    slices.push(term.clone());
                }
            }
        }
    }

    fn contains_symbol(
        &self,
        term: &Term,
        target: &str,
        helper_cache: &mut HashMap<String, bool>,
        active_helpers: &mut HashSet<String>,
    ) -> bool {
        if let Some(symbol) = leaf_symbol(term) {
            if symbol == target {
                return true;
            }
            let Some(definition) = self.graph.get(&symbol) else {
                return false;
            };
            if let Some(cached) = helper_cache.get(&symbol) {
                return *cached;
            }
            if !active_helpers.insert(symbol.clone()) {
                return false;
            }
            let contains =
                self.contains_symbol(definition.body(), target, helper_cache, active_helpers);
            active_helpers.remove(&symbol);
            helper_cache.insert(symbol, contains);
            return contains;
        }

        match term {
            Term::Application { arguments, .. } => arguments.iter().any(|argument| {
                self.contains_symbol(argument, target, helper_cache, active_helpers)
            }),
            Term::Let { var_bindings, term } => {
                var_bindings.iter().any(|(_, value)| {
                    self.contains_symbol(value, target, helper_cache, active_helpers)
                }) || self.contains_symbol(term, target, helper_cache, active_helpers)
            }
            Term::Forall { term, .. }
            | Term::Exists { term, .. }
            | Term::Attributes { term, .. } => {
                self.contains_symbol(term, target, helper_cache, active_helpers)
            }
            Term::Match { term, cases } => {
                self.contains_symbol(term, target, helper_cache, active_helpers)
                    || cases.iter().any(|(_, case)| {
                        self.contains_symbol(case, target, helper_cache, active_helpers)
                    })
            }
            Term::Constant(_) | Term::QualIdentifier(_) => false,
        }
    }

    fn next_symbols(&self, term: &Term, active_helpers: &mut HashSet<String>) -> BTreeSet<String> {
        let mut result = BTreeSet::new();
        self.collect_next_symbols(term, active_helpers, &mut result);
        result
    }

    fn collect_next_symbols(
        &self,
        term: &Term,
        active_helpers: &mut HashSet<String>,
        result: &mut BTreeSet<String>,
    ) {
        if let Some(symbol) = leaf_symbol(term) {
            if self.next_to_current.contains_key(&symbol) {
                result.insert(symbol);
            } else if let Some(definition) = self.graph.get(&symbol) {
                if active_helpers.insert(symbol.clone()) {
                    self.collect_next_symbols(definition.body(), active_helpers, result);
                    active_helpers.remove(&symbol);
                }
            }
            return;
        }
        match term {
            Term::Application { arguments, .. } => {
                for argument in arguments {
                    self.collect_next_symbols(argument, active_helpers, result);
                }
            }
            Term::Let { var_bindings, term } => {
                for (_, value) in var_bindings {
                    self.collect_next_symbols(value, active_helpers, result);
                }
                self.collect_next_symbols(term, active_helpers, result);
            }
            Term::Forall { term, .. }
            | Term::Exists { term, .. }
            | Term::Attributes { term, .. } => {
                self.collect_next_symbols(term, active_helpers, result);
            }
            Term::Match { term, cases } => {
                self.collect_next_symbols(term, active_helpers, result);
                for (_, case) in cases {
                    self.collect_next_symbols(case, active_helpers, result);
                }
            }
            Term::Constant(_) | Term::QualIdentifier(_) => {}
        }
    }
}

fn leaf_symbol(term: &Term) -> Option<String> {
    match term {
        Term::QualIdentifier(identifier) => Some(identifier.get_name()),
        Term::Application {
            qual_identifier,
            arguments,
        } if arguments.is_empty() => Some(qual_identifier.get_name()),
        _ => None,
    }
}

fn insert_min(map: &mut BTreeMap<String, u32>, key: String, distance: u32) {
    match map.get_mut(&key) {
        Some(existing) => *existing = (*existing).min(distance),
        None => {
            map.insert(key, distance);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn array_copy_cone_follows_property_array_through_transition_dataflow() {
        let model = VMTModel::from_path("examples/array/array_copy.vmt").unwrap();
        let cone = build_property_cone(&model);

        assert_eq!(cone.array_distances.get("b"), Some(&0));
        assert!(cone.array_distances.contains_key("a"));
    }
}
