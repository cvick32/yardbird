//! Static control structure shared by array and binder refinement.
//!
//! The index describes source constraints; it never asserts model equalities.
//! Named actions are mutually exclusive in distributed-protocol encodings.
//! Array semantics and quantifier instantiation remain in their theory modules.
use std::collections::{BTreeMap, HashMap, HashSet};

use smt2parser::{
    concrete::{Command, QualIdentifier, Term},
    vmt::{
        bmc::BMCBuilder,
        definition_graph::{DefinitionFrameInfo, DefinitionGraph},
        VMTModel,
    },
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GuardedPathCondition {
    pub expression: Term,
    pub required_value: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StateUpdatePath {
    pub target: String,
    pub target_expression: Term,
    pub value: Term,
    pub guards: Vec<GuardedPathCondition>,
    pub action: Option<String>,
}

/// Keep the whole Boolean formula: sibling guards and disjunctions must not be
/// mistaken for unconditional prerequisites of an individual update.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ActionRequirement {
    pub body: Term,
    pub guards: Vec<GuardedPathCondition>,
    pub binders: Vec<BinderOccurrence>,
}

/// A lowered helper application links back to the compiled BinderRule by name.
/// Its arguments retain the binder's captures. The path is relative to the
/// requirement body, with zero-argument definitions expanded during traversal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BinderOccurrence {
    pub helper: String,
    pub application: Term,
    pub expression_path: Vec<usize>,
}

#[derive(Clone, Debug, Default)]
pub struct ActionEntry {
    pub requirements: Vec<ActionRequirement>,
}

#[derive(Clone, Debug)]
pub struct TransitionIndex {
    property: Term,
    actions: BTreeMap<String, ActionEntry>,
    updates: BTreeMap<String, Vec<StateUpdatePath>>,
    current_variables: Vec<String>,
    next_to_current: HashMap<String, String>,
    definition_frames: DefinitionFrameInfo,
    definitions: DefinitionGraph,
}

impl Default for TransitionIndex {
    fn default() -> Self {
        Self {
            property: Term::QualIdentifier(QualIdentifier::simple("true")),
            actions: BTreeMap::new(),
            updates: BTreeMap::new(),
            current_variables: Vec::new(),
            next_to_current: HashMap::new(),
            definition_frames: DefinitionFrameInfo::default(),
            definitions: DefinitionGraph::default(),
        }
    }
}

impl TransitionIndex {
    /// Analyze after quantifier lowering when binder helper links are needed.
    /// An empty helper set also supports unlowered, ordinary array programs.
    pub fn from_model(model: &VMTModel, binder_helpers: &HashSet<String>) -> Self {
        let current_variables = model.get_all_current_variable_names();
        let next_to_current = model.get_next_to_current_varible_names();
        let definitions = model.get_helper_definitions();
        let mut index = Self {
            property: model.get_property_for_yardbird(),
            actions: model
                .get_action_variables()
                .into_iter()
                .filter_map(|cmd| match cmd {
                    Command::DeclareFun { symbol, .. } => Some((symbol.0, ActionEntry::default())),
                    _ => None,
                })
                .collect(),
            updates: BTreeMap::new(),
            definition_frames: DefinitionFrameInfo::new(
                definitions,
                &current_variables,
                &next_to_current,
            ),
            current_variables,
            next_to_current,
            definitions: definitions.clone(),
        };
        Builder {
            definitions,
            binder_helpers,
            index: &mut index,
        }
        .collect(
            &model.get_trans_condition_for_yardbird(),
            &[],
            &mut HashSet::new(),
        );
        index
    }

    pub fn property(&self) -> &Term {
        &self.property
    }
    pub fn definitions(&self) -> &DefinitionGraph {
        &self.definitions
    }
    pub fn actions(&self) -> &BTreeMap<String, ActionEntry> {
        &self.actions
    }
    pub fn update_paths(&self, state: &str) -> &[StateUpdatePath] {
        self.updates
            .get(state)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }
    pub fn updates(&self) -> impl Iterator<Item = &StateUpdatePath> {
        self.updates.values().flatten()
    }
    pub fn action_updates<'a>(
        &'a self,
        action: &'a str,
    ) -> impl Iterator<Item = &'a StateUpdatePath> {
        self.updates()
            .filter(move |path| path.action.as_deref() == Some(action))
    }
    pub fn index_term(&self, term: &Term, frame: u16) -> Term {
        let mut builder = BMCBuilder::with_definition_frames(
            self.current_variables.clone(),
            self.next_to_current.clone(),
            self.definition_frames.clone(),
        );
        builder.set_depth(frame);
        builder.index_single_step_term(term.clone())
    }

    /// Expand a definition at its actual frame without reframing witness captures.
    #[allow(dead_code)] // Connected by the upcoming obligation-discovery integration.
    pub(crate) fn expand_framed_leaf(&self, term: &Term) -> Option<Term> {
        let name = leaf_symbol(term)?;
        if let Some(definition) = self.definitions.get(&name) {
            return Some(definition.body().clone());
        }
        let (base, frame) = smt2parser::vmt::split_framed_symbol(&name)?;
        let definition = self.definitions.get(&base)?;
        Some(self.index_term(definition.body(), u16::try_from(frame).ok()?))
    }

    /// Selection is local to this model and transition frame. None covers
    /// actionless inputs or a stuttering encoding with no asserted action flag.
    pub fn selected_action(
        &self,
        frame: u16,
        mut evaluate: impl FnMut(&Term) -> anyhow::Result<String>,
    ) -> anyhow::Result<Option<&str>> {
        let mut selected = None;
        for action in self.actions.keys() {
            let term =
                self.index_term(&Term::QualIdentifier(QualIdentifier::simple(action)), frame);
            match evaluate(&term)?.trim() {
                "true" => {
                    anyhow::ensure!(selected.is_none(), "mutually exclusive action flags violated at frame {frame}: {} and {action}", selected.unwrap_or_default());
                    selected = Some(action.as_str());
                }
                "false" => {}
                other => anyhow::bail!("expected Boolean action value for {term}, got {other}"),
            }
        }
        Ok(selected)
    }
}

struct Builder<'a> {
    definitions: &'a DefinitionGraph,
    binder_helpers: &'a HashSet<String>,
    index: &'a mut TransitionIndex,
}

impl Builder<'_> {
    fn collect(
        &mut self,
        term: &Term,
        guards: &[GuardedPathCondition],
        active: &mut HashSet<String>,
    ) {
        if let Some(symbol) = leaf_symbol(term) {
            if let Some(definition) = self.definitions.get(&symbol) {
                if active.insert(symbol.clone()) {
                    self.collect(definition.body(), guards, active);
                    active.remove(&symbol);
                }
            }
            return;
        }
        if let Term::Attributes { term, .. } = term {
            self.collect(term, guards, active);
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
            "=>" if arguments.len() == 2 => {
                let mut nested = guards.to_vec();
                nested.push(GuardedPathCondition {
                    expression: arguments[0].clone(),
                    required_value: true,
                });
                self.record_action(&arguments[1], guards, &nested);
                self.collect(&arguments[1], &nested, active);
            }
            "ite" if arguments.len() == 3 => {
                for (required_value, branch) in [(true, &arguments[1]), (false, &arguments[2])] {
                    let mut nested = guards.to_vec();
                    nested.push(GuardedPathCondition {
                        expression: arguments[0].clone(),
                        required_value,
                    });
                    self.record_action(branch, guards, &nested);
                    self.collect(branch, &nested, active);
                }
            }
            "or" => {
                for branch in arguments {
                    let mut nested = guards.to_vec();
                    nested.push(GuardedPathCondition {
                        expression: branch.clone(),
                        required_value: true,
                    });
                    self.record_action(branch, guards, &nested);
                    self.collect(branch, &nested, active);
                }
            }
            "and" => {
                for arg in arguments {
                    self.collect(arg, guards, active);
                }
            }
            "=" if arguments.len() == 2 => {
                for (left, right) in [
                    (&arguments[0], &arguments[1]),
                    (&arguments[1], &arguments[0]),
                ] {
                    if let Some(target) =
                        leaf_symbol(left).and_then(|s| self.index.next_to_current.get(&s).cloned())
                    {
                        self.record_update(target, left.clone(), right.clone(), guards);
                        break;
                    }
                }
            }
            // Do not interpret equalities inside negation, quantifiers, or
            // arbitrary applications as assignments. The containing action
            // requirement retains those formulas for theory-specific analysis.
            _ => {}
        }
    }

    fn action_for(&self, guards: &[GuardedPathCondition]) -> Option<String> {
        guards
            .iter()
            .filter(|g| g.required_value)
            .find_map(|g| self.positive_action(&g.expression, &mut HashSet::new()))
    }

    fn positive_action(&self, term: &Term, active: &mut HashSet<String>) -> Option<String> {
        if let Some(symbol) = leaf_symbol(term) {
            if self.index.actions.contains_key(&symbol) {
                return Some(symbol);
            }
            if active.insert(symbol.clone()) {
                let found = self
                    .definitions
                    .get(&symbol)
                    .and_then(|d| self.positive_action(d.body(), active));
                active.remove(&symbol);
                return found;
            }
        }
        match term {
            Term::Application {
                qual_identifier,
                arguments,
            } if qual_identifier.get_name() == "and" => arguments
                .iter()
                .find_map(|a| self.positive_action(a, active)),
            Term::Attributes { term, .. } => self.positive_action(term, active),
            _ => None,
        }
    }

    fn record_action(
        &mut self,
        body: &Term,
        previous: &[GuardedPathCondition],
        guards: &[GuardedPathCondition],
    ) {
        let Some(action) = self.action_for(guards) else {
            return;
        };
        if self.action_for(previous).as_ref() == Some(&action) {
            return;
        }
        let body = expand_leaf_helper(body, self.definitions);
        let mut binders = Vec::new();
        self.collect_binders(&body, &mut Vec::new(), &mut HashSet::new(), &mut binders);
        let requirement = ActionRequirement {
            body: body.clone(),
            guards: guards.to_vec(),
            binders,
        };
        let requirements = &mut self.index.actions.get_mut(&action).unwrap().requirements;
        if !requirements.contains(&requirement) {
            requirements.push(requirement);
        }
    }

    fn collect_binders(
        &self,
        term: &Term,
        path: &mut Vec<usize>,
        active: &mut HashSet<String>,
        out: &mut Vec<BinderOccurrence>,
    ) {
        if let Some(symbol) = leaf_symbol(term) {
            if let Some(definition) = self.definitions.get(&symbol) {
                if active.insert(symbol.clone()) {
                    self.collect_binders(definition.body(), path, active, out);
                    active.remove(&symbol);
                }
            }
        }
        match term {
            Term::Application {
                qual_identifier,
                arguments,
            } => {
                let helper = qual_identifier.get_name();
                if self.binder_helpers.contains(&helper) {
                    out.push(BinderOccurrence {
                        helper,
                        application: term.clone(),
                        expression_path: path.clone(),
                    });
                }
                for (i, arg) in arguments.iter().enumerate() {
                    path.push(i);
                    self.collect_binders(arg, path, active, out);
                    path.pop();
                }
            }
            Term::Attributes { term, .. } => self.collect_binders(term, path, active, out),
            _ => {}
        }
    }

    fn record_update(
        &mut self,
        target: String,
        target_expression: Term,
        value: Term,
        guards: &[GuardedPathCondition],
    ) {
        let expanded = expand_leaf_helper(&value, self.definitions);
        if let Term::Application {
            qual_identifier,
            arguments,
        } = &expanded
        {
            if qual_identifier.get_name() == "ite" && arguments.len() == 3 {
                for (required_value, branch) in [(true, &arguments[1]), (false, &arguments[2])] {
                    let mut nested = guards.to_vec();
                    nested.push(GuardedPathCondition {
                        expression: arguments[0].clone(),
                        required_value,
                    });
                    self.record_update(
                        target.clone(),
                        target_expression.clone(),
                        branch.clone(),
                        &nested,
                    );
                }
                return;
            }
        }
        let action = self.action_for(guards);
        self.index
            .updates
            .entry(target.clone())
            .or_default()
            .push(StateUpdatePath {
                target,
                target_expression,
                value: expanded,
                guards: guards.to_vec(),
                action,
            });
    }
}

pub(crate) fn expand_leaf_helper(term: &Term, definitions: &DefinitionGraph) -> Term {
    let mut expanded = term.clone();
    let mut active = HashSet::new();
    while let Some(symbol) = leaf_symbol(&expanded) {
        let Some(definition) = definitions.get(&symbol) else {
            break;
        };
        if !active.insert(symbol) {
            break;
        }
        expanded = definition.body().clone();
    }
    expanded
}

pub(crate) fn leaf_symbol(term: &Term) -> Option<String> {
    match term {
        Term::QualIdentifier(id) => Some(id.get_name()),
        Term::Application {
            qual_identifier,
            arguments,
        } if arguments.is_empty() => Some(qual_identifier.get_name()),
        _ => None,
    }
}

#[cfg(test)]
mod tests;
