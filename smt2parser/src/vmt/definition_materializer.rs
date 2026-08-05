use std::collections::{HashMap, HashSet};

use crate::concrete::{Command, QualIdentifier, Symbol, Term};

use super::{
    bmc::BMCBuilder,
    definition_graph::{free_symbols, DefinitionFrameInfo, DefinitionGraph},
    VARIABLE_FRAME_DELIMITER,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct DefinitionInstance {
    name: String,
    anchor: Option<u16>,
}

impl DefinitionInstance {
    fn symbol(&self) -> String {
        match self.anchor {
            Some(anchor) => format!("{}{}{}", self.name, VARIABLE_FRAME_DELIMITER, anchor),
            None => self.name.clone(),
        }
    }
}

#[derive(Clone, Debug)]
struct MaterializedDefinition {
    declaration: Command,
    assertion: Term,
}

/// A BMC-indexed root plus the shared definitions needed to interpret it.
#[derive(Clone, Debug)]
pub struct MaterializedTerm {
    pub root: Term,
    /// All reachable definitions, including definitions emitted previously.
    pub support: Vec<Term>,
    /// Declarations that must be installed before asserting this root.
    pub new_declarations: Vec<Command>,
    /// Definitional equalities that must be installed before asserting this root.
    pub new_definitions: Vec<Term>,
}

/// Lazily creates one solver symbol and equality for each reachable
/// `(helper-definition, frame)` pair.
#[derive(Clone, Debug)]
pub struct DefinitionMaterializer {
    graph: DefinitionGraph,
    frames: DefinitionFrameInfo,
    materialized: HashMap<DefinitionInstance, MaterializedDefinition>,
    materialization_order: Vec<DefinitionInstance>,
    emitted: HashSet<DefinitionInstance>,
}

impl DefinitionMaterializer {
    pub fn new(graph: DefinitionGraph, frames: DefinitionFrameInfo) -> Self {
        Self {
            graph,
            frames,
            materialized: HashMap::new(),
            materialization_order: Vec::new(),
            emitted: HashSet::new(),
        }
    }

    pub fn declarations(&self) -> Vec<Command> {
        self.materialization_order
            .iter()
            .map(|instance| self.materialized[instance].declaration.clone())
            .collect()
    }

    pub fn definitions(&self) -> Vec<Term> {
        self.materialization_order
            .iter()
            .map(|instance| self.materialized[instance].assertion.clone())
            .collect()
    }

    pub fn materialize(&mut self, root: Term, bmc_builder: &mut BMCBuilder) -> MaterializedTerm {
        let mut order = Vec::new();
        let mut seen = HashSet::new();
        for symbol in free_symbols(&root) {
            if let Some(instance) = self.instance_from_symbol(&symbol) {
                self.ensure_instance(instance, bmc_builder, &mut seen, &mut order);
            }
        }

        let support = order
            .iter()
            .map(|instance| self.materialized[instance].assertion.clone())
            .collect();
        let mut new_declarations = Vec::new();
        let mut new_definitions = Vec::new();
        for instance in order {
            if self.emitted.insert(instance.clone()) {
                let definition = &self.materialized[&instance];
                new_declarations.push(definition.declaration.clone());
                new_definitions.push(definition.assertion.clone());
            }
        }

        MaterializedTerm {
            root,
            support,
            new_declarations,
            new_definitions,
        }
    }

    fn ensure_instance(
        &mut self,
        instance: DefinitionInstance,
        bmc_builder: &mut BMCBuilder,
        seen: &mut HashSet<DefinitionInstance>,
        order: &mut Vec<DefinitionInstance>,
    ) {
        if !seen.insert(instance.clone()) {
            return;
        }

        let definition = self
            .graph
            .get(&instance.name)
            .expect("definition instance must refer to a known helper")
            .clone();
        for dependency in definition.dependencies() {
            let dependency = DefinitionInstance {
                name: dependency.clone(),
                anchor: self
                    .frames
                    .is_state_dependent(dependency)
                    .then_some(instance.anchor.unwrap_or(0)),
            };
            self.ensure_instance(dependency, bmc_builder, seen, order);
        }

        if !self.materialized.contains_key(&instance) {
            let saved_depth = bmc_builder.depth;
            let saved_width = bmc_builder.width;
            bmc_builder.set_depth(instance.anchor.unwrap_or(0));
            let indexed_body = definition.body().clone().accept(bmc_builder).unwrap();
            bmc_builder.set_depth(saved_depth);
            bmc_builder.width = saved_width;

            let symbol = instance.symbol();
            let declaration = Command::DeclareFun {
                symbol: Symbol(symbol.clone()),
                parameters: vec![],
                sort: definition.sort().clone(),
            };
            let assertion = Term::Application {
                qual_identifier: QualIdentifier::simple("="),
                arguments: vec![
                    Term::QualIdentifier(QualIdentifier::simple(symbol)),
                    indexed_body,
                ],
            };
            self.materialized.insert(
                instance.clone(),
                MaterializedDefinition {
                    declaration,
                    assertion,
                },
            );
            self.materialization_order.push(instance.clone());
        }

        order.push(instance);
    }

    fn instance_from_symbol(&self, symbol: &str) -> Option<DefinitionInstance> {
        if self.graph.contains(symbol) && !self.frames.is_state_dependent(symbol) {
            return Some(DefinitionInstance {
                name: symbol.to_string(),
                anchor: None,
            });
        }

        let (name, frame) = symbol.rsplit_once(VARIABLE_FRAME_DELIMITER)?;
        if !self.graph.contains(name) || !self.frames.is_state_dependent(name) {
            return None;
        }
        Some(DefinitionInstance {
            name: name.to_string(),
            anchor: Some(frame.parse().ok()?),
        })
    }
}
