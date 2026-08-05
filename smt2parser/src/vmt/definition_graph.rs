use std::collections::{BTreeSet, HashMap, HashSet};

use crate::concrete::{Command, FunctionDec, Identifier, QualIdentifier, Sort, Symbol, Term};

use super::VMTError;

const VMT_METADATA_ATTRIBUTES: [&str; 6] =
    ["next", "action", "axiom", "init", "trans", "invar-property"];

/// A zero-argument SMT-LIB definition retained as a shared VMT helper.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HelperDefinition {
    name: String,
    sort: Sort,
    body: Term,
    free_symbols: Vec<String>,
    dependencies: Vec<String>,
}

impl HelperDefinition {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn sort(&self) -> &Sort {
        &self.sort
    }

    pub fn body(&self) -> &Term {
        &self.body
    }

    pub fn free_symbols(&self) -> &[String] {
        &self.free_symbols
    }

    pub fn dependencies(&self) -> &[String] {
        &self.dependencies
    }

    fn to_command(&self) -> Command {
        Command::DefineFun {
            sig: FunctionDec {
                name: Symbol(self.name.clone()),
                parameters: vec![],
                result: self.sort.clone(),
            },
            term: self.body.clone(),
        }
    }
}

/// The shared, validated DAG of ordinary zero-argument VMT helper definitions.
///
/// Definitions are stored in dependency-first order so serialization and BMC
/// materialization never need to expand the graph into a tree.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DefinitionGraph {
    definitions: Vec<HelperDefinition>,
    indices: HashMap<String, usize>,
}

/// The relative state frames used by every helper definition.
///
/// Offset 0 denotes a current-state dependency and offset 1 denotes a
/// next-state dependency. Empty footprints are frame-independent and can be
/// shared across every BMC depth.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DefinitionFrameInfo {
    offsets: HashMap<String, BTreeSet<i16>>,
}

impl DefinitionFrameInfo {
    pub fn new(
        graph: &DefinitionGraph,
        current_variables: &[String],
        next_variables: &HashMap<String, String>,
    ) -> Self {
        let current_variables = current_variables.iter().collect::<HashSet<_>>();
        let mut offsets = HashMap::<String, BTreeSet<i16>>::new();

        // DefinitionGraph iteration is dependency-first.
        for definition in graph.iter() {
            let mut definition_offsets = BTreeSet::new();
            for symbol in definition.free_symbols() {
                if current_variables.contains(symbol) {
                    definition_offsets.insert(0);
                } else if next_variables.contains_key(symbol) {
                    definition_offsets.insert(1);
                } else if let Some(dependency_offsets) = offsets.get(symbol) {
                    definition_offsets.extend(dependency_offsets);
                }
            }
            offsets.insert(definition.name().to_string(), definition_offsets);
        }

        Self { offsets }
    }

    pub fn contains(&self, name: &str) -> bool {
        self.offsets.contains_key(name)
    }

    pub fn is_state_dependent(&self, name: &str) -> bool {
        self.offsets
            .get(name)
            .is_some_and(|offsets| !offsets.is_empty())
    }

    pub fn offsets(&self, name: &str) -> Option<&BTreeSet<i16>> {
        self.offsets.get(name)
    }
}

impl DefinitionGraph {
    pub(super) fn from_commands(commands: Vec<Command>) -> Result<Self, VMTError> {
        let mut raw = Vec::with_capacity(commands.len());
        let mut raw_indices = HashMap::with_capacity(commands.len());

        for command in commands {
            let Command::DefineFun { sig, term } = command else {
                continue;
            };
            debug_assert!(sig.parameters.is_empty());
            let name = sig.name.0;
            if raw_indices.insert(name.clone(), raw.len()).is_some() {
                return Err(VMTError::DuplicateDefinition(name));
            }
            raw.push((name, sig.result, term));
        }

        let helper_names = raw_indices.keys().cloned().collect::<HashSet<_>>();
        let mut unordered = Vec::with_capacity(raw.len());
        for (name, sort, body) in raw {
            let free_symbols = free_symbols(&body);
            let dependencies = free_symbols
                .iter()
                .filter(|symbol| helper_names.contains(*symbol))
                .cloned()
                .collect();
            unordered.push(HelperDefinition {
                name,
                sort,
                body,
                free_symbols,
                dependencies,
            });
        }

        let mut order = Vec::with_capacity(unordered.len());
        let mut visited = HashSet::with_capacity(unordered.len());
        let mut visiting = HashSet::with_capacity(unordered.len());
        for definition in &unordered {
            visit_definition(
                definition.name(),
                &unordered,
                &raw_indices,
                &mut visiting,
                &mut visited,
                &mut order,
            )?;
        }

        let definitions = order
            .into_iter()
            .map(|index| unordered[index].clone())
            .collect::<Vec<_>>();
        let indices = definitions
            .iter()
            .enumerate()
            .map(|(index, definition)| (definition.name.clone(), index))
            .collect();

        Ok(Self {
            definitions,
            indices,
        })
    }

    pub fn is_empty(&self) -> bool {
        self.definitions.is_empty()
    }

    pub fn len(&self) -> usize {
        self.definitions.len()
    }

    pub fn contains(&self, name: &str) -> bool {
        self.indices.contains_key(name)
    }

    pub fn get(&self, name: &str) -> Option<&HelperDefinition> {
        self.indices
            .get(name)
            .map(|index| &self.definitions[*index])
    }

    pub fn iter(&self) -> impl Iterator<Item = &HelperDefinition> {
        self.definitions.iter()
    }

    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.definitions.iter().map(|definition| definition.name())
    }

    pub fn as_commands(&self) -> Vec<Command> {
        self.definitions
            .iter()
            .map(HelperDefinition::to_command)
            .collect()
    }
}

fn visit_definition(
    name: &str,
    definitions: &[HelperDefinition],
    indices: &HashMap<String, usize>,
    visiting: &mut HashSet<String>,
    visited: &mut HashSet<String>,
    order: &mut Vec<usize>,
) -> Result<(), VMTError> {
    if visited.contains(name) {
        return Ok(());
    }
    if !visiting.insert(name.to_string()) {
        return Err(VMTError::CyclicDefinition(name.to_string()));
    }

    let index = indices[name];
    for dependency in definitions[index].dependencies() {
        visit_definition(dependency, definitions, indices, visiting, visited, order)?;
    }

    visiting.remove(name);
    visited.insert(name.to_string());
    order.push(index);
    Ok(())
}

/// Expands only VMT metadata aliases, such as `.def_9` carrying `:next`.
/// Ordinary helpers are deliberately left as references in the resulting term.
pub(super) struct MetadataAliasExpander {
    aliases: HashMap<String, Term>,
    resolved: HashMap<String, Term>,
    resolving: HashSet<String>,
}

impl MetadataAliasExpander {
    pub(super) fn from_commands(commands: &[Command]) -> Self {
        let aliases = commands
            .iter()
            .filter_map(|command| match command {
                Command::DefineFun { sig, term }
                    if sig.parameters.is_empty() && has_vmt_metadata(term) =>
                {
                    Some((sig.name.0.clone(), strip_attributes(term.clone())))
                }
                _ => None,
            })
            .collect();
        Self {
            aliases,
            resolved: HashMap::new(),
            resolving: HashSet::new(),
        }
    }

    pub(super) fn expand(&mut self, term: Term) -> Result<Term, VMTError> {
        self.expand_with_bindings(term, &mut HashSet::new())
    }

    fn expand_with_bindings(
        &mut self,
        term: Term,
        bindings: &mut HashSet<String>,
    ) -> Result<Term, VMTError> {
        match term {
            Term::Constant(constant) => Ok(Term::Constant(constant)),
            Term::QualIdentifier(qual_identifier) => {
                if let Some(symbol) = simple_symbol(&qual_identifier) {
                    if !bindings.contains(&symbol.0) {
                        if let Some(expanded) = self.resolve(&symbol.0)? {
                            return Ok(expanded);
                        }
                    }
                }
                Ok(Term::QualIdentifier(qual_identifier))
            }
            Term::Application {
                qual_identifier,
                arguments,
            } => {
                if arguments.is_empty() {
                    if let Some(symbol) = simple_symbol(&qual_identifier) {
                        if !bindings.contains(&symbol.0) {
                            if let Some(expanded) = self.resolve(&symbol.0)? {
                                return Ok(expanded);
                            }
                        }
                    }
                }
                Ok(Term::Application {
                    qual_identifier,
                    arguments: arguments
                        .into_iter()
                        .map(|argument| self.expand_with_bindings(argument, bindings))
                        .collect::<Result<Vec<_>, _>>()?,
                })
            }
            Term::Let { var_bindings, term } => {
                let var_bindings = var_bindings
                    .into_iter()
                    .map(|(symbol, value)| {
                        self.expand_with_bindings(value, bindings)
                            .map(|value| (symbol, value))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let inserted =
                    bind_symbols(bindings, var_bindings.iter().map(|(symbol, _)| symbol));
                let term = self.expand_with_bindings(*term, bindings)?;
                unbind_symbols(bindings, inserted);
                Ok(Term::Let {
                    var_bindings,
                    term: Box::new(term),
                })
            }
            Term::Forall { vars, term } => {
                let inserted = bind_symbols(bindings, vars.iter().map(|(symbol, _)| symbol));
                let term = self.expand_with_bindings(*term, bindings)?;
                unbind_symbols(bindings, inserted);
                Ok(Term::Forall {
                    vars,
                    term: Box::new(term),
                })
            }
            Term::Exists { vars, term } => {
                let inserted = bind_symbols(bindings, vars.iter().map(|(symbol, _)| symbol));
                let term = self.expand_with_bindings(*term, bindings)?;
                unbind_symbols(bindings, inserted);
                Ok(Term::Exists {
                    vars,
                    term: Box::new(term),
                })
            }
            Term::Match { term, cases } => {
                let term = self.expand_with_bindings(*term, bindings)?;
                let cases = cases
                    .into_iter()
                    .map(|(symbols, case)| {
                        let inserted = bind_symbols(bindings, symbols.iter());
                        let case = self.expand_with_bindings(case, bindings);
                        unbind_symbols(bindings, inserted);
                        case.map(|case| (symbols, case))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Term::Match {
                    term: Box::new(term),
                    cases,
                })
            }
            Term::Attributes { term, attributes } => Ok(Term::Attributes {
                term: Box::new(self.expand_with_bindings(*term, bindings)?),
                attributes,
            }),
        }
    }

    fn resolve(&mut self, name: &str) -> Result<Option<Term>, VMTError> {
        if let Some(term) = self.resolved.get(name) {
            return Ok(Some(term.clone()));
        }
        let Some(term) = self.aliases.get(name).cloned() else {
            return Ok(None);
        };
        if !self.resolving.insert(name.to_string()) {
            return Err(VMTError::CyclicDefinition(name.to_string()));
        }
        let term = self.expand_with_bindings(term, &mut HashSet::new())?;
        self.resolving.remove(name);
        self.resolved.insert(name.to_string(), term.clone());
        Ok(Some(term))
    }
}

fn has_vmt_metadata(term: &Term) -> bool {
    match term {
        Term::Attributes { attributes, .. } => attributes
            .iter()
            .any(|(keyword, _)| VMT_METADATA_ATTRIBUTES.contains(&keyword.0.as_str())),
        _ => false,
    }
}

fn strip_attributes(mut term: Term) -> Term {
    while let Term::Attributes { term: inner, .. } = term {
        term = *inner;
    }
    term
}

fn simple_symbol(qual_identifier: &QualIdentifier) -> Option<&Symbol> {
    match qual_identifier {
        QualIdentifier::Simple {
            identifier: Identifier::Simple { symbol },
        } => Some(symbol),
        _ => None,
    }
}

fn bind_symbols<'a>(
    bindings: &mut HashSet<String>,
    symbols: impl Iterator<Item = &'a Symbol>,
) -> Vec<String> {
    symbols
        .filter_map(|symbol| {
            if bindings.insert(symbol.0.clone()) {
                Some(symbol.0.clone())
            } else {
                None
            }
        })
        .collect()
}

fn unbind_symbols(bindings: &mut HashSet<String>, symbols: Vec<String>) {
    for symbol in symbols {
        bindings.remove(&symbol);
    }
}

pub(super) fn free_symbols(term: &Term) -> Vec<String> {
    let mut symbols = BTreeSet::new();
    collect_free_symbols(term, &mut HashSet::new(), &mut symbols);
    symbols.into_iter().collect()
}

fn collect_free_symbols(
    term: &Term,
    bindings: &mut HashSet<String>,
    symbols: &mut BTreeSet<String>,
) {
    match term {
        Term::Constant(_) => {}
        Term::QualIdentifier(qual_identifier) => {
            if let Some(symbol) = simple_symbol(qual_identifier) {
                if !bindings.contains(&symbol.0) {
                    symbols.insert(symbol.0.clone());
                }
            }
        }
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            if arguments.is_empty() {
                if let Some(symbol) = simple_symbol(qual_identifier) {
                    if !bindings.contains(&symbol.0) {
                        symbols.insert(symbol.0.clone());
                    }
                }
            }
            for argument in arguments {
                collect_free_symbols(argument, bindings, symbols);
            }
        }
        Term::Let { var_bindings, term } => {
            for (_, value) in var_bindings {
                collect_free_symbols(value, bindings, symbols);
            }
            let inserted = bind_symbols(bindings, var_bindings.iter().map(|(symbol, _)| symbol));
            collect_free_symbols(term, bindings, symbols);
            unbind_symbols(bindings, inserted);
        }
        Term::Forall { vars, term } | Term::Exists { vars, term } => {
            let inserted = bind_symbols(bindings, vars.iter().map(|(symbol, _)| symbol));
            collect_free_symbols(term, bindings, symbols);
            unbind_symbols(bindings, inserted);
        }
        Term::Match { term, cases } => {
            collect_free_symbols(term, bindings, symbols);
            for (case_symbols, case) in cases {
                let inserted = bind_symbols(bindings, case_symbols.iter());
                collect_free_symbols(case, bindings, symbols);
                unbind_symbols(bindings, inserted);
            }
        }
        Term::Attributes { term, .. } => collect_free_symbols(term, bindings, symbols),
    }
}
