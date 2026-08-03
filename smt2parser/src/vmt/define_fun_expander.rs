use std::collections::{HashMap, HashSet};

use crate::concrete::{Command, Identifier, QualIdentifier, Symbol, Term};

use super::VMTError;

/// Expands zero-argument `define-fun` commands as SMT-LIB constant macros.
///
/// VMT generators such as MathSAT use these definitions heavily and reference
/// them from the init, transition, and property terms. Top-level attributes on
/// a definition describe VMT metadata and do not change the definition's value,
/// so they are removed when that value is substituted at a use site.
pub(super) struct DefineFunExpander {
    definitions: HashMap<String, Term>,
    resolved: HashMap<String, Term>,
    resolving: HashSet<String>,
}

impl DefineFunExpander {
    pub(super) fn from_commands(commands: &[Command]) -> Self {
        let definitions = commands
            .iter()
            .filter_map(|command| match command {
                Command::DefineFun { sig, term } if sig.parameters.is_empty() => {
                    Some((sig.name.0.clone(), strip_attributes(term.clone())))
                }
                _ => None,
            })
            .collect();
        Self {
            definitions,
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
        let Some(term) = self.definitions.get(name).cloned() else {
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
