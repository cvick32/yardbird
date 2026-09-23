//! Run-local identities for parsed input binders, captured before alpha-renaming.
//! Locations refer to VMTModel::as_commands(), not byte offsets in the input file.

use std::collections::{BTreeMap, HashMap, HashSet};

use serde::{Deserialize, Serialize};
use smt2parser::{
    concrete::{Command, Sort, Symbol, Term},
    vmt::VMTModel,
};

use crate::theories::quantifiers::app;

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(default)]
pub struct QuantifierProvenance {
    pub sources: BTreeMap<String, QuantifierSource>,
    pub rules: BTreeMap<String, LoweredQuantifier>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct QuantifierSource {
    pub kind: String,
    pub formula: String,
    pub command_index: usize,
    pub command: String,
    pub expression_path: Vec<usize>,
    pub parent_source_id: Option<String>,
    pub variables: Vec<SourceVariable>,
    pub property_witnesses: Vec<PropertyWitness>,
    pub eliminated_as_constant_array: bool,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SourceVariable {
    pub name: String,
    pub sort: String,
    pub scoped_name: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PropertyWitness {
    pub scoped_variable: String,
    pub witness: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LoweredQuantifier {
    pub source_id: String,
    pub helper: String,
    pub kind: String,
    pub variables: Vec<LoweredVariable>,
    pub captures: Vec<(String, String)>,
    pub witnesses: Vec<String>,
    pub lowered_body: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LoweredVariable {
    pub scoped_name: String,
    pub lowered_name: String,
}

impl QuantifierProvenance {
    pub(crate) fn source_for_variables(&self, variables: &[(Symbol, Sort)]) -> Option<String> {
        let first = variables.first()?;
        self.sources.iter().find_map(|(id, source)| {
            source
                .variables
                .iter()
                .any(|v| v.scoped_name == first.0 .0)
                .then(|| id.clone())
        })
    }

    pub(crate) fn record_property_witnesses(&mut self, bindings: &[(Symbol, Symbol)]) {
        for (variable, witness) in bindings {
            for source in self.sources.values_mut() {
                if source.variables.iter().any(|v| v.scoped_name == variable.0) {
                    source.property_witnesses.push(PropertyWitness {
                        scoped_variable: variable.0.clone(),
                        witness: witness.0.clone(),
                    });
                }
            }
        }
    }
}

struct Scoper {
    reserved: HashSet<String>,
    next: usize,
    enabled: bool,
    provenance: QuantifierProvenance,
    command_index: usize,
    command: String,
}

impl Scoper {
    fn rewrite(
        &mut self,
        term: Term,
        scope: &HashMap<String, String>,
        path: Vec<usize>,
        parent: Option<String>,
    ) -> Term {
        let capture_locations = self.enabled;
        let child = |index| {
            if !capture_locations {
                return vec![];
            }
            let mut p = path.clone();
            p.push(index);
            p
        };
        match term {
            Term::QualIdentifier(id) => scope
                .get(&id.get_name())
                .map(|name| app(name, vec![]))
                .unwrap_or(Term::QualIdentifier(id)),
            Term::Application {
                qual_identifier,
                arguments,
            } => Term::Application {
                qual_identifier,
                arguments: arguments
                    .into_iter()
                    .enumerate()
                    .map(|(i, t)| self.rewrite(t, scope, child(i), parent.clone()))
                    .collect(),
            },
            Term::Attributes { term, attributes } => Term::Attributes {
                term: Box::new(self.rewrite(*term, scope, child(0), parent)),
                attributes,
            },
            Term::Let { var_bindings, term } => {
                let mut inner = scope.clone();
                for (symbol, _) in &var_bindings {
                    inner.remove(&symbol.0);
                }
                let body_index = var_bindings.len();
                Term::Let {
                    var_bindings: var_bindings
                        .into_iter()
                        .enumerate()
                        .map(|(i, (s, t))| (s, self.rewrite(t, scope, child(i), parent.clone())))
                        .collect(),
                    term: Box::new(self.rewrite(*term, &inner, child(body_index), parent)),
                }
            }
            term @ (Term::Forall { .. } | Term::Exists { .. } | Term::Lambda { .. }) => {
                let kind = match &term {
                    Term::Forall { .. } => "forall",
                    Term::Exists { .. } => "exists",
                    _ => "lambda",
                };
                let formula = self.enabled.then(|| term.to_string());
                let (vars, term) = match term {
                    Term::Forall { vars, term }
                    | Term::Exists { vars, term }
                    | Term::Lambda { vars, term } => (vars, term),
                    _ => unreachable!(),
                };
                let mut inner = scope.clone();
                let mut variables = Vec::new();
                let vars = vars
                    .into_iter()
                    .map(|(symbol, sort)| {
                        let name = loop {
                            let name = format!("__yardbird_scoped_binder_{}", self.next);
                            self.next += 1;
                            if self.reserved.insert(name.clone()) {
                                break name;
                            }
                        };
                        if self.enabled {
                            variables.push(SourceVariable {
                                name: symbol.0.clone(),
                                sort: sort.to_string(),
                                scoped_name: name.clone(),
                            });
                        }
                        inner.insert(symbol.0, name.clone());
                        (Symbol(name), sort)
                    })
                    .collect();
                let source_id = formula.map(|formula| {
                    let id = format!(
                        "q{}:{}",
                        self.command_index,
                        path.iter()
                            .map(usize::to_string)
                            .collect::<Vec<_>>()
                            .join(".")
                    );
                    self.provenance.sources.insert(
                        id.clone(),
                        QuantifierSource {
                            kind: kind.into(),
                            formula,
                            command_index: self.command_index,
                            command: self.command.clone(),
                            expression_path: path.clone(),
                            parent_source_id: parent.clone(),
                            variables,
                            property_witnesses: vec![],
                            eliminated_as_constant_array: false,
                        },
                    );
                    id
                });
                let term = Box::new(self.rewrite(*term, &inner, child(0), source_id.or(parent)));
                match kind {
                    "forall" => Term::Forall { vars, term },
                    "exists" => Term::Exists { vars, term },
                    _ => Term::Lambda { vars, term },
                }
            }
            // Preserve the existing scoping behavior for unsupported match expressions.
            other => other,
        }
    }
}

/// Rename lexical binders before let expansion or property Herbrandization.
/// In `(let ((a x)) (forall ((x S)) a))`, expanding `a` must not capture
/// the free `x`. Provenance observes this pass without changing fresh names.
pub(crate) fn scope_model(
    model: VMTModel,
    enabled: bool,
) -> anyhow::Result<(VMTModel, QuantifierProvenance)> {
    let commands = model.as_commands();
    let reserved = commands
        .iter()
        .flat_map(|c| {
            c.to_string()
                .split(|c: char| c.is_whitespace() || matches!(c, '(' | ')' | '|'))
                .map(str::to_string)
                .collect::<Vec<_>>()
        })
        .collect();
    let mut scoper = Scoper {
        reserved,
        next: 0,
        enabled,
        provenance: QuantifierProvenance::default(),
        command_index: 0,
        command: String::new(),
    };
    let commands = commands
        .into_iter()
        .enumerate()
        .map(|(index, command)| {
            scoper.command_index = index;
            match command {
                Command::DefineFun { sig, term } => {
                    scoper.command = format!("define-fun {}", sig.name);
                    Command::DefineFun {
                        sig,
                        term: scoper.rewrite(term, &HashMap::new(), vec![], None),
                    }
                }
                Command::Assert { term } => {
                    scoper.command = "assert".into();
                    Command::Assert {
                        term: scoper.rewrite(term, &HashMap::new(), vec![], None),
                    }
                }
                other => other,
            }
        })
        .collect();
    Ok((VMTModel::checked_from(commands)?, scoper.provenance))
}
