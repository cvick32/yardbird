use serde::{Deserialize, Serialize};
use smt2parser::concrete::Term;

/// One axiom-variable binding in a complete theory instantiation.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct InstantiationSubstitution {
    pub variable: String,
    pub term: String,
}

/// Link to a property-rooted explanation in one solver model.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct CountermodelOrigin {
    pub model_version: u64,
    pub depth: u16,
    pub node: usize,
}

/// Stable provenance carried from whole-candidate selection to solver placement.
///
/// The stored terms use Yardbird's relative frame notation (`a+0`, `i+1`).
/// Installation rewrites these bindings for each absolute BMC placement.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InstantiationProvenance {
    abstract_instantiation_id: String,
    relative_substitution: Vec<(String, Term)>,
    countermodel_origin: Option<CountermodelOrigin>,
}

impl InstantiationProvenance {
    pub fn new(
        abstract_instantiation_id: String,
        relative_substitution: Vec<(String, Term)>,
    ) -> Self {
        Self {
            abstract_instantiation_id,
            relative_substitution,
            countermodel_origin: None,
        }
    }

    pub(crate) fn with_countermodel_origin(mut self, origin: Option<CountermodelOrigin>) -> Self {
        self.countermodel_origin = origin;
        self
    }

    pub fn countermodel_origin(&self) -> Option<&CountermodelOrigin> {
        self.countermodel_origin.as_ref()
    }

    pub fn abstract_instantiation_id(&self) -> &str {
        &self.abstract_instantiation_id
    }

    pub fn into_parts(self) -> (String, Vec<(String, Term)>) {
        (self.abstract_instantiation_id, self.relative_substitution)
    }

    pub(crate) fn relative_bindings(&self) -> &[(String, Term)] {
        &self.relative_substitution
    }

    pub fn relative_substitution(&self) -> Vec<InstantiationSubstitution> {
        substitution_records(&self.relative_substitution)
    }
}

fn substitution_records(substitution: &[(String, Term)]) -> Vec<InstantiationSubstitution> {
    substitution
        .iter()
        .map(|(variable, term)| InstantiationSubstitution {
            variable: variable.clone(),
            term: term.to_string(),
        })
        .collect()
}
