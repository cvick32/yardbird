use serde::{Deserialize, Serialize};
use smt2parser::{
    concrete::Term,
    vmt::{bmc::BMCBuilder, quantified_instantiator::Instance},
};

/// One axiom-variable binding in a complete theory instantiation.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct InstantiationSubstitution {
    pub variable: String,
    pub term: String,
}

/// Stable provenance carried from whole-candidate selection to solver placement.
///
/// The stored terms use Yardbird's relative frame notation (`a+0`, `i+1`).
/// [`at_frame`](Self::at_frame) produces the exact absolute substitution asserted
/// for a particular BMC placement.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InstantiationProvenance {
    abstract_instantiation_id: String,
    relative_substitution: Vec<(String, Term)>,
}

impl InstantiationProvenance {
    pub fn new(
        abstract_instantiation_id: String,
        relative_substitution: Vec<(String, Term)>,
    ) -> Self {
        Self {
            abstract_instantiation_id,
            relative_substitution,
        }
    }

    pub fn abstract_instantiation_id(&self) -> &str {
        &self.abstract_instantiation_id
    }

    pub fn into_parts(self) -> (String, Vec<(String, Term)>) {
        (self.abstract_instantiation_id, self.relative_substitution)
    }

    pub fn relative_substitution(&self) -> Vec<InstantiationSubstitution> {
        substitution_records(&self.relative_substitution)
    }

    pub fn at_frame(&self, bmc_builder: &mut BMCBuilder) -> Vec<InstantiationSubstitution> {
        self.relative_substitution
            .iter()
            .map(|(variable, term)| InstantiationSubstitution {
                variable: variable.clone(),
                term: term
                    .clone()
                    .accept(bmc_builder)
                    .expect("BMC substitution terms should rewrite")
                    .to_string(),
            })
            .collect()
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

/// A normalized theory instance together with its exact candidate provenance.
#[derive(Clone, Debug)]
pub struct InstantiationRequest {
    pub(crate) inst: Instance,
    pub(crate) provenance: Option<InstantiationProvenance>,
}

impl InstantiationRequest {
    pub fn untracked(inst: Instance) -> Self {
        Self {
            inst,
            provenance: None,
        }
    }

    pub fn provenanced(inst: Instance, provenance: InstantiationProvenance) -> Self {
        Self {
            inst,
            provenance: Some(provenance),
        }
    }
}

#[derive(Clone, Debug)]
pub struct StoredInstantiation {
    pub inst: Instance,
    pub provenance: Option<InstantiationProvenance>,
}

/// Observable outcome of installing one whole theory instantiation.
///
/// An abstract instance may be new while adding no solver-visible assertion
/// because every materialized placement was removed by canonical deduplication.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct InstantiationInstallResult {
    pub abstract_instance_added: bool,
    pub indexed_assertions_attempted: u64,
    pub indexed_assertions_added: u64,
    pub indexed_assertions_deduplicated: u64,
    pub helper_assertions_attempted: u64,
    pub helper_assertions_added: u64,
    pub helper_assertions_deduplicated: u64,
}

impl InstantiationInstallResult {
    pub fn solver_assertions_added(self) -> u64 {
        self.indexed_assertions_added + self.helper_assertions_added
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn provenance_rewrites_the_complete_substitution_at_the_requested_frame() {
        let mut builder = BMCBuilder::new(vec![], Default::default());
        builder.set_depth(4);
        builder.set_width(1);
        let provenance = InstantiationProvenance::new(
            "candidate-1".to_string(),
            vec![
                ("?a".to_string(), "a+0".parse().unwrap()),
                ("?i".to_string(), "i+1".parse().unwrap()),
            ],
        );

        assert_eq!(
            provenance.at_frame(&mut builder),
            vec![
                InstantiationSubstitution {
                    variable: "?a".to_string(),
                    term: "a@3".to_string(),
                },
                InstantiationSubstitution {
                    variable: "?i".to_string(),
                    term: "i@4".to_string(),
                },
            ]
        );
    }
}
