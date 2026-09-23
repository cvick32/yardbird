//! Frame-specific materialization of shared candidate provenance.
use crate::rule_matching::provenance::{InstantiationProvenance, InstantiationSubstitution};
use smt2parser::vmt::bmc::BMCBuilder;

impl InstantiationProvenance {
    pub fn at_frame(&self, bmc_builder: &mut BMCBuilder) -> Vec<InstantiationSubstitution> {
        self.relative_bindings()
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
