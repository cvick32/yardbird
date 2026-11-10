//! Optional source-order decomposition of a conjunctive bounded property.
//! Never split disjunctions or move conjuncts across guards or binders.
use smt2parser::concrete::Term;

pub(crate) fn parts(property: &Term, split: bool) -> Vec<Term> {
    if split {
        if let Term::Application {
            qual_identifier,
            arguments,
        } = property
        {
            if qual_identifier.get_name() == "and" && !arguments.is_empty() {
                return arguments
                    .iter()
                    .flat_map(|part| parts(part, true))
                    .collect();
            }
        }
    }
    vec![property.clone()]
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn only_positive_top_level_conjunctions_are_partitioned() {
        let property = "(and a (and b c))".parse().unwrap();
        assert_eq!(
            parts(&property, true)
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>(),
            ["a", "b", "c"]
        );
        assert_eq!(parts(&property, false), vec![property]);
        let empty = Term::Application {
            qual_identifier: smt2parser::concrete::QualIdentifier::simple("and"),
            arguments: vec![],
        };
        assert_eq!(parts(&empty, true), vec![empty]);
        for text in ["(or a b)", "(=> a (and b c))", "(not (and a b))"] {
            let property = text.parse().unwrap();
            assert_eq!(parts(&property, true), vec![property]);
        }
    }
}
