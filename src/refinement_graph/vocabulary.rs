//! Bounded, deterministic enumeration of well-typed ground terms.
//!
//! Each sweep uses a frozen term pool. Constructors take turns, one tuple at a
//! time, so a large product cannot starve another constructor. New terms enter
//! the next sweep. These are model queries and vocabulary, never assertions.
use super::*;
use crate::theories::quantifiers::term_sort;
use smt2parser::concrete::QualIdentifier;
use std::collections::BTreeMap;

// Construction must not inherit the lowerer's fallback that guesses an
// unknown operator's result from its first argument (e.g. a BV comparison).
// Skip uncertain roots; their independently typed subterms remain available.
fn construction_sort(term: &Term, signatures: &HashMap<String, (Vec<Sort>, Sort)>) -> Option<Sort> {
    use smt2parser::vmt::array_abstractor::string_to_sort;
    match term {
        Term::QualIdentifier(_) | Term::Constant(_) => {
            term_sort(term, signatures, &HashMap::new()).ok()
        }
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            let name = qual_identifier.get_name();
            if let Some((_, sort)) = signatures.get(&name) {
                return Some(sort.clone());
            }
            match name.as_str() {
                "and" | "or" | "not" | "=>" | "=" | "distinct" | "<" | "<=" | ">" | ">="
                | "xor" | "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt"
                | "bvsge" => Some(string_to_sort("Bool")),
                "to_real" => Some(string_to_sort("Real")),
                "to_int" => Some(string_to_sort("Int")),
                "+" | "-" | "*" => {
                    let sorts = arguments
                        .iter()
                        .map(|a| construction_sort(a, signatures))
                        .collect::<Option<Vec<_>>>()?;
                    let int = string_to_sort("Int");
                    let real = string_to_sort("Real");
                    if sorts.iter().all(|s| *s == int) {
                        Some(int)
                    } else if sorts.iter().all(|s| *s == int || *s == real) {
                        Some(real)
                    } else {
                        None
                    }
                }
                "ite" if arguments.len() == 3 => {
                    let yes = construction_sort(&arguments[1], signatures)?;
                    let no = construction_sort(&arguments[2], signatures)?;
                    (yes == no).then_some(yes)
                }
                _ => None,
            }
        }
        _ => None,
    }
}

#[derive(Default)]
pub(super) struct VocabularyGrowth {
    constructors: Vec<Constructor>,
    next: usize,
}

struct Constructor {
    name: String,
    arguments: Vec<Vec<Term>>,
    indices: Option<Vec<usize>>,
    integer_offset: Option<&'static str>,
}

impl Constructor {
    fn next(&mut self) -> Option<Term> {
        let indices = self.indices.as_mut()?;
        let mut arguments = indices
            .iter()
            .zip(&self.arguments)
            .map(|(i, terms)| terms[*i].clone())
            .collect::<Vec<_>>();
        if let Some(offset) = self.integer_offset {
            arguments.push(offset.parse().unwrap());
        }
        let term = Term::Application {
            qual_identifier: QualIdentifier::simple(&self.name),
            arguments,
        };
        let mut carry = true;
        for (index, choices) in indices.iter_mut().zip(&self.arguments).rev() {
            *index += 1;
            if *index < choices.len() {
                carry = false;
                break;
            }
            *index = 0;
        }
        if carry {
            self.indices = None;
        }
        Some(term)
    }
}

impl VocabularyGrowth {
    fn from_graph(graph: &RefinementGraph) -> Self {
        let mut terms: BTreeMap<String, Vec<Term>> = BTreeMap::new();
        for expression in &graph.terms {
            let term = crate::terms::language::expr_to_term(expression.clone());
            if let Some(sort) = construction_sort(&term, &graph.signatures) {
                terms.entry(sort.to_string()).or_default().push(term);
            }
        }
        // Logical constants are available even when the input has no ground
        // Boolean roots. They become graph nodes only through budgeted terms.
        terms.entry("Bool".into()).or_default().extend([
            "true".parse::<Term>().unwrap(),
            "false".parse::<Term>().unwrap(),
        ]);
        for pool in terms.values_mut() {
            pool.sort_by_key(ToString::to_string);
            pool.dedup();
        }
        let mut signatures = graph.signatures.iter().collect::<Vec<_>>();
        signatures.sort_by_key(|(name, _)| *name);
        let mut constructors = Vec::new();
        for (name, (parameters, _)) in signatures {
            if parameters.is_empty() {
                continue;
            }
            let Some(arguments) = parameters
                .iter()
                .map(|s| terms.get(&s.to_string()).cloned())
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            constructors.push(Constructor {
                name: name.clone(),
                indices: Some(vec![0; arguments.len()]),
                arguments,
                integer_offset: None,
            });
        }
        if let Some(integers) = terms.get("Int") {
            for name in ["+", "-"] {
                constructors.push(Constructor {
                    name: name.into(),
                    arguments: vec![integers.clone()],
                    indices: Some(vec![0]),
                    integer_offset: Some("1"),
                });
            }
        }
        if let Some(booleans) = terms.get("Bool") {
            constructors.push(Constructor {
                name: "not".into(),
                arguments: vec![booleans.clone()],
                indices: Some(vec![0]),
                integer_offset: None,
            });
        }
        Self {
            constructors,
            next: 0,
        }
    }

    fn next(&mut self) -> Option<Term> {
        for _ in 0..self.constructors.len() {
            let index = self.next;
            self.next = (self.next + 1) % self.constructors.len();
            if let Some(term) = self.constructors[index].next() {
                return Some(term);
            }
        }
        None
    }
}

pub(crate) struct GrowthReport {
    pub examined: usize,
    pub added: usize,
}

impl RefinementGraph {
    pub(crate) fn grow_vocabulary(
        &mut self,
        smt: &dyn ProblemContext,
        budget: usize,
    ) -> anyhow::Result<GrowthReport> {
        self.register_context(smt);
        let before = self.terms.len();
        let mut growth = self
            .growth
            .take()
            .unwrap_or_else(|| VocabularyGrowth::from_graph(self));
        let mut examined = 0;
        while examined < budget {
            let Some(term) = growth.next() else {
                // End this operation at the sweep boundary. The next call sees
                // terms admitted during this sweep or by another graph stage.
                self.growth = None;
                self.rebuild();
                return Ok(GrowthReport {
                    examined,
                    added: self.terms.len() - before,
                });
            };
            examined += 1;
            self.admit(smt, &term, true)?;
        }
        self.growth = Some(growth);
        self.rebuild();
        Ok(GrowthReport {
            examined,
            added: self.terms.len() - before,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn construction_does_not_guess_sorts_of_width_changing_operations() {
        let signatures = HashMap::new();
        assert_eq!(
            construction_sort(&"(bvult #x01 #x02)".parse().unwrap(), &signatures)
                .unwrap()
                .to_string(),
            "Bool"
        );
        assert!(
            construction_sort(&"((_ extract 3 0) #x01)".parse().unwrap(), &signatures).is_none()
        );
        assert_eq!(
            construction_sort(&"(+ 1 (to_real 2))".parse().unwrap(), &signatures)
                .unwrap()
                .to_string(),
            "Real"
        );
    }
}
