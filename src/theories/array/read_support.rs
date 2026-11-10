//! Ground read/write support at source indices. These are the same built-in
//! axioms as ordinary array search; model equalities never enter the formulas.
use super::rule::ArrayAxiomKind;
use crate::rule_matching::{
    candidate::SymbolicInstance, rule::QuantifiedRule, source_terms::SourceTerms,
};
use smt2parser::concrete::{QualIdentifier, Term};
use std::{
    collections::{HashMap, HashSet, VecDeque},
    rc::Rc,
};
fn app(name: &str, arguments: Vec<Term>) -> Term {
    Term::Application {
        qual_identifier: QualIdentifier::simple(name),
        arguments,
    }
}
struct Cursor {
    index_sort: String,
    value_sort: String,
    array: Term,
    indices: Rc<Vec<Term>>,
    next: usize,
    constant: bool,
}
#[derive(Default)]
pub(crate) struct ArrayReadSupport {
    jobs: VecDeque<Cursor>,
    constructors: HashMap<String, ConstructorSupport>,
    seen: HashSet<Term>,
}
impl ArrayReadSupport {
    pub fn new(types: &[(String, String)], source: &SourceTerms) -> Self {
        let mut result = Self::default();
        for (is, vs) in types {
            let sort = smt2parser::vmt::array_abstractor::string_to_sort(is);
            let indices = source.pools.get(&sort).cloned().unwrap_or_default();
            for (prefix, constant) in [("Write", false), ("ConstArr", true)] {
                result.constructors.insert(
                    format!("{prefix}_{is}_{vs}"),
                    (is.clone(), vs.clone(), indices.clone(), constant),
                );
            }
        }
        // Type and constructor order is deterministic even though the source
        // index uses hash tables for lookups.
        for (is, vs) in types {
            for prefix in ["Write", "ConstArr"] {
                for term in source
                    .applications
                    .get(&format!("{prefix}_{is}_{vs}"))
                    .into_iter()
                    .flatten()
                {
                    result.remember(term);
                }
            }
        }
        result
    }
    /// Ground QIs can expose stores absent from the original ground formula.
    /// Admit those constructors, including from satisfied QIs, but never add
    /// generated reads to the frozen index pool.
    pub fn remember(&mut self, term: &Term) {
        if let Term::Attributes { term, .. } = term {
            self.remember(term);
            return;
        }
        if let Term::Application {
            qual_identifier,
            arguments,
        } = term
        {
            if let Some((is, vs, indices, constant)) =
                self.constructors.get(&qual_identifier.get_name())
            {
                if self.seen.insert(term.clone()) && (!constant || !indices.is_empty()) {
                    self.jobs.push_back(Cursor {
                        index_sort: is.clone(),
                        value_sort: vs.clone(),
                        array: term.clone(),
                        indices: indices.clone(),
                        next: 0,
                        constant: *constant,
                    });
                }
            }
            for argument in arguments {
                self.remember(argument);
            }
        }
    }
    pub fn pending(&self) -> bool {
        !self.jobs.is_empty()
    }
    pub fn next(&mut self) -> Option<SymbolicInstance> {
        let job = loop {
            let job = self.jobs.pop_front()?;
            // The constructor's own index already has its read-after-write
            // equation. Do not emit the equivalent ITE equation a second time.
            if !job.constant && job.next > 0 {
                let Term::Application { arguments, .. } = &job.array else {
                    unreachable!()
                };
                if job.indices[job.next - 1] == arguments[1] {
                    self.advance(job);
                    continue;
                }
            }
            break job;
        };
        let Term::Application { arguments, .. } = &job.array else {
            unreachable!()
        };
        let read = format!("Read_{}_{}", job.index_sort, job.value_sort);
        let (kind, term, bindings) = if job.constant {
            let index = job.indices[job.next].clone();
            (
                ArrayAxiomKind::ConstantArray,
                app(
                    "=",
                    vec![
                        app(&read, vec![job.array.clone(), index.clone()]),
                        arguments[0].clone(),
                    ],
                ),
                vec![("?a".into(), arguments[0].clone()), ("?b".into(), index)],
            )
        } else if job.next == 0 {
            (
                ArrayAxiomKind::ReadAfterWrite,
                app(
                    "=",
                    vec![
                        app(&read, vec![job.array.clone(), arguments[1].clone()]),
                        arguments[2].clone(),
                    ],
                ),
                vec![
                    ("?a".into(), arguments[0].clone()),
                    ("?idx".into(), arguments[1].clone()),
                    ("?val".into(), arguments[2].clone()),
                ],
            )
        } else {
            let index = job.indices[job.next - 1].clone();
            (
                ArrayAxiomKind::ReadOverWrite,
                app(
                    "=",
                    vec![
                        app(&read, vec![job.array.clone(), index.clone()]),
                        app(
                            "ite",
                            vec![
                                app("=", vec![arguments[1].clone(), index.clone()]),
                                arguments[2].clone(),
                                app(&read, vec![arguments[0].clone(), index.clone()]),
                            ],
                        ),
                    ],
                ),
                vec![
                    ("?a".into(), arguments[0].clone()),
                    ("?idx".into(), arguments[1].clone()),
                    ("?val".into(), arguments[2].clone()),
                    ("?c".into(), index),
                ],
            )
        };
        let rule = QuantifiedRule::array_axiom(kind, &job.index_sort, &job.value_sort);
        self.advance(job);
        Some(SymbolicInstance {
            rule,
            term,
            bindings,
        })
    }

    fn advance(&mut self, mut job: Cursor) {
        job.next += 1;
        if job.next < job.indices.len() + usize::from(!job.constant) {
            self.jobs.push_back(job);
        }
    }
}

type ConstructorSupport = (String, String, Rc<Vec<Term>>, bool);

#[cfg(test)]
mod tests {
    use super::*;
    use smt2parser::vmt::array_abstractor::string_to_sort;
    #[test]
    fn attributed_quantifier_bodies_expose_the_same_stores_once() {
        let mut source = SourceTerms::default();
        source
            .pools
            .insert(string_to_sort("Int"), Rc::new(vec!["7".parse().unwrap()]));
        let mut support = ArrayReadSupport::new(&[("Int".into(), "Int".into())], &source);
        support.remember(
            &"(! (= a (Write_Int_Int b 5 9)) :named body)"
                .parse()
                .unwrap(),
        );
        support.remember(&"(= a (Write_Int_Int b 5 9))".parse().unwrap());
        let first = support.next().unwrap();
        let second = support.next().unwrap();
        assert!(first
            .term
            .to_string()
            .contains("(Read_Int_Int (Write_Int_Int b 5 9) 5)"));
        assert!(second
            .term
            .to_string()
            .contains("(ite (= 5 7) 9 (Read_Int_Int b 7))"));
        assert!(support.next().is_none());
    }

    #[test]
    fn qi_stores_gain_support_without_growing_the_index_pool() {
        let mut source = SourceTerms::default();
        source
            .pools
            .insert(string_to_sort("Int"), Rc::new(vec!["5".parse().unwrap()]));
        let mut support = ArrayReadSupport::new(&[("Int".into(), "Int".into())], &source);
        let qi = "(=> q (= (Read_Int_Int a 5) (Read_Int_Int (Write_Int_Int b 5 9) 5)))"
            .parse()
            .unwrap();
        support.remember(&qi);
        support.remember(&qi);
        let mut instances = Vec::new();
        while let Some(instance) = support.next() {
            instances.push(instance);
            assert!(instances.len() < 5);
        }
        assert_eq!(instances.len(), 1); // Own-index ITE duplicates are omitted.
        assert!(instances
            .iter()
            .any(|i| i.term.to_string() == "(= (Read_Int_Int (Write_Int_Int b 5 9) 5) 9)"));
        assert!(instances
            .iter()
            .all(|i| !i.term.to_string().contains("(Read_Int_Int b (Read_")));
    }

    #[test]
    fn complete_reads_are_valid_for_aliasing_indices_and_nested_writes() {
        for (is, vs) in [("Int", "Int"), ("Bool", "Int"), ("Int", "Bool")] {
            let mut source = SourceTerms::default();
            source.pools.insert(
                string_to_sort(is),
                Rc::new(vec!["i".parse().unwrap(), "j".parse().unwrap()]),
            );
            let mut support = ArrayReadSupport::new(&[(is.into(), vs.into())], &source);
            support.remember(
                &format!("(Write_{is}_{vs} (Write_{is}_{vs} a i v) j w)")
                    .parse()
                    .unwrap(),
            );
            let mut count = 0;
            let mut complete = 0;
            while let Some(instance) = support.next() {
                count += 1;
                assert!(count <= 4, "own-index equations must not be duplicated");
                complete += usize::from(
                    instance.rule.kind()
                        == crate::rule_matching::rule::QuantifiedRuleKind::ArrayAxiom(
                            ArrayAxiomKind::ReadOverWrite,
                        ),
                );
                // Independent semantic oracle; production keeps both theories
                // abstract. Unconstrained i/j exercise equal and unequal cases.
                let formula = instance
                    .term
                    .to_string()
                    .replace(&format!("Read_{is}_{vs}"), "select")
                    .replace(&format!("Write_{is}_{vs}"), "store");
                let solver = z3::Solver::new();
                solver.from_string(format!("(declare-const a (Array {is} {vs})) (declare-const i {is}) (declare-const j {is}) (declare-const v {vs}) (declare-const w {vs}) (assert (not {formula}))"));
                assert_eq!(solver.check(), z3::SatResult::Unsat, "{formula}");
            }
            assert_eq!((count, complete), (4, 2));
        }
    }
}
