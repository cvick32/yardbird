//! Ground instances of already checked universal properties. Witness metadata
//! comes from Herbrandization, never from a symbol-name heuristic. Substitution
//! changes only an arbitrary witness; every state term retains its proved frame.
use super::substitute;
use crate::rule_matching::source_terms::SourceTerms;
use smt2parser::concrete::{Sort, Symbol, Term};
use std::collections::HashSet;

#[derive(Default)]
pub(crate) struct ProvedPropertyInstances {
    witnesses: Vec<(Symbol, Sort)>,
    proved: Vec<(u16, Term)>,
    installed: HashSet<Term>,
}
impl ProvedPropertyInstances {
    pub fn new(witnesses: Vec<(Symbol, Sort)>) -> Self {
        Self {
            witnesses,
            ..Default::default()
        }
    }
    /// The caller must have proved this property UNSAT under its negation, and
    /// must not generalize auxiliary property restrictions involving witnesses.
    pub fn remember(&mut self, frame: u16, property: Term) {
        if !self.witnesses.is_empty() {
            self.installed.insert(property.clone());
            self.proved.push((frame, property));
        }
    }
    pub fn instances(&mut self, source: &SourceTerms, limit: usize) -> Vec<(u16, Term)> {
        let mut result = Vec::new();
        if limit == 0 {
            return result;
        }
        // Prefer the immediately preceding proof; older proofs remain eligible.
        for (frame, property) in self.proved.iter().rev() {
            for (witness, sort) in &self.witnesses {
                let Some(indices) = source.pools.get(sort) else {
                    continue;
                };
                let framed = Symbol(format!("{}@{frame}", witness.0));
                for index in indices.iter() {
                    let term = substitute(property.clone(), vec![(framed.clone(), index.clone())]);
                    if self.installed.insert(term.clone()) {
                        result.push((*frame, term));
                        if result.len() == limit {
                            return result;
                        }
                    }
                }
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use smt2parser::vmt::array_abstractor::string_to_sort;
    use std::rc::Rc;

    #[test]
    fn substitutes_only_certified_witnesses_and_never_shifts_state_frames() {
        let int = string_to_sort("Int");
        let mut pool = ProvedPropertyInstances::new(vec![(Symbol("fresh".into()), int.clone())]);
        let mut source = SourceTerms::default();
        source.pools.insert(
            int,
            Rc::new(vec!["i@4".parse().unwrap(), "j@4".parse().unwrap()]),
        );
        source.pools.insert(
            string_to_sort("Bool"),
            Rc::new(vec!["false".parse().unwrap()]),
        );
        assert!(pool.instances(&source, 10).is_empty());
        pool.remember(
            2,
            "(and (= (Read_Int_Int a@2 fresh@2) 0) (= ordinary@2 fresh@2))"
                .parse()
                .unwrap(),
        );
        assert!(pool.instances(&source, 0).is_empty());
        let first = pool.instances(&source, 1);
        assert_eq!(first.len(), 1);
        assert_eq!(first[0].0, 2);
        assert_eq!(
            first[0].1.to_string(),
            "(and (= (Read_Int_Int a@2 i@4) 0) (= ordinary@2 i@4))"
        );
        let rest = pool.instances(&source, 10);
        assert_eq!(rest.len(), 1);
        assert!(rest[0].1.to_string().contains("a@2 j@4"));
        assert!(pool.instances(&source, 10).is_empty());
        let mut uncertified = ProvedPropertyInstances::default();
        uncertified.remember(2, "(= yardbird_herbrand_0@2 0)".parse().unwrap());
        assert!(uncertified.instances(&source, 10).is_empty());
    }
    #[test]
    fn grounded_instances_follow_the_proved_universal_at_the_original_frame() {
        let int = string_to_sort("Int");
        let mut pool = ProvedPropertyInstances::new(vec![(Symbol("fresh".into()), int.clone())]);
        pool.remember(
            2,
            "(= (Read_Int_Int a@2 fresh@2) (Read_Int_Int b@2 fresh@2))"
                .parse()
                .unwrap(),
        );
        let mut source = SourceTerms::default();
        source.pools.insert(
            int,
            Rc::new(vec!["i@4".parse().unwrap(), "(+ i@4 1)".parse().unwrap()]),
        );
        let instances = pool.instances(&source, 10);
        assert_eq!(instances.len(), 2);
        for (_, term) in instances {
            let formula = term.to_string().replace("Read_Int_Int", "select");
            let solver = z3::Solver::new();
            solver.from_string(format!(
                "(declare-const a@2 (Array Int Int))
                (declare-const b@2 (Array Int Int)) (declare-const i@4 Int)
                (assert (forall ((i Int)) (= (select a@2 i) (select b@2 i))))
                (assert (not {formula}))"
            ));
            assert_eq!(solver.check(), z3::SatResult::Unsat);
        }
    }
}
