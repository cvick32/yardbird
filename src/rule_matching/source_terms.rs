//! Immutable typed source vocabulary. Generated instances never feed this pool.
use crate::theories::quantifiers::term_sort;
use smt2parser::concrete::{Sort, Term};
use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};

#[derive(Default)]
pub(crate) struct SourceTerms {
    pub pools: HashMap<Sort, Rc<Vec<Term>>>,
    pub applications: HashMap<String, Vec<Term>>,
}
impl SourceTerms {
    pub fn new(roots: Vec<&Term>, signatures: &HashMap<String, (Vec<Sort>, Sort)>) -> Self {
        let mut seen = HashSet::new();
        let mut queue = roots;
        while let Some(term) = queue.pop() {
            if !seen.insert(term.clone()) {
                continue;
            }
            match term {
                Term::Application { arguments, .. } => queue.extend(arguments),
                Term::Attributes { term, .. } => queue.push(term),
                _ => {}
            }
        }
        // The Boolean domain needs only these two representatives.
        seen.insert("true".parse().unwrap());
        seen.insert("false".parse().unwrap());
        let mut terms = seen.into_iter().collect::<Vec<_>>();
        terms.sort_by_cached_key(ToString::to_string);
        let mut result = Self::default();
        let mut pools = HashMap::<Sort, Vec<Term>>::new();
        for term in terms {
            if let Term::Application {
                qual_identifier, ..
            } = &term
            {
                result
                    .applications
                    .entry(qual_identifier.get_name())
                    .or_default()
                    .push(term.clone());
            }
            if let Ok(sort) = term_sort(&term, signatures, &HashMap::new()) {
                if sort.to_string() == "Bool"
                    && !matches!(term.to_string().as_str(), "true" | "false")
                {
                    continue;
                }
                pools.entry(sort).or_default().push(term);
            }
        }
        result.pools = pools.into_iter().map(|(s, t)| (s, Rc::new(t))).collect();
        result
    }
}
