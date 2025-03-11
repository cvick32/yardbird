use std::collections::HashMap;

use crate::concrete::{Symbol, SyntaxBuilder, Term};

#[derive(Clone)]
pub struct BMCBuilder {
    pub visitor: SyntaxBuilder,
    pub current_variables: Vec<String>,
    pub next_variables: HashMap<String, String>,
    pub depth: u16,
}

impl BMCBuilder {
    pub fn new(current_variables: Vec<String>, next_variables: HashMap<String, String>) -> Self {
        BMCBuilder {
            visitor: SyntaxBuilder,
            current_variables,
            next_variables,
            depth: 0,
        }
    }

    pub fn set_depth(&mut self, depth: u16) {
        self.depth = depth;
    }

    pub fn add_step(&mut self) {
        self.depth += 1;
    }

    /// Have to set the depth to minus 1 so that we get the transition from 0->1 for depth 1.
    pub fn index_transition_term(&mut self, trans_term: Term) -> Term {
        self.set_depth(self.depth - 1);
        let indexed_term = trans_term.accept(self).unwrap();
        self.set_depth(self.depth);
        indexed_term
    }

    pub fn index_single_step_term(&mut self, term: Term) -> Term {
        term.accept(self).unwrap()
    }
}

impl crate::rewriter::Rewriter for BMCBuilder {
    type V = SyntaxBuilder;
    type Error = crate::concrete::Error;

    fn visitor(&mut self) -> &mut Self::V {
        &mut self.visitor
    }

    fn process_symbol(&mut self, s: Symbol) -> Result<Symbol, Self::Error> {
        if self.current_variables.contains(&s.0) {
            Ok(Symbol(format!("{}@{}", s.0, &self.depth)))
        } else if self.next_variables.contains_key(&s.0) {
            let next = self.depth + 1;
            let current_variable_name = self.next_variables.get(&s.0).unwrap();
            Ok(Symbol(format!(
                "{}@{}",
                current_variable_name,
                &next.to_string()
            )))
        } else {
            Ok(s)
        }
    }
}
