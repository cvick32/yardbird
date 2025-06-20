use std::collections::HashMap;

use crate::concrete::{Symbol, SyntaxBuilder, Term};

#[derive(Clone)]
pub struct BMCBuilder {
    pub visitor: SyntaxBuilder,
    pub current_variables: Vec<String>,
    pub next_variables: HashMap<String, String>,
    pub depth: u16,
    pub width: u16, // Width of the current instantiation being processed
}

impl BMCBuilder {
    pub fn new(current_variables: Vec<String>, next_variables: HashMap<String, String>) -> Self {
        BMCBuilder {
            visitor: SyntaxBuilder,
            current_variables,
            next_variables,
            depth: 0,
            width: 0,
        }
    }

    pub fn set_depth(&mut self, depth: u16) {
        self.depth = depth;
    }

    pub fn set_width(&mut self, width: u16) {
        self.width = width;
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
        // Check if this is a normalized symbol with + offset (from UnquantifiedInstantiator)
        if let Some((var_name, offset_str)) = s.0.split_once('+') {
            if let Ok(normalized_offset) = offset_str.parse::<u16>() {
                // For reverse instantiation: concrete_offset = current_depth - (width - normalized_offset)
                // This ensures we work backwards from the current depth
                let concrete_offset = if self.width > 0 && normalized_offset < self.width {
                    self.depth - (self.width - 1 - normalized_offset)
                } else if normalized_offset <= self.depth {
                    // Fallback: if width is not set, use simple subtraction
                    self.depth - normalized_offset
                } else {
                    // If normalized_offset > current_depth, we can't instantiate at this depth
                    // This should be handled by the calling code, but we'll use 0 as fallback
                    0
                };
                return Ok(Symbol(format!("{}@{}", var_name, concrete_offset)));
            }
        }
        
        // Original logic for @ notation
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
