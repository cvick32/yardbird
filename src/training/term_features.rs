//! Feature extraction from ArrayExpr terms.
//!
//! These features are used for training models to predict good instantiation terms.

use rustc_hash::FxHashSet;
use smt2parser::vmt::VARIABLE_FRAME_DELIMITER;

use crate::theories::array::array_axioms::{ArrayExpr, ArrayLanguage};

/// Features extracted from a term for training.
#[derive(Debug, Clone, Default)]
pub struct TermFeatures {
    /// Whether the term is a constant (no frame indices)
    pub is_constant: bool,
    /// Whether the term is a simple variable (single symbol)
    pub is_variable: bool,
    /// Whether the term appears in property vocabulary
    pub in_property_vocab: bool,
    /// Whether the term appears in transition/init vocabulary
    pub in_transition_vocab: bool,
    /// Frame index if term is a state variable (None for constants)
    pub frame_index: Option<i32>,
    /// AST size (number of nodes)
    pub ast_size: i32,
}

impl TermFeatures {
    /// Extract features from an ArrayExpr.
    ///
    /// # Arguments
    /// * `expr` - The expression to extract features from
    /// * `property_terms` - Set of term strings that appear in the property
    /// * `transition_terms` - Set of term strings that appear in init/transition
    pub fn extract(
        expr: &ArrayExpr,
        property_terms: &FxHashSet<String>,
        transition_terms: &FxHashSet<String>,
    ) -> Self {
        let expr_str = expr.to_string();
        let ast_size = expr.as_ref().len() as i32;

        // Check if it's a single symbol (variable)
        let is_variable = expr.as_ref().len() == 1
            && matches!(
                &expr.as_ref()[0],
                ArrayLanguage::Symbol(_) | ArrayLanguage::Num(_)
            );

        // Check if constant (no frame delimiter in any node)
        let is_constant = !Self::contains_frame_index(expr);

        // Extract frame index from the root or first variable found
        let frame_index = Self::extract_frame_index(expr);

        // Check vocabulary membership
        let in_property_vocab = property_terms.contains(&expr_str);
        let in_transition_vocab = transition_terms.contains(&expr_str);

        TermFeatures {
            is_constant,
            is_variable,
            in_property_vocab,
            in_transition_vocab,
            frame_index,
            ast_size,
        }
    }

    /// Check if the expression contains any frame-indexed variables
    fn contains_frame_index(expr: &ArrayExpr) -> bool {
        for node in expr.as_ref() {
            if let ArrayLanguage::Symbol(sym) = node {
                if sym.as_str().contains(VARIABLE_FRAME_DELIMITER) {
                    return true;
                }
            }
        }
        false
    }

    /// Extract the frame index from the expression (first one found)
    fn extract_frame_index(expr: &ArrayExpr) -> Option<i32> {
        for node in expr.as_ref() {
            if let ArrayLanguage::Symbol(sym) = node {
                if let Some((_, frame_str)) = sym.as_str().split_once(VARIABLE_FRAME_DELIMITER) {
                    if let Ok(frame) = frame_str.parse::<i32>() {
                        return Some(frame);
                    }
                }
            }
        }
        None
    }

    /// Compute cost from a YardbirdCostFunction for this expression.
    ///
    /// This is a separate method because it requires the cost function.
    pub fn compute_cost<CF>(expr: &ArrayExpr, cost_fn: &mut CF) -> i32
    where
        CF: egg::CostFunction<ArrayLanguage, Cost = u32>,
    {
        cost_fn.cost_rec(expr) as i32
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_variable() {
        let expr: ArrayExpr = "x".parse().unwrap();
        let features = TermFeatures::extract(&expr, &FxHashSet::default(), &FxHashSet::default());

        assert!(features.is_variable);
        assert!(features.is_constant);
        assert_eq!(features.ast_size, 1);
        assert_eq!(features.frame_index, None);
    }

    #[test]
    fn test_framed_variable() {
        let expr: ArrayExpr = "x@0".parse().unwrap();
        let features = TermFeatures::extract(&expr, &FxHashSet::default(), &FxHashSet::default());

        assert!(features.is_variable);
        assert!(!features.is_constant);
        assert_eq!(features.frame_index, Some(0));
    }

    #[test]
    fn test_complex_expression() {
        let expr: ArrayExpr = "(Read Int Int A 0)".parse().unwrap();
        let features = TermFeatures::extract(&expr, &FxHashSet::default(), &FxHashSet::default());

        assert!(!features.is_variable);
        assert!(features.is_constant);
        assert!(features.ast_size > 1);
    }

    #[test]
    fn test_vocabulary_membership() {
        let expr: ArrayExpr = "x".parse().unwrap();
        let mut property_terms = FxHashSet::default();
        property_terms.insert("x".to_string());

        let features = TermFeatures::extract(&expr, &property_terms, &FxHashSet::default());

        assert!(features.in_property_vocab);
        assert!(!features.in_transition_vocab);
    }
}
