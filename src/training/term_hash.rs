//! Canonical term hashing for matching terms to unsat core.
//!
//! The hash must be canonical so that the same term produces the same hash
//! whether seen during decision making or when parsing the unsat core.

use rustc_hash::FxHasher;
use std::hash::{Hash, Hasher};

use crate::theories::array::array_axioms::ArrayExpr;

/// Compute a canonical hash for an ArrayExpr.
///
/// This uses the string representation of the expression and FxHash for speed.
/// The hash is consistent across runs for the same term.
pub fn canonical_term_hash(expr: &ArrayExpr) -> String {
    let term_str = expr.to_string();
    let mut hasher = FxHasher::default();
    term_str.hash(&mut hasher);
    let hash = hasher.finish();
    format!("{:016x}", hash)
}

/// Compute a canonical hash from a term string directly.
pub fn canonical_term_hash_from_string(term_str: &str) -> String {
    let mut hasher = FxHasher::default();
    term_str.hash(&mut hasher);
    let hash = hasher.finish();
    format!("{:016x}", hash)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hash_consistency() {
        let expr1: ArrayExpr = "(Read Int Int A 0)".parse().unwrap();
        let expr2: ArrayExpr = "(Read Int Int A 0)".parse().unwrap();

        assert_eq!(canonical_term_hash(&expr1), canonical_term_hash(&expr2));
    }

    #[test]
    fn test_hash_different_terms() {
        let expr1: ArrayExpr = "(Read Int Int A 0)".parse().unwrap();
        let expr2: ArrayExpr = "(Read Int Int A 1)".parse().unwrap();

        assert_ne!(canonical_term_hash(&expr1), canonical_term_hash(&expr2));
    }

    #[test]
    fn test_hash_from_string() {
        let term_str = "(Read Int Int A 0)";
        let expr: ArrayExpr = term_str.parse().unwrap();

        // String-based hash should match expr-based hash
        assert_eq!(
            canonical_term_hash_from_string(&expr.to_string()),
            canonical_term_hash(&expr)
        );
    }
}
