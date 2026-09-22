//! Bounded, model-independent selection once before the first solver check.
use std::collections::HashMap;

/// Eager seeding is opt-in. Budgets apply to the initial batch, before replay.
#[derive(Clone, Copy, Debug)]
pub struct EagerInstantiation {
    pub max_instances: usize,
    pub max_candidates: usize,
    pub diversify_ties: bool,
}

impl Default for EagerInstantiation {
    fn default() -> Self {
        Self {
            max_instances: 32,
            max_candidates: 512,
            diversify_ties: true,
        }
    }
}

/// Cost is primary. Diversity only breaks equal-cost ties; lexical order makes
/// the result independent of hash iteration and input enumeration order.
pub(crate) fn order<T>(
    mut items: Vec<(u32, String, String, T)>,
    limit: usize,
    diversify: bool,
) -> Vec<T> {
    let mut counts = HashMap::<String, usize>::new();
    let mut result = Vec::new();
    while !items.is_empty() && result.len() < limit {
        let best = (0..items.len())
            .min_by_key(|&i| {
                let (cost, family, key, _) = &items[i];
                (
                    *cost,
                    if diversify {
                        counts.get(family).copied().unwrap_or(0)
                    } else {
                        0
                    },
                    key,
                )
            })
            .unwrap();
        let (_, family, _, item) = items.swap_remove(best);
        *counts.entry(family).or_default() += 1;
        result.push(item);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn diversity_breaks_ties_without_overriding_cost_and_is_deterministic() {
        let items = vec![
            (1, "i".into(), "a".into(), "i"),
            (1, "i".into(), "b".into(), "i+1"),
            (1, "j".into(), "c".into(), "j"),
            (2, "n".into(), "d".into(), "n"),
        ];
        assert_eq!(order(items.clone(), 4, true), ["i", "j", "i+1", "n"]);
        assert_eq!(order(items.clone(), 2, false), ["i", "i+1"]);
        let mut reversed = items;
        reversed.reverse();
        assert_eq!(order(reversed, 2, true), ["i", "j"]);
    }
}
