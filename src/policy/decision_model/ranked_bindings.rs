//! Lazy k-best Cartesian-product enumeration of per-binding distributions.
use std::{
    cmp::Ordering,
    collections::{BinaryHeap, HashSet},
};

use serde_json::{json, Value};

pub(super) struct RankedBindings {
    pub response: Value,
    pub probability_product: Option<f64>,
    pub matches_model_choice: bool,
}

impl RankedBindings {
    pub fn chosen(response: &Value) -> Self {
        Self {
            response: json!({"answers":response["answers"]}),
            probability_product: None,
            matches_model_choice: true,
        }
    }
}

#[derive(Clone)]
struct Entry {
    log_score: f64,
    indices: Vec<usize>,
}

impl PartialEq for Entry {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}
impl Eq for Entry {}
impl PartialOrd for Entry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Entry {
    fn cmp(&self, other: &Self) -> Ordering {
        self.log_score
            .total_cmp(&other.log_score)
            .then_with(|| other.indices.cmp(&self.indices))
    }
}

pub(super) fn top_bindings(
    request: &Value,
    response: &Value,
    limit: usize,
) -> anyhow::Result<Vec<RankedBindings>> {
    anyhow::ensure!(limit > 0, "candidate limit must be positive");
    // Preserve the original choice-only experiment as an explicit baseline.
    if limit == 1 {
        return Ok(vec![RankedBindings::chosen(response)]);
    }
    let questions = request["questions"]
        .as_object()
        .ok_or_else(|| anyhow::anyhow!("missing binding questions"))?;
    anyhow::ensure!(!questions.is_empty(), "no binding questions");
    let mut names = Vec::new();
    let mut domains = Vec::new();
    for (name, question) in questions {
        let criteria = question["criteria"]
            .as_object()
            .ok_or_else(|| anyhow::anyhow!("missing criteria for {name}"))?;
        let answer = &response["answers"][name];
        anyhow::ensure!(answer["type"] == "choice", "non-choice answer for {name}");
        let probabilities = answer["probabilities"]
            .as_object()
            .ok_or_else(|| anyhow::anyhow!("missing probabilities for {name}"))?;
        anyhow::ensure!(
            probabilities.len() == criteria.len() && !criteria.is_empty(),
            "incomplete probability table for {name}"
        );
        let mut domain = Vec::new();
        for (id, value) in probabilities {
            anyhow::ensure!(
                criteria.contains_key(id),
                "unoffered probability option {id} for {name}"
            );
            let p = value
                .as_f64()
                .filter(|p| p.is_finite() && (0.0..=1.0).contains(p))
                .ok_or_else(|| anyhow::anyhow!("invalid probability for {name}/{id}"))?;
            domain.push((id.clone(), p));
        }
        anyhow::ensure!(
            domain.iter().any(|(_, p)| *p > 0.0),
            "all probabilities are zero for {name}"
        );
        domain.sort_by(|a, b| b.1.total_cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
        names.push(name);
        domains.push(domain);
    }
    let score = |indices: &[usize]| {
        indices
            .iter()
            .enumerate()
            .map(|(i, j)| domains[i][*j].1.ln())
            .sum()
    };
    let indices = vec![0; domains.len()];
    let mut heap = BinaryHeap::from([Entry {
        log_score: score(&indices),
        indices: indices.clone(),
    }]);
    let mut seen = HashSet::from([indices]);
    let mut result = Vec::new();
    while result.len() < limit {
        let Some(entry) = heap.pop() else {
            break;
        };
        let mut answers = serde_json::Map::new();
        let mut matches_model_choice = true;
        for (i, name) in names.iter().enumerate() {
            let id = &domains[i][entry.indices[i]].0;
            matches_model_choice &=
                response["answers"][*name]["choice"].as_str() == Some(id.as_str());
            answers.insert((*name).clone(), json!({"type":"choice","choice":id}));
        }
        result.push(RankedBindings {
            response: json!({"answers":answers}),
            probability_product: Some(entry.log_score.exp()),
            matches_model_choice,
        });
        for i in 0..domains.len() {
            let mut next = entry.indices.clone();
            next[i] += 1;
            if next[i] < domains[i].len() && seen.insert(next.clone()) {
                heap.push(Entry {
                    log_score: score(&next),
                    indices: next,
                });
            }
        }
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> (Value, Value) {
        let mut questions = serde_json::Map::new();
        let mut answers = serde_json::Map::new();
        for (name, p, sub) in [("a", 0.17, 0.09), ("b", 0.14, 0.08), ("c", 0.10, 0.09)] {
            questions.insert(
                name.into(),
                json!({"criteria":{"first":null,"sub":null,"zero":null}}),
            );
            answers.insert(name.into(), json!({"type":"choice","choice":"first","probabilities":{"first":p,"sub":sub,"zero":0.0}}));
        }
        (json!({"questions":questions}), json!({"answers":answers}))
    }

    #[test]
    fn heap_matches_exhaustive_product_order_without_duplicates() {
        let (request, response) = fixture();
        let ranked = top_bindings(&request, &response, 100).unwrap();
        assert_eq!(ranked.len(), 27);
        assert_eq!(ranked[1].response["answers"]["c"]["choice"], "sub");
        assert_eq!(ranked[1].response["answers"]["a"]["choice"], "first");
        assert_eq!(ranked[1].response["answers"]["b"]["choice"], "first");
        assert!(ranked[0].matches_model_choice);
        assert!(!ranked[1].matches_model_choice);
        let mut brute = Vec::new();
        for a in [0.17, 0.09, 0.0] {
            for b in [0.14, 0.08, 0.0] {
                for c in [0.10, 0.09, 0.0] {
                    brute.push(a * b * c);
                }
            }
        }
        brute.sort_by(|a: &f64, b| b.total_cmp(a));
        for (candidate, expected) in ranked.iter().zip(brute) {
            assert!((candidate.probability_product.unwrap() - expected).abs() < 1e-15);
        }
        assert_eq!(
            ranked
                .iter()
                .map(|r| r.response.to_string())
                .collect::<HashSet<_>>()
                .len(),
            27
        );
        let limited = top_bindings(&request, &response, 10).unwrap();
        assert_eq!(limited.len(), 10);
        for (a, b) in limited.iter().zip(&ranked) {
            assert_eq!(a.response, b.response);
        }
    }

    #[test]
    fn malformed_distributions_are_rejected_and_choice_only_needs_no_probabilities() {
        let (request, response) = fixture();
        for probabilities in [
            Value::Null,
            json!({"first":0.8}),
            json!({"first":0.8,"sub":-0.1,"zero":0.0}),
            json!({"first":0.8,"sub":0.2,"unknown":0.0}),
        ] {
            let mut bad = response.clone();
            bad["answers"]["a"]["probabilities"] = probabilities;
            assert!(top_bindings(&request, &bad, 10).is_err());
            let single = top_bindings(&request, &bad, 1).unwrap();
            assert_eq!(single.len(), 1);
            assert!(single[0].matches_model_choice);
        }
    }
}
