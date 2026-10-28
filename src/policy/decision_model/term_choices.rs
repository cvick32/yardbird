//! Deterministic balanced term groups for the provider's 255-option limit.
//! Group and within-group probabilities form a path product. Each retained
//! group is an independent question, never a Cartesian binding combination.
use serde_json::{json, Value};

use super::ranked_bindings::{top_bindings, RankedBindings};

pub(super) const MAX_CHOICES: usize = 255;

struct Branch {
    ids: Vec<String>,
    log_score: f64,
    matches_model_choice: bool,
}

pub(super) struct TermChoiceSearch {
    original: Value,
    name: String,
    frontier: Vec<Branch>,
    completed: Vec<RankedBindings>,
    beam_width: usize,
    keep: usize,
}

/// Numeric stable IDs, balanced contiguous partitions. Recurse only if a group
/// itself exceeds the cap (also handles domains larger than 255 squared).
fn groups(ids: &[String]) -> Vec<Vec<String>> {
    let count = ids.len().div_ceil(MAX_CHOICES).min(MAX_CHOICES);
    let base = ids.len() / count;
    let extra = ids.len() % count;
    let mut start = 0;
    (0..count)
        .map(|i| {
            let end = start + base + usize::from(i < extra);
            let group = ids[start..end].to_vec();
            start = end;
            group
        })
        .collect()
}

impl TermChoiceSearch {
    pub fn new(original: &Value, beam_width: usize, keep: usize) -> anyhow::Result<Self> {
        let questions = original["questions"]
            .as_object()
            .ok_or_else(|| anyhow::anyhow!("missing binding questions"))?;
        anyhow::ensure!(
            questions.len() == 1 && beam_width > 0 && keep > 0,
            "term choice search needs one question and positive limits"
        );
        let (name, question) = questions.iter().next().unwrap();
        let criteria = question["criteria"]
            .as_object()
            .ok_or_else(|| anyhow::anyhow!("missing term criteria"))?;
        anyhow::ensure!(!criteria.is_empty(), "empty term domain");
        let mut ids = criteria.keys().cloned().collect::<Vec<_>>();
        ids.sort_by_key(|id| {
            (
                id.strip_prefix('t')
                    .and_then(|n| n.parse::<u64>().ok())
                    .unwrap_or(u64::MAX),
                id.clone(),
            )
        });
        Ok(Self {
            original: original.clone(),
            name: name.clone(),
            frontier: vec![Branch {
                ids,
                log_score: 0.0,
                matches_model_choice: true,
            }],
            completed: Vec::new(),
            beam_width,
            keep,
        })
    }

    pub fn stage(&self) -> &'static str {
        if self.frontier.iter().any(|b| b.ids.len() > MAX_CHOICES) {
            "conditional_binding_group"
        } else {
            "conditional_binding"
        }
    }

    fn question_name(&self, index: usize) -> String {
        if self.frontier.len() == 1 {
            self.name.clone()
        } else {
            format!("{}_group{index}", self.name)
        }
    }

    pub fn request(&self) -> Value {
        let mut request = self.original.clone();
        let mut questions = serde_json::Map::new();
        for (index, branch) in self.frontier.iter().enumerate() {
            let mut question = self.original["questions"][&self.name].clone();
            if branch.ids.len() > MAX_CHOICES {
                question["criteria"] = json!(groups(&branch.ids)
                    .into_iter()
                    .enumerate()
                    .map(|(i, ids)| (format!("g{i}"), json!({"term_ids": ids})))
                    .collect::<serde_json::Map<_, _>>());
                question["instructions"] = json!(format!(
                    "Select the GROUP containing the best term for the binding task below. Groups are arbitrary balanced partitions of stable numeric term IDs, with no semantic meaning. Look up every group's term_ids in the full state.terms catalogue. Return a group ID; a subsequent question will select a term inside a retained group. Preserve state.fixed_bindings. Binding task: {}",
                    question["instructions"].as_str().unwrap_or_default()));
            } else {
                question["criteria"] = json!(branch
                    .ids
                    .iter()
                    .map(|id| (
                        id.clone(),
                        self.original["questions"][&self.name]["criteria"][id].clone()
                    ))
                    .collect::<serde_json::Map<_, _>>());
            }
            questions.insert(self.question_name(index), question);
        }
        request["questions"] = json!(questions);
        request
    }

    pub fn advance(&mut self, response: &Value) -> anyhow::Result<()> {
        let request = self.request();
        let mut frontier = Vec::new();
        let mut completed = Vec::new();
        for (index, branch) in self.frontier.iter().enumerate() {
            let name = self.question_name(index);
            let partition = (branch.ids.len() > MAX_CHOICES).then(|| groups(&branch.ids));
            let keep = if partition.is_some() {
                self.beam_width
            } else {
                self.keep
            };
            // Each question ranks alternatives for the SAME slot. Do not use
            // top_bindings on the batch: that would form a Cartesian product.
            let ranked = top_bindings(
                &json!({"questions":{&name:&request["questions"][&name]}}),
                &json!({"answers":{&name:&response["answers"][&name]}}),
                keep.max(2),
            )?;
            for candidate in ranked.into_iter().take(keep) {
                let p = candidate
                    .probability_product
                    .expect("validated probabilities");
                if p == 0.0 {
                    continue;
                }
                let log_score = branch.log_score + p.ln();
                let matches_model_choice =
                    branch.matches_model_choice && candidate.matches_model_choice;
                let id = candidate.response["answers"][&name]["choice"]
                    .as_str()
                    .unwrap();
                if let Some(partition) = &partition {
                    let index: usize = id.strip_prefix('g').unwrap().parse()?;
                    frontier.push(Branch {
                        ids: partition[index].clone(),
                        log_score,
                        matches_model_choice,
                    });
                } else {
                    completed.push(RankedBindings {
                        response: json!({"answers":{&self.name:{"type":"choice","choice":id}}}),
                        probability_product: Some(log_score.exp()),
                        matches_model_choice,
                    });
                }
            }
        }
        frontier.sort_by(|a, b| {
            b.log_score
                .total_cmp(&a.log_score)
                .then_with(|| a.ids.cmp(&b.ids))
        });
        frontier.truncate(self.beam_width);
        self.frontier = frontier;
        self.completed.extend(completed);
        self.completed.sort_by(|a, b| {
            b.probability_product
                .unwrap()
                .total_cmp(&a.probability_product.unwrap())
                .then_with(|| a.response.to_string().cmp(&b.response.to_string()))
        });
        self.completed.truncate(self.keep);
        Ok(())
    }

    pub fn is_complete(&self) -> bool {
        self.frontier.is_empty()
    }
    pub fn results(self) -> Vec<RankedBindings> {
        self.completed
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn partition_boundaries_preserve_every_id_and_recurse_beyond_255_squared() {
        for n in [256, 273, 510, 511, 65025, 65026] {
            let ids = (0..n).map(|i| format!("t{i}")).collect::<Vec<_>>();
            let partitions = groups(&ids);
            assert!(partitions.len() <= MAX_CHOICES);
            assert_eq!(partitions.concat(), ids);
            let min = partitions.iter().map(Vec::len).min().unwrap();
            let max = partitions.iter().map(Vec::len).max().unwrap();
            assert!(max - min <= 1);
            assert!(max < n);
        }
    }

    #[test]
    fn small_domains_are_unchanged_and_malformed_answers_do_not_advance() {
        for n in [1, 255, 256] {
            let criteria = (0..n)
                .map(|i| (format!("t{i}"), Value::Null))
                .collect::<serde_json::Map<_, _>>();
            let request = json!({"state":{"terms":"complete"}, "questions":{"idx":{"type":"choice","criteria":criteria}}});
            let mut search = TermChoiceSearch::new(&request, 3, 10).unwrap();
            let before = search.request();
            if n <= 255 {
                assert_eq!(before, request);
            }
            assert!(search.advance(&json!({"answers":{}})).is_err());
            assert_eq!(search.request(), before);
            assert!(!search.is_complete());
        }
    }
}
