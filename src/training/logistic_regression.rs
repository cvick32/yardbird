//! Lightweight logistic-regression inference for array term candidates.
//!
//! This evaluates the JSON model emitted by `tools/ml_ranker/train_ranker.py`.
//! The model is deliberately simple: normalized numeric features, explicit
//! one-hot categorical features, and one linear dot product.

use std::{collections::HashSet, fs, path::Path};

use serde::Deserialize;

const EXPECTED_NUMERIC_FEATURES: &[&str] = &[
    "is_constant",
    "is_variable",
    "in_property_vocab",
    "in_transition_vocab",
    "has_frame_index",
    "frame_index_clipped",
    "ast_size",
    "log_ast_size",
    "current_cost",
    "log_current_cost",
    "bmc_depth",
    "slot_index",
    "cost_rank",
    "cost_rank_frac",
    "candidate_count",
    "log_candidate_count",
];

const FRAME_SENTINEL: i32 = -999;

#[derive(Clone, Debug, Deserialize)]
pub struct LogisticRegressionModel {
    #[allow(dead_code)]
    model_type: String,
    #[allow(dead_code)]
    label: String,
    feature_spec: FeatureSpec,
    weights: Vec<f64>,
}

#[derive(Clone, Debug, Deserialize)]
struct FeatureSpec {
    numeric_features: Vec<String>,
    numeric_mean: Vec<f64>,
    numeric_std: Vec<f64>,
    hash_dim: Option<usize>,
    #[serde(default)]
    hashed_categorical_features: Vec<String>,
    #[allow(dead_code)]
    #[serde(default)]
    categorical_feature_templates: Vec<String>,
    #[serde(default)]
    categorical_vocab: Vec<String>,
    unknown_categorical_policy: Option<String>,
}

#[derive(Clone, Debug)]
pub struct LogisticRegressionCandidateFeatures<'a> {
    pub axiom_name: &'a str,
    pub slot_index: u32,
    pub is_constant: bool,
    pub is_variable: bool,
    pub in_property_vocab: bool,
    pub in_transition_vocab: bool,
    pub frame_index: Option<i32>,
    pub ast_size: i32,
    pub current_cost: i32,
    pub bmc_depth: u16,
    pub cost_rank: usize,
    pub cost_rank_frac: f64,
    pub candidate_count: usize,
}

impl LogisticRegressionModel {
    pub fn from_path(path: impl AsRef<Path>) -> anyhow::Result<Self> {
        let text = fs::read_to_string(path.as_ref())?;
        let model: Self = serde_json::from_str(&text)?;
        model.validate()?;
        Ok(model)
    }

    fn validate(&self) -> anyhow::Result<()> {
        if self.model_type != "weighted_logistic_regression" {
            anyhow::bail!(
                "logistic-regression model_type must be `weighted_logistic_regression`, got `{}`",
                self.model_type
            );
        }
        if self.feature_spec.hash_dim.is_some()
            || !self.feature_spec.hashed_categorical_features.is_empty()
        {
            anyhow::bail!(
                "hashed categorical logistic-regression models are no longer supported; retrain with the current one-hot tools/ml_ranker/train_ranker.py"
            );
        }
        let expected = EXPECTED_NUMERIC_FEATURES
            .iter()
            .map(|feature| feature.to_string())
            .collect::<Vec<_>>();
        if self.feature_spec.numeric_features != expected {
            anyhow::bail!(
                "logistic-regression model numeric features do not match Yardbird runtime. expected {:?}, got {:?}",
                expected,
                self.feature_spec.numeric_features
            );
        }
        if self.feature_spec.numeric_mean.len() != EXPECTED_NUMERIC_FEATURES.len()
            || self.feature_spec.numeric_std.len() != EXPECTED_NUMERIC_FEATURES.len()
        {
            anyhow::bail!("logistic-regression model normalization vector length is invalid");
        }
        if self
            .feature_spec
            .unknown_categorical_policy
            .as_deref()
            .is_some_and(|policy| policy != "zero")
        {
            anyhow::bail!("logistic-regression model unknown_categorical_policy must be `zero`");
        }
        let unique_vocab = self
            .feature_spec
            .categorical_vocab
            .iter()
            .collect::<HashSet<_>>();
        if unique_vocab.len() != self.feature_spec.categorical_vocab.len() {
            anyhow::bail!("logistic-regression model categorical_vocab contains duplicate entries");
        }
        let expected_weight_count =
            1 + EXPECTED_NUMERIC_FEATURES.len() + self.feature_spec.categorical_vocab.len();
        if self.weights.len() != expected_weight_count {
            anyhow::bail!(
                "logistic-regression model has {} weights, expected {}",
                self.weights.len(),
                expected_weight_count
            );
        }
        Ok(())
    }

    /// Return the raw linear score. Higher scores are ranked first.
    pub fn score(&self, features: &LogisticRegressionCandidateFeatures<'_>) -> f64 {
        let mut score = self.weights[0];
        for (index, value) in self.numeric_values(features).into_iter().enumerate() {
            let mean = self.feature_spec.numeric_mean[index];
            let std = self.feature_spec.numeric_std[index].max(1e-9);
            score += self.weights[1 + index] * ((value - mean) / std);
        }

        let categorical_offset = 1 + EXPECTED_NUMERIC_FEATURES.len();
        for feature in self.categorical_values(features) {
            if let Some(index) = self
                .feature_spec
                .categorical_vocab
                .iter()
                .position(|known| known == &feature)
            {
                score += self.weights[categorical_offset + index];
            }
        }
        score
    }

    fn numeric_values(&self, features: &LogisticRegressionCandidateFeatures<'_>) -> [f64; 16] {
        let frame_index = features.frame_index.unwrap_or(FRAME_SENTINEL);
        let frame_clipped = if frame_index == FRAME_SENTINEL {
            0
        } else {
            frame_index.clamp(-20, 20)
        };
        let ast_size = features.ast_size.max(0);
        let current_cost = features.current_cost.max(0);
        let candidate_count = features.candidate_count;
        [
            bool_as_f64(features.is_constant),
            bool_as_f64(features.is_variable),
            bool_as_f64(features.in_property_vocab),
            bool_as_f64(features.in_transition_vocab),
            bool_as_f64(features.frame_index.is_some()),
            f64::from(frame_clipped),
            f64::from(features.ast_size),
            f64::from(ast_size).ln_1p(),
            f64::from(features.current_cost),
            f64::from(current_cost).ln_1p(),
            f64::from(features.bmc_depth),
            f64::from(features.slot_index),
            features.cost_rank as f64,
            features.cost_rank_frac,
            candidate_count as f64,
            (candidate_count as f64).ln_1p(),
        ]
    }

    fn categorical_values(
        &self,
        features: &LogisticRegressionCandidateFeatures<'_>,
    ) -> [String; 3] {
        [
            format!("axiom={}", features.axiom_name),
            format!("slot={}", features.slot_index),
            format!("axiom_slot={}:{}", features.axiom_name, features.slot_index),
        ]
    }
}

fn bool_as_f64(value: bool) -> f64 {
    if value {
        1.0
    } else {
        0.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scores_with_expected_dimensions() {
        let model = LogisticRegressionModel {
            model_type: "weighted_logistic_regression".to_string(),
            label: "direct_core_chosen_candidate".to_string(),
            feature_spec: FeatureSpec {
                numeric_features: EXPECTED_NUMERIC_FEATURES
                    .iter()
                    .map(|feature| feature.to_string())
                    .collect(),
                numeric_mean: vec![0.0; EXPECTED_NUMERIC_FEATURES.len()],
                numeric_std: vec![1.0; EXPECTED_NUMERIC_FEATURES.len()],
                hash_dim: None,
                hashed_categorical_features: vec![],
                categorical_feature_templates: vec![
                    "axiom".to_string(),
                    "slot".to_string(),
                    "axiom_slot".to_string(),
                    "cost_fn".to_string(),
                ],
                categorical_vocab: vec![
                    "axiom=read-after-write-Int-Int".to_string(),
                    "slot=0".to_string(),
                    "axiom_slot=read-after-write-Int-Int:0".to_string(),
                    "cost_fn=bmc-cost".to_string(),
                ],
                unknown_categorical_policy: Some("zero".to_string()),
            },
            weights: vec![0.0; 1 + EXPECTED_NUMERIC_FEATURES.len() + 4],
        };
        model.validate().unwrap();
        let features = LogisticRegressionCandidateFeatures {
            axiom_name: "read-after-write-Int-Int",
            slot_index: 0,
            is_constant: true,
            is_variable: false,
            in_property_vocab: false,
            in_transition_vocab: true,
            frame_index: Some(0),
            ast_size: 1,
            current_cost: 2,
            bmc_depth: 3,
            cost_rank: 1,
            cost_rank_frac: 0.0,
            candidate_count: 4,
        };
        assert_eq!(model.score(&features), 0.0);
    }

    #[test]
    fn one_hot_categorical_weights_contribute_by_vocab_entry() {
        let categorical_vocab = vec![
            "axiom=read-after-write-Int-Int".to_string(),
            "slot=0".to_string(),
            "axiom_slot=read-after-write-Int-Int:0".to_string(),
            "cost_fn=bmc-cost".to_string(),
        ];
        let mut weights = vec![0.0; 1 + EXPECTED_NUMERIC_FEATURES.len() + categorical_vocab.len()];
        let categorical_offset = 1 + EXPECTED_NUMERIC_FEATURES.len();
        weights[categorical_offset] = 2.0;
        weights[categorical_offset + 1] = 3.0;

        let model = LogisticRegressionModel {
            model_type: "weighted_logistic_regression".to_string(),
            label: "direct_core_chosen_candidate".to_string(),
            feature_spec: FeatureSpec {
                numeric_features: EXPECTED_NUMERIC_FEATURES
                    .iter()
                    .map(|feature| feature.to_string())
                    .collect(),
                numeric_mean: vec![0.0; EXPECTED_NUMERIC_FEATURES.len()],
                numeric_std: vec![1.0; EXPECTED_NUMERIC_FEATURES.len()],
                hash_dim: None,
                hashed_categorical_features: vec![],
                categorical_feature_templates: vec![],
                categorical_vocab,
                unknown_categorical_policy: Some("zero".to_string()),
            },
            weights,
        };
        let features = LogisticRegressionCandidateFeatures {
            axiom_name: "read-after-write-Int-Int",
            slot_index: 0,
            is_constant: false,
            is_variable: false,
            in_property_vocab: false,
            in_transition_vocab: false,
            frame_index: None,
            ast_size: 0,
            current_cost: 0,
            bmc_depth: 0,
            cost_rank: 0,
            cost_rank_frac: 0.0,
            candidate_count: 0,
        };

        assert_eq!(model.score(&features), 5.0);
    }

    #[test]
    fn rejects_old_hashed_categorical_models() {
        let model = LogisticRegressionModel {
            model_type: "weighted_logistic_regression".to_string(),
            label: "direct_core_chosen_candidate".to_string(),
            feature_spec: FeatureSpec {
                numeric_features: EXPECTED_NUMERIC_FEATURES
                    .iter()
                    .map(|feature| feature.to_string())
                    .collect(),
                numeric_mean: vec![0.0; EXPECTED_NUMERIC_FEATURES.len()],
                numeric_std: vec![1.0; EXPECTED_NUMERIC_FEATURES.len()],
                hash_dim: Some(64),
                hashed_categorical_features: vec!["axiom".to_string()],
                categorical_feature_templates: vec![],
                categorical_vocab: vec![],
                unknown_categorical_policy: Some("zero".to_string()),
            },
            weights: vec![0.0; 65],
        };

        let err = model.validate().unwrap_err();
        assert!(
            err.to_string()
                .contains("hashed categorical logistic-regression models are no longer supported"),
            "unexpected error: {err}"
        );
    }
}
