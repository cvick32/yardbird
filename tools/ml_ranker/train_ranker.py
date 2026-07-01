#!/usr/bin/env python3
"""Train and evaluate a small per-slot Yardbird term ranker.

This is a dependency-light prototype. It reads a family split manifest, exports
candidate rows from the Yardbird training database with psql, trains a weighted
logistic model using numpy, and reports ranking metrics by split.
"""

from __future__ import annotations

import argparse
import csv
import io
import json
import math
import os
import subprocess
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import numpy as np


SPLITS = ("train", "dev", "eval", "unassigned")
FRAME_SENTINEL = -999


@dataclass(frozen=True)
class Family:
    family_id: str
    split: str
    parent_family: str
    benchmark_paths: tuple[str, ...]


def parse_manifest(path: Path) -> list[Family]:
    """Parse the small YAML subset used by eval/splits/array-family-v1.yaml."""
    families: list[Family] = []
    current: dict[str, object] | None = None
    in_paths = False

    def finish_current() -> None:
        nonlocal current
        if current is None:
            return
        family_id = str(current["id"])
        split = str(current.get("split", "unassigned"))
        parent_family = str(current.get("parent_family", family_id))
        paths = tuple(current.get("benchmark_paths", ()))
        families.append(Family(family_id, split, parent_family, paths))
        current = None

    for raw_line in path.read_text().splitlines():
        line = raw_line.split("#", 1)[0].rstrip()
        stripped = line.strip()
        if not stripped:
            continue

        if stripped.startswith("- id:"):
            finish_current()
            current = {"id": stripped.split(":", 1)[1].strip(), "benchmark_paths": []}
            in_paths = False
            continue

        if current is None:
            continue

        if stripped.startswith("split:"):
            current["split"] = stripped.split(":", 1)[1].strip()
            in_paths = False
        elif stripped.startswith("parent_family:"):
            current["parent_family"] = stripped.split(":", 1)[1].strip()
            in_paths = False
        elif stripped == "benchmark_paths:":
            in_paths = True
        elif in_paths and stripped.startswith("- "):
            current_paths = current.setdefault("benchmark_paths", [])
            assert isinstance(current_paths, list)
            current_paths.append(stripped[2:].strip())

    finish_current()
    if not families:
        raise ValueError(f"no families found in manifest {path}")
    for family in families:
        if family.split not in SPLITS:
            raise ValueError(f"unknown split {family.split!r} for family {family.family_id}")
        if not family.benchmark_paths:
            raise ValueError(f"family {family.family_id} has no benchmark_paths")
    return families


def load_dotenv(repo_root: Path) -> None:
    env_path = repo_root / ".env"
    if not env_path.exists():
        return
    for raw_line in env_path.read_text().splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        os.environ.setdefault(key.strip(), value.strip().strip("'\""))


def sql_literal(value: str) -> str:
    return "'" + value.replace("'", "''") + "'"


def manifest_values_sql(families: Iterable[Family]) -> str:
    rows = []
    for family in families:
        for benchmark_path in family.benchmark_paths:
            rows.append(
                "("
                + ", ".join(
                    [
                        sql_literal(benchmark_path),
                        sql_literal(family.split),
                        sql_literal(family.family_id),
                        sql_literal(family.parent_family),
                    ]
                )
                + ")"
            )
    return ",\n".join(rows)


def build_export_query(
    families: list[Family],
    cost_function: str | None,
    include_unsuccessful: bool,
) -> str:
    values = manifest_values_sql(families)
    filters = []
    if cost_function:
        filters.append(f"b.cost_function = {sql_literal(cost_function)}")
    if not include_unsuccessful:
        filters.append("b.success IS TRUE")
    where_clause = ""
    if filters:
        where_clause = "WHERE " + " AND ".join(filters)

    return f"""
COPY (
WITH manifest(benchmark_path, split, family_id, parent_family) AS (
    VALUES
{values}
),
decision_core AS (
    SELECT
        aid.decision_id,
        bool_or(ai.in_unsat_core) AS decision_core_positive
    FROM abstract_instantiation_decisions aid
    JOIN abstract_instantiations ai ON ai.id = aid.abstract_instantiation_id
    GROUP BY aid.decision_id
),
matched_benchmarks AS (
    SELECT
        b.id AS benchmark_id,
        b.name AS benchmark_name,
        b.cost_function,
        b.success,
        m.split,
        m.family_id,
        m.parent_family
    FROM benchmarks b
    JOIN manifest m
      ON b.name = m.benchmark_path
      OR b.name = regexp_replace(m.benchmark_path, '^.*/', '')
    {where_clause}
)
SELECT
    mb.benchmark_id,
    mb.benchmark_name,
    mb.cost_function,
    mb.success,
    mb.split,
    mb.family_id,
    mb.parent_family,
    d.id AS decision_id,
    d.decision_key,
    d.bmc_depth,
    d.axiom_name,
    d.slot_index,
    c.id AS candidate_id,
    c.term,
    c.term_hash,
    c.is_constant,
    c.is_variable,
    c.in_property_vocab,
    c.in_transition_vocab,
    COALESCE(c.frame_index, {FRAME_SENTINEL}) AS frame_index,
    c.ast_size,
    c.current_cost,
    c.was_chosen,
    COALESCE(dc.decision_core_positive, FALSE) AS decision_core_positive
FROM matched_benchmarks mb
JOIN decisions d ON d.benchmark_id = mb.benchmark_id
JOIN candidates c ON c.decision_id = d.id
LEFT JOIN decision_core dc ON dc.decision_id = d.id
ORDER BY mb.split, mb.benchmark_id, d.id, c.id
) TO STDOUT WITH CSV HEADER
"""


def export_rows(database_url: str, query: str) -> list[dict[str, str]]:
    proc = subprocess.run(
        ["psql", database_url, "-X", "-q", "-v", "ON_ERROR_STOP=1", "-c", query],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if proc.returncode != 0:
        sys.stderr.write(proc.stderr)
        raise SystemExit(proc.returncode)
    return list(csv.DictReader(io.StringIO(proc.stdout)))


def parse_bool(value: str) -> bool:
    return value.lower() in {"t", "true", "1", "yes"}


def add_decision_rank_features(rows: list[dict[str, object]]) -> None:
    by_decision: dict[int, list[dict[str, object]]] = defaultdict(list)
    for row in rows:
        by_decision[int(row["decision_id"])].append(row)

    for group in by_decision.values():
        ordered = sorted(
            group,
            key=lambda row: (
                int(row["current_cost"]),
                int(row["ast_size"]),
                str(row["term_hash"]),
                int(row["candidate_id"]),
            ),
        )
        count = len(ordered)
        for rank, row in enumerate(ordered, start=1):
            row["cost_rank"] = rank
            row["candidate_count"] = count
            row["cost_rank_frac"] = 0.0 if count <= 1 else (rank - 1) / (count - 1)


def normalize_rows(raw_rows: list[dict[str, str]]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for raw in raw_rows:
        was_chosen = parse_bool(raw["was_chosen"])
        decision_core_positive = parse_bool(raw["decision_core_positive"])
        frame_index = int(raw["frame_index"])
        row: dict[str, object] = {
            "benchmark_id": int(raw["benchmark_id"]),
            "benchmark_name": raw["benchmark_name"],
            "cost_function": raw["cost_function"],
            "success": parse_bool(raw["success"]),
            "split": raw["split"],
            "family_id": raw["family_id"],
            "parent_family": raw["parent_family"],
            "decision_id": int(raw["decision_id"]),
            "decision_key": raw["decision_key"],
            "bmc_depth": int(raw["bmc_depth"]),
            "axiom_name": raw["axiom_name"],
            "slot_index": int(raw["slot_index"]),
            "candidate_id": int(raw["candidate_id"]),
            "term": raw["term"],
            "term_hash": raw["term_hash"],
            "is_constant": parse_bool(raw["is_constant"]),
            "is_variable": parse_bool(raw["is_variable"]),
            "in_property_vocab": parse_bool(raw["in_property_vocab"]),
            "in_transition_vocab": parse_bool(raw["in_transition_vocab"]),
            "frame_index": frame_index,
            "has_frame_index": frame_index != FRAME_SENTINEL,
            "ast_size": int(raw["ast_size"]),
            "current_cost": int(raw["current_cost"]),
            "was_chosen": was_chosen,
            "decision_core_positive": decision_core_positive,
            "label": was_chosen and decision_core_positive,
        }
        rows.append(row)
    add_decision_rank_features(rows)
    return rows


NUMERIC_FEATURES = [
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
]


def numeric_values(row: dict[str, object]) -> list[float]:
    frame_index = int(row["frame_index"])
    frame_clipped = 0 if frame_index == FRAME_SENTINEL else max(-20, min(20, frame_index))
    ast_size = int(row["ast_size"])
    current_cost = int(row["current_cost"])
    candidate_count = int(row["candidate_count"])
    return [
        float(bool(row["is_constant"])),
        float(bool(row["is_variable"])),
        float(bool(row["in_property_vocab"])),
        float(bool(row["in_transition_vocab"])),
        float(bool(row["has_frame_index"])),
        float(frame_clipped),
        float(ast_size),
        math.log1p(max(0, ast_size)),
        float(current_cost),
        math.log1p(max(0, current_cost)),
        float(row["bmc_depth"]),
        float(row["slot_index"]),
        float(row["cost_rank"]),
        float(row["cost_rank_frac"]),
        float(candidate_count),
        math.log1p(max(0, candidate_count)),
    ]


def categorical_features(row: dict[str, object]) -> list[str]:
    # Deliberately omit benchmark/family/term identity. We want generalization,
    # not a memorized lookup table over the manifest.
    return [
        f"axiom={row['axiom_name']}",
        f"slot={row['slot_index']}",
        f"axiom_slot={row['axiom_name']}:{row['slot_index']}",
        f"cost_fn={row['cost_function']}",
    ]


@dataclass
class FeatureSpec:
    categorical_vocab: list[str]
    numeric_mean: list[float]
    numeric_std: list[float]


def fit_feature_spec(rows: list[dict[str, object]]) -> FeatureSpec:
    numeric = np.asarray([numeric_values(row) for row in rows], dtype=np.float64)
    mean = numeric.mean(axis=0)
    std = numeric.std(axis=0)
    std[std < 1e-9] = 1.0
    categorical_vocab = sorted(
        {feature for row in rows for feature in categorical_features(row)}
    )
    return FeatureSpec(categorical_vocab, mean.tolist(), std.tolist())


def build_matrix(rows: list[dict[str, object]], spec: FeatureSpec) -> np.ndarray:
    numeric = np.asarray([numeric_values(row) for row in rows], dtype=np.float64)
    mean = np.asarray(spec.numeric_mean, dtype=np.float64)
    std = np.asarray(spec.numeric_std, dtype=np.float64)
    numeric = (numeric - mean) / std

    categorical_index = {
        feature: index for index, feature in enumerate(spec.categorical_vocab)
    }
    categorical = np.zeros((len(rows), len(spec.categorical_vocab)), dtype=np.float64)
    for i, row in enumerate(rows):
        for feature in categorical_features(row):
            if feature in categorical_index:
                categorical[i, categorical_index[feature]] += 1.0

    intercept = np.ones((len(rows), 1), dtype=np.float64)
    return np.concatenate([intercept, numeric, categorical], axis=1)


def sigmoid(logits: np.ndarray) -> np.ndarray:
    clipped = np.clip(logits, -40, 40)
    return 1.0 / (1.0 + np.exp(-clipped))


def train_logistic(
    x_train: np.ndarray,
    y_train: np.ndarray,
    epochs: int,
    learning_rate: float,
    l2: float,
    positive_weight: float | None,
) -> tuple[np.ndarray, dict[str, float]]:
    pos = int(y_train.sum())
    neg = int(len(y_train) - pos)
    if pos == 0:
        raise ValueError("training split has no positive labels")

    if positive_weight is None:
        positive_weight = min(50.0, max(1.0, neg / max(1, pos)))

    sample_weight = np.ones_like(y_train, dtype=np.float64)
    sample_weight[y_train > 0.5] = positive_weight
    weight_sum = sample_weight.sum()

    weights = np.zeros(x_train.shape[1], dtype=np.float64)
    l2_mask = np.ones_like(weights)
    l2_mask[0] = 0.0

    for _ in range(epochs):
        pred = sigmoid(x_train @ weights)
        grad = (x_train.T @ ((pred - y_train) * sample_weight)) / weight_sum
        grad += l2 * weights * l2_mask
        weights -= learning_rate * grad

    pred = sigmoid(x_train @ weights)
    eps = 1e-12
    loss = -np.sum(
        sample_weight
        * (y_train * np.log(pred + eps) + (1.0 - y_train) * np.log(1.0 - pred + eps))
    ) / weight_sum
    return weights, {
        "positive_weight": float(positive_weight),
        "weighted_log_loss": float(loss),
        "positive_rows": float(pos),
        "negative_rows": float(neg),
    }


def split_rows(rows: list[dict[str, object]], split: str) -> list[dict[str, object]]:
    return [row for row in rows if row["split"] == split]


def rank_metrics(
    rows: list[dict[str, object]],
    score_by_candidate: dict[int, float],
    use_model: bool,
) -> dict[str, object]:
    by_decision: dict[int, list[dict[str, object]]] = defaultdict(list)
    for row in rows:
        by_decision[int(row["decision_id"])].append(row)

    reciprocal_ranks = []
    ranks = []
    percentiles = []
    top1 = top3 = top5 = 0
    positive_decisions = 0
    candidate_counts = []

    for group in by_decision.values():
        if not any(bool(row["label"]) for row in group):
            continue
        positive_decisions += 1
        candidate_counts.append(len(group))
        if use_model:
            ordered = sorted(
                group,
                key=lambda row: (
                    -score_by_candidate[int(row["candidate_id"])],
                    int(row["current_cost"]),
                    int(row["ast_size"]),
                    str(row["term_hash"]),
                    int(row["candidate_id"]),
                ),
            )
        else:
            ordered = sorted(
                group,
                key=lambda row: (
                    int(row["current_cost"]),
                    int(row["ast_size"]),
                    str(row["term_hash"]),
                    int(row["candidate_id"]),
                ),
            )

        positive_ranks = [
            rank for rank, row in enumerate(ordered, start=1) if bool(row["label"])
        ]
        best_rank = min(positive_ranks)
        ranks.append(best_rank)
        reciprocal_ranks.append(1.0 / best_rank)
        denom = max(1, len(group) - 1)
        percentiles.append((best_rank - 1) / denom)
        top1 += best_rank <= 1
        top3 += best_rank <= 3
        top5 += best_rank <= 5

    if positive_decisions == 0:
        return {
            "positive_decisions": 0,
            "mrr": None,
            "top1": None,
            "top3": None,
            "top5": None,
            "mean_rank": None,
            "mean_rank_percentile": None,
            "mean_candidates_per_positive_decision": None,
        }

    return {
        "positive_decisions": positive_decisions,
        "mrr": float(np.mean(reciprocal_ranks)),
        "top1": float(top1 / positive_decisions),
        "top3": float(top3 / positive_decisions),
        "top5": float(top5 / positive_decisions),
        "mean_rank": float(np.mean(ranks)),
        "median_rank": float(np.median(ranks)),
        "mean_rank_percentile": float(np.mean(percentiles)),
        "mean_candidates_per_positive_decision": float(np.mean(candidate_counts)),
    }


def make_score_map(rows: list[dict[str, object]], scores: np.ndarray) -> dict[int, float]:
    return {
        int(row["candidate_id"]): float(score)
        for row, score in zip(rows, scores, strict=True)
    }


def summarize_dataset(families: list[Family], rows: list[dict[str, object]]) -> dict[str, object]:
    manifest_benchmarks_by_split = Counter()
    manifest_families_by_split = Counter()
    for family in families:
        manifest_families_by_split[family.split] += 1
        manifest_benchmarks_by_split[family.split] += len(family.benchmark_paths)

    rows_by_split = Counter(str(row["split"]) for row in rows)
    labels_by_split = Counter(str(row["split"]) for row in rows if bool(row["label"]))
    decisions_by_split: dict[str, set[int]] = defaultdict(set)
    positive_decisions_by_split: dict[str, set[int]] = defaultdict(set)
    matched_benchmarks_by_split: dict[str, set[str]] = defaultdict(set)
    for row in rows:
        split = str(row["split"])
        decisions_by_split[split].add(int(row["decision_id"]))
        matched_benchmarks_by_split[split].add(str(row["benchmark_name"]))
        if bool(row["decision_core_positive"]):
            positive_decisions_by_split[split].add(int(row["decision_id"]))

    return {
        "manifest": {
            split: {
                "benchmarks": manifest_benchmarks_by_split[split],
                "families": manifest_families_by_split[split],
            }
            for split in SPLITS
        },
        "extracted": {
            split: {
                "candidate_rows": rows_by_split[split],
                "positive_candidate_rows": labels_by_split[split],
                "decisions": len(decisions_by_split[split]),
                "core_positive_decisions": len(positive_decisions_by_split[split]),
                "matched_benchmarks": len(matched_benchmarks_by_split[split]),
            }
            for split in SPLITS
        },
        "total_candidate_rows": len(rows),
    }


def write_json(path: Path, data: object) -> None:
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--database-url")
    parser.add_argument("--cost-function", default="bmc-cost")
    parser.add_argument("--all-cost-functions", action="store_true")
    parser.add_argument("--include-unsuccessful", action="store_true")
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--epochs", type=int, default=600)
    parser.add_argument("--learning-rate", type=float, default=0.25)
    parser.add_argument("--l2", type=float, default=1e-4)
    parser.add_argument("--positive-weight", type=float)
    args = parser.parse_args()

    repo_root = Path.cwd()
    load_dotenv(repo_root)

    database_url = (
        args.database_url
        or os.environ.get("YARDBIRD_DATABASE_URL")
        or os.environ.get("DATABASE_URL")
    )
    if not database_url:
        parser.error("provide --database-url or set YARDBIRD_DATABASE_URL")
    if database_url.startswith("postgresql+"):
        database_url = "postgresql://" + database_url.split("://", 1)[1]

    families = parse_manifest(args.manifest)
    query = build_export_query(
        families,
        None if args.all_cost_functions else args.cost_function,
        args.include_unsuccessful,
    )
    raw_rows = export_rows(database_url, query)
    rows = normalize_rows(raw_rows)
    if not rows:
        raise SystemExit("no candidate rows extracted; check DB URL, manifest, and cost filter")

    args.out_dir.mkdir(parents=True, exist_ok=True)
    summary = summarize_dataset(families, rows)
    write_json(args.out_dir / "dataset-summary.json", summary)

    train_rows = split_rows(rows, "train")
    if not train_rows:
        raise SystemExit("no train rows extracted")

    spec = fit_feature_spec(train_rows)
    x_train = build_matrix(train_rows, spec)
    y_train = np.asarray([float(bool(row["label"])) for row in train_rows], dtype=np.float64)
    weights, train_info = train_logistic(
        x_train,
        y_train,
        args.epochs,
        args.learning_rate,
        args.l2,
        args.positive_weight,
    )

    metrics: dict[str, object] = {
        "label": "direct_core_chosen_candidate",
        "cost_function_filter": None if args.all_cost_functions else args.cost_function,
        "training": train_info,
        "splits": {},
    }
    all_scores_by_candidate: dict[int, float] = {}
    for split in SPLITS:
        split_data = split_rows(rows, split)
        if not split_data:
            continue
        x_split = build_matrix(split_data, spec)
        scores = sigmoid(x_split @ weights)
        score_map = make_score_map(split_data, scores)
        all_scores_by_candidate.update(score_map)
        metrics["splits"][split] = {
            "rows": len(split_data),
            "positive_rows": int(sum(bool(row["label"]) for row in split_data)),
            "decisions": len({int(row["decision_id"]) for row in split_data}),
            "model": rank_metrics(split_data, score_map, use_model=True),
            "current_cost_baseline": rank_metrics(split_data, score_map, use_model=False),
        }

    model = {
        "model_type": "weighted_logistic_regression",
        "label": "direct_core_chosen_candidate",
        "feature_spec": {
            "numeric_features": NUMERIC_FEATURES,
            "numeric_mean": spec.numeric_mean,
            "numeric_std": spec.numeric_std,
            "categorical_feature_templates": [
                "axiom",
                "slot",
                "axiom_slot",
                "cost_fn",
            ],
            "categorical_vocab": spec.categorical_vocab,
            "unknown_categorical_policy": "zero",
        },
        "weights": weights.tolist(),
        "training": train_info,
    }
    write_json(args.out_dir / "metrics.json", metrics)
    write_json(args.out_dir / "model.json", model)

    print(json.dumps(metrics, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
