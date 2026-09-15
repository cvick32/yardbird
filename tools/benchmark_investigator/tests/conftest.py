import json
import subprocess
import sys

import pytest


@pytest.fixture
def source_root(tmp_path):
    root = tmp_path / "source"
    (root / "src").mkdir(parents=True)
    (root / "src/lib.rs").write_text("// strategy_sat\npub fn hello() {}\n")
    (root / "Cargo.toml").write_text('[package]\nname="fixture"\nversion="0.1.0"\n')
    (root / "one.vmt").write_text("; fixture one\n")
    (root / "two.vmt").write_text("; fixture two\n")
    subprocess.run(["git", "init", "-q", str(root)], check=True)
    subprocess.run(
        [
            "git",
            "-C",
            str(root),
            "-c",
            "user.email=test@example.test",
            "-c",
            "user.name=Test",
            "commit",
            "--allow-empty",
            "-qm",
            "fixture",
        ],
        check=True,
    )
    return root


@pytest.fixture
def profile():
    return {
        "timing_secs": {"driver_check_strategy_total": 5.0},
        "driver_records": [
            {
                "bmc_depth": 0,
                "refinement_step": 0,
                "action": "next_depth",
                "timing_secs": {"driver_step_total": 2.0, "strategy_sat": 1.0},
                "indexed_assertions_before": 0,
                "indexed_assertions_after": 3,
            },
            {
                "bmc_depth": 1,
                "refinement_step": 0,
                "action": "timeout",
                "timing_secs": {"driver_step_total": 3.0, "strategy_sat": 2.0},
                "indexed_assertions_before": 3,
                "indexed_assertions_after": 5,
            },
        ],
        "cost_records": [
            {
                "bmc_depth": d,
                "refinement_step": 0,
                "timing_secs": {"rule_matching_total": float(d + 1)},
                "counters": {"model_satisfied_matches_filtered": 4},
                "egraph": {
                    "nodes_before_update": 2,
                    "nodes_after_update": 10 + d,
                    "classes_after_update": 5,
                },
                "rule_instantiation": {
                    "candidates_generated": 6,
                    "candidates_selected": 2,
                    "by_rule": {
                        "read-after-write": {
                            "search_secs": 0.2,
                            "apply_secs": 0.3,
                            "search_calls": 1,
                            "substitutions_explored": 8,
                            "candidates_generated": 6,
                            "candidates_selected": 2,
                        }
                    },
                },
            }
            for d in (0, 1)
        ],
        "solver_checks": [
            {
                "depth": d,
                "refinement_step": 0,
                "check_id": d,
                "result": result,
                "timing_ns": {"raw_check": 500_000_000, "total_check_handling": 600_000_000},
                "statistics_delta": {"stats": {"conflicts": 3}},
            }
            for d, result in [(0, "Unsat"), (1, "Sat")]
        ],
    }


@pytest.fixture
def fake_binary(tmp_path, profile):
    path = tmp_path / "fake-yardbird"
    data = {
        "profiling": profile,
        "run_progress": {
            "termination_reason": "depth_limit",
            "deepest_completed_depth": 1,
            "current_depth": 1,
            "current_refinement_step": 0,
        },
        "found_proof": False,
        "counterexample": False,
        "total_refinement_steps": 2,
        "total_instantiations_added": 5,
    }
    path.write_text(
        f"#!{sys.executable}\nimport json,sys\nprint('Z3 version: fixture',file=sys.stderr)\nprint({json.dumps(data)!r})\n"
    )
    path.chmod(0o755)
    return path
