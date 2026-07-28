#!/usr/bin/env python3
"""Build pinned and locally instrumented Z3, then run the same smoke queries."""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import os
import shlex
import statistics
import subprocess
import sys
import tarfile
import time
from datetime import datetime, timezone
from pathlib import Path


HERE = Path(__file__).resolve().parent
CONFIG = HERE / "config.json"
RESULTS = {"sat", "unsat", "unknown"}


def run(command: list[str], *, env=None, show=False) -> str:
    if show:
        print(shlex.join(command), flush=True)
    completed = subprocess.run(
        command,
        env=env,
        text=True,
        stdout=None if show else subprocess.PIPE,
        stderr=None if show else subprocess.PIPE,
        check=False,
    )
    if completed.returncode:
        raise RuntimeError(
            f"{shlex.join(command)} failed ({completed.returncode})\n"
            f"{completed.stdout or ''}{completed.stderr or ''}"
        )
    return completed.stdout.strip() if completed.stdout else ""


def git(checkout: Path, *args: str) -> str:
    return run(["git", "-C", str(checkout), *args])


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def source_state(checkout: Path, pinned: str) -> dict:
    head = git(checkout, "rev-parse", "HEAD")
    ancestor = subprocess.run(
        ["git", "-C", str(checkout), "merge-base", "--is-ancestor", pinned, head],
        check=False,
    ).returncode == 0
    if not ancestor:
        raise RuntimeError(f"{checkout} is not based on pinned revision {pinned}")

    patch = subprocess.check_output(
        ["git", "-C", str(checkout), "diff", "--binary", "HEAD"]
    )
    untracked_digest = hashlib.sha256()
    untracked = git(
        checkout, "ls-files", "--others", "--exclude-standard"
    ).splitlines()
    for name in untracked:
        path = checkout / name
        if path.is_file():
            untracked_digest.update(name.encode())
            untracked_digest.update(path.read_bytes())
    return {
        "path": str(checkout),
        "head": head,
        "dirty": bool(patch or untracked),
        "patch_sha256": hashlib.sha256(patch).hexdigest(),
        "untracked_sha256": untracked_digest.hexdigest(),
    }


def materialize_stock(checkout: Path, revision: str, destination: Path) -> None:
    archive = subprocess.check_output(
        ["git", "-C", str(checkout), "archive", "--format=tar", revision]
    )
    destination.mkdir(parents=True)
    with tarfile.open(fileobj=io.BytesIO(archive), mode="r:") as tar:
        if sys.version_info >= (3, 12):
            tar.extractall(destination, filter="data")
        else:
            tar.extractall(destination)


def find_z3(build_dir: Path) -> Path:
    binaries = [
        path
        for path in build_dir.rglob("z3")
        if path.is_file() and os.access(path, os.X_OK)
    ]
    if not binaries:
        raise RuntimeError(f"No z3 executable found under {build_dir}")
    return min(binaries, key=lambda path: len(path.parts))


def cache_value(build_dir: Path, name: str) -> str:
    prefix = f"{name}:"
    for line in (build_dir / "CMakeCache.txt").read_text().splitlines():
        if line.startswith(prefix):
            return line.split("=", 1)[1]
    raise RuntimeError(f"CMake cache does not contain {name}")


def build_z3(
    label: str,
    source: Path,
    build_dir: Path,
    config: dict,
    args: argparse.Namespace,
) -> dict:
    configure = ["cmake", "-S", str(source), "-B", str(build_dir)]
    if args.generator:
        configure += ["-G", args.generator]
    configure += [
        f"-D{name}={value}" for name, value in sorted(config["cmake"].items())
    ]

    env = os.environ.copy()
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    if args.cc:
        env["CC"] = args.cc
    if args.cxx:
        env["CXX"] = args.cxx

    print(f"[{label}] configure", flush=True)
    run(configure, env=env, show=True)
    build = [
        "cmake",
        "--build",
        str(build_dir),
        "--config",
        config["cmake"]["CMAKE_BUILD_TYPE"],
        "--parallel",
        str(args.jobs),
        "--target",
        "shell",
    ]
    print(f"[{label}] build", flush=True)
    run(build, env=env, show=True)

    binary = find_z3(build_dir).resolve()
    compiler = cache_value(build_dir, "CMAKE_CXX_COMPILER")
    return {
        "source": str(source),
        "binary": str(binary),
        "binary_sha256": sha256_file(binary),
        "version": run([str(binary), "--version"]),
        "compiler": compiler,
        "compiler_version": run([compiler, "--version"]),
        "release_flags": cache_value(build_dir, "CMAKE_CXX_FLAGS_RELEASE"),
        "configure_command": configure,
        "build_command": build,
    }


def solver_results(output: str) -> list[str]:
    return [line.strip() for line in output.splitlines() if line.strip() in RESULTS]


def compare(builds: dict, config: dict, runs: int, timeout: float) -> dict:
    timings = {
        label: {query["file"]: [] for query in config["queries"]}
        for label in builds
    }
    observed = {}
    labels = tuple(builds)
    for repetition in range(runs):
        order = labels if repetition % 2 == 0 else tuple(reversed(labels))
        for label in order:
            binary = builds[label]["binary"]
            for query in config["queries"]:
                query_path = HERE / query["file"]
                started = time.perf_counter()
                completed = subprocess.run(
                    [binary, str(query_path)],
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    timeout=timeout,
                    check=False,
                )
                elapsed_ms = (time.perf_counter() - started) * 1000
                if completed.returncode:
                    raise RuntimeError(f"{label} failed on {query_path}")
                result = solver_results(completed.stdout)
                if result != query["results"]:
                    raise RuntimeError(
                        f"{label} returned {result} for {query_path.name}; "
                        f"expected {query['results']}"
                    )
                observed.setdefault(label, {})[query["file"]] = result
                timings[label][query["file"]].append(elapsed_ms)
    if observed[labels[0]] != observed[labels[1]]:
        raise RuntimeError("Stock and instrumented results differ")
    return {
        "runs": runs,
        "results": observed[labels[0]],
        "results_equal": True,
        "median_ms": {
            label: {
                query: statistics.median(samples)
                for query, samples in query_timings.items()
            }
            for label, query_timings in timings.items()
        },
        "timings_are_diagnostic_only": True,
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Build pinned and instrumented Z3 with matching flags."
    )
    parser.add_argument("--z3-checkout", required=True, type=Path)
    parser.add_argument("--instrumented-checkout", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--generator")
    parser.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    parser.add_argument("--cc")
    parser.add_argument("--cxx")
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--timeout", type=float, default=30)
    args = parser.parse_args()

    try:
        config = json.loads(CONFIG.read_text())
        stock_checkout = args.z3_checkout.resolve()
        instrumented_checkout = (
            args.instrumented_checkout or args.z3_checkout
        ).resolve()
        pinned = config["pinned"]

        revision = git(
            stock_checkout, "rev-parse", f"{pinned['revision']}^{{commit}}"
        )
        tree = git(stock_checkout, "rev-parse", f"{revision}^{{tree}}")
        if revision != pinned["revision"] or tree != pinned["tree"]:
            raise RuntimeError("Stock checkout does not contain the pinned Z3 tree")
        if (instrumented_checkout / "scripts/VERSION.txt").read_text().strip() != pinned[
            "version"
        ]:
            raise RuntimeError("Instrumented checkout is not the pinned Z3 version")
        instrumented_state = source_state(instrumented_checkout, revision)

        output = args.output.resolve()
        output.mkdir(parents=True, exist_ok=False)
        stock_source = output / "source" / "stock"
        materialize_stock(stock_checkout, revision, stock_source)

        builds = {
            "stock": build_z3(
                "stock", stock_source, output / "build/stock", config, args
            ),
            "instrumented": build_z3(
                "instrumented",
                instrumented_checkout,
                output / "build/instrumented",
                config,
                args,
            ),
        }
        manifest = {
            "schema": "yardbird-z3-builder-result-v1",
            "created_at": datetime.now(timezone.utc).isoformat(),
            "pinned_source": pinned,
            "instrumented_source": instrumented_state,
            "shared_cmake_settings": config["cmake"],
            "builds": builds,
            "comparison": compare(builds, config, args.runs, args.timeout),
        }
        manifest_path = output / "manifest.json"
        manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
        print(f"Wrote {manifest_path}")
        print(f"Z3_STOCK_BIN={builds['stock']['binary']}")
        print(f"Z3_INSTRUMENTED_BIN={builds['instrumented']['binary']}")
        return 0
    except (
        FileExistsError,
        FileNotFoundError,
        RuntimeError,
        subprocess.CalledProcessError,
        subprocess.TimeoutExpired,
    ) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
