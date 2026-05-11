from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
from datetime import datetime
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
BENCHMARK_ROOT = ROOT / "benchmark_results" / "main_eval"
INDEX_PATH = BENCHMARK_ROOT / "runs_index.json"
DEFAULT_CONFIG = ROOT / "garden" / "benchmark_config.yaml"
GARDEN_BIN = ROOT / "target" / "release" / "garden"
PAPER_GRAPHICS_VENV_PY = ROOT / "paper-graphics" / ".venv" / "bin" / "python"
REPORT_BUILDER = ROOT / "paper-graphics" / "report" / "build_report.py"
STATUS_RUNNING = "RUNNING"
STATUS_COMPLETED = "COMPLETED"
STATUS_FAILED = "FAILED"


class CommandError(RuntimeError):
    pass


def now_local() -> datetime:
    return datetime.now().astimezone()


def iso_now() -> str:
    return now_local().isoformat()


def ensure_dir(path: Path) -> Path:
    path.mkdir(parents=True, exist_ok=True)
    return path


def slugify(value: str) -> str:
    slug = re.sub(r"[^A-Za-z0-9]+", "-", value.strip()).strip("-").lower()
    return slug or "run"


def timestamp_filename(dt: datetime | None = None) -> str:
    current = dt or now_local()
    return current.strftime("%m_%d_%Y_%H_%M.json")


def run_id_for(env: str, name: str | None = None) -> str:
    prefix = slugify(name) if name else "eval"
    return f"{prefix}-{env}-{now_local().strftime('%Y%m%d_%H%M%S')}"


def load_json(path: Path, default: Any = None) -> Any:
    if not path.exists():
        return default
    return json.loads(path.read_text())


def write_json(path: Path, payload: Any) -> None:
    ensure_dir(path.parent)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def run_command(
    args: list[str],
    cwd: Path | None = None,
    check: bool = True,
    capture_output: bool = True,
) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        args,
        cwd=str(cwd) if cwd else None,
        text=True,
        capture_output=capture_output,
    )
    if check and result.returncode != 0:
        stderr = result.stderr.strip() if result.stderr else ""
        stdout = result.stdout.strip() if result.stdout else ""
        message = (
            stderr or stdout or f"Command failed with exit code {result.returncode}"
        )
        raise CommandError(f"{' '.join(args)}\n{message}")
    return result


def choose_report_python() -> str:
    if PAPER_GRAPHICS_VENV_PY.exists():
        return str(PAPER_GRAPHICS_VENV_PY)
    return shutil.which("python3") or sys.executable


def read_index() -> dict[str, Any]:
    return load_json(INDEX_PATH, default={"runs": []})


def update_index(manifest: dict[str, Any]) -> None:
    index = read_index()
    runs = [
        run for run in index.get("runs", []) if run.get("run_id") != manifest["run_id"]
    ]
    runs.append(
        {
            "run_id": manifest["run_id"],
            "name": manifest.get("name"),
            "env": manifest["env"],
            "status": manifest["status"],
            "started_at": manifest["started_at"],
            "updated_at": manifest["updated_at"],
            "benchmark_types": manifest["benchmark_types"],
            "manifest_path": manifest["manifest_path"],
        }
    )
    runs.sort(key=lambda run: run["started_at"], reverse=True)
    index["runs"] = runs
    write_json(INDEX_PATH, index)


def manifest_path_for(run_id: str) -> Path:
    return BENCHMARK_ROOT / run_id / "run.json"


def save_manifest(manifest: dict[str, Any]) -> None:
    manifest["updated_at"] = iso_now()
    path = Path(manifest["manifest_path"])
    write_json(path, manifest)
    update_index(manifest)


def load_manifest(run_id: str) -> dict[str, Any]:
    path = manifest_path_for(run_id)
    if not path.exists():
        raise FileNotFoundError(f"Unknown run id: {run_id}")
    return load_json(path)


def resolve_run_id(args: Any) -> str | None:
    return args.run_id or args.aws_run_id


def summarize_status(subruns: list[dict[str, Any]]) -> tuple[str, dict[str, int]]:
    counts = {STATUS_RUNNING: 0, STATUS_COMPLETED: 0, STATUS_FAILED: 0}
    for subrun in subruns:
        counts[subrun["status"]] = counts.get(subrun["status"], 0) + 1

    if counts[STATUS_FAILED]:
        overall = STATUS_FAILED
    elif counts[STATUS_RUNNING]:
        overall = STATUS_RUNNING
    else:
        overall = STATUS_COMPLETED
    return overall, counts


def base_manifest(
    run_id: str,
    env: str,
    benchmark_types: list[str],
    config_path: Path,
    name: str | None,
) -> dict[str, Any]:
    run_dir = ensure_dir(BENCHMARK_ROOT / run_id)
    return {
        "run_id": run_id,
        "name": name or run_id,
        "env": env,
        "status": STATUS_RUNNING,
        "started_at": iso_now(),
        "updated_at": iso_now(),
        "completed_at": None,
        "benchmark_types": benchmark_types,
        "config_path": str(config_path),
        "run_dir": str(run_dir),
        "manifest_path": str(run_dir / "run.json"),
        "progress": {
            "completed": 0,
            "failed": 0,
            "running": len(benchmark_types),
            "total": len(benchmark_types),
        },
        "report": None,
        "subruns": [],
    }


def refresh_progress(manifest: dict[str, Any]) -> None:
    overall, counts = summarize_status(manifest["subruns"])
    manifest["status"] = overall
    manifest["progress"] = {
        "completed": counts.get(STATUS_COMPLETED, 0),
        "failed": counts.get(STATUS_FAILED, 0),
        "running": counts.get(STATUS_RUNNING, 0),
        "total": len(manifest["subruns"]),
    }
    if overall == STATUS_COMPLETED and manifest.get("completed_at") is None:
        manifest["completed_at"] = iso_now()


def ensure_garden_binary() -> None:
    if GARDEN_BIN.exists():
        return
    run_command(["cargo", "build", "--release", "-p", "garden"], cwd=ROOT, check=True)


def relative_to_root(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def build_report_for_run(manifest: dict[str, Any]) -> None:
    if manifest["status"] != STATUS_COMPLETED:
        raise RuntimeError(
            f"Run {manifest['run_id']} is not complete yet; current status is {manifest['status']}"
        )

    run_dir = Path(manifest["run_dir"])
    report_dir = ensure_dir(run_dir / "report")
    report_python = choose_report_python()

    run_command(
        [
            report_python,
            str(REPORT_BUILDER),
            "--manifest",
            manifest["manifest_path"],
            "--run-dir",
            str(run_dir),
        ],
        cwd=ROOT,
        check=True,
        capture_output=False,
    )

    report_meta_path = report_dir / "report_metadata.json"
    if report_meta_path.exists():
        manifest["report"] = load_json(report_meta_path)
        save_manifest(manifest)


def print_run_summary(manifest: dict[str, Any]) -> None:
    print(f"Run ID: {manifest['run_id']}")
    print(f"Name: {manifest.get('name')}")
    print(f"Environment: {manifest['env']}")
    print(f"Status: {manifest['status']}")
    print(
        "Progress: "
        f"{manifest['progress']['completed']}/{manifest['progress']['total']} completed, "
        f"{manifest['progress']['running']} running, "
        f"{manifest['progress']['failed']} failed"
    )
    print(f"Started: {manifest['started_at']}")
    if manifest.get("completed_at"):
        print(f"Completed: {manifest['completed_at']}")
    print(f"Manifest: {relative_to_root(Path(manifest['manifest_path']))}")

    for subrun in manifest["subruns"]:
        line = f"  - {subrun['benchmark_type']}: {subrun['status']} ({subrun['mode']})"
        if subrun["mode"] == "aws":
            line += f" instance={subrun['instance_id']}"
        elif subrun["mode"] == "lab":
            line += f" vmid={subrun['worker_vmid']}"
            if subrun.get("worker_ip"):
                line += f" ip={subrun['worker_ip']}"
            if subrun.get("worker_destroyed_at"):
                line += " destroyed=yes"
        print(line)

    if manifest.get("report"):
        workbook = manifest["report"].get("workbook_pdf")
        if workbook:
            print(f"Workbook PDF: {workbook}")
