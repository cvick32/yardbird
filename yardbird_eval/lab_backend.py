from __future__ import annotations

import os
import shlex
import shutil
import urllib.parse
from pathlib import Path
from string import Template
from typing import Any

from .common import (
    ROOT,
    STATUS_COMPLETED,
    STATUS_FAILED,
    STATUS_RUNNING,
    base_manifest,
    iso_now,
    refresh_progress,
    run_command,
    run_id_for,
    save_manifest,
    slugify,
)
from .object_store import object_store_download, object_store_head_object
from .proxmox import (
    CommandError,
    proxmox_next_vmid,
    proxmox_request,
    proxmox_vm_status,
    proxmox_wait_for_guest_ip,
    proxmox_wait_for_task,
    scp_to_host,
    ssh_run,
    wait_for_ssh,
)


LAB_DIR = ROOT / "lab"
LAB_WORKER_BOOTSTRAP_TEMPLATE = LAB_DIR / "worker_bootstrap.sh"
DEFAULT_LAB_R2_PREFIX = "main-eval"
DEFAULT_LAB_R2_REGION = "auto"
DEFAULT_LAB_WORKER_USER = "yardbird"


def env_default(name: str, fallback: str | None = None) -> str | None:
    return os.environ.get(name, fallback)


def r2_credentials() -> dict[str, str | None]:
    return {
        "access_key_id": os.environ.get("YARDBIRD_R2_ACCESS_KEY_ID"),
        "secret_access_key": os.environ.get("YARDBIRD_R2_SECRET_ACCESS_KEY"),
        "session_token": os.environ.get("YARDBIRD_R2_SESSION_TOKEN"),
    }


def normalize_r2_prefix(prefix: str) -> str:
    return prefix.strip("/").strip() or DEFAULT_LAB_R2_PREFIX


def resolve_private_key_path(value: str | None) -> Path:
    if not value:
        raise RuntimeError(
            "Provide --lab-worker-ssh-key (private key path) for lab runs"
        )
    path = Path(value).expanduser()
    if not path.exists():
        raise FileNotFoundError(f"Lab worker SSH private key not found: {path}")
    return path.resolve()


def resolve_public_key(private_key_path: Path, explicit_value: str | None) -> str:
    if explicit_value:
        explicit_path = Path(explicit_value).expanduser()
        if explicit_path.exists():
            return explicit_path.read_text().strip()
        return explicit_value.strip()
    public_key_path = Path(f"{private_key_path}.pub")
    if not public_key_path.exists():
        raise FileNotFoundError(
            f"Could not find public key for {private_key_path}; provide --lab-worker-ssh-public-key"
        )
    return public_key_path.read_text().strip()


def git_origin_url() -> str:
    return run_command(["git", "remote", "get-url", "origin"], cwd=ROOT).stdout.strip()


def git_head_commit() -> str:
    return run_command(["git", "rev-parse", "HEAD"], cwd=ROOT).stdout.strip()


def render_worker_bootstrap(replacements: dict[str, Any]) -> str:
    template = Template(LAB_WORKER_BOOTSTRAP_TEMPLATE.read_text())
    quoted = {key: shlex.quote(str(value)) for key, value in replacements.items()}
    return template.substitute(quoted)


def require_lab_value(value: str | None, flag_name: str) -> str:
    if value:
        return value
    raise RuntimeError(f"Provide {flag_name} for lab runs")


def lab_proxmox_settings(
    args: Any,
    manifest: dict[str, Any] | None = None,
    *,
    require_credentials: bool,
) -> dict[str, Any]:
    manifest_lab = manifest.get("lab", {}) if manifest else {}
    api_url = args.lab_proxmox_api_url or manifest_lab.get("proxmox_api_url")
    token_id = args.lab_proxmox_token_id or env_default("PROXMOX_TOKEN_ID")
    token_secret = args.lab_proxmox_token_secret or env_default("PROXMOX_TOKEN_SECRET")
    node = args.lab_proxmox_node or manifest_lab.get("proxmox_node")
    insecure = args.lab_proxmox_insecure or manifest_lab.get("proxmox_insecure", False)
    settings = {
        "api_url": api_url,
        "token_id": token_id,
        "token_secret": token_secret,
        "node": node,
        "insecure": insecure,
    }
    if require_credentials:
        settings["api_url"] = require_lab_value(
            settings["api_url"], "--lab-proxmox-api-url"
        )
        settings["token_id"] = require_lab_value(
            settings["token_id"], "--lab-proxmox-token-id"
        )
        settings["token_secret"] = require_lab_value(
            settings["token_secret"], "--lab-proxmox-token-secret"
        )
        settings["node"] = require_lab_value(settings["node"], "--lab-proxmox-node")
    return settings


def maybe_destroy_lab_worker(
    subrun: dict[str, Any], proxmox: dict[str, Any] | None
) -> None:
    if subrun.get("keep_vm") or subrun.get("worker_destroyed_at"):
        return
    if not proxmox or not all(
        [
            proxmox.get("api_url"),
            proxmox.get("token_id"),
            proxmox.get("token_secret"),
            proxmox.get("node"),
        ]
    ):
        subrun["cleanup_pending"] = True
        return

    vmid = int(subrun["worker_vmid"])
    base_url = proxmox["api_url"]
    node = proxmox["node"]
    token_id = proxmox["token_id"]
    token_secret = proxmox["token_secret"]
    insecure = proxmox["insecure"]

    try:
        status = proxmox_vm_status(
            base_url,
            node,
            vmid,
            token_id,
            token_secret,
            insecure=insecure,
        )
        if status.get("status") == "running":
            stop_upid = proxmox_request(
                "POST",
                base_url,
                f"/nodes/{node}/qemu/{vmid}/status/stop",
                token_id,
                token_secret,
                insecure=insecure,
            )
            proxmox_wait_for_task(
                base_url,
                node,
                str(stop_upid),
                token_id,
                token_secret,
                insecure=insecure,
            )
    except CommandError as exc:
        message = str(exc).lower()
        if "not found" not in message and "does not exist" not in message:
            subrun["cleanup_error"] = str(exc)
            return

    try:
        delete_upid = proxmox_request(
            "DELETE",
            base_url,
            f"/nodes/{node}/qemu/{vmid}",
            token_id,
            token_secret,
            params={"purge": 1},
            insecure=insecure,
        )
        proxmox_wait_for_task(
            base_url,
            node,
            str(delete_upid),
            token_id,
            token_secret,
            insecure=insecure,
        )
    except CommandError as exc:
        message = str(exc).lower()
        if "not found" not in message and "does not exist" not in message:
            subrun["cleanup_error"] = str(exc)
            return

    subrun["worker_destroyed_at"] = iso_now()
    subrun["cleanup_pending"] = False
    subrun.pop("cleanup_error", None)


def launch_lab_run(args: Any) -> dict[str, Any]:
    config_path = Path(args.config).expanduser().resolve()
    if not config_path.exists():
        raise FileNotFoundError(f"Lab benchmark config not found: {config_path}")

    proxmox = lab_proxmox_settings(args, require_credentials=True)
    private_key_path = resolve_private_key_path(args.lab_worker_ssh_key)
    public_key = resolve_public_key(private_key_path, args.lab_worker_ssh_public_key)
    worker_template = require_lab_value(
        args.lab_worker_template, "--lab-worker-template"
    )
    worker_user = args.lab_worker_user or DEFAULT_LAB_WORKER_USER
    r2_bucket = require_lab_value(args.lab_r2_bucket, "--lab-r2-bucket")
    r2_endpoint_url = require_lab_value(
        args.lab_r2_endpoint_url, "--lab-r2-endpoint-url"
    )
    r2_region = args.lab_r2_region or DEFAULT_LAB_R2_REGION
    r2_prefix = normalize_r2_prefix(args.lab_r2_prefix or DEFAULT_LAB_R2_PREFIX)
    creds = r2_credentials()
    repo_url = git_origin_url()
    repo_commit = git_head_commit()

    run_id = run_id_for("lab", args.name)
    manifest = base_manifest(run_id, "lab", args.benchmark_type, config_path, args.name)
    run_dir = Path(manifest["run_dir"])
    lab_launch_dir = run_dir / "lab"
    lab_launch_dir.mkdir(parents=True, exist_ok=True)
    manifest["training_enabled"] = False
    manifest["training_version"] = None
    manifest["postgres_sidecar"] = None
    manifest["lab"] = {
        "proxmox_api_url": proxmox["api_url"],
        "proxmox_node": proxmox["node"],
        "proxmox_insecure": proxmox["insecure"],
        "worker_template": worker_template,
        "worker_user": worker_user,
        "keep_vms": args.lab_keep_vms,
        "r2_bucket": r2_bucket,
        "r2_region": r2_region,
        "r2_endpoint_url": r2_endpoint_url,
        "r2_prefix": r2_prefix,
        "r2_access_key_configured": bool(creds["access_key_id"] and creds["secret_access_key"]),
        "repo_url": repo_url,
        "repo_commit": repo_commit,
    }

    for index, matrix in enumerate(args.benchmark_type, start=1):
        matrix_slug = slugify(matrix)
        vm_name = f"yardbird-{run_id[:20]}-{matrix_slug[:20]}-{index:02d}"
        vmid = proxmox_next_vmid(
            proxmox["api_url"],
            proxmox["token_id"],
            proxmox["token_secret"],
            insecure=proxmox["insecure"],
        )
        remote_run_root = f"/home/{worker_user}/yardbird-lab/{run_id}/{matrix_slug}"
        remote_config_path = f"{remote_run_root}/benchmark_config.yaml"
        remote_bootstrap_path = f"{remote_run_root}/worker_bootstrap.sh"
        local_launch_subdir = lab_launch_dir / matrix_slug
        local_launch_subdir.mkdir(parents=True, exist_ok=True)
        local_config_snapshot = local_launch_subdir / "benchmark_config.yaml"
        local_bootstrap_script = local_launch_subdir / "worker_bootstrap.sh"
        shutil.copyfile(config_path, local_config_snapshot)

        object_prefix = f"{r2_prefix}/{run_id}/{matrix_slug}"
        raw_path = run_dir / "raw" / matrix / "results.json"
        download_dir = run_dir / "downloads" / matrix
        subrun = {
            "benchmark_type": matrix,
            "status": STATUS_RUNNING,
            "started_at": iso_now(),
            "completed_at": None,
            "mode": "lab",
            "worker_vmid": vmid,
            "worker_node": proxmox["node"],
            "worker_name": vm_name,
            "worker_template": worker_template,
            "worker_user": worker_user,
            "worker_ip": None,
            "keep_vm": args.lab_keep_vms,
            "result_path": str(raw_path),
            "download_dir": str(download_dir),
            "remote_run_root": remote_run_root,
            "local_launch_dir": str(local_launch_subdir),
            "r2_bucket": r2_bucket,
            "r2_region": r2_region,
            "r2_endpoint_url": r2_endpoint_url,
            "r2_prefix": object_prefix,
            "r2_results_key": f"{object_prefix}/results.json",
            "r2_log_key": f"{object_prefix}/run.log",
            "r2_metadata_key": f"{object_prefix}/metadata.json",
            "r2_completion_key": f"{object_prefix}/completion.json",
            "r2_failure_key": f"{object_prefix}/failure.json",
        }
        manifest["subruns"].append(subrun)
        save_manifest(manifest)

        try:
            clone_upid = proxmox_request(
                "POST",
                proxmox["api_url"],
                f"/nodes/{proxmox['node']}/qemu/{worker_template}/clone",
                proxmox["token_id"],
                proxmox["token_secret"],
                params={"newid": vmid, "name": vm_name, "target": proxmox["node"]},
                insecure=proxmox["insecure"],
            )
            proxmox_wait_for_task(
                proxmox["api_url"],
                proxmox["node"],
                str(clone_upid),
                proxmox["token_id"],
                proxmox["token_secret"],
                insecure=proxmox["insecure"],
            )
            configure_upid = proxmox_request(
                "POST",
                proxmox["api_url"],
                f"/nodes/{proxmox['node']}/qemu/{vmid}/config",
                proxmox["token_id"],
                proxmox["token_secret"],
                params={
                    "ciuser": worker_user,
                    "sshkeys": public_key,
                    "ipconfig0": "ip=dhcp",
                },
                insecure=proxmox["insecure"],
            )
            proxmox_wait_for_task(
                proxmox["api_url"],
                proxmox["node"],
                str(configure_upid),
                proxmox["token_id"],
                proxmox["token_secret"],
                insecure=proxmox["insecure"],
            )
            start_upid = proxmox_request(
                "POST",
                proxmox["api_url"],
                f"/nodes/{proxmox['node']}/qemu/{vmid}/status/start",
                proxmox["token_id"],
                proxmox["token_secret"],
                insecure=proxmox["insecure"],
            )
            proxmox_wait_for_task(
                proxmox["api_url"],
                proxmox["node"],
                str(start_upid),
                proxmox["token_id"],
                proxmox["token_secret"],
                insecure=proxmox["insecure"],
            )
            worker_ip = proxmox_wait_for_guest_ip(
                proxmox["api_url"],
                proxmox["node"],
                vmid,
                proxmox["token_id"],
                proxmox["token_secret"],
                insecure=proxmox["insecure"],
            )
            subrun["worker_ip"] = worker_ip
            wait_for_ssh(worker_user, worker_ip, private_key_path)

            rendered_bootstrap = render_worker_bootstrap(
                {
                    "run_root": remote_run_root,
                    "result_path": f"{remote_run_root}/results.json",
                    "log_path": f"{remote_run_root}/run.log",
                    "metadata_path": f"{remote_run_root}/metadata.json",
                    "completion_path": f"{remote_run_root}/completion.json",
                    "failure_path": f"{remote_run_root}/failure.json",
                    "repo_url": repo_url,
                    "repo_commit": repo_commit,
                    "matrix_name": matrix,
                    "config_path": remote_config_path,
                    "r2_bucket": r2_bucket,
                    "r2_region": r2_region,
                    "r2_endpoint_url": r2_endpoint_url,
                    "r2_access_key_id": creds["access_key_id"] or "",
                    "r2_secret_access_key": creds["secret_access_key"] or "",
                    "r2_session_token": creds["session_token"] or "",
                    "r2_results_key": subrun["r2_results_key"],
                    "r2_log_key": subrun["r2_log_key"],
                    "r2_metadata_key": subrun["r2_metadata_key"],
                    "r2_completion_key": subrun["r2_completion_key"],
                    "r2_failure_key": subrun["r2_failure_key"],
                }
            )
            local_bootstrap_script.write_text(rendered_bootstrap)

            ssh_run(
                worker_user,
                worker_ip,
                private_key_path,
                f"mkdir -p {shlex.quote(remote_run_root)}",
                capture_output=True,
            )
            scp_to_host(
                local_config_snapshot,
                worker_user,
                worker_ip,
                private_key_path,
                remote_config_path,
            )
            scp_to_host(
                local_bootstrap_script,
                worker_user,
                worker_ip,
                private_key_path,
                remote_bootstrap_path,
            )
            ssh_run(
                worker_user,
                worker_ip,
                private_key_path,
                (
                    f"chmod +x {shlex.quote(remote_bootstrap_path)} && "
                    f"nohup bash {shlex.quote(remote_bootstrap_path)} "
                    ">/dev/null 2>&1 </dev/null &"
                ),
                capture_output=True,
            )
            probe_state = probe.stdout.strip()
            if probe_state not in {"LOG_READY", "PID_RUNNING"}:
                diagnostics = ssh_run(
                    worker_user,
                    worker_ip,
                    private_key_path,
                    (
                        f"echo '--- ls ---'; ls -lah {shlex.quote(remote_run_root)}; "
                        f"echo '--- launcher stdout ---'; "
                        f"if [ -f {shlex.quote(remote_run_root + '/launcher.stdout.log')} ]; then "
                        f"tail -n 100 {shlex.quote(remote_run_root + '/launcher.stdout.log')}; fi; "
                        f"echo '--- launcher stderr ---'; "
                        f"if [ -f {shlex.quote(remote_run_root + '/launcher.stderr.log')} ]; then "
                        f"tail -n 100 {shlex.quote(remote_run_root + '/launcher.stderr.log')}; fi"
                    ),
                    capture_output=True,
                    check=False,
                )
                raise RuntimeError(
                    "Remote bootstrap exited before creating a run log. "
                    f"Probe={probe_state!r}. Diagnostics:\n{diagnostics.stdout}\n{diagnostics.stderr}"
                )

            subrun["launcher_pid"] = int(launch_pid)
            subrun["launcher_probe_state"] = probe_state
            subrun["worker_started_at"] = iso_now()
            subrun["last_observed_vm_state"] = "running"
            refresh_progress(manifest)
            save_manifest(manifest)
        except Exception as exc:
            subrun["status"] = STATUS_FAILED
            subrun["completed_at"] = iso_now()
            subrun["error"] = str(exc)
            maybe_destroy_lab_worker(subrun, proxmox)
            refresh_progress(manifest)
            save_manifest(manifest)
            raise

    return manifest


def refresh_lab_run(manifest: dict[str, Any], args: Any) -> dict[str, Any]:
    proxmox = lab_proxmox_settings(args, manifest=manifest, require_credentials=False)
    can_query_proxmox = all(
        [
            proxmox.get("api_url"),
            proxmox.get("token_id"),
            proxmox.get("token_secret"),
            proxmox.get("node"),
        ]
    )

    for subrun in manifest["subruns"]:
        results_exist = object_store_head_object(
            subrun["r2_bucket"],
            subrun["r2_results_key"],
            subrun["r2_region"],
            subrun.get("r2_endpoint_url"),
        )
        completion_exists = object_store_head_object(
            subrun["r2_bucket"],
            subrun["r2_completion_key"],
            subrun["r2_region"],
            subrun.get("r2_endpoint_url"),
        )
        failure_exists = object_store_head_object(
            subrun["r2_bucket"],
            subrun["r2_failure_key"],
            subrun["r2_region"],
            subrun.get("r2_endpoint_url"),
        )

        state = None
        if can_query_proxmox and not subrun.get("worker_destroyed_at"):
            try:
                current = proxmox_vm_status(
                    proxmox["api_url"],
                    subrun["worker_node"],
                    int(subrun["worker_vmid"]),
                    proxmox["token_id"],
                    proxmox["token_secret"],
                    insecure=proxmox["insecure"],
                )
                state = current.get("status")
            except CommandError as exc:
                subrun["last_proxmox_error"] = str(exc)

        subrun["last_observed_vm_state"] = state or subrun.get("last_observed_vm_state")
        subrun["last_checked_at"] = iso_now()
        new_status = subrun["status"]
        if results_exist and completion_exists:
            new_status = STATUS_COMPLETED
        elif failure_exists:
            new_status = STATUS_FAILED
        elif state in {"stopped", "paused"}:
            new_status = STATUS_FAILED
        else:
            new_status = STATUS_RUNNING

        if new_status != subrun["status"]:
            subrun["status"] = new_status
            if new_status in {STATUS_COMPLETED, STATUS_FAILED} and not subrun.get(
                "completed_at"
            ):
                subrun["completed_at"] = iso_now()

        if subrun["status"] in {STATUS_COMPLETED, STATUS_FAILED}:
            maybe_destroy_lab_worker(subrun, proxmox if can_query_proxmox else None)

    refresh_progress(manifest)
    save_manifest(manifest)
    return manifest


def download_lab_artifacts(manifest: dict[str, Any]) -> None:
    for subrun in manifest["subruns"]:
        if subrun["status"] != STATUS_COMPLETED:
            raise RuntimeError(
                f"Cannot download artifacts for incomplete benchmark type {subrun['benchmark_type']}"
            )

        raw_path = Path(subrun["result_path"])
        download_dir = Path(subrun["download_dir"])
        download_dir.mkdir(parents=True, exist_ok=True)
        bucket = subrun["r2_bucket"]
        region = subrun["r2_region"]
        endpoint_url = subrun.get("r2_endpoint_url")
        downloads = {
            subrun["r2_results_key"]: raw_path,
            subrun["r2_log_key"]: download_dir / "run.log",
            subrun["r2_metadata_key"]: download_dir / "metadata.json",
            subrun["r2_completion_key"]: download_dir / "completion.json",
        }

        for object_key, local_path in downloads.items():
            if local_path.exists():
                continue
            object_store_download(bucket, object_key, local_path, region, endpoint_url)

        subrun["downloaded_at"] = iso_now()
        subrun["download_dir"] = str(download_dir)
        subrun["result_path"] = str(raw_path)

    save_manifest(manifest)
