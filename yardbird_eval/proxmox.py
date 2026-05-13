from __future__ import annotations

import ipaddress
import ssl
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any

from .common import CommandError, run_command


DEFAULT_PROXMOX_API_PATH = "/api2/json"
DEFAULT_TASK_TIMEOUT_SECONDS = 300
DEFAULT_GUEST_READY_TIMEOUT_SECONDS = 300
DEFAULT_SSH_READY_TIMEOUT_SECONDS = 300


def proxmox_api_root(base_url: str) -> str:
    trimmed = base_url.rstrip("/")
    if trimmed.endswith(DEFAULT_PROXMOX_API_PATH):
        return trimmed
    return f"{trimmed}{DEFAULT_PROXMOX_API_PATH}"


def proxmox_request(
    method: str,
    base_url: str,
    path: str,
    token_id: str,
    token_secret: str,
    *,
    params: dict[str, Any] | None = None,
    insecure: bool = False,
) -> Any:
    url = f"{proxmox_api_root(base_url)}{path}"
    payload = None
    encoded_params = None
    if params:
        filtered = {
            key: value
            for key, value in params.items()
            if value is not None and value != ""
        }
        encoded_params = urllib.parse.urlencode(filtered, doseq=True)
    if encoded_params:
        if method.upper() in {"GET", "DELETE"}:
            separator = "&" if "?" in url else "?"
            url = f"{url}{separator}{encoded_params}"
        else:
            payload = encoded_params.encode()

    request = urllib.request.Request(
        url,
        data=payload,
        method=method.upper(),
        headers={"Authorization": f"PVEAPIToken={token_id}={token_secret}"},
    )
    ssl_context = ssl._create_unverified_context() if insecure else None
    try:
        with urllib.request.urlopen(
            request, context=ssl_context, timeout=30
        ) as response:
            body = response.read().decode()
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode().strip()
        raise CommandError(
            f"Proxmox API {method.upper()} {path} failed with {exc.code}: {detail or exc.reason}"
        ) from exc
    except urllib.error.URLError as exc:
        raise CommandError(
            f"Proxmox API {method.upper()} {path} failed: {exc.reason}"
        ) from exc

    if not body:
        return None
    decoded = __import__("json").loads(body)
    errors = decoded.get("errors") if isinstance(decoded, dict) else None
    if errors:
        raise CommandError(
            f"Proxmox API {method.upper()} {path} returned errors: {errors}"
        )
    if isinstance(decoded, dict) and "data" in decoded:
        return decoded["data"]
    return decoded


def proxmox_task_status(
    base_url: str,
    node: str,
    upid: str,
    token_id: str,
    token_secret: str,
    *,
    insecure: bool = False,
) -> dict[str, Any]:
    quoted_upid = urllib.parse.quote(upid, safe="")
    status = proxmox_request(
        "GET",
        base_url,
        f"/nodes/{node}/tasks/{quoted_upid}/status",
        token_id,
        token_secret,
        insecure=insecure,
    )
    if not isinstance(status, dict):
        raise CommandError(f"Unexpected Proxmox task payload for {upid}: {status!r}")
    return status


def proxmox_wait_for_task(
    base_url: str,
    node: str,
    upid: str,
    token_id: str,
    token_secret: str,
    *,
    insecure: bool = False,
    timeout_seconds: int = DEFAULT_TASK_TIMEOUT_SECONDS,
) -> dict[str, Any]:
    deadline = time.time() + timeout_seconds
    while time.time() < deadline:
        status = proxmox_task_status(
            base_url,
            node,
            upid,
            token_id,
            token_secret,
            insecure=insecure,
        )
        if status.get("status") == "stopped":
            exit_status = status.get("exitstatus")
            if exit_status not in {None, "OK"}:
                raise CommandError(
                    f"Proxmox task {upid} failed with exit status {exit_status}"
                )
            return status
        time.sleep(3)
    raise TimeoutError(f"Timed out waiting for Proxmox task {upid}")


def proxmox_next_vmid(
    base_url: str,
    token_id: str,
    token_secret: str,
    *,
    insecure: bool = False,
) -> int:
    return int(
        proxmox_request(
            "GET",
            base_url,
            "/cluster/nextid",
            token_id,
            token_secret,
            insecure=insecure,
        )
    )


def proxmox_vm_status(
    base_url: str,
    node: str,
    vmid: int,
    token_id: str,
    token_secret: str,
    *,
    insecure: bool = False,
) -> dict[str, Any]:
    status = proxmox_request(
        "GET",
        base_url,
        f"/nodes/{node}/qemu/{vmid}/status/current",
        token_id,
        token_secret,
        insecure=insecure,
    )
    if not isinstance(status, dict):
        raise CommandError(
            f"Unexpected Proxmox VM status payload for VM {vmid}: {status!r}"
        )
    return status


def proxmox_qemu_agent_interfaces(
    base_url: str,
    node: str,
    vmid: int,
    token_id: str,
    token_secret: str,
    *,
    insecure: bool = False,
) -> list[dict[str, Any]]:
    payload = proxmox_request(
        "GET",
        base_url,
        f"/nodes/{node}/qemu/{vmid}/agent/network-get-interfaces",
        token_id,
        token_secret,
        insecure=insecure,
    )
    if isinstance(payload, dict) and "result" in payload:
        payload = payload["result"]
    if not isinstance(payload, list):
        raise CommandError(
            f"Unexpected guest agent interface payload for VM {vmid}: {payload!r}"
        )
    return payload


def candidate_guest_ips(interfaces: list[dict[str, Any]]) -> list[str]:
    candidates: list[str] = []
    for interface in interfaces:
        name = interface.get("name", "")
        if name == "lo" or name.startswith(("docker", "veth", "br-")):
            continue
        for address in interface.get("ip-addresses", []):
            if address.get("ip-address-type") != "ipv4":
                continue
            value = address.get("ip-address")
            if not value:
                continue
            parsed = ipaddress.ip_address(value)
            if parsed.is_loopback or parsed.is_link_local or parsed.is_unspecified:
                continue
            candidates.append(value)
    return candidates


def proxmox_wait_for_guest_ip(
    base_url: str,
    node: str,
    vmid: int,
    token_id: str,
    token_secret: str,
    *,
    insecure: bool = False,
    timeout_seconds: int = DEFAULT_GUEST_READY_TIMEOUT_SECONDS,
) -> str:
    deadline = time.time() + timeout_seconds
    last_error: str | None = None
    while time.time() < deadline:
        try:
            interfaces = proxmox_qemu_agent_interfaces(
                base_url,
                node,
                vmid,
                token_id,
                token_secret,
                insecure=insecure,
            )
            ips = candidate_guest_ips(interfaces)
            if ips:
                return ips[0]
        except CommandError as exc:
            last_error = str(exc)
        time.sleep(5)
    if last_error:
        raise TimeoutError(f"Timed out waiting for VM {vmid} guest IP: {last_error}")
    raise TimeoutError(f"Timed out waiting for VM {vmid} guest IP")


def ssh_option_args(private_key_path: Path) -> list[str]:
    return [
        "-n",
        "-o",
        "BatchMode=yes",
        "-o",
        "ConnectTimeout=10",
        "-o",
        "StrictHostKeyChecking=no",
        "-o",
        "UserKnownHostsFile=/dev/null",
        "-i",
        str(private_key_path),
    ]


def ssh_run(
    user: str,
    host: str,
    private_key_path: Path,
    command: str,
    *,
    capture_output: bool = True,
    check: bool = True,
    timeout_seconds: int | None = None,
):
    return run_command(
        ["ssh", *ssh_option_args(private_key_path), f"{user}@{host}", command],
        check=check,
        capture_output=capture_output,
        timeout=timeout_seconds,
    )


def scp_to_host(
    local_path: Path,
    user: str,
    host: str,
    private_key_path: Path,
    remote_path: str,
) -> None:
    run_command(
        [
            "scp",
            *ssh_option_args(private_key_path),
            str(local_path),
            f"{user}@{host}:{remote_path}",
        ],
        check=True,
        capture_output=True,
    )


def wait_for_ssh(
    user: str,
    host: str,
    private_key_path: Path,
    *,
    timeout_seconds: int = DEFAULT_SSH_READY_TIMEOUT_SECONDS,
) -> None:
    deadline = time.time() + timeout_seconds
    while time.time() < deadline:
        result = ssh_run(
            user,
            host,
            private_key_path,
            "true",
            capture_output=True,
            check=False,
        )
        if result.returncode == 0:
            return
        time.sleep(5)
    raise TimeoutError(f"Timed out waiting for SSH on {user}@{host}")
