# Yardbird Lab Evaluation

This directory holds the first Proxmox-backed lab runner slice for `main_eval.py`.

Current scope:

- `--env lab` launches one ephemeral Proxmox VM per requested garden matrix
- each worker clones the current repo commit, builds `yardbird` and `garden`, runs the matrix, and uploads artifacts to R2
- `main_eval.py --run-id ... --status` refreshes run state from R2 and, when Proxmox credentials are available, also observes and cleans up worker VMs
- `main_eval.py --run-id ... --generate-report` downloads R2 artifacts and builds the normal workbook report

Not in this slice yet:

- Docker-based worker execution
- Postgres sidecar provisioning
- `--lab-train` / full training logging orchestration

## Worker Template Requirements

The Proxmox worker template should be an Ubuntu VM with:

- `cloud-init`
- `qemu-guest-agent`
- `git`
- `cargo` / Rust toolchain
- `python3` and `pip`
- `aws` CLI
- network access to GitHub and the configured R2 endpoint

The current bootstrap script also installs `z3-solver` into the worker user's local Python site-packages before building.

## Recommended Environment Variables

You can pass everything as CLI flags, but these env vars make the flow much easier to reuse:

```bash
export PROXMOX_API_URL="https://proxmox.example:8006/api2/json"
export PROXMOX_TOKEN_ID="user@pve!token-name"
export PROXMOX_TOKEN_SECRET="..."
export PROXMOX_NODE="pve-node-1"
export LAB_WORKER_TEMPLATE="9000"
export LAB_WORKER_SSH_KEY="$HOME/.ssh/yardbird_lab"
export LAB_R2_BUCKET="yardbird-lab"
export LAB_R2_ENDPOINT_URL="https://<account>.r2.cloudflarestorage.com"
export LAB_R2_REGION="auto"
export LAB_R2_PREFIX="main-eval"
export YARDBIRD_R2_ACCESS_KEY_ID="..."
export YARDBIRD_R2_SECRET_ACCESS_KEY="..."
```

`main_eval.py` loads the repo-root `.env` file automatically before parsing arguments. Existing shell environment variables still win over `.env` values.

The `YARDBIRD_R2_*` variables are used for the lab R2 flow specifically, so they do not clobber unrelated AWS credentials you may still need for the older AWS-backed path.

If the public key is not at `${LAB_WORKER_SSH_KEY}.pub`, also set:

```bash
export LAB_WORKER_SSH_PUBLIC_KEY="$HOME/.ssh/yardbird_lab.pub"
```

## Launch a Lab Evaluation

```bash
python3 main_eval.py \
  --env lab \
  --name proxmox-smoke \
  --benchmark-type quick
```

That creates a local manifest under `benchmark_results/main_eval/<run-id>/run.json`.

## Refresh Status

```bash
python3 main_eval.py --run-id <run-id> --status
```

Status is considered complete when both of these exist in R2 for a subrun:

- `results.json`
- `completion.json`

If `failure.json` exists, the subrun is marked failed.

When Proxmox credentials are available during a refresh, completed or failed workers are destroyed automatically unless the run was launched with `--lab-keep-vms`.

## Build the Report

```bash
python3 main_eval.py --run-id <run-id> --generate-report
```

That downloads:

- `results.json`
- `run.log`
- `metadata.json`
- `completion.json`

into the local run directory and then builds the normal report workbook.

## Artifact Layout

Each matrix uploads to:

```text
<LAB_R2_PREFIX>/<run-id>/<matrix-slug>/results.json
<LAB_R2_PREFIX>/<run-id>/<matrix-slug>/run.log
<LAB_R2_PREFIX>/<run-id>/<matrix-slug>/metadata.json
<LAB_R2_PREFIX>/<run-id>/<matrix-slug>/completion.json
<LAB_R2_PREFIX>/<run-id>/<matrix-slug>/failure.json
```

## Important Current Limitation

This phase intentionally keeps the worker runtime simple: the benchmark runs directly inside the worker VM after bootstrapping, not inside Docker yet.

That means this slice is good for validating:

- Proxmox VM lifecycle
- SSH/bootstrap flow
- R2 artifact durability
- report generation from lab runs

The next implementation slice should move the worker execution into Docker and then add the optional Postgres sidecar for training runs.
