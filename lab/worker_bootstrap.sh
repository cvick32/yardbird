#!/usr/bin/env bash
set -euo pipefail

RUN_ROOT=${run_root}
RESULT_PATH=${result_path}
LOG_PATH=${log_path}
METADATA_PATH=${metadata_path}
COMPLETION_PATH=${completion_path}
FAILURE_PATH=${failure_path}
REPO_URL=${repo_url}
REPO_COMMIT=${repo_commit}
MATRIX_NAME=${matrix_name}
CONFIG_PATH=${config_path}
R2_BUCKET=${r2_bucket}
R2_REGION=${r2_region}
R2_ENDPOINT_URL=${r2_endpoint_url}
R2_ACCESS_KEY_ID=${r2_access_key_id}
R2_SECRET_ACCESS_KEY=${r2_secret_access_key}
R2_SESSION_TOKEN=${r2_session_token}
R2_RESULTS_KEY=${r2_results_key}
R2_LOG_KEY=${r2_log_key}
R2_METADATA_KEY=${r2_metadata_key}
R2_COMPLETION_KEY=${r2_completion_key}
R2_FAILURE_KEY=${r2_failure_key}

export MATRIX_NAME
export REPO_COMMIT

export PATH="$${HOME}/.cargo/bin:$${HOME}/.local/bin:/usr/local/cargo/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin:/snap/bin:$${PATH:-}"
if [ -f "$${HOME}/.cargo/env" ]; then
    . "$${HOME}/.cargo/env"
fi

if [ -n "$${R2_ACCESS_KEY_ID}" ] && [ -n "$${R2_SECRET_ACCESS_KEY}" ]; then
    export AWS_ACCESS_KEY_ID="$${R2_ACCESS_KEY_ID}"
    export AWS_SECRET_ACCESS_KEY="$${R2_SECRET_ACCESS_KEY}"
    export AWS_DEFAULT_REGION="$${R2_REGION}"
fi
if [ -n "$${R2_SESSION_TOKEN}" ]; then
    export AWS_SESSION_TOKEN="$${R2_SESSION_TOKEN}"
fi

mkdir -p "$${RUN_ROOT}"
exec > >(tee -a "$${LOG_PATH}") 2>&1

upload_file() {
    local source_path="$$1"
    local object_key="$$2"
    aws --endpoint-url "$${R2_ENDPOINT_URL}" s3 cp "$${source_path}" \
        "s3://$${R2_BUCKET}/$${object_key}" \
        --region "$${R2_REGION}"
}

write_failure_marker() {
    local message="$$1"
    FAILURE_MESSAGE="$${message}" python3 - <<'PY' > "$${FAILURE_PATH}"
import json
import os
from datetime import datetime, timezone

payload = {
    "status": "failed",
    "message": os.environ["FAILURE_MESSAGE"],
    "finished_at": datetime.now(timezone.utc).isoformat(),
}
print(json.dumps(payload, indent=2))
PY
    upload_file "$${FAILURE_PATH}" "$${R2_FAILURE_KEY}" || true
}

trap 'write_failure_marker "worker bootstrap failed"' ERR

echo "[INFO] Starting Yardbird lab worker bootstrap"
echo "[INFO] Matrix: $${MATRIX_NAME}"
echo "[INFO] Repo: $${REPO_URL}"
echo "[INFO] Ref: origin/main (launcher commit: $${REPO_COMMIT})"

for cmd in git cargo python3 aws; do
    if ! command -v "$${cmd}" >/dev/null 2>&1; then
        echo "[ERROR] Required command missing: $${cmd}"
        exit 1
    fi
done

python3 -m pip install --user z3-solver==4.15.3 >/dev/null
Z3_SITE_DIR="$$(python3 -c 'import site; print(site.getusersitepackages())')"
export Z3_SYS_Z3_HEADER="$${Z3_SITE_DIR}/z3/include/z3.h"
export LD_LIBRARY_PATH="$${Z3_SITE_DIR}/z3/lib:$${LD_LIBRARY_PATH:-}"

WORKTREE_DIR="$${RUN_ROOT}/repo"
if [ ! -d "$${WORKTREE_DIR}/.git" ]; then
    git clone "$${REPO_URL}" "$${WORKTREE_DIR}"
fi

cd "$${WORKTREE_DIR}"
git fetch origin main --tags --prune
git checkout --force main
git reset --hard origin/main
REPO_COMMIT="$$(git rev-parse HEAD)"
export REPO_COMMIT
echo "[INFO] Using origin/main at $${REPO_COMMIT}"

echo "[INFO] Building yardbird and garden"
cargo build --release -p yardbird
cargo build --release -p garden

echo "[INFO] Running garden"
./target/release/garden \
    --config "$${CONFIG_PATH}" \
    --matrix "$${MATRIX_NAME}" \
    --output "$${RESULT_PATH}"

python3 - <<'PY' > "$${METADATA_PATH}"
import json
import os
from datetime import datetime, timezone

payload = {
    "status": "completed",
    "matrix": os.environ["MATRIX_NAME"],
    "repo_commit": os.environ["REPO_COMMIT"],
    "finished_at": datetime.now(timezone.utc).isoformat(),
}
print(json.dumps(payload, indent=2))
PY

python3 - <<'PY' > "$${COMPLETION_PATH}"
import json
from datetime import datetime, timezone

payload = {
    "status": "completed",
    "finished_at": datetime.now(timezone.utc).isoformat(),
}
print(json.dumps(payload, indent=2))
PY

echo "[INFO] Uploading artifacts to R2"
upload_file "$${RESULT_PATH}" "$${R2_RESULTS_KEY}"
upload_file "$${LOG_PATH}" "$${R2_LOG_KEY}"
upload_file "$${METADATA_PATH}" "$${R2_METADATA_KEY}"
upload_file "$${COMPLETION_PATH}" "$${R2_COMPLETION_KEY}"

echo "[INFO] Worker completed successfully"
