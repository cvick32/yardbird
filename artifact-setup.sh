#!/bin/bash
set -e
exec > >(tee /var/log/yardbird-setup.log) 2>&1

echo "[INFO] Starting Yardbird environment setup"

# ---------------------------------------------------------------------
# 1. System-level dependencies (run as root)
# ---------------------------------------------------------------------
echo "[INFO] Installing system dependencies"
apt-get update -y
apt-get install -y git curl cmake build-essential python3 python3-pip pkg-config libssl-dev libclang-dev

# ---------------------------------------------------------------------
# 2. Create yardbird user (if missing)
# ---------------------------------------------------------------------
if ! id yardbird &>/dev/null; then
    echo "[INFO] Creating yardbird user"
    useradd -m -s /bin/bash yardbird
    echo "yardbird ALL=(ALL) NOPASSWD:ALL" > /etc/sudoers.d/yardbird
fi

# Ensure home ownership
chown -R yardbird:yardbird /home/yardbird

# ---------------------------------------------------------------------
# 3. Install and build Yardbird as yardbird user
# ---------------------------------------------------------------------
sudo -u yardbird bash <<'EOF'
set -e
cd /home/yardbird

log() { echo "[INFO] $(date): $1"; }

# --- Install Z3 (Python + native libs) ---
log "Installing Z3 Python package"
python3 -m pip install --user z3-solver==4.15.3
export LD_LIBRARY_PATH="$HOME/.local/lib/python3.10/site-packages/z3/lib/"
echo "export LD_LIBRARY_PATH=${LD_LIBRARY_PATH}" >> ~/.bashrc

# --- Install Rust toolchain ---
if ! command -v cargo >/dev/null; then
    log "Installing Rust toolchain"
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
    echo 'source "$HOME/.cargo/env"' >> ~/.bashrc
    source "$HOME/.cargo/env"
fi

# --- Clone and build Yardbird ---
if [ ! -d yardbird ]; then
    log "Cloning yardbird repository"
    git clone https://github.com/cvick32/yardbird.git
fi
cd yardbird

log "Building yardbird"
Z3_SYS_Z3_HEADER="$HOME/.local/lib/python3.10/site-packages/z3/include/z3.h" cargo build --release -p yardbird

log "Building garden"
Z3_SYS_Z3_HEADER="$HOME/.local/lib/python3.10/site-packages/z3/include/z3.h" cargo build --release -p garden

# --- Install binaries to ~/.local/bin and add to PATH ---
mkdir -p ~/.local/bin
cp ./target/release/yardbird ~/.local/bin/
cp ./target/release/garden ~/.local/bin/
echo 'export PATH=$HOME/.local/bin:$PATH' >> ~/.bashrc

log "Setup complete for yardbird user"
EOF

echo "[INFO] Yardbird setup finished successfully"
