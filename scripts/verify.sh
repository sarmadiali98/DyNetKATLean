#!/bin/bash
# verify.sh — combined Lean + Python validation
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)

echo "=== Lean build ==="
cd "$ROOT/lean"
lake build DyNetKAT

echo "=== Python tests ==="
cd "$ROOT/python"
if [ -f .venv/bin/python ]; then
    .venv/bin/python -m pytest -q
else
    python3 -m pytest -q || {
        echo "pytest not found. Run: python3 -m venv .venv && ./.venv/bin/python -m pip install pytest"
        exit 1
    }
fi

echo "=== All checks passed ==="
