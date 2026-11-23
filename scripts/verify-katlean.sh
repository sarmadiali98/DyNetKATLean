#!/usr/bin/env bash
set -euo pipefail
exec "$(dirname "$0")/../packages/KATLean/verify.sh" verify
