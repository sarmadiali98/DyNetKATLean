#!/usr/bin/env bash
set -euo pipefail
exec "$(dirname "$0")/../packages/NetKATLean/verify.sh" verify
