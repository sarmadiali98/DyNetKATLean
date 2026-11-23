#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# Git limits the scan to tracked text. Binary blobs are excluded.
dash=$(printf '\342\200\224')
if git grep -nI -F -e "$dash" --; then
    echo 'Tracked text contains a Unicode U+2014 character.' >&2
    exit 1
else
    status=$?
    if [[ $status -ne 1 ]]; then
        exit "$status"
    fi
fi
echo 'Tracked text check passed.'
