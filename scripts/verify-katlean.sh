#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../lean"

# Check the entire generic source set, including modules outside the umbrella.
if grep -nHE '^import[[:space:]]+(DyNetKAT|DyNetKATLean|NetKATLean|KATLean\.NetKAT)([.[:space:]]|$)' \
    KATLean.lean KATLean/*.lean KATLean/Native/*.lean \
    test_katlean_import.lean test_native_kat.lean test_kat_completeness.lean test_symbolic_kat.lean; then
    echo 'KATLean imports a higher layer' >&2
    exit 1
fi

lake build KATLean
for test in test_katlean_import test_native_kat test_kat_completeness test_symbolic_kat; do
    lake env lean "$test.lean"
done
