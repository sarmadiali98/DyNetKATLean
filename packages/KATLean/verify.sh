#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
unset LEAN_PATH LEAN_SRC_PATH

smoke() {
    lake env lean test_katlean_import.lean
}

test_all() {
    for test in test_*.lean; do
        lake env lean "$test"
    done
}

case "${1:-verify}" in
    build) lake build ;;
    smoke) lake build; smoke ;;
    test-all) lake build; test_all ;;
    verify)
        # Check every owned source, including the test-only explicit solver.
        if grep -nHE '^import[[:space:]]+' KATLean.lean KATLean/*.lean KATLean/Native/*.lean test_*.lean |
            grep -vE ':import[[:space:]]+(KATLean|Mathlib|Lean|Std|Init)([.[:space:]]|$)'; then
            echo 'Unexpected KATLean import' >&2
            exit 1
        fi
        lake build
        test_all
        ;;
    consumer-test) lake build; python3 consumer-test.py ;;
    *) echo "Usage: $0 [build|smoke|test-all|verify|consumer-test]" >&2; exit 2 ;;
esac
