#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
unset LEAN_PATH LEAN_SRC_PATH

verify_package() (
    cd "packages/$1"
    printf '\n=== %s: package verification and consumer ===\n' "$1"
    ./verify.sh verify
    ./verify.sh consumer-test
    printf '%s verify and consumer-test: PASS\n' "$1"
)

case "${1:-all}" in
    KATLean|NetKATLean|DyNetKATLean)
        verify_package "$1"
        ;;
    all)
        # The Docker snapshot has no Git index. CI checks the checkout before building it.
        if [[ -e .git ]]; then
            bash scripts/check-em-dashes.sh
        fi
        for package in KATLean NetKATLean DyNetKATLean; do
            verify_package "$package"
        done
        (
            cd lean
            # Compile the optional Lean modules exercised by regression tests.
            # No external KATch executable is used.
            lake build DyNetKAT dynetkat +DyNetKAT.Experimental +DyNetKAT.NetKAT.Legacy
            for test in test_*.lean; do
                printf '\n=== Integration Lean test: %s ===\n' "$test"
                lake env lean "$test"
            done
        )
        scripts/verify.sh
        python3 scripts/verify-package-independence.py
        printf '\n=== Release verification passed ===\n'
        ;;
    *)
        echo "Usage: $0 [all|KATLean|NetKATLean|DyNetKATLean]" >&2
        exit 2
        ;;
esac
