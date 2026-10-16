# DyNetKAT-Lean

Faithful Lean 4 formalization of the **original DyNetKAT calculus**:
*DyNetKAT: An Algebra of Dynamic Networks* (arXiv:2102.10035v4, FoSSaCS 2022).

## Goal

A self-contained formal verification of DyNetKAT — syntax, operational
semantics, the E_DNK axiomatization (A0–A15 + AIP), bisimilarity,
soundness, ground-completeness, and the safety analysis framework — as
described faithfully in the paper.

This is **not** a reproduction of the journal extension
(log-based extraction, SDNRacer causality, bounded schedules).  That work
lives in `/Users/ali/Desktop/DyNetKAT` (read-only reference only).

## Structure

```
DyNetKAT-Lean/
├── lean/          # Lean 4 formalization (trusted semantic core)
├── python/        # Auxiliary scripts & golden tests (untrusted adapter)
├── docs/          # Research notes, conformance mapping, proof roadmap
├── scripts/       # Build & validation scripts
├── AGENTS.md      # Agent instructions
├── HANDOFF.md     # Persistent project memory
├── PLAN.md        # Phased roadmap
└── README.md      # This file
```

## Building

```bash
cd lean
lake build DyNetKAT    # authoritative Lean build
```

## Testing

```bash
cd python
python3 -m pytest -q   # Python auxiliary tests
```

Combined check:
```bash
./scripts/verify.sh
```
