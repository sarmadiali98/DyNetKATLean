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
├── PLAN.md        # Phased roadmap
└── README.md      # This file
```

## Project Policies

- The primary source is the FoSSaCS 2022 paper, *DyNetKAT: An Algebra of
  Dynamic Networks* (arXiv:2102.10035v4). Its printed page and figure
  references are authoritative; the journal extension is outside this
  project's semantic scope.
- Lean 4 is the trusted semantic core. Python is limited to auxiliary scripts,
  golden-value checks, and experiments; it does not carry research-critical
  semantics.
- Preserve the paper's syntax, semantics, equations, and per-packet
  consistency. Distinguish paper definitions from implementation choices and
  extensions, and state finite-domain, termination, or boundedness assumptions
  explicitly.
- Do not use `axiom`, `sorry`, or `admit` as substitutes for proofs. Any
  temporary proof hole must be isolated and explained. Record mathematical
  findings and design conflicts in the relevant `docs/` files.
- Use Lean 4 / Lake, `UpperCamelCase` for types and constructors, and
  `lowerCamelCase` for definitions and theorems. Use Python 3 type hints,
  `snake_case`, and deterministic serialization.

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

A no-argument `lake build` that reports `[0/0]` does not compile the library;
always validate the explicit `DyNetKAT` target. If the system Python lacks
pytest, use a virtual environment and install `pytest>=8` there.
