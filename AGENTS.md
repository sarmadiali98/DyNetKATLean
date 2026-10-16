# Agent Instructions — DyNetKAT-Lean (Formalization)

## Purpose

Self-contained formalization of the **original DyNetKAT calculus** in Lean 4,
as faithfully as possible to *DyNetKAT: An Algebra of Dynamic Networks*
(arXiv:2102.10035v4 / FoSSaCS 2022).

This is a *new* repository.  The journal-extension repository
`/Users/ali/Desktop/DyNetKAT` is **READ ONLY** and must not be modified.
This project is **independent** of that repository.

## Source of truth

- **Primary source:** `DyNetKAT.pdf` (arXiv:2102.10035v4, 22 May 2021) — the
  FoSSaCS published version.  The journal version
  (`DyNetKAT_Journal.pdf`) is NOT consulted for the calculus semantics.
- The paper's printed page numbers and figure/table references are authoritative.
- External mathematical sources cited by the paper (e.g., NetKAT `[2]`,
  process-algebra `[3]`, SDNRacer `[30]`) are referenced for background only;
  the DyNetKAT paper itself defines the semantics to be formalized.

## Semantic boundary

- **Lean 4** is the trusted semantic core: NetKAT denotational model,
  DyNetKAT syntax and operational semantics, bisimilarity, the E_DNK
  derivability relation, AIP, normalization, soundness, ground-completeness,
  safety syntax and analysis.
- **Python** is an untrusted adapter layer for *auxiliary* scripts,
  golden-value checks, and experiments only.  Python does **not** carry
  research-critical mathematical semantics.

## Code and naming conventions

- Lean: Lean 4 / Lake; `UpperCamelCase` for types/constructors,
  `lowerCamelCase` for definitions/theorems.
- Python: Python 3 type hints, `snake_case`, deterministic serialization.

## Build and validation

### Lean

    cd lean && lake build DyNetKAT

A no-argument `lake build` that reports `[0/0]` is **not** sufficient — it
does not compile the library target.  Always build `DyNetKAT` explicitly.

### Python

    cd python && python3 -m pytest -q

(Use `python3 -m venv .venv && ./.venv/bin/python -m pip install "pytest>=8"`
if system `python3` lacks `pytest`.)

### Combined

    scripts/verify.sh

## Non-negotiable principles

1. The original DyNetKAT paper is the source of truth; do not invent semantics.
2. Preserve syntax, semantics, equations, and theorem statements.
3. Keep DyNetKAT's per-packet consistency semantics.
4. No `axiom`, `sorry`, or `admit` as substitutes for proof.
5. Isolate any temporary `sorry` with an explanatory comment and handoff note.
6. Distinguish paper definitions from implementation and genuine extensions.
7. State finite-domain, termination, and boundedness assumptions explicitly.
8. Record findings in `docs/` as work proceeds.
9. Update `HANDOFF.md` after meaningful work.
10. Raise a **Research / Design Alarm** in `docs/DESIGN_ALARMS.md` and
    `HANDOFF.md` whenever evidence conflicts with a modeling or proof decision.
