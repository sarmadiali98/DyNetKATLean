# PLAN.md — DyNetKAT-Lean Formalization Roadmap

## Objective

Formally verify the original *DyNetKAT* calculus in Lean 4, faithfully to the
paper (arXiv:2102.10035v4 / FoSSaCS 2022).  Source of truth: `DyNetKAT.pdf`.

## Phases

### Phase 0 — Paper audit & repo foundation  (COMPLETED)

- Identify exact paper version.  ✅
- Read paper incrementally; create `docs/PAPER_CONFORMANCE.md`.  ✅
- Audit existing repo `/Users/ali/Desktop/DyNetKAT` for reuse;
  create `docs/REUSE_AUDIT.md`.  ✅
- Create `docs/DESIGN_ALARMS.md` (empty / stub).  ✅
- Propose Lean architecture (recorded in this file).  ✅
- Create `docs/PROOF_OBLIGATIONS.md`.  ✅
- Initialize Lean/Lake project; smoke-test build.  ✅
- Add Mathlib4 dependency (required for Fintype, Finset, coinduction).  ✅

### Phase 1 — NetKAT semantic core  (COMPLETED)

- Self-contained dup-free NetKAT denotational model (§I-A of the paper).  ✅
- Packet model: finite fields → values; complete tests & assignments.  ✅
- NetKAT policy syntax, denotational semantics ⟦−⟧.  ✅
- NetKAT star over finite packet domains (finite iteration).  ✅
- Basic identities & normalization (Lemma 5).  ✅ (basic identities; Lemma 5 deferred)
- Python golden tests (16 tests).  ✅
- `lake build DyNetKAT` passes.  ✅
- No `sorry`, `admit`, or `axiom`.  ✅

### Phase 2 — DyNetKAT syntax & operational semantics

- DyNetKAT process syntax (Fig. 5).
- Multi-packet configurations (d, H, H′).
- Labeled small-step semantics (Fig. 8).
- Labels: (σ,σ′) | x?r | x!r | rcfg(x,r).
- Per-packet consistency (Theorem 3 / design rationale).

### Phase 3 — Extended DyNetKAT & axiomatization

- Restriction δ_ℒ(−), projection π_n(−).
- Left-merge ⌊⌊ and communication-merge | |.
- rcfg constants.
- Full axiom set A0–A15 + AIP + A16 (Fig. 11).

### Phase 4 — Bisimilarity & semantic results

- Coinductive bisimilarity (Definition 2).
- Semantic layering (Proposition 1).
- Branching finiteness (Lemma 8).
- Soundness of all axioms (Lemma 10, 11).
- Soundness & ground-completeness (Theorem 1).
- Normal forms (Definition 6, Lemma 9).

### Phase 5 — Safety framework

- Safety property syntax (Definition 12).
- Head normal forms (Definition 13).
- Semantic map ⟦−⟧ (Definition 14).
- Trace-equivalence axioms E_DNK^tr (Definition 15).
- Safe network systems (Definition 16).
- Extended sugars (Definition 17).

### Phase 6 — Examples & experiments

- Stateful firewall (Fig. 1 / §II).
- Distributed controller (Fig. 2).
- FatTree case study (§V) — Python adapter for large-scale experiments.

## Architecture principles

- Lean owns formal identifiers, packet & policy semantics, event IR,
  causality, legal schedules, extraction meaning, safety checking, and
  correctness theorems.
- Python parses raw logs, adapts datasets/tools, orchestrates experiments,
  and serializes canonical inputs/outputs.
- Minimal initial fragment: NetKAT syntax + denotational semantics + DyNetKAT
  syntax.  Build incrementally; do not formalize all of NetKAT upfront.
- **Mathlib4** will be used for `Fintype`, `Finset`, coinduction, and set
  operations.  The faithful formalization of finite-domain semantics,
  coinductive bisimilarity, and completeness proofs requires this support.
- See `docs/ARCHITECTURE.md` for detailed design decisions.

## Next session task (exact)

**Phase 2 — DyNetKAT syntax & operational semantics.**

Create:
1. `lean/DyNetKAT/DyNetKAT/AST.lean` — DyNetKAT process syntax (Fig. 5) with
   deadlock, policy sequencing, send/receive, rcfg, parallel, choice,
   recursion variables.
2. `lean/DyNetKAT/DyNetKAT/Config.lean` — configurations `(d, H, H′)` as
   a structure with pending and handled packet lists.
3. `lean/DyNetKAT/DyNetKAT/Action.lean` — labels γ:
   `(σ,σ′) | x?r | x!r | rcfg(x,r)`.
4. `lean/DyNetKAT/DyNetKAT/Semantics.lean` — labeled small-step SOS (Fig. 8).
