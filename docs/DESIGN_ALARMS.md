# DESIGN_ALARMS.md — Research / Design Alarms

This file records conflicts between source evidence and implementation
decisions or proof statements.  Alarms must be resolved before the conflicting
work proceeds.

---

| ID | Date | Type | Severity | Title | Status |
|----|------|------|----------|-------|--------|
| A1 | 2026-10-16 | architecture pressure | Medium | Existing repo is a journal extension, not faithful DyNetKAT | Resolved (decision: start fresh) |

---

## A1 — Existing repository is a journal extension, not faithful DyNetKAT

**Date:** 2026-10-16

**Type:** Architecture pressure

**Severity:** Medium

**Expected claim (from task):** Implement the original DyNetKAT calculus
faithfully in Lean 4.

**Evidence:**
- The existing repository at `/Users/ali/Desktop/DyNetKAT` implements a
  journal extension (log-based extraction, SDNRacer-specific causality,
  bounded schedules).  See `REUSE_AUDIT.md`.
- Key deviations from the paper:
  - `Policy` includes `dup` — paper uses NetKAT⁻ᵈᵘᵖ (dup-free).
  - `Configuration` has a `flowTable` field — paper's config is `(d, H, H′)`.
  - `evalPolicy` uses bounded fuel — paper uses denotational `⟦N⟧`.
  - `Label` type differs (concrete packets vs. `(σ,σ′) | x?r | x!r | rcfg(x,r)`).
  - Missing operators: `⌊⌊`, `| |`, `δ_ℒ(−)`, `π_n(−)`, `rcfg_{x,r}` constant.
- The existing `docs/RESEARCH_NOTES.md` confirms these deviations:
  > "The repository's new explicit `flowTable` is thus an analysis abstraction,
  > not a source-faithful state representation; a relation to the paper's
  > recursive process semantics remains unproved."

**Conflict:** The existing code structure differs fundamentally from the
paper's calculus.  Reusing it would require either (a) modifying the paper's
semantics to match the code, or (b) discarding most of the code and
reimplementing from scratch.

**Impacted work:** All syntax, semantics, and proof work in the new repo.

**Interpretations:**
1. The existing repo serves only as a secondary reference for understanding
   the paper's intuition; it must not be treated as authoritative.
2. The new formalization must start from the paper, not from the existing code.

**Resolution options:**
- (Recommended) Start fresh in `/Users/ali/Desktop/DyNetKAT-Lean`.  Use the
  existing repo only as a conceptual reference and for toolchain/version
  information.
- (Not recommended) Attempt to adapt the existing code — would require
  extensive rewriting and would conflate the journal extension with the
  original calculus.

**Decision:** Start fresh.  Mark as resolved.

---

_(Add new alarms above this line as they are discovered.)_
