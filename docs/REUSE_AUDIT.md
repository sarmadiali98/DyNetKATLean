# REUSE_AUDIT.md — Existing Repository Reuse Audit

**Audit target:** `/Users/ali/Desktop/DyNetKAT` (the journal-extension repository).

**Status:** READ ONLY — no files modified.

**Verdict:** The existing repository implements a **log-based journal extension**
of DyNetKAT, not the original calculus.  Its components deviate from the paper
in ways that make direct reuse **inappropriate** for the faithful formalization.
**No components are directly reusable** for the canonical DyNetKAT language.

---

## Component inventory

### A. `lean/DyNetKAT/AST/NetKAT.lean`

**What it contains:**
```lean
inductive Predicate where | true | false | switchEq (switchId : Nat)
  | fieldEq (field : String) (value : Nat) | and | or | not
inductive Policy where | drop | id | test | assign | opaque | union | seq | star | dup
```

**Matches the paper?** No.
- `dup` is included — but the DyNetKAT paper uses **NetKAT⁻ᵈᵘᵖ** (dup-free).
- `switchEq` uses `Nat` for switchId — the paper's packets are functions
  over arbitrary fields.
- `opaque` with `Nat` token — no paper analog.
- No `CompleteTest` / `CompleteAssignment` distinction.
- No finite-domain / Fintype infrastructure.

**Reusability verdict:** NOT reusable.  The entire type is a mismatch.

### B. `lean/DyNetKAT/AST/DyNetKAT.lean`

**What it contains:**
```lean
inductive Message where | unit | policy | opaque
inductive Process where | deadlock | policy | recv | send | choice | seq
  | parallel | recurse | var
```

**Matches the paper?** Partial structure, but significant deviations.
- `recurse (index : Nat) (body : Process)` and `var (index : Nat)` — the paper
  uses named recursive variables `X` with `X ≜ d`.  This indexed approach
  differs.
- Missing: `rcfg(x,r)` as a distinct constant (the repo has `recv`/`send`
  carrying `Message`, but no `rcfg` constructor).
- Missing: `⌊⌊` (left-merge) and `|` (communication-merge) operators.
- Missing: `δ_ℒ(−)` (restriction) and `π_n(−)` (projection).
- `parallel` corresponds to `‖` but the paper also has `| |` (comm-merge).

**Reusability verdict:** NOT reusable — missing critical operators and
uses a different recursion encoding.

### C. `lean/DyNetKAT/Semantics/Basic.lean`

**What it contains:**
- `Packet` structure with `switchId`, `port`, `tpSrc : Nat` fields.
- `evalPolicyFuel` / `evalPolicy`: executable list-based denotation with
  **bounded fuel** for `star` (fuel = 1).
- `Label` type: `packet`, `drop`, `flowUpdate`, `send`, `recv`, `reconfig`.
- `Step` and `ConfigStep` inductive relations.
- `Configuration` with `flowTable`, `pending`, `handled` fields.

**Matches the paper?** No.
- **Deviation 1:** `Configuration` includes a `flowTable : List (Nat × Policy)`
  field.  The paper's configuration is `(d, H, H′)` — **no flow table**.  As
  documented in the existing `RESEARCH_NOTES.md` (p. 17-22): "The repository's
  new explicit `flowTable` is thus an analysis abstraction, not a source-faithful
  state representation; a relation to the paper's recursive process semantics
  remains unproved."
- **Deviation 2:** `Label` uses concrete `(input, output)` packet pairs and
  `flowUpdate sourcePort policy` — the paper's labels are
  `(σ,σ′) | x?r | x!r | rcfg(x,r)`.
- **Deviation 3:** `evalPolicy` is an **executable** evaluator with bounded
  fuel, not a mathematical denotation `⟦N⟧ ⊆ Packet × Packet`.
- **Deviation 4:** The drop case label is `.drop input` — needs paper
  verification.

**Reusability verdict:** NOT reusable.  The semantic model is fundamentally
different.

### D. `lean/DyNetKAT/Safety/Basic.lean`

**What it contains:**
- `UnsafeAction`: `packet (input output)`, `drop input`, `reconfig channel message`.
- `UnsafeTrace`: `action`, `plus`, `seq` (no `*`).
- `head` / `tail` operators (matching the paper's Section V operators).
- `uns` (unsafe) function using bounded `matchFuel`.
- `isNormalForm` checking.
- `violates` function.

**Matches the paper?** Partial.
- The `head`/`tail` operators (Eqs. 29-33) match the paper §V.
- But: `UnsafeTrace` lacks `*`, `true`, and negation sugars from Def 17.
- `actionMatches` uses concrete packet matching, not abstract `α·π`.
- `violates` checks specifically for `.reconfig 0 .unit` — hardcoded, not
  general.
- `uns` is bounded by `trace.length + 1` fuel — a **bounded approximation**,
  not the full semantic map.

**Reusability verdict:** NOT reusable for formal verification.  The
`head`/`tail` operator structure is paper-faithful and may inspire the
Lean representation, but the implementation is bounded/executable, not
mathematical.

### E. Lean project configuration

- `lakefile.toml`: pure Lake, no Mathlib, `name = "dynetkat"`, `version = "0.1.0"`.
- `lean-toolchain`: `leanprover/lean4:v4.19.0`.
- `lake-manifest.json`: empty packages (no external deps).

**Reusability verdict:** The toolchain version (`v4.19.0`) is useful
information.  Consider whether to use the same version or a newer one.

### F. Python `src/dynetkat/`

- `events.py`, `extraction.py`, `causality.py`, `schedule.py`,
  `flow_semantics.py`, `state_safety.py`, etc.
- All implement the journal-specific log-analysis pipeline.

**Reusability verdict:** NOT reusable.  These implement log parsing,
causality graphs, and bounded schedule enumeration — none of which exist
in the original DyNetKAT paper.

### G. `docs/RESEARCH_NOTES.md`

The existing `docs/RESEARCH_NOTES.md` is a valuable **reference document**
that records the authors' understanding of the paper.  It documents:
- Packet model and per-packet consistency.
- Guarded recursion and finite branching.
- Bisimilarity, restriction, projection, AIP.
- Safety framework and FatTree examples.
- Key evidence quotes and ambiguity notes.

**Reusability verdict:** CONCEPTUALLY reusable.  This document provides
a good secondary summary of the paper.  However, it conflates the paper's
original calculus with the journal extension.  Will be used as a cross-
reference only, not copied.

---

## Summary table

| Component / File | Matches paper? | Faithful? | Reusable? | Notes |
|---|---|---|---|---|
| `AST/NetKAT.lean` | No (has `dup`, `opaque`) | No | No | Dup-free fragment needed |
| `AST/DyNetKAT.lean` | Partial | No (missing ops) | No | No rcfg/⌊⌊/| |/δ/π |
| `Semantics/Basic.lean` | No | No (flowTable, fuel) | No | Executable, not denotational |
| `Safety/Basic.lean` | Partial (head/tail) | No (bounded) | No | Bounded approximation |
| Project toolchain | Yes | Yes | Partial | v4.19.0, no Mathlib |
| `docs/RESEARCH_NOTES.md` | Partial | Partial | Reference only | Confers journal extension |
| Python adapters | No | No | No | Log-specific |

## Conclusion

**No Lean or Python components from the existing repository are directly
reusable for the faithful DyNetKAT formalization.**  The existing code
implements a different language (journal log extension) with different
syntax, semantics, and assumptions.

The **paper itself** (`DyNetKAT.pdf`, arXiv:2102.10035v4) is the only source
of truth.  The existing `docs/RESEARCH_NOTES.md` provides a useful secondary
reference for paper understanding, but care must be taken to separate it from
the journal extension content.

The new repository must implement DyNetKAT **from scratch** in Lean 4,
faithful to the paper.
