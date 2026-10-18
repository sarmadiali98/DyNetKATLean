# NETKAT_AUDIT.md — Audit of NetKAT Phase 1.5 Implementation

**Audit date:** 2026-10-16 (Phase 1.5) / 2026-10-17 (Task 2N)
**Repository:** `/Users/ali/Desktop/DyNetKAT-Lean`
**Paper:** *DyNetKAT: An Algebra of Dynamic Networks*, arXiv:2102.10035v4 (FoSSaCS 2022)
**Scope:**
- Phase 1.5: NetKAT semantic core — `Packet.lean`, `AST.lean`, `Semantics.lean`, Python tests.
- Task 2N: Complete-Test Conformance Audit — Definition 4 (Complete Tests & Assignments), p. 8.

---

## 0. Task 2N — Complete-Test Conformance Audit (Definition 4)

**Task date:** 2026-10-17
**Task ID:** 2N
**Objective:** Verify that `CompleteTest` and `CompleteAssignment` faithfully implement Definition 4 of the paper.

### 0.1 Exact paper definition

**Definition 4 (Complete Tests & Assignments [2], p. 8), verbatim:**

> "Let F = {f₁, . . . , fₙ} be a set of field names with values in Vᵢ, for i ∈ {1, . . . , n}.
> We call *complete test* (typically denoted by α) an expression f₁=v₁ · . . . · fₙ=vₙ, with vᵢ ∈ Vᵢ, for i ∈ {1, . . . , n}.
> We call *complete assignment* (typically denoted by π) an expression f₁←v₁ · . . . · fₙ←vₙ, with vᵢ ∈ Vᵢ, for i ∈ {1, . . . , n}.
> We sometimes write σα to denote the network packet whose fields are assigned the corresponding values in α; symmetrically for σπ."

**Key requirements derived from Definition 4:**
1. A complete test α assigns **exactly one value** to **every** field (total valuation).
2. A complete assignment π overwrites **every** field (total transformation).
3. The notation σα / σπ treats α and π as *valuations* (functions F → Vᵢ) applied to a packet σ.
4. Complete tests and general predicates (Figure 3: `Pr ::= 0 | 1 | f=v | Pr+Pr | Pr·Pr | ¬Pr`) are **distinct** concepts.

**Context from the paper (Lemma 5, p. 647):** "Let A be the set of all complete tests, and Π be the set of all complete assignments. ... Consequently, A and Π are finite." — The finiteness of A and Π follows from the finiteness of each Vᵢ.

### 0.2 Corresponding Lean definitions (as of Task 2R-L, 2026-10-17)

| Paper concept | Lean definition | File:Line |
|---|---|---|
| Complete test α (`f₁=v₁ · ... · fₙ=vₙ`, total valuation) | `def CompleteTest := CtxPkt` | `Packet.lean:193` |
| Complete assignment π (`f₁←v₁ · ... · fₙ←vₙ`, total valuation) | `def CompleteAssignmentValuation := CtxPkt` | `Packet.lean:253` |
| α holds on σ (all fields match) | `def holdsComplete (alpha sigma) := forall f, alpha f = sigma f` | `Packet.lean:204` |
| Apply π to σ (⟦π⟧(σ) = π) | `def applyValuation (pi sigma) := pi` | `Packet.lean:268` |
| ⟦α⟧ = {(σ,σ) \| α holds on σ} | `.completeTest α => holdsComplete α σ ∧ σ = τ` | `Semantics.lean:67` |
| ⟦f←v⟧ = {(σ, σ[f:=v])} (primitive single-field assignment) | `.assign1 f v => τ = Packet.update σ f v` | `Semantics.lean:68` |
| ⟦completeAssignExpr π⟧(σ,τ) ↔ τ = π (complete assignment semantics) | `completeAssignExpr_sem` theorem | `Semantics.lean:635` |
| AST constructor for α | `completeTest : CompleteTest → NetKAT` | `AST.lean:93` |
| AST constructor for f←v (primitive) | `assign1 : FieldName → FieldValueEnum → NetKAT` | `AST.lean:94` |
| Build complete assignment π as compound expression | `completeAssignExpr : CompleteAssignmentValuation → NetKAT` | `AST.lean:137` |

**Legacy types removed (Task 2R-K):** `CompleteAssignment := CtxPkt → CtxPkt`
and `applyAssign` have been removed from `Packet.lean`. Only a comment at
`Packet.lean:239` documents their removal. No active code references remain.

The concrete packet type is `CtxPkt := Packet FieldName FieldValueEnum` where
- `FieldName` is a 4-element inductive type (`tpSrc`, `tpDst`, `swId`, `port`) with `[Fintype FieldName]` (`Packet.lean:117-129`).
- `FieldValueEnum` is a 4-element inductive type (`v0`, `v1`, `v8`, `v9`) with `[Fintype FieldValueEnum]` (`Packet.lean:132-144`).

### 0.3 Correspondence check

#### 0.3.1 Complete tests — equivalent ✅

**Paper:** α = `f₁=v₁ · ... · fₙ=vₙ` — every field assigned exactly one value.
**Lean:** `CompleteTest := CtxPkt = FieldName → FieldValueEnum` — a total function from fields to values.

The total-function representation **enforces** totality by construction: there is no
way to construct a `CompleteTest` that leaves a field unspecified or assigns
conflicting values. The `holdsComplete` function checks `forall f, alpha f = sigma f`,
which is exactly the paper's semantics: α holds on σ iff every field value matches.

**Mathematical equivalence:** ✅ The set of total functions `FieldName → FieldValueEnum`
is in bijection with the set of complete test expressions `f₁=v₁ · ... · fₙ=vₙ`
(each function corresponds to exactly one such expression, and vice versa).
The representation is faithful and introduces **no additional assumptions**.

#### 0.3.2 Complete assignments — fully conformant ✅ (as of Task 2R-L, 2026-10-17)

**Paper:** π = `f₁←v₁ · ... · fₙ←vₙ` — overwrites every field. The notation σπ
denotes the packet resulting from applying π to σ. A complete assignment is a
specific *syntactic form* that always overwrites all fields, implemented as a
sequence of primitive single-field assignments per the PA axioms.

**Lean:** The legacy `CompleteAssignment := CtxPkt → CtxPkt` (arbitrary function
superset) has been **removed**. It is replaced by:
- `CompleteAssignmentValuation := CtxPkt` — a total valuation `FieldName → FieldValueEnum`,
  the direct dual of `CompleteTest`. By construction, every field maps to exactly
  one value, matching Definition 4.
- `applyValuation (pi sigma) := pi` — returns the valuation π itself, matching
  Definition 4's σπ = π ("the result equals the valuation").
- `completeAssignExpr (π)` — builds `assign1 f₀ (π f₀) ; assign1 f₁ (π f₁) ; ...`
  from the `fieldEnum` enumeration, implementing `f₁←v₁ · ... · fₙ←vₙ`.
- `completeAssignExpr_sem` — proves `⟦completeAssignExpr π⟧(σ,τ) ↔ τ = π`.

The paper-faithful representation treats π as a valuation (field → value), and
σπ is the packet where every field is overwritten to π's value. No completeness
invariant is needed — the total-function type enforces it by construction.

**Assessment:** ✅ Fully conformant. The superset issue is eliminated. All
assignment theorems are proven with no `sorry`/`admit`/`axiom`.

#### 0.3.3 Single-field assignments — primitive constructor `f←v` ✅ (as of Task 2R-L, 2026-10-17)

The legacy `fieldAssign` helper (`AST.lean` old lines 112-113) has been **removed**.
It is replaced by the paper's primitive single-field assignment constructor:

- `assign1 : FieldName → FieldValueEnum → NetKAT` (`AST.lean:94`) — the paper's
  `f←n` basic term per Figure 3 (p. 5).
- Semantics: `| .assign1 f v => τ = Packet.update σ f v` (`Semantics.lean:68`) —
  matches the paper's `⟦f←v⟧ = {(σ, σ[f:=v])}`.

A single-field assignment `f←v` is a **distinct syntactic category** from complete
assignments π per Definition 4. Complete assignments are built as sequences of
`assign1` operations via `completeAssignExpr`, matching the paper's normal-form
decomposition: `f₁←v₁ · ... · fₙ←vₙ = (f₁←v₁);...;(fₙ←vₙ)` per the PA axioms
(Figure 4).

#### 0.3.4 Complete tests and general predicates — distinct ✅

The implementation correctly maintains the paper's distinction:
- `Predicate` inductive (`AST.lean:37-44`): `pFalse`, `pTrue`, `pFieldEq`, `pAnd`, `pOr`, `pNot` — matches Figure 3.
- `CompleteTest` is a separate type (`CtxPkt`, a total function).
- The `NetKAT` AST has **separate constructors**: `test : Predicate → NetKAT` (line 92) and `completeTest : CompleteTest → NetKAT` (line 93).
- The `holdsFinset` legacy path (`Packet.lean:182`) is **not used** in `Semantics.lean` — only `holdsComplete` is referenced (line 67).

**Assessment:** ✅ No conflation. General predicates and complete tests remain distinct types.

#### 0.3.5 Total-valuation representation preserves paper meaning ✅

- `holdsComplete`: `forall f, alpha f = sigma f` — exactly the paper's "α holds on σ iff all field values match."
- `applyValuation`: `pi sigma := pi` — exactly the paper's `σπ` notation (π applied to σ, output equals π).
- Semantics: `.completeTest α => holdsComplete α σ ∧ σ = τ` — matches `⟦α⟧ = {(σ,σ) | α holds on σ}`.
- Semantics: `⟦completeAssignExpr π⟧(σ,τ) ↔ τ = π` — matches `⟦π⟧ = {(σ, π)}` (σπ = π); proven by `completeAssignExpr_sem` theorem.

**Assessment:** ✅ The total-valuation representation preserves the paper's meaning for complete tests and complete assignments. The `holdsComplete_iff_eq` theorem (`Packet.lean:218`) establishes the proven correspondence: a complete test α holds on σ iff σ = α. For complete assignments, `applyValuation` and `completeAssignExpr_sem` establish σπ = π (the result of a complete assignment equals the valuation itself, independently of the input packet). No conflation between total valuations and arbitrary functions remains.

### 0.4 Missing proof obligations

| # | Obligation | Paper reference | Status |
|---|---|---|---|
| 1 | `Fintype CtxPkt` instance | Lemma 5: "A and Π are finite" | **Satisfied** — `instance : Fintype CtxPkt` at `Packet.lean:158-161` (established by Task 2S); `Fintype CompleteTest` and `Fintype CompleteAssignmentValuation` instances also registered at `Packet.lean:198-200` and `Packet.lean:258-260` |
| 2 | `Fintype CompleteTest` (finite A) | Lemma 5: "A is finite" | **Satisfied** — `instance : Fintype CompleteTest` at `Packet.lean:198-200`, obtained by transferring `Fintype CtxPkt` along `CompleteTest = CtxPkt` |
| 3 | `Fintype CompleteAssignmentValuation` (finite Π) | Lemma 5: "Π is finite" | **Satisfied** — `instance : Fintype CompleteAssignmentValuation` at `Packet.lean:258-260`, obtained by transferring `Fintype CtxPkt` along `CompleteAssignmentValuation = CtxPkt` |
| 4 | Completeness invariant for complete assignments | Definition 4: π = `f₁←v₁ · ... · fₙ←vₙ` | **Satisfied (by construction)** — `CompleteAssignmentValuation := CtxPkt` (a total valuation) enforces one-value-per-field by type, and `applyValuation pi _sigma := pi` directly returns π, matching σπ = π |
| 5 | Equivalence of `CompleteTest` representation ↔ Definition 4 | Definition 4 | **Proven** — `holdsComplete_iff_eq` (`Packet.lean:218`) establishes that a complete test α holds on σ iff σ = α, confirming exactly-one-packet-matching semantics |
| 6 | Each complete test specifies exactly one value per field | Definition 4: "vi ∈ Vi for i ∈ {1,...,n}" | **Proven (by construction + theorem)** — `CompleteTest := CtxPkt` (total function `FieldName → FieldValueEnum`) enforces one value per field; `holdsComplete_iff_eq` confirms uniqueness |

### 0.5 Actual semantic discrepancies

| # | Discrepancy | Severity | Paper reference | Lean location |
|---|---|---|---|---|
| 1 | `holdsFinset` (legacy `Finset FieldEq` path) conflates predicate `1` with complete test | Low (not used in semantics) | Definition 4 | `Packet.lean:182` |
| 2 | `holdsFinset` empty-set-as-true behavior | Low (not used in semantics) | Definition 4 | `Packet.lean:182` |

> **Note on resolved discrepancies (Task 2R-L):** The legacy `CompleteAssignment := CtxPkt → CtxPkt` (arbitrary function superset, old `Packet.lean:177`) and `fieldAssign` (old `AST.lean:112-113`) were both **removed** as part of the assignment conformance migration (Task 2R-K). The current `CompleteAssignmentValuation := CtxPkt` (total valuation at `Packet.lean:253`) enforces totality by construction. The `Fintype CtxPkt` instance (`Packet.lean:158-161`) was also established (Task 2S). These are no longer discrepancies.

### 0.6 Conclusions

1. **Complete tests are faithfully implemented** ✅ — The total-function
   representation (`CompleteTest := CtxPkt`) enforces exactly-one-value-per-field
   by construction, matching Definition 4. `holdsComplete` correctly checks
   all fields. The `holdsComplete_iff_eq` theorem (`Packet.lean:218`) proves the
   key correspondence: α holds on σ iff σ = α. No additional assumptions are introduced.

2. **Complete assignments are faithfully represented** ✅ —
   The legacy `CompleteAssignment := CtxPkt → CtxPkt` (arbitrary function superset)
   has been removed. The replacement `CompleteAssignmentValuation := CtxPkt` (total
   valuation at `Packet.lean:253`) is the direct dual of `CompleteTest` and enforces
   one-value-per-field by construction. Its semantics (`completeAssignExpr_sem`,
   `Semantics.lean:635`) proves `⟦completeAssignExpr π⟧(σ,τ) ↔ τ = π`, matching
   Definition 4's σπ = π. `applyValuation pi _sigma := pi` (`Packet.lean:268`)
   directly returns π, confirming the output depends only on π, not σ.

3. **Complete tests and general predicates are distinct** ✅ — Separate `Predicate`
   (inductive, `AST.lean:37-44`) and `CompleteTest` (total valuation) types with
   separate AST constructors (`test` at `AST.lean:92`, `completeTest` at `AST.lean:93`).
   No conflation. The only legacy artifact is `holdsFinset` (`Packet.lean:182`),
   which is retained as a backward-compatibility helper but is **not used** in the
   active semantics (`Semantics.lean:67` uses `holdsComplete`).

4. **No missing assumptions for complete tests** ✅ — The representation introduces
   no assumptions absent from Definition 4 for complete tests. The `Fintype` instances
   for `CtxPkt`, `CompleteTest`, and `CompleteAssignmentValuation` are all registered
   (`Packet.lean:158-200, 258-260`), satisfying the finiteness requirement of
   Lemma 5 for the finite (4×4) concrete domain.

5. **Finite-domain infrastructure** ✅ — The `[Fintype CtxPkt]` instance
   (`Packet.lean:158-161`) is established. However, the star-termination theorem
   (`star_terminates` — proof that `StarClosure` stabilizes in ≤ `|CtxPkt|²` steps on
   a finite domain) is **not yet proven**. This is a separate obligation from
   complete-test representation and remains deferred.

---

## 1. Summary of Changes (as of Task 2R-L, 2026-10-17)

The repository has one commit (`0393869`, "Phase 1: Implement NetKAT semantic core")
plus uncommitted working-tree changes implementing the Phase 1.5 NetKAT semantic core
and the assignment conformance migration (Tasks 2O–2R-L):

| File | Status | Summary of Changes |
|------|--------|--------------------|
| `lean/DyNetKAT/NetKAT/Packet.lean` | Modified | Parameterized `Packet` over generic `FieldType`/`Value`; `CtxPkt` abbreviation; `CompleteTest`/`CompleteAssignmentValuation` as total valuations; `applyValuation`; paper update theorems; examples. Legacy `CompleteAssignment`/`applyAssign` removed. |
| `lean/DyNetKAT/NetKAT/AST.lean` | Modified | `Predicate` inductive (pFalse, pTrue, pFieldEq, pAnd, pOr, pNot); `assign1` primitive constructor; `fieldEnum`; `completeAssignExpr`; `fieldEnum_complete`/`fieldEnum_nodup` theorems. Legacy `fieldAssign` and `.assign` constructor removed. |
| `lean/DyNetKAT/NetKAT/Semantics.lean` | Modified | `Semantics` over `CtxPkt`; predicate/completeTest/assign1 semantics; Kleene/Boolean/packet algebra theorems; `assign1_sem`, `assign1_seq_sem`, `assign_list_sem`, `fieldEnum_updates_complete`, `completeAssignExpr_sem`. Legacy `.assign` clause and `assign_sem`/`fieldAssign_sem` removed. |
| `docs/DESIGN_ALARMS.md` | Modified | A2–A6 recorded; A7 recorded (Open), marked Resolved by Task 2R-L evidence. |
| `docs/NETKAT_AUDIT.md` | Modified | Updated for conformance verification. |

**No changes** to `python/tests/test_netkat.py` or `python/pyproject.toml`.

---

## 2. Build Status

`lake build DyNetKAT` — **SUCCESS** (exit code 0). Build completes successfully:

```
✔ [540/541] Built DyNetKAT
Build completed successfully.
```

### Build warnings (non-fatal, pre-existing, not introduced by Task 2R-L)

- `AST.lean` dupNamespace linter warnings (all `NetKAT` constructors) — pre-existing.
- `Semantics.lean:586` unused variable `h` — pre-existing in `test_assign_same_field`.
- `git diff --check` reports a new blank line at EOF in `Semantics.lean:656` —
  pre-existing, not introduced by Task 2R-L.

---

## 3. Paper-to-Lean Conformance Audit

### 3.1 Packet Model

**Question:** Is the packet model generic, or still restricted to four fields and four values?

**Paper (Definition 1, p. 5):** "Let F = {f1,...,fn} be a set of field names fi with i ∈ {1,...,n}. We call network packet a function in F → ℕ." The paper says values are in finite domains; it does **not** fix 4 fields or 4 values.

**Current implementation:** The previous agent parameterized the *foundation*:
- `def Packet (FieldType : Type) (Value : Type) := FieldType -> Value` (generic)  ✅
- `namespace Packet` with generic `get`, `update`, `ext`, and update theorems over `{FieldType Value : Type}`.  ✅
- A concrete test fixture: `inductive FieldName` (tpSrc, tpDst, swId, port), `inductive FieldValueEnum` (v0, v1, v8, v9), `abbrev CtxPkt := Packet FieldName FieldValueEnum`.  ✅

**Classification:** ***Already corrected by previous agent.***

The parameterization follows the paper's abstraction. The concrete 4×4 instance
is retained only as a test fixture (matching the design decision in A2).

However, the paper notes per-field value domains (`Vi`), whereas the implementation
uses a single `Value` type for all fields. This is a minor simplification — the
finiteness argument applies equally — but should be documented.

> **Note:** The `Fintype` instances for `FieldName` and `FieldValueEnum` exist,
> but there is no `Fintype CtxPkt` instance (finiteness of the packet domain,
> required for star termination). This was flagged in the original alarms as
> "Open" and remains so.

### 3.2 Complete Tests (Definition 4, p. 8)

**Question:** Are complete tests guaranteed to specify exactly one value for every field?

**Paper (Definition 4, p. 8):** "We call *complete test* ... an expression f₁=v₁ · … · fₙ=vₙ, with vi ∈ Vi, for i ∈ {1,...,n}." A complete test is a **total valuation** — every field gets exactly one value.

**Current implementation:**
- `def CompleteTest := CtxPkt` — represented as a total function `FieldName → FieldValueEnum`.  ✅
- `def holdsComplete (alpha : CtxPkt) (sigma : CtxPkt) : Prop := forall f, alpha f = sigma f` — checks all fields.  ✅

The representation as a total function **enforces** totality by construction —
there is no way to construct a `CompleteTest` that leaves a field unspecified.

**Legacy helper `holdsFinset`:** The `holdsFinset` function (`Packet.lean:182`)
is a **legacy** helper that operates on `Finset FieldEq` (a set of field=value
pairs), not on `CompleteTest`. It is a partial (non-total) test predicate: an
empty `Finset` is treated as the predicate `true` (matching all packets), which
is **not** a complete test per Definition 4 (which requires totality). This
`holdsFinset` helper is retained for backward compatibility but is **not used**
in the active NetKAT semantics — `Semantics.lean:67` uses `holdsComplete` for
`.completeTest`. The `Predicate` inductive (`AST.lean:37-44`) is the proper
typed representation for non-complete predicates including `f=v` tests.

**Classification:** ***Canonical representation is `CompleteTest := CtxPkt`** ✅
— A total function `FieldName → FieldValueEnum` enforcing totality by
construction. `holdsComplete_iff_eq` (`Packet.lean:218`) proves the
one-to-one correspondence: α holds on σ iff σ = α.

### 3.3 Predicate Syntax (Figure 3, p. 5)

**Question:** Are predicate negation, conjunction, disjunction, true, and false represented?

**Paper (Figure 3, p. 5):** `Pr ::= 0 | 1 | Pr+Pr | Pr·Pr | ¬Pr` — predicates include false (0), true (1), disjunction (+), conjunction (·), and negation (¬).

**Current implementation:**
- `inductive Predicate | pFalse | pTrue | pFieldEq | pAnd | pOr | pNot`  ✅
- `def eval (Pr : Predicate) (σ : CtxPkt) : Bool` with full semantics.  ✅
- Boolean algebra lemmas: `not_not`, `excluded_middle`, `contra`, `deMorgan_or`, `deMorgan_and`.  ✅

**Classification:** ***Already corrected by previous agent.***

The paper's `Pr ::= 0 | 1 | Pr+Pr | Pr·Pr | ¬Pr` does not explicitly list `f=v` as
a predicate constructor (it's a shorthand), but the implementation correctly
makes `pFieldEq` an atomic predicate, which matches the paper's usage where
`f=v` is a basic predicate.

### 3.4 NetKAT AST (dup-free fragment)

**Question:** Does the AST cover the required dup-free NetKAT syntax?

**Paper (Eq. 1, p. 6; §I-B):** `N ::= 0 | 1 | f=v | f←n | α | π | N + N | N·N | N*`
(DyNetKAT uses NetKAT⁻ᵈᵘᵖ, i.e., without `dup`).

**Current implementation:**
```lean
inductive NetKAT
  | drop             : NetKAT                  -- 0
  | id               : NetKAT                  -- 1
  | test             : Predicate → NetKAT      -- Pr (general predicate)
  | completeTest     : CompleteTest → NetKAT  -- α (complete test)
  | assign1          : FieldName → FieldValueEnum → NetKAT  -- f←v (primitive single-field assignment)
  | union            : NetKAT → NetKAT → NetKAT  -- N + N
  | seq              : NetKAT → NetKAT → NetKAT  -- N ; N
  | star             : NetKAT → NetKAT          -- N *
```

The legacy `.assign` constructor (which took arbitrary `CtxPkt → CtxPkt` functions)
has been **removed** (Task 2R-J). Complete assignments π are now represented as
total valuations (`CompleteAssignmentValuation := CtxPkt`) that are compiled to
NetKAT expressions via `completeAssignExpr`, which builds a sequence of `assign1`
operations for every field.

**Classification:** ***Conformant** ✅. The AST includes the paper's primitive
`f←v` (`assign1`) as a basic NetKAT term, and complete assignments are represented
as total valuations (not arbitrary functions).

### 3.5 Denotational Semantics

**Question:** Does the denotational semantics match the paper?

**Paper (Figure 3, p. 5–6; §I-B "Semantics"):**
- `⟦0⟧ = ∅`
- `⟦1⟧ = {(σ,σ)}`
- `⟦f=n⟧ = {(σ,σ) | σ(f) = n}` — but the paper's full semantics operates on **histories** `h ∈ H`, with `⟦N⟧ : N → (H → 𝒫(H))`
- `⟦¬a⟧(h) = {h} \ ⟦a⟧(h)`
- `⟦α⟧ = ∩_{f=v ∈ α} ⟦f=v⟧` (conjunction of field tests)
- `⟦π⟧ = {(σ, π(σ))}`
- `⟦N₁+N₂⟧ = ⟦N₁⟧ ∪ ⟦N₂⟧`
- `⟦N₁·N₂⟧ = ⟦N₁⟧ • ⟦N₂⟧` (relational composition)
- `⟦N*⟧ = ⋃ₖ⟦N⟧ᵏ` (reflexive-transitive closure)

**Current implementation:**
```lean
def Semantics (N : NetKAT) : CtxPkt → CtxPkt → Prop :=
  match N with
  | .drop => False
  | .id => σ = τ
  | .test Pr => Pr.holds σ ∧ σ = τ
  | .completeTest α => holdsComplete α σ ∧ σ = τ
  | .assign1 f v => τ = Packet.update σ f v
  | .union n₁ n₂ => Semantics n₁ σ τ ∨ Semantics n₂ σ τ
  | .seq n₁ n₂ => ∃ ρ, Semantics n₁ σ ρ ∧ Semantics n₂ ρ τ
  | .star n => StarClosure (Semantics n) σ τ
```

**Findings:**

| Semantic clause | Paper | Current | Match? |
|---|---|---|---|
| `⟦0⟧` | ∅ | `False` | ✅ |
| `⟦1⟧` | `{(σ,σ)}` | `σ = τ` | ✅ |
| `⟦f=v⟧` | `{(σ,σ) \| σ(f)=v}` | `Pr.holds σ ∧ σ=τ` (via `.test (.pFieldEq ...)`) | ✅ |
| `⟦¬a⟧` | `{h} \ ⟦a⟧(h)` | `¬Pr.holds σ ∧ σ=τ` | ✅ (for single-packet semantics) |
| `⟦α⟧` | `∩_{f=v∈α} ⟦f=v⟧` | `holdsComplete α σ ∧ σ=τ` | ✅ (`holdsComplete` checks all fields) |
| `⟦f←v⟧` | `{(σ, σ[f:=v])}` | `τ = Packet.update σ f v` (`.assign1`) | ✅ |
| `⟦π⟧` | σπ = π (overwrite all fields) | `completeAssignExpr π` → proven `⟦⟧(σ,τ) ↔ τ = π` | ✅ (`completeAssignExpr_sem`) |
| `⟦N₁+N₂⟧` | `⟦N₁⟧ ∪ ⟦N₂⟧` | `∨` | ✅ |
| `⟦N₁·N₂⟧` | relational composition | `∃ ρ, ... ∧ ...` | ✅ |
| `⟦N*⟧` | `⋃ₖ ⟦N⟧ᵏ` | `StarClosure (Semantics n)` | ✅ |

**Classification:** ***Conformant** ✅. All semantic clauses match the paper. The
build succeeds and all theorems are machine-checked with no proof holes.

### 3.6 Kleene Star as Unbounded Closure

**Question:** Is Kleene star represented as unbounded closure?

**Paper:** `⟦N*⟧ = ⋃ₖ⟦N⟧ᵏ` — reflexive-transitive closure. On finite domains this is finite.

**Current implementation:**
```lean
inductive StarClosure {α : Type} (R : α → α → Prop) : α → α → Prop
  | refl : ∀ a, StarClosure R a a
  | step : ∀ {a b c}, R a b → StarClosure R b c → StarClosure R a c
```
This is the standard inductive reflexive-transitive closure — the correct
representation of `⋃ₖ⟦N⟧ᵏ`.  ✅

**Classification:** ***Conformant.***

The star is correctly represented as inductive reflexive-transitive closure.
On a finite packet domain, this terminates (finite number of distinct paths).

### 3.7 Paper Example — `(tp_src = 8);drop`

**Paper reference:** §I-A (running example). The policy `(tp_src = 8);drop`
drops packets with `tp_src = 8` and passes others (the test fails → drop).

**Lean:** `def examplePolicy : NetKAT := .seq tpSrc8Test .drop` where
`tpSrc8Test := .test (.pFieldEq ⟨.tpSrc, .v8⟩)`.

**Python:** `semantics_seq(lambda p: semantics_test(test, p), semantics_drop, p8)`
returns `set()` for `p8` with `tp_src = 8` (test passes, then drop produces ∅).

**Classification:** ***Conformant.***

Both implementations correctly model `(tp_src = 8);drop` as: packets with
`tp_src = 8` are dropped (test passes → drop → ∅), packets with `tp_src ≠ 8`
are also dropped (test fails → ∅). Result is always ∅, matching the paper.

> **Note:** The Python `CompleteTest.holds` treats empty constraints as `True`
> (passes on all packets). This is the paper's predicate `1`, not a complete
> test. The Lean implementation distinguishes these via the separate
> `Predicate` type (with `pTrue`) and `CompleteTest` (total valuation).

---

## 4. Remaining Discrepancies and Unresolved Issues (as of Task 2R-L, 2026-10-17)

### 4.1 Build status

`lake build DyNetKAT` — **SUCCESS** (exit code 0). Build completed successfully.
No compilation errors or proof holes remain. The audit sections below describe
the state **after** the assignment conformance migration (Tasks 2O–2R-L).

### 4.2 Build warnings (non-fatal, pre-existing, not introduced by this task)

| Issue | File:Line | Notes |
|---|---|---|
| `git diff --check` | `Semantics.lean:656` | New blank line at EOF (pre-existing) |
| dupNamespace linter warnings | `AST.lean` (all `NetKAT` constructors) | Pre-existing; do not repair per instructions |
| Unused variable `h` | `Semantics.lean:586` | Pre-existing in `test_assign_same_field` |

### 4.3 Semantic concerns (not build-breaking)

| Issue | Paper Reference | Status |
|---|---|---|
| `holdsFinset` (legacy helper, not a complete test) | Definition 4, p. 8 | **Retained but isolated** — legacy `Finset FieldEq`-based helper for partial field-value tests; not used in `.completeTest` semantics (only `holdsComplete` is referenced at `Semantics.lean:67`). This is a non-canonical helper, not a parallel representation of complete tests. |
| Per-field value domains `Vi` vs. single `Value` | Definition 1, p. 5 | **Minor simplification** — documented, acceptable |
| Semantics over single packets vs. histories | Figure 3, p. 181 | **Equivalent for dup-free** — documented in comments at `Semantics.lean:20-25` |

### 4.4 What remains for Lemma 5 (NOT addressed by Task 2R-L)

- Lemma 5 (normal forms) is the Phase 1 deliverable but is **not yet implemented**.
- `[Fintype CtxPkt]` instance **is established** (`Packet.lean:158-161`); however,
  the star-termination theorem (`star_terminates` — proof that `StarClosure`
  stabilizes in ≤ `|CtxPkt|²` steps) is not yet proven, blocking computable star
  evaluation and normalization of star terms.

---

## 5. Paper Conformance Summary (as of Task 2R-L, 2026-10-17)

| Audit Item | Paper Requirement | Current Status | Classification |
|---|---|---|---|
| 1. Packet model generic? | Definition 1: parameterized over finite fields | Parameterized `Packet F V` + concrete fixture | **Conformant** ✅ |
| 2. Complete tests total? | Definition 4: every field assigned a value | `CompleteTest := CtxPkt` (total function) | **Conformant** ✅ |
| 3. Predicate negation/conj/disj? | Figure 3: `Pr ::= 0\|1\|Pr+Pr\|Pr·Pr\|¬Pr` | Full `Predicate` inductive + eval | **Conformant** ✅ |
| 4. Primitive `f←v` constructor? | Figure 3: `N ::= ... \| f←n \| ...` | `assign1 : FieldName → FieldValueEnum → NetKAT` | **Conformant** ✅ |
| 5. Complete assignments as total valuations? | Definition 4: π = `f₁←v₁ · ... · fₙ←vₙ` | `CompleteAssignmentValuation := CtxPkt`; `applyValuation`; `completeAssignExpr` | **Conformant** ✅ |
| 6. Complete-assignment semantics proven? | Definition 4: σπ = π | `completeAssignExpr_sem` proves `⟦completeAssignExpr π⟧(σ,τ) ↔ τ = π` | **Proven** ✅ |
| 7. Single-field assignment semantics? | Figure 3: `⟦f←v⟧ = {(σ, σ[f:=v])}` | `assign1_sem`: `⟦assign1 f v⟧(σ,τ) ↔ τ = Packet.update σ f v` | **Proven** ✅ |
| 8. No arbitrary packet-function constructor? | Definition 4: π is a valuation, not arbitrary function | Legacy `.assign` constructor **removed**; no `assign` in `NetKAT` inductive | **Eliminated** ✅ |
| 9. Semantics match paper? | Figure 3 | All clauses match; build succeeds | **Conformant** ✅ |
| 10. Star as unbounded closure? | Figure 3: `⋃ₖ⟦N⟧ᵏ` | `StarClosure` inductive rtc | **Conformant** ✅ |
| 11. `Fintype` for finiteness? | Lemma 5: "A and Π are finite" | `[Fintype CtxPkt]` at `Packet.lean:158-161`; `Fintype CompleteTest`/`Fintype CompleteAssignmentValuation` also registered | **Established** ✅ |

---

## 6. Recommendations (as of Task 2R-L)

### 6.1 Completed (assignment conformance)

All assignments in the previous (stale) recommendations have been addressed:
- ✅ Legacy `CompleteAssignment := CtxPkt → CtxPkt` and `applyAssign` removed.
- ✅ `assign1` constructor added as paper primitive `f←v`.
- ✅ `CompleteAssignmentValuation := CtxPkt` (total valuation) as sole representation.
- ✅ `completeAssignExpr` builds compound assignments from `assign1`.
- ✅ `completeAssignExpr_sem`, `assign1_sem`, `assign_list_sem`, `fieldEnum_updates_complete`
  all proven — no `sorry`/`admit`/`axiom`.
- ✅ Build passes (`lake build DyNetKAT` exit code 0).
- ✅ No dangling references to legacy types.

### 6.2 Remaining (out of scope for Task 2R-L)

- Implement Lemma 5 (normal forms) — Phase 1 deliverable, requires `E_NK` derivability relation.
- Prove `star_terminates` — the theorem that `StarClosure` stabilizes in ≤ `|CtxPkt|²` steps on finite domains (blocks computable star evaluation and star-term normalization).

> **Note:** `[Fintype CtxPkt]` (including `Fintype CompleteTest` and `Fintype CompleteAssignmentValuation`) **has been established** (`Packet.lean:158-200, 258-260`) in a subsequent task. This recommendation is retained from the Task 2R-L perspective but is now satisfied.

---

## 7. Build Preservation

**Yes.** The working-tree changes (now compiling successfully) are conceptually
sound and align with the paper. They correctly:

- Parameterize the packet model over generic finite types.
- Introduce the `Predicate` type matching Figure 3.
- Represent `CompleteTest` as a total valuation (`CompleteTest := CtxPkt`).
- Represent `CompleteAssignmentValuation` as a total valuation (dual of `CompleteTest`).
- Add `assign1` as the paper's primitive single-field assignment `f←v`.
- Add `completeAssignExpr` to compose single-field assignments into complete assignments.
- Add Boolean algebra lemmas (BA-EXCL-MID, BA-CONTRA, De Morgan).
- Add Kleene algebra and packet algebra laws.
- Prove `completeAssignExpr_sem`, `assign1_sem`, `assign_list_sem`,
  `fieldEnum_updates_complete` — no `sorry`/`admit`/`axiom`.

The changes should be **preserved as-is**. Do not revert to the Phase 1 base
(committed HEAD), which lacks the `Predicate` type and the complete test/assignment
distinction.

---

## 8. Next Task

**Implement Lemma 5 (normal forms)** — the remaining Phase 1 deliverable.
Requires adding the `[Fintype CtxPkt]` instance (star termination / finite A and Π).
This is out of scope for Task 2R-L per the task restrictions ("Do not begin the
`Fintype CtxPkt` task").