# DESIGN_ALARMS.md - Research / Design Alarms

This file records conflicts between source evidence and implementation
decisions or proof statements.  Alarms must be resolved before the conflicting
work proceeds.

---

| ID | Date | Type | Severity | Title | Status |
|----|------|------|----------|-------|--------|
| A7 | 2026-10-17 | semantic deviation from paper | High | CompleteAssignment admits arbitrary functions; single-field assignments conflated with complete assignments | **Resolved (2026-10-17)** |
| A1 | 2026-10-16 | architecture pressure | Medium | Existing repo is a journal extension, not faithful DyNetKAT | Resolved (decision: start fresh) |

---

## A1 - Existing repository is a journal extension, not faithful DyNetKAT

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
  - `Policy` includes `dup` - paper uses NetKAT⁻ᵈᵘᵖ (dup-free).
  - `Configuration` has a `flowTable` field - paper's config is `(d, H, H′)`.
  - `evalPolicy` uses bounded fuel - paper uses denotational `⟦N⟧`.
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
- (Not recommended) Attempt to adapt the existing code - would require
  extensive rewriting and would conflate the journal extension with the
  original calculus.

**Decision:** Start fresh.  Mark as resolved.

---

## A2 - Discrepancy: Packet model is hardcoded rather than parameterized

**Date:** 2026-10-16

**Type:** Semantic deviation from paper

**Severity:** High - this is a modeling deviation, not a correctness bug

**Paper reference:** Definition 1 (p. 5): "Let F = {f1,...,fn} be a set of field names with values in Vi, for i∈{1,...,n}. We call *network packet* a function in F → ℕ."

**Evidence from paper:**
- Paper p. 5: "we consider network packets with values in finite domains"
- Definition 4 (p. 8): complete tests and assignments use "F = {f1,...,fn} with values in Vi"
- The paper is explicitly parameterized over finite field sets; it does not fix 4 fields or 4 values.

**Current implementation:** `Packet.lean` hardcodes `FieldName` (4 constructors) and `FieldValue` (4 constructors), with `Packet := FieldName → FieldValue`. This is a concrete instance, not the parameterized model the paper requires.

**Impact:** Theorem statements mention `FieldName`/`FieldValue` directly, tying all future results to a specific 4×4 packet domain. The paper's Lemma 5, Definition 4, and all normal-form results must be parameterized.

**Resolution:** Refactor to parameterize over `FieldType : Type` with `[Fintype FieldType]` and `FieldValue : FieldType → Type` with `[∀ f, Fintype (FieldValue f)]`. Keep the concrete 4-field/4-value instance as a test fixture. The `Packet` type becomes `FieldType → ∀ f, FieldValue f` (a dependent function).

**Status:** Open - will be resolved in Phase 1.5 implementation.

---

## A3 - Discrepancy: CompleteTest uses Finset FieldEq without completeness enforcement

**Date:** 2026-10-16

**Type:** Semantic deviation from paper

**Severity:** High

**Paper reference:** Definition 4 (p. 8): "We call *complete test* ... an expression f₁=v₁ · … · fₙ=vₙ, with vi ∈ Vi, for i∈{1,...,n}."

**Evidence from paper:**
- Definition 4 explicitly requires a complete test to assign a value to EVERY field: `f₁=v₁ · … · fₙ=vₙ`.
- The empty expression `⟨⟩` (empty Finset) is NOT a complete test - it is the paper's `Pr` predicate `1` (true), but not a complete test.
- The current `holds` function: `def holds (α : Finset FieldEq) (p : Packet) : Prop := ∀ fe ∈ α, p fe.field = fe.value` - this treats an empty set as "holds on all packets", which is the predicate `true`, NOT a complete test.

**Current implementation:** `CompleteTest := Finset FieldEq` with `holds`. No completeness invariant is enforced. A `test` with 0 or 1 field pairs is allowed and treated as a valid complete test.

**Impact:** The distinction between "general predicate" and "complete test" (which the paper explicitly maintains) is lost. Definition 4 requires complete tests to be total valuations.

**Resolution:** Represent `CompleteTest` as a total packet valuation (`FieldType → ∀ f, FieldValue f`) or enforce a completeness invariant on `Finset FieldEq` (each field appears exactly once). Keep `Predicate` as a separate type for general boolean predicates (including negation). The `holds` function for complete tests should require the test to cover all fields.

**Status:** Open - will be resolved in Phase 1.5 implementation.

---

## A4 - Discrepancy: Missing Boolean predicate syntax (negation, disjunction)

**Date:** 2026-10-16

**Type:** Missing implementation coverage

**Severity:** High

**Paper reference:** Figure 3 (NetKAT syntax): `Pr ::= 0 | 1 | Pr+Pr | Pr·Pr | ¬Pr`

**Evidence from paper:**
- Figure 3 defines NetKAT predicates with: false (`0`), true (`1`), disjunction (`+`), conjunction (`·`), and negation (`¬`).
- The semantics table includes: `⟦¬a⟧(h) ≜ {h} \ ⟦a⟧(h)` (set difference).
- Complete tests `α` are the special case of conjunctions `f₁=v₁ · … · fₙ=vₙ`.

**Current implementation:** The AST has 7 constructors: `drop, id, test, assign, union, seq, star`. There is:
- No `Predicate` type with `false`, `true`, `and`, `or`, `not`.
- `test : Finset FieldEq → NetKAT` represents complete tests (conjunctions), but cannot represent negation or disjunction of predicates.
- While `union` can represent `Pr + Pr` at the policy level, `¬Pr` (predicate negation) has no representation.

**Impact:** Cannot faithfully represent NetKAT predicates as defined in Figure 3. Predicate complement laws (BA-EXCL-MID, BA-CONTRA) cannot be stated or proved.

**Resolution:** Introduce a `Predicate` inductive type with constructors `pFalse`, `pTrue`, `pAnd`, `pOr`, `pNot`, `pFieldEq` (atomic), and an embedding `predToNetKAT : Predicate → NetKAT`. Prove semantic correspondence. Complete tests become a special case (conjunctions over all fields). The current `test` constructor can remain as syntactic sugar for complete tests.

**Status:** Open - will be resolved in Phase 1.5 implementation.

---

## A5 - Discrepancy: Semantics defined over single packets, not histories

**Date:** 2026-10-16

**Type:** Equivalent representation choice

**Severity:** Low - this is a valid simplification for the dup-free fragment

**Paper reference:** Figure 3 (NetKAT Semantics): `⟦N⟧ : N → (H → 𝒫(H))` where `H` is the set of packet histories.

**Evidence from paper:**
- The paper's denotational semantics maps NetKAT policies to `H → 𝒫(H)` (history → set of histories).
- The `cpol_;✓` rule in Fig. 8 uses `⟦p⟧(σ::⟨⟩)` - applying NetKAT semantics to a single-packet history (σ prepended to empty history).
- Lemma 5 (p. 13) works with the dup-free fragment where `G(p) = {αi·πi | i ∈ I}` - no history tracking needed.

**Current implementation:** `Semantics (N : NetKAT) : Packet → Packet → Prop` - a binary relation on single packets, not histories.

**Analysis:** This is a valid equivalence for the dup-free fragment. Without `dup`, histories are always of the form `σ::⟨⟩` (single packet). The operational rule `(cpol_;✓)` confirms: `⟦p⟧(σ::⟨⟩)` is used, evaluating on a single-packet history. The current `Packet → Packet → Prop` semantics is semantically equivalent for NetKAT⁻ᵈᵘᵖ.

**Resolution:** Keep the single-packet semantics but document the correspondence formally: `⟦N⟧(σ) = {σ′ | (σ,σ′) ∈ ⟦N⟧_single}` is equivalent to `{σ'::⟨⟩ | σ'::⟨⟩ ∈ ⟦N⟧_history(σ::⟨⟩)}` when `dup` is absent.

**Status:** Resolved - this is an equivalent representation, not a deviation. Document the correspondence.

---

## A6 - Discrepancy: Missing Boolean algebra axioms and packet algebra axioms

**Date:** 2026-10-16

**Type:** Missing implementation coverage

**Severity:** Medium - needed for Section 6 foundational theorems

**Paper reference:** Figure 4 (NetKAT axioms E_NK): BA-EXCL-MID, BA-CONTRA, PA-MOD-MOD-COMM, PA-MOD-FILTER-COMM, PA-MOD-FILTER, PA-FILTER-MOD, PA-CONTRA, PA-MATCH-ALL, etc.

**Evidence from paper:**
- Figure 4 lists 20+ axioms including Boolean algebra (BA), Kleene algebra (KA), and packet algebra (PA) axioms.
- The current implementation has NO formal axioms or semantic equivalence proofs for these.

**Current implementation:** Only basic lemmas: `drop_empty`, `id_diag`, `union_sem`, `seq_sem`, `star_refl`, `star_step`, `fieldTest_sem`, `fieldAssign_sem`.

**Impact:** Section 6 theorems (Boolean complement laws, assignment overwriting, etc.) cannot be proven without the axiom framework.

**Resolution:** Prove axioms semantically (as lemmas about the denotational semantics) rather than as a separate equational theory. This is sufficient for the Phase 1.5 scope.

**Status:** Open - will be resolved in Phase 1.5 implementation.

---

## A7 - CompleteAssignment admits arbitrary functions; single-field assignments conflated with complete assignments

**Date:** 2026-10-17

**Type:** Semantic deviation from paper

**Severity:** High - affects Definition 4 conformance

**Status:** Resolved (Task 2R-L, 2026-10-17)

**Paper reference:** Definition 4 (p. 8) and Figure 3 (NetKAT Syntax & Semantics, p. 5).

### Paper requirements

**Definition 4 (p. 8), verbatim:**
> "Let F = {f₁,...,fₙ} be a set of field names with values in Vᵢ, for i ∈ {1,...,n}. We call *complete assignment* (typically denoted by π) an expression f₁←v₁ · ... · fₙ←vₙ, with vᵢ ∈ Vᵢ, for i ∈ {1,...,n}. ... We sometimes write σα to denote the network packet whose fields are assigned the corresponding values in α; symmetrically for σπ."

**Key points:**
1. A **complete assignment** π = `f₁←v₁ · ... · fₙ←vₙ` overwrites **every** field.
2. The notation σπ denotes the packet where each field f gets the value π(f) - i.e., π acts as a **valuation** (field → value), not an arbitrary transformation.
3. **Figure 3 (NetKAT Syntax)** lists `f←n` as a basic NetKAT term (`N ::= Pr | f←n | ...`). Single-field assignment `f←n` is distinct from a complete assignment `f₁←v₁ · ... · fₙ←vₙ`.
4. Figure 3 (Semantics): `Jf←nK(σ::h) = {σ[f:=n]::h}` - a single-field assignment changes only field f, leaving all others unchanged.

### Current implementation (pre-correction state - before resolution)

| Paper concept | Lean definition | File:Line |
|---|---|---|
| CompleteAssignment π (overwrites all fields) | `def CompleteAssignment := CtxPkt → CtxPkt` | `Packet.lean:177` (legacy; **removed in Task 2R-K**) |
| Single-field assignment f←v | `def fieldAssign (f v) := .assign (fun σ => Packet.update σ f v)` | `AST.lean:112-113` (legacy; **removed in Task 2R-J**)

### Discrepancy

1. **Superset representation:** `CompleteAssignment := CtxPkt → CtxPkt` admits **arbitrary** functions from packets to packets. Not every such function corresponds to a complete assignment `f₁←v₁ · ... · fₙ←vₙ`. A function could conditionally modify fields based on packet contents, copy one field to another, etc. The paper's π is a **valuation** (field → value), and σπ means "overwrite every field f with π(f)".

2. **Single-field assignments accepted as CompleteAssignment:** `fieldAssign` creates `.assign (fun σ => Packet.update σ f v)`, which updates only **one** field. This function is a `CompleteAssignment` by type, but it is **not** a complete assignment per Definition 4 (it does not overwrite every field). The paper's single-field assignment `f←n` is a separate syntactic category.

### Impact

- The type `CompleteAssignment` does not enforce the "overwrite every field" invariant from Definition 4.
- `fieldAssign` violates the semantic contract: it passes a single-field overwriter where the paper expects a total field valuation.
- No proof obligation ensures that `.assign π` only accepts total field-overwriting functions.

### Recommended minimal correction

**Option 1 (minimal - align with CompleteTest representation):**
Change `CompleteAssignment` from `CtxPkt → CtxPkt` to `CtxPkt` (a total valuation `FieldName → FieldValueEnum`), mirroring `CompleteTest`. Then:
- `σπ` is computed by `fun σ f => π f` (overwrite every field with π's value).
- Semantics: `.assign π => ∀ f, τ f = π f` (or equivalently `τ = π` as a function).
- `fieldAssign` must be either removed or redefined to compose single-field updates into a complete valuation when the context requires it.

**Option 2 (preserve single-field assignment support):**
Keep two separate types:
- `SingleAssignment := FieldName × FieldValueEnum` (for `f←n`).
- `CompleteAssignment := CtxPkt` (a total valuation, same as `CompleteTest`).

The AST `assign` constructor takes `CompleteAssignment`; single-field assignments are represented as NetKAT terms via a separate mechanism (e.g., the paper's `f←n` is part of `N ::= ... | f←n | ...`).

**Paper-faithful position:** The paper's NetKAT syntax (Figure 3) has `f←n` as a basic term with semantics `σ[f:=n]`. Complete assignments `f₁←v₁ · ... · fₙ←vₙ` appear in **normal forms** (Lemma 5, Definition 6), where they are products of single-field assignments. The two are related via the PA axioms (e.g., `f←n · f←n₀ ≡ f←n₀`).

**Recommendation:** Option 1 is the smallest correction that preserves the paper's semantics. Represent `CompleteAssignment` as a total valuation (`CtxPkt`), consistent with `CompleteTest`. This makes σπ = π (as a function), and the semantics becomes `⟦π⟧(σ) = π` (the output packet is π itself, since π defines all field values). This is the direct dual of `CompleteTest`.

### Affected definitions and theorems

| Artifact | File:Line | Impact |
|---|---|---|
| `CompleteAssignment := CtxPkt → CtxPkt` | `Packet.lean:177` | Type changes to `CtxPkt` |
| `applyAssign` | `Packet.lean:185` | Redefine for new type |
| `assign_sem` theorem | `Semantics.lean:224-226` | Proof must change |
| `assign_overwrite` theorem | `Semantics.lean:460-469` | Proof must change (relies on composition of `Packet.update`) |
| `assign_comm_diff` theorem | `Semantics.lean:472-476` | Proof must change |
| `assign_test_same_field` theorem | `Semantics.lean:479-484` | Proof must change |
| `test_assign_same_field` theorem | `Semantics.lean:487-490` | Proof must change |
| `fieldAssign` function | `AST.lean:112-113` | Must be redefined or removed |
| `fieldAssign_sem` theorem | `Semantics.lean:235-238` | Must change or be removed |
| `assign` constructor (AST) | `AST.lean:94` | Parameter type changes |
| `assign` case in `Semantics` | `Semantics.lean:68` | Semantics clause changes |
| Python `semantics_assign` | `python/tests/test_netkat.py:79-81` | Mirror must change |

### Conformance verification (Task 2R-L, 2026-10-17)

The migration to a paper-faithful assignment representation was completed across
Tasks 2O–2R-K. The following evidence confirms Definition 4 and Figure 3 conformance:

**Definitions in place (all verified):**
- `CompleteAssignmentValuation := CtxPkt` (`Packet.lean:253`) - a total valuation
  `FieldName → FieldValueEnum`, the direct dual of `CompleteTest`. Admits only
  total field-overwriting valuations, matching Definition 4's σπ notation.
- `applyValuation (π σ) := π` (`Packet.lean:268`) - the output equals the valuation π
  itself, matching Definition 4's "σπ equals π".
- `assign1 : FieldName → FieldValueEnum → NetKAT` (`AST.lean:94`) - the paper's
  primitive single-field assignment constructor `f←v` (Figure 3, p. 5).
- `fieldEnum : List FieldName` (`AST.lean:137`) - enumerates all fields exactly
  once; proven complete (`fieldEnum_complete`, `AST.lean:150`) and nodup
  (`fieldEnum_nodup`, `AST.lean:156`).
- `completeAssignExpr (π) : NetKAT` (`AST.lean:137`) - composes `assign1 f (π f)`
  for every field via sequential composition, implementing `f₁←v₁ · ... · fₙ←vₙ`.
- Semantics clause `| .assign1 f v => τ = Packet.update σ f v` (`Semantics.lean:68`) -
  matches the paper's `⟦f←v⟧ = {(σ, σ[f:=v])}`.

**Theorems proving correspondence (all verified, machine-checked):**
- `assign1_sem` (`Semantics.lean:263`) - `⟦f←v⟧` maps σ to `σ[f↦v]`.
- `assign1_seq_sem` (`Semantics.lean:277`) - `⟦(f←v);N⟧(σ,τ) ↔ ⟦N⟧(σ[f:=v],τ)`.
- `assign_list_sem` (`Semantics.lean:311`) - fold of `assign1` equals fold of
  `Packet.update`.
- `fieldEnum_updates_complete` (`Semantics.lean:595`) - updating every field to π's
  values yields π, independent of input.
- `completeAssignExpr_sem` (`Semantics.lean:635`) - `⟦completeAssignExpr π⟧(σ,τ) ↔ τ = π`.
- `applyValuation_field` (`Packet.lean:277`) - applying π yields a packet whose
  every field is π's value.

**Legacy representation removed:**
- `CompleteAssignment := CtxPkt → CtxPkt` - removed (`Packet.lean`; only referenced
  in a comment at `Packet.lean:239`).
- `applyAssign` - removed (dead code, no callers).
- `fieldAssign` - removed, superseded by `assign1` (paper primitive).
- `.assign` AST constructor - removed, superseded by `completeAssignExpr`.
- `.assign` semantics clause - removed.
- `assign_sem` theorem - removed, superseded by `completeAssignExpr_sem`.
- `fieldAssign_sem` theorem - removed, superseded by `assign1_sem`.

**Verification results:**
- `lake build DyNetKAT` - SUCCESS (exit code 0). Build completed successfully.
- `git diff --check` - 1 pre-existing warning (`Semantics.lean:656`: new blank
  line at EOF); not introduced by this task.
- Proof-hole scan (`sorry`/`admit`/`axiom` in `.lean` files) - 0 matches
  (only the English word "axioms" appears in comments at `Semantics.lean:353`).

**Classification:** ✅ Conformance established. The assignment implementation
faithfully represents the paper's Definition 4 (complete assignments as total
valuations) and Figure 3 (primitive `f←v` constructor with `σ[f:=v]` semantics).
The legacy arbitrary-function `CompleteAssignment` type and its `applyAssign`
function are fully removed with no dangling references.

**Status:** Resolved - design decision implemented and verified. A7 is now
eligible for closure.
