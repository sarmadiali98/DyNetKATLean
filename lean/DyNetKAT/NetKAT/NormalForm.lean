------------------------------------------------------------------------
-- NetKAT⁻ᵈᵘᵖ normal forms
--
-- Per Lemma 5 (printed p. 13, §III-A) of the DyNetKAT paper
-- (arXiv:2102.10035v4):
--
--   "We call a NetKAT⁻ᵈᵘᵖ policy q in normal form (n.f.) whenever q is of
--   shape  Σ_{α·π ∈ A} α · π  with A = {α_i · π_i | i ∈ I}.
--   For every NetKAT⁻ᵈᵘᵖ policy p there exists a NetKAT⁻ᵈᵘᵖ policy q in
--   n.f. such that  E_NK ⊢ p ≡ q."
--
-- Representation:
--   A normal form is a *finite set* of pairs (α, π), where
--     α ranges over CompleteTest                (total valuations on fields)
--     π ranges over CompleteAssignmentValuation  (total valuations on fields)
--   i.e. a `Finset (CompleteTest × CompleteAssignmentValuation)`.
--
-- Interpretation:
--   Each pair (α, π) translates to the NetKAT term  α · π
--   = NetKAT.seq (NetKAT.completeTest α) (completeAssignExpr π),
--   i.e. a complete test followed by a complete assignment.
--   The whole normal form is the union (Σ) of all such terms.
--   The empty normal form translates to `NetKAT.drop` (0).
--
-- This module ONLY defines the representation and interpretation.
-- It does NOT implement a normalization algorithm or prove Lemma 5.
-- It does NOT define G(p).
------------------------------------------------------------------------

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import DyNetKAT.NetKAT.Packet
import DyNetKAT.NetKAT.AST
import DyNetKAT.NetKAT.Semantics

namespace DyNetKAT.NetKAT

open scoped Finset Classical

------------------------------------------------------------------------
-- Normal form type
------------------------------------------------------------------------

/-- A NetKAT⁻ᵈᵘᵖ normal form (Lemma 5, paper p. 13).

A normal form is a finite set of pairs `(α, π)` where:
- `α : CompleteTest` is a complete test (a total valuation
  `FieldName → FieldValueEnum` that assigns a value to every field,
  per Definition 4, p. 8).
- `π : CompleteAssignmentValuation` is a complete assignment valuation
  (the direct dual: a total valuation that overwrites every field,
  per Definition 4, p. 8).

The normal form represents the NetKAT expression `Σ_{(α,π) ∈ A} α · π` —
a union of complete-test-then-complete-assignment terms. The set `A` is
finite by construction (it is a `Finset`), reflecting the paper's statement
that `A` and `Π` are finite (printed p. 13: "Consequently, A and Π are finite").

This is the shape prescribed by Lemma 5: `q = Σ_{α·π ∈ A} α · π`. -/
abbrev NormalForm := Finset (CompleteTest × CompleteAssignmentValuation)

/-- The empty normal form (no summands). By Lemma 5, this corresponds to
the NetKAT zero term `0` (drop), since `Σ_{α·π ∈ ∅} α · π = 0`. -/
def NormalForm.empty : NormalForm := ∅

------------------------------------------------------------------------
-- Interpretation: NormalForm → NetKAT
------------------------------------------------------------------------

/-- Translate a normal-form summand `(α, π)` into the NetKAT term `α · π`.

Per Lemma 5 (printed p. 13), each summand `α · π` is a complete test
followed by a complete assignment. This uses the existing
paper-faithful constructors:
- `NetKAT.completeTest α` — the complete test (α), per `AST.lean`.
- `NetKAT.completeAssignExpr π` — the complete assignment (π) built from
  primitive single-field assignments, per `AST.lean`.

The sequential composition `NetKAT.seq` yields `α ; π`. -/
def NormalForm.ofSummand
    (pair : CompleteTest × CompleteAssignmentValuation) : NetKAT :=
  match pair with
    | (α, π) => NetKAT.seq (NetKAT.completeTest α) (NetKAT.completeAssignExpr π)

/-- A normal form's summands, as a deduplicated list (via `Finset.toList`).

Because a `Finset` is a finite set with no duplicate elements, `Finset.toList`
yields a list with no duplicates. `Finset.toList` returns `[]` if and only if
the `Finset` is empty.

This definition is `noncomputable` because `Finset.toList` relies on classical
choice for set-to-list conversion. -/
noncomputable def NormalForm.summandsToList (nf : NormalForm) :
    List (CompleteTest × CompleteAssignmentValuation) :=
  Finset.toList nf

/-- Interpret a normal form as a NetKAT expression.

`interpret nf = Σ_{(α,π) ∈ nf} (α · π)`

Each pair `(α, π)` is translated by `ofSummand` to
`NetKAT.seq (NetKAT.completeTest α) (completeAssignExpr π)` = `α · π`,
matching Lemma 5 (paper p. 13): `q = Σ_{α·π ∈ A} α · π`.

The empty normal form translates to `NetKAT.drop` (the zero / empty relation),
matching `Σ_{α·π ∈ ∅} α · π = 0`.

Because `summandsToList` returns `[]` exactly when `nf` is empty, the match is
total: the `[]` branch yields `NetKAT.drop`; the `head :: tail` branch folds
the remaining summands with `NetKAT.union` (the `+` operator).

This definition is marked `noncomputable` because `Finset.toList` is
noncomputable (it relies on classical choice for set-to-list conversion). -/
noncomputable def NormalForm.interpret (nf : NormalForm) : NetKAT :=
  match NormalForm.summandsToList nf with
  | [] => NetKAT.drop
  | head :: tail =>
     tail.foldr
      (fun pair acc => NetKAT.union (NormalForm.ofSummand pair) acc)
      (NormalForm.ofSummand head)

------------------------------------------------------------------------
-- Single-summand semantics (Task 3B)
------------------------------------------------------------------------

/-- Semantics of a single normal-form summand `α · π` (Lemma 5, paper p. 13).

For a complete test α, complete assignment π, and packets σ, τ:

  ⟦α · π⟧(σ, τ)  ↔  holdsComplete α σ ∧ τ = π

**Proof:** By definition, `ofSummand (α, π) = .seq (.completeTest α) (completeAssignExpr π)`.
- `seq_sem` gives: `∃ ρ, ⟦α⟧(σ,ρ) ∧ ⟦completeAssignExpr π⟧(ρ,τ)`.
- `completeTest_sem` gives: `⟦α⟧(σ,ρ) ↔ holdsComplete α σ ∧ σ = ρ`, so `ρ = σ`.
- `completeAssignExpr_sem` gives: `⟦completeAssignExpr π⟧(ρ,τ) ↔ τ = π`.

Substituting `ρ = σ` and simplifying yields the result. -/
theorem ofSummand_sem (α : CompleteTest) (π : CompleteAssignmentValuation)
 (σ τ : CtxPkt) :
 Semantics (NormalForm.ofSummand (α, π)) σ τ ↔
 holdsComplete α σ ∧ τ = π := by
  unfold NormalForm.ofSummand
  -- Goal: Semantics (.seq (.completeTest α) (completeAssignExpr π)) σ τ ↔ holdsComplete α σ ∧ τ = π
  rw [seq_sem]
  -- Goal: (∃ ρ, Semantics (.completeTest α) σ ρ ∧ Semantics (completeAssignExpr π) ρ τ) ↔ holdsComplete α σ ∧ τ = π
  constructor
  · -- Forward: ∃ ρ, ⟦α⟧(σ,ρ) ∧ ⟦π⟧(ρ,τ)  →  holdsComplete α σ ∧ τ = π
    rintro ⟨ρ, h₁, h₂⟩
    -- completeTestEmbed α = .completeTest α, so unfold the alias before rewriting
    rw [← NetKAT.completeTestEmbed] at h₁
    rw [completeTest_sem] at h₁
    rcases h₁ with ⟨hα, hρ⟩
    subst hρ
    -- Now ρ = σ, and h₂: Semantics (completeAssignExpr π) σ τ
    rw [completeAssignExpr_sem] at h₂
    exact ⟨hα, h₂⟩
  · -- Reverse: holdsComplete α σ ∧ τ = π  →  ∃ ρ, ⟦α⟧(σ,ρ) ∧ ⟦π⟧(ρ,τ)
    rintro ⟨hα, hτ⟩
    use σ
    constructor
    · -- ⟦α⟧(σ,σ): holdsComplete α σ ∧ σ = σ
      rw [← NetKAT.completeTestEmbed]
      rw [completeTest_sem]
      exact ⟨hα, rfl⟩
    · -- ⟦completeAssignExpr π⟧(σ,τ): τ = π
      rw [completeAssignExpr_sem]
      exact hτ

------------------------------------------------------------------------
-- Semantic correctness (for reference; proved in a later task)
------------------------------------------------------------------------

-- The semantic correctness of `NormalForm.interpret` is established in a
-- later task (Task 3C): for all σ, τ,
--   Semantics (NormalForm.interpret nf) σ τ
--     ↔ ∃ (α, π) ∈ nf, Semantics (NormalForm.ofSummand (α, π)) σ τ
--
-- In particular, by `completeAssignExpr_sem` (Semantics.lean):
--   Semantics (ofSummand (α, π)) σ τ  ↔  holdsComplete α σ ∧ τ = π
-- and `drop_empty` gives the empty-normal-form case:
--   Semantics NetKAT.drop σ τ  =  False

--------------------------------------------------------------------------
-- List-fold semantics (Task 3C-1: helper theorem for the Finset interpretation)
--------------------------------------------------------------------------

/-- Semantics of the list-fold underlying `NormalForm.interpret` (Task 3C-1).

For a list `xs` of complete-test/complete-assignment pairs, the folded
expression denotes precisely the union of its summands. The fold uses the
same combining function and base case (`NetKAT.drop`) as `NormalForm.interpret`.

The equivalence is: the relation of the folded NetKAT expression holds on
`(sigma, tau)` if and only if some pair `(alpha, pi)` in `xs` satisfies
`holdsComplete alpha sigma` and `tau = pi`.

Proof is by induction on `xs`, using `union_sem`, `ofSummand_sem`, and
the induction hypothesis. -/
theorem fold_sem
    (xs : List (CompleteTest × CompleteAssignmentValuation))
    (σ τ : CtxPkt) :
    Semantics (xs.foldr
      (fun (pair : CompleteTest × CompleteAssignmentValuation) acc =>
        NetKAT.union (NormalForm.ofSummand pair) acc)
      NetKAT.drop) σ τ ↔
    ∃ (α : CompleteTest) (π : CompleteAssignmentValuation),
      (α, π) ∈ xs ∧ holdsComplete α σ ∧ τ = π := by
  induction xs generalizing σ τ with
  | nil =>
    -- LHS: Semantics (foldr f drop []) = Semantics drop = False.
    -- RHS: exists pair in [], ... = False.
    simp only [List.foldr]
    -- Semantics .drop σ τ is False by definition; exists over [] is False.
    tauto

  | cons head tail ih =>
    -- LHS: foldr f drop (head :: tail) = union (ofSummand head) (foldr f drop tail)
    simp only [List.foldr]
    -- Apply union_sem: union n1 n2 <-> n1 \/ n2
    rw [union_sem]
    -- Apply ofSummand_sem to the head part after destructuring pair.
    cases head with
    | mk α π =>
      rw [ofSummand_sem]
      -- Apply IH to the tail fold.
      rw [ih]
      constructor
      · -- Forward direction
        rintro (⟨hα, hτ⟩ | ⟨γ, δ, hmem, hγ, hδ⟩)
        · use α, π
          constructor
          · show (α, π) ∈ (α, π) :: tail
            simp only [List.mem_cons_self]
          · exact ⟨hα, hτ⟩
        · use γ, δ
          exact ⟨List.mem_cons_of_mem _ hmem, hγ, hδ⟩
      · -- Reverse direction
        intro h
        rcases h with ⟨γ, δ, hmem, hγ, hδ⟩
        rcases List.mem_cons.mp hmem with (hhead | htail)
        · cases hhead
          left
          exact ⟨hγ, hδ⟩
        · right
          exact ⟨γ, δ, htail, hγ, hδ⟩


------------------------------------------------------------------------
-- Interpret semantics (Task 3C-2)
------------------------------------------------------------------------

/-- Relational semantics of `NormalForm.interpret`.

For a normal form `nf` and packets `σ`, `τ`:
  ⟦interpret(nf)⟧(σ, τ)  ↔  ∃ (α, π) ∈ nf, holdsComplete α σ ∧ τ = π

The proof unfolds `interpret` and `summandsToList`, then establishes
semantic equivalence between the `match` form (used by `interpret`) and
the `foldr`-with-`drop` form (used by `fold_sem`). The equivalence relies
on `union_sem` (∨ semantics) and that `drop` (empty relation) is the
right identity for `union` (⟦N + 0⟧ ↔ ⟦N⟧).
Finally, `Finset.mem_toList` converts between list and Finset membership. -/
theorem interpret_sem (nf : NormalForm) (σ τ : CtxPkt) :
    Semantics (NormalForm.interpret nf) σ τ ↔
    ∃ (α : CompleteTest) (π : CompleteAssignmentValuation),
      (α, π) ∈ nf ∧ holdsComplete α σ ∧ τ = π := by
  unfold NormalForm.interpret NormalForm.summandsToList
  -- After unfolding: match Finset.toList nf with …
  -- Prove general equivalence: match form ↔ foldr-with-drop.
  have h_gen :
      ∀ ls' : List (CompleteTest × CompleteAssignmentValuation),
        Semantics (match ls' with
        | [] => NetKAT.drop
        | head :: tail => tail.foldr
          (fun pair acc => NetKAT.union (NormalForm.ofSummand pair) acc)
          (NormalForm.ofSummand head)) σ τ ↔
        Semantics (ls'.foldr
          (fun pair acc => NetKAT.union (NormalForm.ofSummand pair) acc)
          NetKAT.drop) σ τ := by
    intro ls'
    induction ls' generalizing σ τ with
    | nil => rfl
    | cons head tail _ =>
      -- Need: tail.foldr f (ofSummand head) ↔ union (ofSummand head) (tail.foldr f drop)
      -- Prove by induction on tail.
      have h_sub :
          ∀ ts : List (CompleteTest × CompleteAssignmentValuation),
            Semantics (ts.foldr
              (fun pair acc => NetKAT.union (NormalForm.ofSummand pair) acc)
              (NormalForm.ofSummand head)) σ τ ↔
            Semantics ((NormalForm.ofSummand head).union
              (ts.foldr (fun pair acc => NetKAT.union (NormalForm.ofSummand pair) acc)
                NetKAT.drop)) σ τ := by
        intro ts
        induction ts generalizing σ τ with
        | nil =>
          -- ofSummond head ↔ union (ofSummond head) drop
          -- ⟦union n drop⟧ ↔ ⟦n⟧ ∨ ⟦drop⟧; ⟦drop⟧ = False
          rw [union_sem]
          -- Need to show: A ↔ A ∨ False, where A = Semantics (ofSummond head) σ τ
          -- Semantics .drop σ τ reduces to False by definition.
          -- Use `unfold Semantics` to make it explicit.
          unfold Semantics
          -- Now False appears; use tauto.
          tauto
        | cons h tl ihl =>
          simp only [List.foldr]
          rw [union_sem, union_sem, union_sem]
          specialize ihl σ τ
          rw [ihl, union_sem]
          tauto
      rw [h_sub tail]
      rfl
  -- Apply h_gen to convert match form → foldr-with-drop.
  rw [h_gen (Finset.toList nf)]
  -- Apply fold_sem to convert to existential over Finset.toList nf.
  rw [fold_sem]
  -- Convert Finset.tolist membership ↔ Finset membership.
  constructor
  · rintro ⟨α, π, hmem, hα, hτ⟩
    exact ⟨α, π, Finset.mem_toList.1 hmem, hα, hτ⟩
  · rintro ⟨α, π, hmem, hα, hτ⟩
    exact ⟨α, π, Finset.mem_toList.2 hmem, hα, hτ⟩

  --------------------------------------------------------------------------
  -- Empty normal form semantics (Task 3D-3)
  --------------------------------------------------------------------------

  /-- The empty normal form represents the NetKAT drop policy (0).

  Mathematically: ⟦interpret(∅)⟧ = ⟦0⟧

  Proof: `NormalForm.empty` is `∅` (the empty Finset). `summandsToList ∅`
  is `Finset.toList ∅` = `[]` (empty list). `interpret` matches `[]` and
  returns `NetKAT.drop`. So `interpret empty` is definitionally equal to
  `NetKAT.drop`, making the theorem judgmentally true. -/
  theorem emptyNF_sem (σ τ : CtxPkt) :
      Semantics (NormalForm.interpret NormalForm.empty) σ τ ↔
      Semantics NetKAT.drop σ τ := by
    -- By interpret_sem, LHS ↔ ∃ (α,π) ∈ ∅, holdsComplete α σ ∧ τ = π.
    -- Since no element is in ∅, the existential is unsatisfiable (= False).
    -- RHS is Semantics .drop σ τ, which is structurally False.
    -- So False ↔ False.
    rw [interpret_sem]
    unfold Semantics
    constructor
    · rintro ⟨_, _, hmem, _⟩
      exact (Finset.not_mem_empty _ hmem).elim
    · intro h
      cases h

  --------------------------------------------------------------------------
  -- Identity normal form (Task 3D-2)
  --------------------------------------------------------------------------

  /-- Normal form of NetKAT identity: `idNF = { (α, α) | α : CompleteTest }`.

  Per the paper (Lemma 5, p. 13), the identity policy `1 ≜ id` has normal
  form `Σ_{α·π ∈ A} α · π` where each summand `α · π` tests α then assigns π.
  For identity, the assignment π must equal the test α (the packet passes
  through unchanged), so the set of summands is `{ (α, α) | α : CompleteTest }`.

  `idNF` is constructed as `Finset.map` of the diagonal embedding
  `α ↦ (α, α)` over `Finset.univ : Finset CompleteTest`. `Finset.map`
  requires an embedding `α ↪ β` but does NOT require `DecidableEq` on the
  codomain (unlike `Finset.image`). The diagonal map is injective since
  `α₁ = α₂` implies `(α₁,α₁) = (α₂,α₂)`. Since `CompleteTest` and
  `CompleteAssignmentValuation` are both aliases of `CtxPkt` (a total
  valuation `FieldName → FieldValueEnum`), each α determines the matching
  complete assignment valuation. -/
  def NormalForm.idNF : NormalForm :=
    (Finset.univ : Finset CompleteTest).map
      ⟨fun α : CompleteTest => (α, α),
       fun _ _ h => congr_arg (·.1) h⟩

  /-- Normal form of a NetKAT predicate test: `testNF Pr = {(α, α) | α ∈ CompleteTest, Pr.holds α}`.

  Per the paper (Lemma 5, p. 13), a normal form is a finite set of pairs
  `(α, π)` where α is a complete test and π is a complete assignment. For a
  predicate test `Pr`, the semantic relation is `⟦Pr⟧ = {(σ,σ) | Pr.holds σ}`,
  i.e. the identity restricted to packets satisfying the predicate. In normal
  form, this is represented as the diagonal pairs `(α, α)` where α ranges over
  all complete tests on which `Pr` holds. Each such pair represents
  `α · α` = `completeTest α ; completeAssignExpr α`, which is the identity on
  packet α.

  Construction:
  1. Start with `Finset.univ : Finset CompleteTest` — all complete tests.
  2. Filter by `fun α => Pr.eval α = true` — keep only tests where Pr holds.
     This is the same relation as `Pr.holds α` (defined `Predicate.holds` in
     `AST.lean:59` as `eval Pr σ = true`), expressed using `Bool` equality so
     that `DecidablePred` is available for `Finset.filter`.
  3. Map via the diagonal embedding `α ↦ (α, α)`, using `Finset.map` with the
     injective diagonal embedding (same pattern as `idNF`).

  Uses the same predicate evaluation relation `Predicate.holds` (defined in
  `AST.lean`) as the existing NetKAT `.test` semantics (`Semantics.lean:66`).
  Marked `noncomputable` because `Finset.filter` on a proposition-valued
  predicate relies on classical decidability. -/
  noncomputable def NormalForm.testNF (Pr : Predicate) : NormalForm :=
    ((Finset.univ : Finset CompleteTest).filter (fun α => Pr.eval α = true)).map
      ⟨fun α : CompleteTest => (α, α),
       fun _ _ h => congr_arg (·.1) h⟩

  /-- Semantic correctness of the identity normal form.

  For all packets σ, τ, the interpretation of `idNF` is semantically
  equivalent to `NetKAT.id`.

  Proof:
  - `interpret_sem` gives: ⟦interpret(idNF)⟧(σ,τ) ↔ ∃ (α,π) ∈ idNF, holdsComplete α σ ∧ τ = π.
  - `idNF = map (fun α => (α,α)) univ`, so membership `(α,π) ∈ idNF` means
    `∃ α₀ ∈ univ, (α₀,α₀) = (α,π)`, i.e. `α = π`.
  - By `holdsComplete_iff_eq`: `holdsComplete α σ ↔ σ = α`, so the unique
    satisfying pair is `(σ, σ)`.
  - Thus the relation holds iff `τ = σ`, which is exactly `NetKAT.id` semantics. -/
  theorem idNF_sem (σ τ : CtxPkt) :
      Semantics (NormalForm.interpret NormalForm.idNF) σ τ ↔
      Semantics NetKAT.id σ τ := by
    rw [interpret_sem, id_diag]
    constructor
    · -- Forward: ∃ (α,π) ∈ idNF, holdsComplete α σ ∧ τ = π  →  σ = τ
      rintro ⟨α, π, hmem, hα, hτ⟩
      -- (α,π) ∈ idNF = map (fun a => (a,a)) univ → (α,π) = (a,a) for some a
      rcases Finset.mem_map.mp hmem with ⟨a, _ha, haa⟩
      -- haa: (a, a) = (α, π) (after unfolding the embedding toFun)
      have haa' : (a, a) = (α, π) := by
        -- The embedding's toFun field is `fun α => (α, α)`
        cases haa
        rfl
      -- From (a,a) = (α,π): a = α and a = π, hence α = π
      have hαπ : α = π := by
        cases haa'
        rfl
      subst hαπ
      -- hα: holdsComplete α σ  →  σ = α  (by holdsComplete_iff_eq)
      have hσ : σ = α := (holdsComplete_iff_eq α σ).1 hα
      subst hσ
      -- hτ: τ = π = α = σ
      exact hτ.symm
    · -- Reverse: σ = τ  →  ∃ (α,π) ∈ idNF, holdsComplete α σ ∧ τ = π
      intro h
      -- Witness: the pair (σ, σ) ∈ idNF
      use σ, σ
      constructor
      · -- (σ,σ) ∈ idNF = map (fun a => (a,a)) univ
        apply Finset.mem_map.mpr
        use σ
        constructor
        · exact Finset.mem_univ _
        · rfl
      · -- holdsComplete σ σ ∧ τ = σ
        constructor
        · -- holdsComplete σ σ: by holdsComplete_iff_eq, σ = σ ↔ holdsComplete σ σ
          exact (holdsComplete_iff_eq σ σ).mpr (Eq.refl σ)
        · -- τ = σ (from h : σ = τ)
          exact h.symm

--------------------------------------------------------------------------
-- Test predicate semantics (Task 3D-5: Predicate Normal-Form Semantics)
--------------------------------------------------------------------------

/-- Semantic correctness of the predicate-test normal form.

For all packets σ, τ, the interpretation of `testNF Pr` is semantically
equivalent to the NetKAT predicate test `NetKAT.test Pr`.

Mathematically:
  ⟦interpret(testNF(p))⟧ = ⟦test(p)⟧

**Proof:**
- `interpret_sem` gives LHS ≡ ∃ (α,π) ∈ testNF Pr, holdsComplete α σ ∧ τ = π.
- `testNF Pr = map (fun α => (α,α)) (univ.filter (fun α => Pr.eval α = true))`,
  so `(α,π) ∈ testNF Pr` means `α = π` and `Pr.eval α = true` (i.e., `Pr.holds α`).
- `holdsComplete_iff_eq` gives `holdsComplete α σ ↔ σ = α`.
- Combining: LHS holds iff ∃ α, Pr.holds α ∧ σ = α ∧ τ = α,
  which simplifies to `Pr.holds σ ∧ σ = τ`, exactly `⟦test Pr⟧(σ,τ)`. -/
theorem testNF_sem (Pr : Predicate) (σ τ : CtxPkt) :
    Semantics (NormalForm.interpret (NormalForm.testNF Pr)) σ τ ↔
    Semantics (NetKAT.test Pr) σ τ := by
  rw [interpret_sem]
  -- After interpret_sem, LHS becomes:
  -- ∃ (α,π) ∈ testNF Pr, holdsComplete α σ ∧ τ = π
  constructor
  · -- Forward: ∃ (α,π) ∈ testNF Pr, holdsComplete α σ ∧ τ = π → Pr.holds σ ∧ σ = τ
    rintro ⟨α, π, hmem, hα, hτ⟩
    -- testNF = map (fun a => (a,a)) (univ.filter (fun a => Pr.eval a = true))
    -- So (α,π) ∈ testNF means ∃ α₀ with α₀ ∈ filter, (α₀,α₀) = (α,π)
    rcases Finset.mem_map.mp hmem with ⟨α₀, hfilter, hdiag⟩
    -- hdiag involves the embedding structure. Convert to a plain pair equality.
    have hdiag' : (α₀, α₀) = (α, π) := by
      cases hdiag
      rfl
    -- Destruct pair equality: α₀ = α and α₀ = π
    have h₁ : α₀ = α := congrArg (·.1) hdiag'
    have h₂ : α₀ = π := congrArg (·.2) hdiag'
    subst α  -- α := α₀
    subst π  -- π := α₀
    -- hfilter: α₀ ∈ univ.filter (fun a => Pr.eval a = true), so Pr.holds α₀
    have hpr : Pr.holds α₀ := by
      rw [Finset.mem_filter] at hfilter
      exact hfilter.2
    -- holdsComplete α₀ σ ↔ σ = α₀  (by holdsComplete_iff_eq)
    have hσ : σ = α₀ := (holdsComplete_iff_eq α₀ σ).1 hα
    subst σ  -- σ := α₀ (using hσ : σ = α₀)
    -- hτ : τ = π; after subst π := α₀, hτ : τ = α₀
    -- Use hτ to set τ := α₀
    subst τ
    -- Goal: Pr.holds σ ∧ σ = σ  (after all substitutions, σ = α₀)
    constructor
    · exact hpr
    · rfl
  · -- Reverse: Pr.holds σ ∧ σ = τ → ∃ (α,π) ∈ testNF Pr, holdsComplete α σ ∧ τ = π
    rintro ⟨hpr, hτ⟩
    -- Witness: α = σ, π = σ. Then (σ,σ) ∈ testNF Pr since Pr.holds σ.
    use σ, σ
    constructor
    · -- (σ,σ) ∈ testNF Pr
      apply Finset.mem_map.mpr
      use σ
      constructor
      · -- σ ∈ univ.filter (fun a => Pr.eval a = true)
        -- Pr.holds σ means Pr.eval σ = true
        rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_univ σ
        · exact hpr
      · -- (σ,σ) = (σ,σ) — definitionally, after the embedding
        rfl
    · -- holdsComplete σ σ ∧ τ = σ
      constructor
      · -- holdsComplete σ σ: by holdsComplete_iff_eq, σ = σ ↔ holdsComplete σ σ
        exact (holdsComplete_iff_eq σ σ).mpr (Eq.refl σ)
      · -- τ = σ (from hτ : σ = τ)
        exact hτ.symm

   /-- Union of two normal forms.

   Mathematically: `G(p + q) = G(p) ∪ G(q)`.

   Since a `NormalForm` is a `Finset (CompleteTest × CompleteAssignmentValuation)`,
   the union of two normal forms is the standard `Finset` union operation (`a ∪ b`),
   which represents the finite-set union of the two input normal forms. This
   corresponds to the NetKAT `+` operator whose semantics is set union over
   the relational interpretation.

   No new normal-form representation is introduced: the result is the same
   `Finset` type with membership being the logical OR of the two input
   memberships.

   Marked `noncomputable` because the `DecidableEq` instance for the element
   type `CompleteTest × CompleteAssignmentValuation` (a product of function
   spaces `FieldName → FieldValueEnum`) is obtained via classical decidability.
   Type-class inference does not synthesize `DecidableEq` for the `def`-aliased
   types `CompleteTest` and `CompleteAssignmentValuation` directly, so we
   establish it by rewriting to the underlying function type and using the
   existing `DecidableEq` instance for `FieldName → FieldValueEnum`. -/
   noncomputable def NormalForm.unionNF (a b : NormalForm) : NormalForm :=
     have inst : DecidableEq (CompleteTest × CompleteAssignmentValuation) := by
       change DecidableEq ((FieldName → FieldValueEnum) × (FieldName → FieldValueEnum))
       exact inferInstance
     a ∪ b

   /-- Normal form of a primitive single-field assignment: `assign1NF f v`.


  Per Lemma 5 (paper p. 13), a normal form is a finite set of summands
  `(α, π)`.  The primitive assignment `f ← v` has semantics
    ⟦f←v⟧(σ,τ) ↔ τ = Packet.update σ f v.
  For *every* input packet σ, the output is `Packet.update σ f v`.
  Enumerating over all complete tests α (i.e. all packets), the set of
  summands is:
    { (α, Packet.update α f v) | α ∈ CompleteTest }
  i.e. the diagonal embedding α ↦ (α, Packet.update α f v) over
  `Finset.univ : Finset CompleteTest`.

  Construction: same `Finset.map` pattern as `idNF` and `testNF`, but the
  second component is `Packet.update α f v` instead of `α`.
  Injectivity (first component): `α₁ = α₂` implies
    `(α₁, Packet.update α₁ f v) = (α₂, Packet.update α₂ f v)`,
  proven by `congr_arg (·.1)` — identical to the pattern already used by
  `idNF` and `testNF`.

  Uses `Packet.update` exactly as in the `.assign1` semantics clause
  (`Semantics.lean:68`), with the `[DecidableEq FieldName]` instance
  arising from `FieldName`'s `deriving DecidableEq`.

  Marked `noncomputable` to match `testNF` (which is also noncomputable
  due to `Finset.filter`; here we use `Finset.univ` directly, but the
  `noncomputable` marker ensures consistency and avoids any classical
  choice issues with `Finset.map`). -/
  noncomputable def NormalForm.assign1NF (f : FieldName)
      (v : FieldValueEnum) : NormalForm :=
    (Finset.univ : Finset CompleteTest).map
      ⟨fun α : CompleteTest => (α, Packet.update α f v),
       fun _ _ h => congr_arg (·.1) h⟩

  /-- Semantic correctness of `assign1NF`.

  For all packets σ, τ, the interpretation of `assign1NF f v` is semantically
  equivalent to the primitive single-field assignment `NetKAT.assign1 f v`.

  Mathematically:
    ⟦interpret(assign1NF(f,v))⟧(σ,τ)  ↔  ⟦f←v⟧(σ,τ)

  Proof guidance (per task spec):

  **Forward direction:** Rewrite the LHS using `interpret_sem` to obtain:
  ```
  ∃ (α : CompleteTest) (π : CompleteAssignmentValuation),
    (α, π) ∈ assign1NF f v ∧ holdsComplete α σ ∧ τ = π
  ```
  Extract the input valuation α via `Finset.mem_map`: membership
  `(α, π) ∈ assign1NF f v` means `∃ α₀ ∈ univ, (α₀, Packet.update α₀ f v) = (α, π)`,
  so `π = Packet.update α f v` and `α = α₀`.
  Apply `holdsComplete_iff_eq` to establish `σ = α`.
  Substitute into `τ = π` to derive `τ = Packet.update σ f v`, then apply
  `assign1_sem` for the RHS.

  **Reverse direction:** Choose `α = σ` as the witness. Establish membership
  using `Finset.mem_univ` and `Finset.mem_map` (the diagonal embedding maps
  `σ` to `(σ, Packet.update σ f v)`, which is the pair we exhibit).
  `holdsComplete σ σ` follows from `holdsComplete_iff_eq` with `σ = σ`. -/
  theorem assign1NF_sem (f : FieldName) (v : FieldValueEnum)
      (σ τ : CtxPkt) :
      Semantics (NormalForm.interpret
        (NormalForm.assign1NF f v)) σ τ ↔
      Semantics (NetKAT.assign1 f v) σ τ := by
    -- RHS: use assign1_sem to rewrite to τ = Packet.update σ f v.
    rw [assign1_sem]
    -- LHS: use interpret_sem to rewrite to existential over the Finset.
    rw [interpret_sem]
    constructor
    · -- Forward: ∃ (α,π) ∈ assign1NF f v, holdsComplete α σ ∧ τ = π → τ = Packet.update σ f v
      rintro ⟨α, π, hmem, hα, hτ⟩
      -- assign1NF = map (fun a => (a, Packet.update a f v)) univ.
      -- Extract α₀ such that α₀ ∈ univ and (α₀, Packet.update α₀ f v) = (α, π).
      rcases Finset.mem_map.mp hmem with ⟨α₀, hmem_univ, hpair⟩
      -- Destruct the pair equality: α₀ = α and Packet.update α₀ f v = π.
      have hα_eq : α₀ = α := by
        cases hpair
        rfl
      have hπ_eq : Packet.update α₀ f v = π := by
        cases hpair
        rfl
      subst hα_eq
      subst hπ_eq
      -- Now hα : holdsComplete α₀ σ  →  σ = α₀  (by holdsComplete_iff_eq).
      have hσ : σ = α₀ := (holdsComplete_iff_eq α₀ σ).1 hα
      subst hσ
      -- hτ : τ = Packet.update σ f v (after substitutions).
      exact hτ
    · -- Reverse: τ = Packet.update σ f v → ∃ (α,π) ∈ assign1NF f v, holdsComplete α σ ∧ τ = π
      intro hτ
      -- Witness: α = σ, π = Packet.update σ f v.
      use σ, Packet.update σ f v
      constructor
      · -- (σ, Packet.update σ f v) ∈ assign1NF f v.
        apply Finset.mem_map.mpr
        -- α₀ = σ ∈ univ (everything is in univ), and the pair matches.
        use σ
        constructor
        · exact Finset.mem_univ σ
        · rfl
      · -- holdsComplete σ σ ∧ τ = Packet.update σ f v
        constructor
        · -- holdsComplete σ σ: σ = σ ↔ holdsComplete σ σ.
          exact (holdsComplete_iff_eq σ σ).mpr (Eq.refl σ)
        · -- τ = Packet.update σ f v (from hτ).
          exact hτ

--------------------------------------------------------------------------
-- Union normal form semantics (Task 3E-2)
--------------------------------------------------------------------------

/-- Union of normal forms corresponds to NetKAT choice (`+`).

Mathematically: ⟦interpret(A∪B)⟧ = ⟦interpret(A)+interpret(B)⟧

Proof:
- LHS: by `interpret_sem`, rewrites to `∃ (α,π) ∈ A ∪ B, holdsComplete α σ ∧ τ = π`.
- RHS: by `union_sem`, rewrites to `⟦interpret(A)⟧(σ,τ) ∨ ⟦interpret(B)⟧(σ,τ)`,
  which by `interpret_sem` becomes two existentials over `A` and `B` respectively.
- `Finset.mem_union` converts membership in `A ∪ B` to `(α,π) ∈ A ∨ (α,π) ∈ B`,
  matching the disjunction from `union_sem`. -/
theorem unionNF_sem (a b : NormalForm) (σ τ : CtxPkt) :
    Semantics (NormalForm.interpret (NormalForm.unionNF a b)) σ τ ↔
    Semantics (NetKAT.union
      (NormalForm.interpret a)
      (NormalForm.interpret b)) σ τ := by
  -- Provide the DecidableEq instance needed for Finset operations.
  have inst : DecidableEq (CompleteTest × CompleteAssignmentValuation) := by
    change DecidableEq ((FieldName → FieldValueEnum) × (FieldName → FieldValueEnum))
    exact inferInstance
  -- Apply interpret_sem to both sides.
  rw [interpret_sem]
  rw [union_sem]
  rw [interpret_sem]
  rw [interpret_sem]
  -- Now prove: ∃ pair ∈ unionNF a b, P pair ↔ (∃ pair ∈ a, P pair) ∨ (∃ pair ∈ b, P pair)
  -- We use simp to unfold unionNF and apply mem_union simultaneously.
  constructor
  · -- Forward: ∃ pair ∈ unionNF a b, P → (∃ ∊ a, P) ∨ (∃ ∊ b, P)
    rintro ⟨α, π, h, hα, hτ⟩
    simp only [NormalForm.unionNF, Finset.mem_union] at h
    rcases h with (ha | hb)
    · exact Or.inl ⟨α, π, ha, hα, hτ⟩
    · exact Or.inr ⟨α, π, hb, hα, hτ⟩
  · -- Reverse: (∃ ∊ a, P) ∨ (∃ ∊ b, P) → ∃ pair ∈ unionNF a b, P
    rintro (⟨α, π, ha, hα, hτ⟩ | ⟨α, π, hb, hα, hτ⟩)
    · use α, π
      constructor
      · simp only [NormalForm.unionNF, Finset.mem_union]
        exact Or.inl ha
      · exact ⟨hα, hτ⟩
    · use α, π
      constructor
      · simp only [NormalForm.unionNF, Finset.mem_union]
        exact Or.inr hb
      · exact ⟨hα, hτ⟩

----------------------------------------------------------------------
-- Task 3F-1: Sequential composition of normal forms
----------------------------------------------------------------------

/-- Sequential composition of two normal forms.

For normal forms A and B (each a Finset of `(α, π)` pairs):

    A;B = { (α, ρ) | ∃ π, (α, π) ∈ A ∧ (π, ρ) ∈ B }

This is relational composition on the normal-form representation:
- Select `(α, π)` from `a`.
- Select `(β, ρ)` from `b`.
- Retain the combination only when `π = β` (the output valuation of the first
  summand matches the input valuation of the second).
- Produce `(α, ρ)` (the test of the first composed with the assignment of the second).

**Construction:** The set of result pairs is obtained as the image of the
product `a ×ˢ b` under the filter-and-extract map. Specifically:

1. Form the Cartesian product `a × b` (as `Finset` pairs) — all combinations of
   summands from `a` and `b`.
2. Filter to retain only pairs `((α, π), (β, ρ))` where `π = β` (the
   intermediate valuation matches).
3. Image the survivor to `(α, ρ)`.

`Finset.image` automatically deduplicates the resulting pairs, so duplicate
results collapse naturally through `Finset` semantics.

Marked `noncomputable` to match `unionNF` (the `DecidableEq` instance for the
element type `CompleteTest × CompleteAssignmentValuation` is obtained via
classical decidability, and the filter predicate involves equality on function
types). -/
noncomputable def NormalForm.seqNF (a b : NormalForm) : NormalForm :=
  have inst : DecidableEq (CompleteTest × CompleteAssignmentValuation) := by
    change DecidableEq ((FieldName → FieldValueEnum) × (FieldName → FieldValueEnum))
    exact inferInstance
   Finset.product a b
     |>.filter (fun p => match p with
       | ((α, π), (β, ρ)) => π = β)
     |>.image (fun p => match p with
       | ((α, π), (β, ρ)) => (α, ρ))

-------------------------------------------------------------------------
-- Task 3F-2: Membership characterization for seqNF
-------------------------------------------------------------------------

/-- Membership characterization for sequential composition of normal forms.

Mathematically:

  (α, ρ) ∈ seqNF(A, B)  ↔  ∃ π, (α, π) ∈ A ∧ (π, ρ) ∈ B

This is pure finite-set membership — it follows from `Finset.mem_image`,
`Finset.mem_filter`, and `Finset.mem_product` without any recourse to NetKAT
semantics.

**Proof dependencies:**
- `NormalForm.seqNF` (definition) — the definition being characterized
- `Finset.mem_image` — converts membership in `image` to existential witness
- `Finset.mem_filter` — splits filter membership into predicate + base set membership
- `Finset.mem_product` — splits membership in `Finset.product a b` into `a ∧ b`
- `Prod.mk.inj` — destructures pair equality `(a, b) = (c, d)`

**Restrictions honored:**
- This theorem characterizes the existing `seqNF` definition without changing it.
- The proof uses only finite-set membership and pair-equality reasoning; it does not
  invoke NetKAT semantics.
- No changes to the AST, packet types, or semantic definitions are involved.
- No general normalization function, Kleene-star handling, or additional normal-form
  operation is introduced here.
- The implementation uses the existing `Mathlib.Data.Finset.Prod` import and no
  unproved assumptions.

**Any mathematical blockers:** None. The theorem follows directly from finite-set
membership reasoning using `Finset.mem_image`, `Finset.mem_filter`, and
`Finset.mem_product`. The only technical requirement is providing the `DecidableEq`
instance (matching the `have inst` block in `seqNF` itself) so that `simp only` can
unfold the definition through the `let_fun`. -/
theorem mem_seqNF_iff
    (a b : NormalForm)
    (α : CompleteTest)
    (ρ : CompleteAssignmentValuation) :
    (α, ρ) ∈ NormalForm.seqNF a b ↔
      ∃ π : CompleteAssignmentValuation,
        (α, π) ∈ a ∧ (π, ρ) ∈ b := by
  -- Provide the DecidableEq instance matching the `have inst` block in seqNF
  -- so that `simp only` can unfold the definition through the let_fun.
  have inst : DecidableEq (CompleteTest × CompleteAssignmentValuation) := by
    change DecidableEq ((FieldName → FieldValueEnum) × (FieldName → FieldValueEnum))
    exact inferInstance
  constructor
  · -- Forward: (α,ρ) ∈ seqNF a b  →  ∃ π, (α,π) ∈ a ∧ (π,ρ) ∈ b
    intro h
    simp only [NormalForm.seqNF, Finset.mem_image] at h
    rcases h with ⟨p, hp, hpair⟩
    rcases Finset.mem_filter.mp hp with ⟨hdist, hpred⟩
    rcases Finset.mem_product.mp hdist with ⟨hpa, hpb⟩
    -- Destructure p = ((a1, pi), (beta, rho')) so the `match` in hpair/hpred reduces.
    cases p with
    | mk p1 p2 =>
      cases p1 with
      | mk a1 pi =>
        cases p2 with
        | mk beta rho_prime =>
          dsimp only [Prod.fst, Prod.snd] at *
          -- hpair : (a1, rho_prime) = (α, ρ)
          -- hpred : pi = beta
          obtain ⟨h1, h2⟩ := Prod.mk.inj hpair
          subst h1 h2 hpred
          -- hpa : (α, pi) ∈ a, hpb : (pi, ρ) ∈ b
          exact ⟨pi, hpa, hpb⟩
  · -- Reverse: ∃ π, (α,π) ∈ a ∧ (π,ρ) ∈ b  →  (α,ρ) ∈ seqNF a b
    intro h
    rcases h with ⟨pi, hpa, hpb⟩
    simp only [NormalForm.seqNF, Finset.mem_image]
    use ((α, pi), (pi, ρ))
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_product.mpr ⟨hpa, hpb⟩
      · rfl
    · rfl

  ------------------------------------------------------------------------
  -- Task 3F-3: Sequential composition semantics
  ------------------------------------------------------------------------

  /-- Semantic correctness of sequential composition of normal forms.

  Mathematically:
    ⟦interpret(seqNF(A, B))⟧  =  ⟦interpret(A) ; interpret(B)⟧

  This is the semantic theorem showing that relational composition of NetKAT
  policies corresponds to the finite-set relational composition of their
  normal-form representations.

  **Forward direction:**
  1. `interpret_sem` rewrites LHS to ∃ (α,π) ∈ seqNF a b, holdsComplete α σ ∧ τ = π.
  2. `mem_seqNF_iff` extracts intermediate valuation π': ∃ π', (α,π') ∈ a ∧ (π',π) ∈ b.
  3. `holdsComplete_iff_eq` gives σ = α from holdsComplete α σ.
  4. Substituting: (σ,π') ∈ a and (π',τ) ∈ b.
  5. `interpret_sem` (reversed) gives Semantics (interpret a) σ π' and Semantics (interpret b) π' τ.
  6. `seq_sem` constructs the intermediate-packet witness for the RHS.

  **Reverse direction:**
  1. `seq_sem` extracts intermediate packet π'.
  2. `interpret_sem` extracts (α,π) ∈ a with holdsComplete α σ ∧ π' = π,
     and (β,ρ) ∈ b with holdsComplete β π' ∧ τ = ρ.
  3. `holdsComplete_iff_eq` gives σ = α and π' = β.
  4. `mem_seqNF_iff` constructs (α,ρ) ∈ seqNF a b.
  5. `interpret_sem` concludes.

  **Proof dependencies:**
  | Dependency | Location | Used for |
  |---|---|---|
  | `interpret_sem` | NormalForm.lean:263 | Rewrites interpret to existential |
  | `seq_sem` | Semantics.lean:100 | Rewrites seq semantics to existential |
  | `mem_seqNF_iff` | NormalForm.lean:802 | Characterizes seqNF membership |
  | `holdsComplete_iff_eq` | Packet.lean:218 | Complete test matches exactly one packet | -/
  theorem seqNF_sem (a b : NormalForm) (σ τ : CtxPkt) :
      Semantics (NormalForm.interpret (NormalForm.seqNF a b)) σ τ ↔
      Semantics (NetKAT.seq (NormalForm.interpret a) (NormalForm.interpret b)) σ τ := by
    -- Provide the DecidableEq instance matching the `have inst` block in seqNF.
    have inst : DecidableEq (CompleteTest × CompleteAssignmentValuation) := by
      change DecidableEq ((FieldName → FieldValueEnum) × (FieldName → FieldValueEnum))
      exact inferInstance
    constructor
    · -- Forward: ⟦interpret(seqNF a b)⟧(σ,τ) → ⟦interpret(a);interpret(b)⟧(σ,τ)
      intro h
      -- interpret_sem rewrites LHS: ∃ (α,π) ∈ seqNF a b, holdsComplete α σ ∧ τ = π.
      rw [interpret_sem] at h
      rcases h with ⟨α, π₁, hmem, hα, hτ⟩
      -- mem_seqNF_iff extracts intermediate valuation π₂.
      rw [mem_seqNF_iff] at hmem
      rcases hmem with ⟨π₂, hpa, hpb⟩
      -- holdsComplete_iff_eq: holdsComplete α σ ↔ σ = α.
      have hσ : σ = α := (holdsComplete_iff_eq α σ).1 hα
      subst hσ
      -- Now hpa : (σ, π₂) ∈ a, hpb : (π₂, π₁) ∈ b, hτ : τ = π₁.
      subst hτ
      -- seq_sem for RHS: need ∃ ρ, ⟦interpret a⟧(σ,ρ) ∧ ⟦interpret b⟧(ρ,τ).
      -- Witness: π₂.
      rw [seq_sem]
      refine ⟨π₂, (interpret_sem a σ π₂).mpr ?_, (interpret_sem b π₂ τ).mpr ?_⟩
      · -- ⟦interpret a⟧(σ, π₂): witness (σ, π₂) with holdsComplete σ σ.
        refine ⟨σ, π₂, ?_⟩
        exact ⟨hpa, (holdsComplete_iff_eq σ σ).mpr rfl, rfl⟩
      · -- ⟦interpret b⟧(π₂, τ): witness (π₂, τ) with holdsComplete π₂ π₂.
        refine ⟨π₂, τ, ?_⟩
        exact ⟨hpb, (holdsComplete_iff_eq π₂ π₂).mpr rfl, rfl⟩
    · -- Reverse: ⟦interpret(a);interpret(b)⟧(σ,τ) → ⟦interpret(seqNF a b)⟧(σ,τ)
      intro h
      -- seq_sem extracts intermediate packet π₂.
      rw [seq_sem] at h
      rcases h with ⟨π₂, h₁, h₂⟩
      -- interpret_sem.mp on ⟦interpret a⟧(σ, π₂): ∃ (α,π₃) ∈ a, holdsComplete α σ ∧ π₂ = π₃.
      rcases (interpret_sem a σ π₂).mp h₁ with ⟨α, π₃, hpa, hα, hπ₂⟩
      -- interpret_sem.mp on ⟦interpret b⟧(π₂, τ): ∃ (β,ρ) ∈ b, holdsComplete β π₂ ∧ τ = ρ.
      rcases (interpret_sem b π₂ τ).mp h₂ with ⟨β, ρ, hpb, hβ, hρ⟩
      -- holdsComplete_iff_eq gives σ = α and π₂ = β.
      have hσ : σ = α := (holdsComplete_iff_eq α σ).1 hα
      have hπ₂eq : π₂ = β := (holdsComplete_iff_eq β π₂).1 hβ
      subst hσ hπ₂eq hπ₂
      -- hpa : (σ, π₂) ∈ a, hpb : (π₂, ρ) ∈ b, hπ₂ was π₂ = π₃ so π₃ is gone,
      -- but hpa has π₃ in it which is now π₂. hρ : τ = ρ.
      subst hρ
      -- Now: hpa : (σ, π₂) ∈ a, hpb : (π₂, τ) ∈ b.
      -- interpret_sem.mpr for LHS: need (σ, τ) ∈ seqNF a b and holdsComplete σ σ ∧ τ = τ.
      have hseq : (σ, τ) ∈ NormalForm.seqNF a b := by
        rw [mem_seqNF_iff]
        exact ⟨π₂, hpa, hpb⟩
      exact (interpret_sem (NormalForm.seqNF a b) σ τ).mpr ⟨σ, τ, hseq,
        (holdsComplete_iff_eq σ σ).mpr rfl, rfl⟩
