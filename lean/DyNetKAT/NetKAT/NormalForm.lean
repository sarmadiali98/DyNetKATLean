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

end DyNetKAT.NetKAT
