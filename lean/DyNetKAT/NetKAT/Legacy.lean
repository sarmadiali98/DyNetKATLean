import NetKATLean.Core.Normalization

/-! Exhaustive concrete normal forms and equality, retained for regression
and compatibility. Import this module explicitly to use these constructions. -/

namespace DyNetKAT.NetKAT

open scoped Finset

local infixl:65 " ⊕ " => NetKAT.union
local infixl:70 " ⨟ " => NetKAT.seq

open private word reads word_congr read_eq read_write_self write_assign
  sumOn_congr sumOn_seq_right from NetKATLean.Core.Normalization

private def values : List FieldValueEnum := [.v0, .v1, .v8, .v9]

/-- NetKAT semantic-equivalence checker over the finite packet domain.

    Both policies are evaluated on every possible input packet and their
    complete output sets are compared; the result is `true` exactly when
    all output sets agree. -/
def legacyNetkatEquiv (p q : NetKAT) : Bool :=
  decide (∀ σ : CtxPkt, netkatEquivAt p q σ = true)

/-- Main correctness theorem: the checker returns `true` exactly when both
    policies have identical relational semantics on every packet of the
    finite domain. -/
theorem legacyNetkatEquiv_correct
    (p q : NetKAT) :
    legacyNetkatEquiv p q = true ↔
      ∀ σ τ : CtxPkt,
        Semantics p σ τ ↔ Semantics q σ τ := by
  constructor
  · intro h σ τ
    have h' : (∀ ν : CtxPkt, netkatEquivAt p q ν = true) := decide_eq_true_iff.mp h
    exact netkatEquivAt_sound p q σ (h' σ) τ
  · intro h
    show decide (∀ σ : CtxPkt, netkatEquivAt p q σ = true)
    exact decide_eq_true (fun σ => netkatEquivAt_complete p q σ (h σ))

section

open scoped Classical

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
  1. Start with `Finset.univ : Finset CompleteTest` - all complete tests.
  2. Filter by `fun α => Pr.eval α = true` - keep only tests where Pr holds.
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
      · -- (σ,σ) = (σ,σ) - definitionally, after the embedding
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
  proven by `congr_arg (·.1)` - identical to the pattern already used by
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

1. Form the Cartesian product `a × b` (as `Finset` pairs) - all combinations of
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

This is pure finite-set membership - it follows from `Finset.mem_image`,
`Finset.mem_filter`, and `Finset.mem_product` without any recourse to NetKAT
semantics.

**Proof dependencies:**
- `NormalForm.seqNF` (definition) - the definition being characterized
- `Finset.mem_image` - converts membership in `image` to existential witness
- `Finset.mem_filter` - splits filter membership into predicate + base set membership
- `Finset.mem_product` - splits membership in `Finset.product a b` into `a ∧ b`
- `Prod.mk.inj` - destructures pair equality `(a, b) = (c, d)`

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

end

local instance : DecidableEq CompleteTest := (inferInstance : DecidableEq CtxPkt)
local instance : DecidableEq CompleteAssignmentValuation := (inferInstance : DecidableEq CtxPkt)

private def enumerateFields : List FieldName → List CtxPkt
  | [] => [fun _ => .v0]
  | f :: fs => (enumerateFields fs).flatMap fun p =>
      values.map fun v => Packet.update p f v

private theorem enumerateFields_covers (fs : List FieldName) (σ : CtxPkt) :
    ∃ p ∈ enumerateFields fs, ∀ f ∈ fs, p f = σ f := by
  induction fs with
  | nil => exact ⟨_, List.mem_cons_self, by simp⟩
  | cons f fs ih =>
    obtain ⟨p, hp, he⟩ := ih
    refine ⟨Packet.update p f (σ f), List.mem_flatMap.mpr ⟨p, hp, ?_⟩, ?_⟩
    · exact List.mem_map.mpr ⟨σ f, by cases σ f <;> simp [values], rfl⟩
    · intro g hg
      by_cases h : g = f
      · subst g
        simp [Packet.update]
      · have hm := (List.mem_cons.mp hg).resolve_left h
        simpa [Packet.update, h, Ne.symm h] using he g hm

/-- A fixed order for rendering. Its completeness follows from field enumeration. -/
def packetList : List CtxPkt := enumerateFields NetKAT.fieldEnum

theorem mem_packetList (σ : CtxPkt) : σ ∈ packetList := by
  obtain ⟨p, hp, he⟩ := enumerateFields_covers NetKAT.fieldEnum σ
  have h : p = σ := funext fun f => he f (NetKAT.fieldEnum_complete f)
  exact h ▸ hp

/-- The finite relation computed by the existing exact evaluator. -/
def legacyNetkatNormalForm (p : NetKAT) : NormalForm :=
  (Finset.univ : Finset CtxPkt).biUnion fun σ =>
    ((execute p σ).outputs.getD ∅).image fun τ => (σ, τ)

theorem legacyNetkatNormalForm_mem (p : NetKAT) (σ τ : CtxPkt) :
    (σ, τ) ∈ legacyNetkatNormalForm p ↔ Semantics p σ τ := by
  unfold legacyNetkatNormalForm
  constructor
  · intro h
    obtain ⟨s, _, hs⟩ := Finset.mem_biUnion.mp h
    obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hs
    cases he
    obtain ⟨B, hB, hSem⟩ := execute_correct p σ
    exact (hSem τ).mpr (by simpa [hB, EvalResult.outputs] using ht)
  · intro h
    obtain ⟨B, hB, hSem⟩ := execute_correct p σ
    exact Finset.mem_biUnion.mpr ⟨σ, Finset.mem_univ _, Finset.mem_image.mpr
      ⟨τ, by simpa [hB, EvalResult.outputs] using (hSem τ).mp h, rfl⟩⟩

/-- Legacy Cartesian-product renderer for the concrete regression oracle. -/
def NormalForm.orderedPairs (nf : NormalForm) :
    List (CompleteTest × CompleteAssignmentValuation) :=
  (packetList.flatMap fun σ => packetList.map fun τ => (σ, τ)).filter (fun pair => decide (pair ∈ nf))

theorem NormalForm.mem_orderedPairs (nf : NormalForm)
    (pair : CompleteTest × CompleteAssignmentValuation) :
    pair ∈ nf.orderedPairs ↔ pair ∈ nf := by
  rcases pair with ⟨σ, τ⟩
  rw [orderedPairs, List.mem_filter, decide_eq_true_eq]
  exact ⟨And.right, fun h => ⟨List.mem_flatMap.mpr ⟨σ, mem_packetList σ,
    List.mem_map.mpr ⟨τ, mem_packetList τ, rfl⟩⟩, h⟩⟩

/-- The original exhaustive normalizer, retained for regression. -/
def legacyNormalize (p : NetKAT) : NetKAT :=
  pairSum (legacyNetkatNormalForm p).orderedPairs

theorem legacyNormalize_correct (p : NetKAT) (σ τ : CtxPkt) :
    Semantics (legacyNormalize p) σ τ ↔ Semantics p σ τ :=
  (pairSum_sem _ σ τ).trans
    ((NormalForm.mem_orderedPairs _ _).trans (legacyNetkatNormalForm_mem p σ τ))

set_option maxRecDepth 10000 in
/-- Legacy packet-cardinality proof of star elimination kept for compatibility.
The normalization theorem uses symbolic fixed-point iteration instead. -/
theorem derives_starFree_of_complete (complete : StarFreeComplete) (p : NetKAT) :
    ∃ q, StarFree q ∧ Derives p q := by
  induction p with
  | drop | id | test | completeTest | assign1 =>
    refine ⟨_, ?_, .refl _⟩
    trivial
  | union p q ihp ihq | seq p q ihp ihq =>
    obtain ⟨p', hp', hdp⟩ := ihp
    obtain ⟨q', hq', hdq⟩ := ihq
    first
    | exact ⟨.union p' q', ⟨hp', hq'⟩, .unionCongr hdp hdq⟩
    | exact ⟨.seq p' q', ⟨hp', hq'⟩, .seqCongr hdp hdq⟩
  | star p ih =>
    obtain ⟨q, hq, hd⟩ := ih
    let n := Fintype.card CtxPkt
    have stable : Derives (boundedPolicy q (n + 1)) (boundedPolicy q n) :=
      complete (boundedPolicy_starFree hq _) (boundedPolicy_starFree hq _) (fun σ τ =>
        (boundedPolicy_sem q _ σ τ).trans
          ((reachableWithin_stable_at_card q σ τ).trans (boundedPolicy_sem q _ σ τ).symm))
    exact ⟨_, boundedPolicy_starFree hq _, .trans (.starCongr hd) (derives_star_boundedPolicy (n := n) stable)⟩

private theorem sumOn_map {α β : Type} (xs : List α) (f : α → β) (g : β → NetKAT) :
    sumOn (xs.map f) g = sumOn xs (fun x => g (f x)) := by
  simp [sumOn, List.foldr_map]

private theorem sumOn_append {α : Type} (xs ys : List α) (f : α → NetKAT) :
    Derives (sumOn (xs ++ ys) f) (sumOn xs f ⊕ sumOn ys f) := by
  induction xs with
  | nil => exact .symm (.trans (.plusComm _ _) (.plusZero _))
  | cons x xs ih => exact .trans (.unionCongr (.refl _) ih) (.plusAssoc _ _ _)

private theorem sumOn_flatMap {α β : Type} (xs : List α) (f : α → List β) (g : β → NetKAT) :
    Derives (sumOn (xs.flatMap f) g) (sumOn xs (fun x => sumOn (f x) g)) := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih => exact .trans (sumOn_append _ _ _) (.unionCongr (.refl _) ih)

private theorem field_partition (xs : List FieldName) (hn : xs.Nodup) :
    Derives (sumOn (enumerateFields xs) (fun σ => word (reads σ) xs)) .id := by
  induction xs with
  | nil => exact .plusZero _
  | cons f fs ih =>
    obtain ⟨hnot, hn'⟩ := List.nodup_cons.mp hn
    refine .trans (sumOn_flatMap _ _ _) (.trans (sumOn_congr ?_) (ih hn'))
    intro σ _
    change Derives
      (sumOn (values.map (fun v => Packet.update σ f v)) (fun p => word (reads p) (f :: fs)))
      (word (reads σ) fs)
    have hp : Derives
        (sumOn values (fun v => word (reads (Packet.update σ f v)) (f :: fs)))
        (sumOn values (fun v => NetKAT.fieldTest f v ⨟ word (reads σ) fs)) := by
      apply sumOn_congr
      intro v _
      apply Derives.seqCongr
      · simp [reads, Packet.update]
        exact .refl _
      · apply word_congr
        intro g hg
        have hgf : g ≠ f := fun h => hnot (h ▸ hg)
        simp [reads, Packet.update, hgf, Ne.symm hgf]
        exact .refl _
    change Derives
      (sumOn values (fun v => word (reads (Packet.update σ f v)) (f :: fs)))
      (word (reads σ) fs)
    exact .trans hp (.trans (.symm (sumOn_seq_right values (NetKAT.fieldTest f) _))
      (.trans (.seqCongr (.paMatchAll f) (.refl _)) (.oneSeq _)))

/-- The complete tests partition identity by the packet-field axioms. -/
theorem completeTest_partition :
    Derives .id (sumOn packetList (fun σ => .completeTest σ)) :=
  .symm (.trans (sumOn_congr (fun σ _ => read_eq σ))
    (field_partition NetKAT.fieldEnum NetKAT.fieldEnum_nodup))

theorem derives_id_diagonal : Derives .id (pairSum (packetList.map fun σ => (σ, σ))) := by
  apply Derives.trans completeTest_partition
  change Derives (sumOn packetList (fun σ => .completeTest σ))
    (sumOn (packetList.map fun σ => (σ, σ)) NormalForm.ofSummand)
  rw [sumOn_map]
  exact sumOn_congr (fun σ _ => .symm (read_write_self σ))

theorem derives_assign1_pairs (f : FieldName) (v : FieldValueEnum) :
    Derives (schema := ctxSchema) (.assign1 f v)
      (pairSum (packetList.map fun σ => (σ, Packet.update σ f v))) := by
  let xs : List (CompleteTest × CompleteAssignmentValuation) := packetList.map fun σ => (σ, σ)
  have hd : Derives (.assign1 f v)
      (sumOn xs (fun b => NormalForm.ofSummand b ⨟ .assign1 f v)) :=
    .trans (.symm (.oneSeq _))
      (.trans (.seqCongr derives_id_diagonal (.refl _)) (sumOn_seq_right xs NormalForm.ofSummand _))
  refine .trans hd ?_
  change Derives (sumOn (packetList.map fun σ => (σ, σ)) (fun b => NormalForm.ofSummand b ⨟ .assign1 f v))
    (sumOn (packetList.map fun σ => (σ, Packet.update σ f v)) NormalForm.ofSummand)
  rw [sumOn_map, sumOn_map]
  exact sumOn_congr (fun σ _ =>
    .trans (.symm (.seqAssoc _ _ _)) (.seqCongr (.refl _) (write_assign σ f v)))

-- Compatibility with the concrete diagonal partition.
/-- A predicate derives to the diagonal branches for precisely its satisfying packets. -/
theorem derives_test_pairs (p : Predicate) :
    Derives (.test p) (pairSum ((packetList.filter p.eval).map fun σ => (σ, σ))) := by
  let xs := (packetList.filter p.eval).map (fun σ => (σ, σ))
  have h : ∀ σ τ, Semantics (.test p) σ τ ↔ Semantics (pairSum xs) σ τ := by
    intro σ τ
    rw [pairSum_sem]
    change (p.holds σ ∧ σ = τ) ↔ (σ, τ) ∈ xs
    constructor
    · rintro ⟨hp, rfl⟩
      exact List.mem_map.mpr ⟨σ, List.mem_filter.mpr ⟨mem_packetList σ, hp⟩, rfl⟩
    · intro hm
      obtain ⟨ρ, hρ, he⟩ := List.mem_map.mp hm
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ⟨(List.mem_filter.mp hρ).2, rfl⟩
  exact .trans (normalize_derives_test p)
    ((normalize_pairSum (.test p)).derives_of_equiv ⟨xs, rfl⟩
      (fun σ τ => (normalize_correct _ σ τ).trans (h σ τ)))

end DyNetKAT.NetKAT
