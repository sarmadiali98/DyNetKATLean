------------------------------------------------------------------------
-- Core `head` extraction for the DyNetKAT safety pipeline (S4A)
--
-- Per the DyNetKAT paper (arXiv:2102.10035v4, §V, Eqs. (29)–(32)):
--
--   head(⊥)            = 0                    (29)
--   head(N;D)          = N + head(D)          (30)
--   head(D ⊕ Q)        = head(D) + head(Q)    (31)
--   head(rcfg_{X,N};D) = 0                    (32)
--
-- The paper states (§V): "we assume the input D to the operators head and
-- tail do not contain terms of shape x?q and x!q. This can be ensured by
-- always applying the restriction operator δ on D."  The tool applies
-- `head` to restricted, projected normal forms.
--
-- This module implements `head` on the core fragment spanned by the four
-- equations above, using the actual constructors of `DyNetKAT/AST.lean`:
-- `deadlock`, `nSeq`, `choice`, `rcfgPrefix`.  Every other constructor
-- (recv, send, parallel, leftMerge, commMerge, restrict, project, var) is
-- OUTSIDE the supported fragment and yields explicit failure (`none`),
-- never a silently-extracted policy:
--
--   - `recv`/`send` are communication prefixes, NOT deadlock (⊥): the
--     paper excludes them from `head`'s domain via restriction δ.
--   - `var` is not resolved: recursive variables are unfolded only by a
--     separate projection/unfolding stage (not part of S4A).
--   - `parallel`/`leftMerge`/`commMerge` are not assumed normalized.
--   - NetKAT `.drop` (the extracted `0` of Eq. (29)) is a NetKAT policy;
--     DyNetKAT `.deadlock` (⊥) is a process.  They are distinct types.
--   - NetKAT `union` (+) and DyNetKAT `choice` (⊕) are distinct
--     constructors: Eq. (31) maps a process-level ⊕ to a policy-level +.
--
-- Scope boundary: this module characterizes the paper's `head` equations
-- on the supported syntactic fragment only (theorem `head_spec`).  It does
-- NOT implement `tail`, normalization, restriction δ, projection π_n,
-- recursive-variable resolution, safety-property compilation, or verdicts,
-- and it does NOT establish correctness of the complete DyNetiKAT safety
-- pipeline against arbitrary `Step` traces.
------------------------------------------------------------------------

import DyNetKATLean.Core.AST
import NetKATLean.Core.Semantics

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

variable {schema : NetKAT.PacketSchema}

open DyNetKAT.NetKAT

------------------------------------------------------------------------
-- Core `head` operator (paper Eqs. (29)–(32))
------------------------------------------------------------------------

/-- Core `head` operator (paper §V, Eqs. (29)–(32)).

    Extracts the NetKAT policy representing the current configuration of a
    DyNetKAT process: the sum of all NetKAT policies reachable before any
    reconfiguration event.

    Supported fragment (paper equations, using the actual constructors):
    - `head deadlock           = some .drop`               (29) head(⊥) = 0
    - `head (nSeq N D)         = some (N + head(D))`       (30) head(N;D) = N + head(D)
    - `head (choice D Q)       = some (head(D) + head(Q))` (31)
    - `head (rcfgPrefix x N D) = some .drop`               (32) head(rcfg;D) = 0

    Unsupported constructors return `none` (explicit failure):
    `recv`, `send` (excluded by the paper's restriction precondition -
    they are NOT deadlock), `parallel`, `leftMerge`, `commMerge`,
    `restrict`, `project`, `var` (variables are not resolved here).

    Failure propagates: if a subterm of a supported shape fails, the whole
    extraction fails, so an unsupported subterm is never silently treated
    as the zero policy.  Structurally recursive and executable. -/
def head : DyNetKAT schema → Option (NetKAT schema)
  | .deadlock => some .drop
  | .nSeq N D =>
      match head D with
      | some H => some (NetKAT.union N H)
      | none => none
  | .choice D Q =>
      match head D, head Q with
      | some H₁, some H₂ => some (NetKAT.union H₁ H₂)
      | _, _ => none
  | .rcfgPrefix _ _ _ => some .drop
  | .recv _ _ _ => none
  | .send _ _ _ => none
  | .parallel _ _ => none
  | .leftMerge _ _ => none
  | .commMerge _ _ => none
  | .restrict _ _ => none
  | .project _ _ => none
  | .var _ => none

------------------------------------------------------------------------
-- Defining equations (paper Eqs. (29)–(32))
------------------------------------------------------------------------

/-- Eq. (29): `head(⊥) = 0`.  The extracted `0` is the NetKAT policy
    `.drop`; ⊥ itself is the DyNetKAT process `.deadlock`. -/
theorem head_deadlock : head (schema := schema) .deadlock = some .drop := rfl

/-- Eq. (30): `head(N;D) = N + head(D)`, as a match on the optional
    sub-result.  If `head D` fails, the whole extraction fails. -/
theorem head_nSeq (N : NetKAT schema) (D : DyNetKAT schema) :
    head (.nSeq N D) =
      (match head D with
       | some H => some (NetKAT.union N H)
       | none => none) := rfl

/-- Eq. (31): `head(D ⊕ Q) = head(D) + head(Q)`, as a match on the two
    optional sub-results.  If either side fails, the whole extraction
    fails. -/
theorem head_choice (D Q : DyNetKAT schema) :
    head (.choice D Q) =
      (match head D, head Q with
       | some H₁, some H₂ => some (NetKAT.union H₁ H₂)
       | _, _ => none) := rfl

/-- Eq. (32): `head(rcfg_{X,N};D) = 0`.  The reconfiguration prefix
    contributes no packet-processing policy and its continuation `D` is
    ignored by `head` (it belongs to `tail`). -/
theorem head_rcfgPrefix (x : Channel) (N : NetKAT schema) (D : DyNetKAT schema) :
    head (.rcfgPrefix x N D) = some .drop := rfl

/-- Eq. (30) in the paper's shape: if `head D` succeeds with `H`, then
    `head (N;D) = N + H`. -/
theorem head_nSeq_eq (N : NetKAT schema) (D : DyNetKAT schema) (H : NetKAT schema)
    (hD : head D = some H) :
    head (.nSeq N D) = some (NetKAT.union N H) := by
  rw [head_nSeq, hD]

/-- Eq. (31) in the paper's shape: if `head D` and `head Q` succeed with
    `H₁` and `H₂`, then `head (D ⊕ Q) = H₁ + H₂`. -/
theorem head_choice_eq (D Q : DyNetKAT schema) (H₁ H₂ : NetKAT schema)
    (hD : head D = some H₁) (hQ : head Q = some H₂) :
    head (.choice D Q) = some (NetKAT.union H₁ H₂) := by
  rw [head_choice, hD, hQ]

/-- Failure propagation through `N;D`: if `head D` fails, `head (N;D)`
    fails. -/
theorem head_nSeq_none (N : NetKAT schema) (D : DyNetKAT schema) (h : head D = none) :
    head (.nSeq N D) = none := by
  rw [head_nSeq, h]

/-- Failure propagation through `D ⊕ Q` from the left branch. -/
theorem head_choice_none_left (D Q : DyNetKAT schema) (h : head D = none) :
    head (.choice D Q) = none := by
  rw [head_choice, h]

/-- Failure propagation through `D ⊕ Q` from the right branch.  The match
    in Eq. (31) scrutinizes the left branch first, so both possible values
    of `head D` are discharged explicitly. -/
theorem head_choice_none_right (D Q : DyNetKAT schema) (h : head Q = none) :
    head (.choice D Q) = none := by
  cases hD : head D with
  | none => rw [head_choice, hD, h]
  | some H₁ => rw [head_choice, hD, h]

------------------------------------------------------------------------
-- Supported fragment (Step 3)
------------------------------------------------------------------------

/-- Syntactic predicate characterizing the smallest fragment on which
    core `head` extraction is supported: exactly the shapes covered by
    the paper's Eqs. (29)–(32).

    - `deadlock` is supported unconditionally (Eq. 29).
    - `nSeq N D` is supported when the continuation `D` is supported
      (Eq. 30 recurses into `D`).
    - `choice D Q` is supported when both branches are supported
      (Eq. 31 recurses into both).
    - `rcfgPrefix x N D` is supported unconditionally: Eq. (32) discards
      the continuation, so no condition is put on `D`.

    Every other constructor is outside the fragment; for such expressions
    `head` returns `none` (explicit failure). -/
inductive HeadSupported {schema : NetKAT.PacketSchema} : DyNetKAT schema → Prop
  | deadlock : HeadSupported .deadlock
  | nSeq : ∀ (N : NetKAT schema) (D : DyNetKAT schema),
      HeadSupported D → HeadSupported (.nSeq N D)
  | choice : ∀ (D Q : DyNetKAT schema),
      HeadSupported D → HeadSupported Q → HeadSupported (.choice D Q)
  | rcfgPrefix : ∀ (x : Channel) (N : NetKAT schema) (D : DyNetKAT schema),
      HeadSupported (.rcfgPrefix x N D)

/-- Every expression in the supported fragment produces a successful
    `head` result.  This is the domain theorem for `head`: extraction
    never fails on `HeadSupported` input. -/
theorem head_supported_some (D : DyNetKAT schema) (h : HeadSupported D) :
    ∃ H : NetKAT schema, head D = some H := by
  induction h with
  | deadlock => exact ⟨.drop, head_deadlock⟩
  | nSeq N D _ ih =>
      obtain ⟨H, hH⟩ := ih
      exact ⟨NetKAT.union N H, head_nSeq_eq N D H hH⟩
  | choice D Q _ _ ihD ihQ =>
      obtain ⟨H₁, hH₁⟩ := ihD
      obtain ⟨H₂, hH₂⟩ := ihQ
      exact ⟨NetKAT.union H₁ H₂, head_choice_eq D Q H₁ H₂ hH₁ hH₂⟩
  | rcfgPrefix x N D => exact ⟨.drop, head_rcfgPrefix x N D⟩

/-- Totality with explicit failure: every DyNetKAT expression either is
    supported or makes `head` fail explicitly with `none`.  No expression
    is silently mapped to a policy. -/
theorem head_none_or_supported (D : DyNetKAT schema) :
    head D = none ∨ HeadSupported D := by
  induction D with
  | deadlock => exact Or.inr HeadSupported.deadlock
  | nSeq N D ih =>
      rcases ih with hnone | hsup
      · exact Or.inl (head_nSeq_none N D hnone)
      · exact Or.inr (HeadSupported.nSeq N D hsup)
  | choice D Q ihD ihQ =>
      rcases ihD with hnoneD | hsupD
      · exact Or.inl (head_choice_none_left D Q hnoneD)
      · rcases ihQ with hnoneQ | hsupQ
        · exact Or.inl (head_choice_none_right D Q hnoneQ)
        · exact Or.inr (HeadSupported.choice D Q hsupD hsupQ)
  | rcfgPrefix x N D => exact Or.inr (HeadSupported.rcfgPrefix x N D)
  | recv x N D => exact Or.inl rfl
  | send x N D => exact Or.inl rfl
  | parallel D Q _ _ => exact Or.inl rfl
  | leftMerge D Q _ _ => exact Or.inl rfl
  | commMerge D Q _ _ => exact Or.inl rfl
  | restrict actions D _ => exact Or.inl rfl
  | project n D _ => exact Or.inl rfl
  | var X => exact Or.inl rfl

------------------------------------------------------------------------
-- Independent semantic specification (Step 4)
------------------------------------------------------------------------

/-- Independent relational specification of `head` (paper Eqs. (29)–(32)).

    `HeadSpec D σ τ` holds exactly when the packet pair `(σ, τ)` is
    contributed by the NetKAT policy that `head` should extract from `D`:

      HeadSpec ⊥ (σ,τ)        = false                            (Eq. 29)
      HeadSpec (N;D) (σ,τ)    = ⟦N⟧(σ,τ) ∨ HeadSpec D (σ,τ)      (Eq. 30)
      HeadSpec (D⊕Q) (σ,τ)    = HeadSpec D (σ,τ) ∨ HeadSpec Q (σ,τ)  (Eq. 31)
      HeadSpec (rcfg_{X,N};D) = false                            (Eq. 32)

    The relation is defined by its own constructors and never mentions
    `head`: the only constructors are the ones for the supported shapes,
    so `HeadSpec` is uninhabited (the empty relation) for `deadlock`,
    `rcfgPrefix`, and every unsupported shape.  The characterization
    theorem `head_spec` is stated only on `HeadSupported` inputs; the
    empty spec on unsupported shapes is never used to claim anything
    about them. -/
inductive HeadSpec {schema : NetKAT.PacketSchema} : DyNetKAT schema → schema.Packet → schema.Packet → Prop
  | nSeq_of_sem (N : NetKAT schema) (D : DyNetKAT schema) (σ τ : schema.Packet)
      (h : Semantics N σ τ) : HeadSpec (.nSeq N D) σ τ
  | nSeq_of_tail (N : NetKAT schema) (D : DyNetKAT schema) (σ τ : schema.Packet)
      (h : HeadSpec D σ τ) : HeadSpec (.nSeq N D) σ τ
  | choice_left (D Q : DyNetKAT schema) (σ τ : schema.Packet)
      (h : HeadSpec D σ τ) : HeadSpec (.choice D Q) σ τ
  | choice_right (D Q : DyNetKAT schema) (σ τ : schema.Packet)
      (h : HeadSpec Q σ τ) : HeadSpec (.choice D Q) σ τ

/-- ⟦0⟧ is the empty relation (local restatement of the NetKAT zero
    semantics; cf. `DyNetKAT.NetKAT.drop_empty`). -/
theorem sem_drop_empty (σ τ : schema.Packet) : ¬ Semantics (schema := schema) .drop σ τ :=
  fun h => h

/-- Spec clause for Eq. (30): the head-contribution relation of `N;D` is
    the union of ⟦N⟧ and the contribution of `D`. -/
theorem headSpec_nSeq_iff (N : NetKAT schema) (D : DyNetKAT schema) (σ τ : schema.Packet) :
    HeadSpec (.nSeq N D) σ τ ↔ (Semantics N σ τ ∨ HeadSpec D σ τ) := by
  constructor
  · intro h
    cases h with
    | nSeq_of_sem _ _ _ _ hN => exact Or.inl hN
    | nSeq_of_tail _ _ _ _ ht => exact Or.inr ht
  · intro h
    rcases h with hN | ht
    · exact HeadSpec.nSeq_of_sem N D σ τ hN
    · exact HeadSpec.nSeq_of_tail N D σ τ ht

/-- Spec clause for Eq. (31): the head-contribution relation of `D ⊕ Q`
    is the union of the contributions of `D` and `Q`. -/
theorem headSpec_choice_iff (D Q : DyNetKAT schema) (σ τ : schema.Packet) :
    HeadSpec (.choice D Q) σ τ ↔ (HeadSpec D σ τ ∨ HeadSpec Q σ τ) := by
  constructor
  · intro h
    cases h with
    | choice_left _ _ _ _ h1 => exact Or.inl h1
    | choice_right _ _ _ _ h2 => exact Or.inr h2
  · intro h
    rcases h with h1 | h2
    · exact HeadSpec.choice_left D Q σ τ h1
    · exact HeadSpec.choice_right D Q σ τ h2

/-- Spec clause for Eq. (29): ⊥ contributes the empty relation. -/
theorem headSpec_deadlock_false (σ τ : schema.Packet) : ¬ HeadSpec .deadlock σ τ := by
  intro h
  cases h

/-- Spec clause for Eq. (32): a reconfiguration prefix contributes the
    empty relation. -/
theorem headSpec_rcfgPrefix_false (x : Channel) (N : NetKAT schema) (D : DyNetKAT schema)
    (σ τ : schema.Packet) : ¬ HeadSpec (.rcfgPrefix x N D) σ τ := by
  intro h
  cases h

/-- Semantic characterization of `head` on the supported fragment.

    For any supported input `D`, if `head` returns `H`, then the extracted
    NetKAT policy `H` denotes exactly the head-contribution relation of
    `D`:

      ∀ σ τ, ⟦H⟧(σ,τ) ↔ HeadSpec D (σ,τ)

    This characterizes the paper's `head` equations (29)–(32) on the
    supported syntactic fragment: the extracted policy's relational
    semantics coincides with the independently specified contribution of
    each supported constructor (empty for ⊥ and rcfg-prefixes, ⟦N⟧ plus
    the recursive contribution for `N;D`, the union of both branches for
    `D⊕Q`).

    This does NOT establish correctness of the complete DyNetiKAT safety
    pipeline against arbitrary `Step` traces: no `tail`, no restriction δ,
    no projection π_n, no recursive unfolding, no property compilation. -/
theorem head_spec (D : DyNetKAT schema) (hsup : HeadSupported D) (σ τ : schema.Packet) :
    ∀ H : NetKAT schema, head D = some H → (Semantics H σ τ ↔ HeadSpec D σ τ) := by
  induction hsup with
  | deadlock =>
      intro H hhead
      have hH : H = .drop := by
        rw [head_deadlock] at hhead
        exact (Option.some.inj hhead).symm
      subst hH
      constructor
      · intro hsem
        exact absurd hsem (sem_drop_empty σ τ)
      · intro hspec
        exact absurd hspec (headSpec_deadlock_false σ τ)
  | nSeq N D hDsup ih =>
      intro H hhead
      obtain ⟨H', hH'⟩ := head_supported_some D hDsup
      rw [head_nSeq_eq N D H' hH'] at hhead
      have hH : H = NetKAT.union N H' := (Option.some.inj hhead).symm
      subst hH
      rw [headSpec_nSeq_iff N D σ τ]
      constructor
      · intro hsem
        rcases (union_sem N H' σ τ).mp hsem with hN | htail
        · exact Or.inl hN
        · exact Or.inr ((ih H' hH').mp htail)
      · intro hspec
        rcases hspec with hN | htail
        · exact (union_sem N H' σ τ).mpr (Or.inl hN)
        · exact (union_sem N H' σ τ).mpr (Or.inr ((ih H' hH').mpr htail))
  | choice D Q hDsup hQsup ihD ihQ =>
      intro H hhead
      obtain ⟨H₁, hH₁⟩ := head_supported_some D hDsup
      obtain ⟨H₂, hH₂⟩ := head_supported_some Q hQsup
      rw [head_choice_eq D Q H₁ H₂ hH₁ hH₂] at hhead
      have hH : H = NetKAT.union H₁ H₂ := (Option.some.inj hhead).symm
      subst hH
      rw [headSpec_choice_iff D Q σ τ]
      constructor
      · intro hsem
        rcases (union_sem H₁ H₂ σ τ).mp hsem with h₁ | h₂
        · exact Or.inl ((ihD H₁ hH₁).mp h₁)
        · exact Or.inr ((ihQ H₂ hH₂).mp h₂)
      · intro hspec
        rcases hspec with h₁ | h₂
        · exact (union_sem H₁ H₂ σ τ).mpr (Or.inl ((ihD H₁ hH₁).mpr h₁))
        · exact (union_sem H₁ H₂ σ τ).mpr (Or.inr ((ihQ H₂ hH₂).mpr h₂))
  | rcfgPrefix x N D =>
      intro H hhead
      have hH : H = .drop := by
        rw [head_rcfgPrefix] at hhead
        exact (Option.some.inj hhead).symm
      subst hH
      constructor
      · intro hsem
        exact absurd hsem (sem_drop_empty σ τ)
      · intro hspec
        exact absurd hspec (headSpec_rcfgPrefix_false x N D σ τ)

end DyNetKAT.DyNetKAT
