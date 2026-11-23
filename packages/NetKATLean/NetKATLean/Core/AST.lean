------------------------------------------------------------------------
-- NetKAT syntax (dup-free fragment: NetKAT^dup-free) with predicate language
--
-- Per the DyNetKAT paper (arXiv:2102.10035v4):
--   Eq. 1, p. 6:   N ::= 0 | 1 | α | π | N + N | N;N | N*  (NetKAT^dup-free)
--   Figure 3, p.5: Pr ::= 0 | 1 | f=v | Pr+Pr | Pr·Pr | ¬Pr (predicates)
--   Definition 4, p.8: Complete tests α = f₁=v₁·...·fₙ=vₙ (total valuations)
--
-- Design decisions:
--   1. Predicate type supports the full boolean predicate language (including
--      negation), as required by Figure 3 and Boolean algebra axioms.
--   2. CompleteTest is a total valuation (distinct from general predicates).
--   3. NetKAT AST has `test` for general predicates and `completeTest` for
--      complete tests. Complete tests are embedded as special cases.
--   4. No `dup` — this is NetKAT^dup-free, the fragment used by DyNetKAT.
------------------------------------------------------------------------

import NetKATLean.Core.Packet
import Mathlib.Data.Finset.Basic

namespace DyNetKAT.NetKAT

open Finset

------------------------------------------------------------------------
-- Predicate syntax (Figure 3, p. 5): Pr ::= 0 | 1 | f=v | Pr+Pr | Pr·Pr | ¬Pr
------------------------------------------------------------------------

/-- NetKAT predicates (boolean conditions on packets).
    Per Figure 3, p. 5 of the paper.
    - pFalse: predicate false (0)
    - pTrue:  predicate true (1)
    - pFieldEq: atomic test f=v
    - pAnd:   conjunction (Pr · Pr)
    - pOr:    disjunction (Pr + Pr)
    - pNot:   negation (¬Pr) -/
inductive Predicate (schema : PacketSchema := ctxSchema)
  | pFalse      : Predicate schema  -- 0 (predicate false)
  | pTrue       : Predicate schema  -- 1 (predicate true)
  | pFieldEq    : FieldEq schema → Predicate schema  -- f=v (atomic equality test)
  | pAnd        : Predicate schema → Predicate schema → Predicate schema  -- Pr · Pr (conjunction)
  | pOr         : Predicate schema → Predicate schema → Predicate schema  -- Pr + Pr (disjunction)
  | pNot        : Predicate schema → Predicate schema  -- ¬Pr (negation)
  deriving DecidableEq

namespace Predicate

private def reprConcrete : Predicate → Std.Format
  | .pFalse => "Predicate.pFalse"
  | .pTrue => "Predicate.pTrue"
  | .pFieldEq f => "(Predicate.pFieldEq " ++ repr f ++ ")"
  | .pAnd a b => "(Predicate.pAnd " ++ reprConcrete a ++ " " ++ reprConcrete b ++ ")"
  | .pOr a b => "(Predicate.pOr " ++ reprConcrete a ++ " " ++ reprConcrete b ++ ")"
  | .pNot a => "(Predicate.pNot " ++ reprConcrete a ++ ")"

instance : Repr Predicate := ⟨fun p _ => reprConcrete p⟩

/-- Evaluate a predicate on a concrete packet. -/
def eval {schema : PacketSchema} (Pr : Predicate schema) (σ : schema.Packet) : Bool :=
  match Pr with
  | .pFalse => false
  | .pTrue => true
  | .pFieldEq fe => letI := schema.valueEq fe.field; decide (σ fe.field = fe.value)
  | .pAnd p q => eval p σ && eval q σ
  | .pOr p q => eval p σ || eval q σ
  | .pNot p => !eval p σ

/-- A predicate holds on a packet when eval returns true. -/
def holds {schema : PacketSchema} (Pr : Predicate schema) (σ : schema.Packet) : Prop := eval Pr σ = true

/-- Embedding of a single field=value test into Predicate. -/
def fieldEq (f : FieldName) (v : FieldValueEnum) : Predicate :=
  .pFieldEq ⟨f, v⟩

/-- Predicate: tpSrc = v8. -/
def tpSrc8 : Predicate := fieldEq .tpSrc .v8

/-- Predicate: tpSrc = v9. -/
def tpSrc9 : Predicate := fieldEq .tpSrc .v9

/-- Negation of tpSrc = v8. -/
def notTpSrc8 : Predicate := .pNot tpSrc8

/-- Disjunction: tpSrc = v8 or tpSrc = v9. -/
def tpSrc8Or9 : Predicate := .pOr tpSrc8 tpSrc9

end Predicate

------------------------------------------------------------------------
-- NetKAT^dup-free syntax (paper p. 6, §I-B)
--   N ::= 0 | 1 | Pr | α | π | N+N | N;N | N*
--   - Pr: general predicates (from Figure 3)
--   - α: complete tests (total valuations, Definition 4)
--   - π: complete assignments (total valuations, Definition 4)
------------------------------------------------------------------------

/-- NetKAT^dup-free syntax — the dup-free fragment used by DyNetKAT.
    See paper p. 6, §I-B. -/
inductive NetKAT (schema : PacketSchema := ctxSchema)
  | drop             : NetKAT schema  -- 0 (drop, empty relation)
  | id               : NetKAT schema  -- 1 (identity)
  | test             : Predicate schema → NetKAT schema  -- Pr (predicate test)
  | completeTest     : schema.Packet → NetKAT schema  -- α (complete test)
  | assign1          : (f : schema.Field) → schema.Value f → NetKAT schema  -- f←v (primitive single-field assignment)
  | union            : NetKAT schema → NetKAT schema → NetKAT schema  -- N + N
  | seq              : NetKAT schema → NetKAT schema → NetKAT schema  -- N ; N
  | star             : NetKAT schema → NetKAT schema  -- N *

------------------------------------------------------------------------
-- Shorthand constructors
------------------------------------------------------------------------

namespace NetKAT

/-- Single-field test f=v. -/
def fieldTestFor {schema : PacketSchema} (f : schema.Field) (v : schema.Value f) : NetKAT schema :=
  .test (.pFieldEq ⟨f, v⟩)

/-- Compatibility shorthand with concrete field and value names. -/
abbrev fieldTest (f : FieldName) (v : FieldValueEnum) : NetKAT :=
  fieldTestFor f v

/-- Embed a complete test (total valuation) into NetKAT. -/
def completeTestEmbed (α : CompleteTest) : NetKAT :=
  .completeTest α

/-- Deterministic enumeration of all field names.  Each field appears exactly once.

    `FieldName` is a concrete 4-element inductive type with constructors
    `.tpSrc`, `.tpDst`, `.swId`, `.port`.  This list provides a fixed,
    decidable ordering of all fields — required so that
    `completeAssignExpr` composes the single-field assignments in a
    deterministic order.

    The `Fintype FieldName` instance (in `Packet.lean`) guarantees that
    these four are **all** the fields; the list below is its explicit
    expansion, which is computable and avoids noncomputable `Finset.toList`. -/
def fieldEnum : List FieldName :=
  [FieldName.tpSrc, FieldName.tpDst, FieldName.swId, FieldName.port]

/-- Build a NetKAT expression that applies a complete-assignment valuation
    as a sequence of primitive single-field assignments.

    For each field `f`, generate `assign1 f (π f)` and compose them
    sequentially with `;`.  Every field appears exactly once, so the
    expression overwrites every field of the packet — matching the paper's
    Definition 4 (`f₁←v₁ · ... · fₙ←vₙ`) at the level of single-field updates.

    The field enumeration is taken from `fieldEnum`, which lists each
    `FieldName` constructor exactly once in a fixed order. -/
def completeAssignExpr (π : CompleteAssignmentValuation) : NetKAT :=
  match fieldEnum with
  | [] => .id
  | f :: fs =>
    let assignRest :=
      fs.foldr (fun f' acc => .seq (assign1 f' (π f')) acc) .id
    .seq (assign1 f (π f)) assignRest

/-- Choice: N + N — shorthand for union -/
def plus (n₁ n₂ : NetKAT) : NetKAT := .union n₁ n₂

/-- Coverage: `fieldEnum` enumerates every `FieldName` constructor exactly once.
    For every field `f`, `f` appears as a member of `fieldEnum`. -/
theorem fieldEnum_complete : ∀ f : FieldName, f ∈ fieldEnum := by
  intro f
  cases f <;> decide

/-- No-duplicates: `fieldEnum` contains each field at most once.
    This is `List.Nodup fieldEnum`. -/
theorem fieldEnum_nodup : List.Nodup fieldEnum := by
  decide

end NetKAT

------------------------------------------------------------------------
-- NetKAT term size (for well-founded induction in star semantics)
------------------------------------------------------------------------

/-- The size of a NetKAT term. -/
def NetKAT.size {schema : PacketSchema} : NetKAT schema → Nat
  | .drop => 1
  | .id => 1
  | .test _ => 1
  | .completeTest _ => 1
  | .assign1 _ _ => 1
  | .union n₁ n₂ => 1 + size n₁ + size n₂
  | .seq n₁ n₂ => 1 + size n₁ + size n₂
  | .star n => 1 + size n

------------------------------------------------------------------------
-- Concrete examples
------------------------------------------------------------------------

/-- The NetKAT term `0` (drop). -/
example : NetKAT := .drop

/-- The NetKAT term `1` (identity). -/
example : NetKAT := .id

/-- A test: tpSrc = v8 (via predicate). -/
def tpSrc8Test : NetKAT := NetKAT.fieldTest .tpSrc .v8

/-- Sequencing: (tpSrc = v8) ; drop -/
def examplePolicy : NetKAT := .seq tpSrc8Test .drop

/-- Choice: id + drop -/
def exampleChoice : NetKAT := .plus .id .drop

/-- Star: id* -/
def exampleStar : NetKAT := .star .id

------------------------------------------------------------------------
-- Predicate Boolean algebra lemmas
------------------------------------------------------------------------

namespace Predicate

/-- Double negation elimination: ¬¬Pr evaluates the same as Pr. -/
theorem not_not (Pr : Predicate) (σ : CtxPkt) :
    eval (.pNot (.pNot Pr)) σ = eval Pr σ := by
  simp [eval]

/-- Excluded middle: Pr ∨ ¬Pr is always true. -/
theorem excluded_middle (Pr : Predicate) (σ : CtxPkt) :
    eval (.pOr Pr (.pNot Pr)) σ = true := by
  simp [eval, Bool.or, Bool.not]
  cases eval Pr σ <;> simp

/-- Contradiction: Pr ∧ ¬Pr is always false. -/
theorem contra (Pr : Predicate) (σ : CtxPkt) :
    eval (.pAnd Pr (.pNot Pr)) σ = false := by
  simp [eval, Bool.and, Bool.not]
  cases eval Pr σ <;> simp

/-- De Morgan's law: ¬(Pr₁ ∨ Pr₂) = ¬Pr₁ ∧ ¬Pr₂. -/
theorem deMorgan_or (Pr₁ Pr₂ : Predicate) (σ : CtxPkt) :
    eval (.pNot (.pOr Pr₁ Pr₂)) σ = eval (.pAnd (.pNot Pr₁) (.pNot Pr₂)) σ := by
  simp [eval, Bool.not_or, Bool.and]

/-- De Morgan's law: ¬(Pr₁ ∧ Pr₂) = ¬Pr₁ ∨ ¬Pr₂. -/
theorem deMorgan_and (Pr₁ Pr₂ : Predicate) (σ : CtxPkt) :
    eval (.pNot (.pAnd Pr₁ Pr₂)) σ = eval (.pOr (.pNot Pr₁) (.pNot Pr₂)) σ := by
  simp [eval, Bool.not_and, Bool.or]

end Predicate

end DyNetKAT.NetKAT
