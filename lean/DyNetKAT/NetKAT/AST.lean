import DyNetKAT.NetKAT.Packet
import Mathlib.Data.Finset.Insert

namespace DyNetKAT.NetKAT
open Finset

------------------------------------------------------------------------
-- NetKAT syntax (dup-free fragment: NetKAT⁻ᵈᵘᵖ)
------------------------------------------------------------------------
-- Per the DyNetKAT paper (arXiv:2102.10035v4, p. 6, §I-B):
--
--   N ::= 0 | 1 | f=v | f←v | α | π | N + N | N;N | N*
--
-- where α ranges over complete tests, π over complete assignments.
-- The dup operator from full NetKAT is excluded: this is NetKAT⁻ᵈᵘᵖ.

set_option linter.dupNamespace false

/-- NetKAT⁻ᵈᵘᵖ syntax — the dup-free fragment used by DyNetKAT.
    See paper p. 6, §I-B. -/
inductive NetKAT
  | drop      : NetKAT                              -- 0 (drop)
  | id        : NetKAT                              -- 1 (identity)
  | test      : Finset FieldEq → NetKAT             -- α (complete test)
  | assign    : (Packet → Packet) → NetKAT           -- π (complete assignment: transformation)
  | union     : NetKAT → NetKAT → NetKAT            -- N + N
  | seq       : NetKAT → NetKAT → NetKAT            -- N ; N
  | star      : NetKAT → NetKAT                     -- N *

------------------------------------------------------------------------
-- Shorthand constructors
------------------------------------------------------------------------

/-- Single-field test f=v. -/
def NetKAT.fieldTest (f : FieldName) (v : FieldValue) : NetKAT :=
  .test (singleton ⟨f, v⟩)

/-- Single-field assignment f←v. -/
def NetKAT.fieldAssign (f : FieldName) (v : FieldValue) : NetKAT :=
  .assign (fun σ => Packet.update σ f v)

/-- Choice: N + N — shorthand for union -/
def NetKAT.plus (n₁ n₂ : NetKAT) : NetKAT := .union n₁ n₂

------------------------------------------------------------------------
-- NetKAT term size (for well-founded induction in star semantics)
------------------------------------------------------------------------

/-- The size of a NetKAT term. -/
def NetKAT.size : NetKAT → Nat
  | .drop => 1
  | .id => 1
  | .test _ => 1
  | .assign _ => 1
  | .union n₁ n₂ => 1 + size n₁ + size n₂
  | .seq n₁ n₂ => 1 + size n₁ + size n₂
  | .star n => 1 + size n

------------------------------------------------------------------------
-- Examples
------------------------------------------------------------------------

/-- The NetKAT term `0` (drop). -/
example : NetKAT := .drop

/-- The NetKAT term `1` (identity). -/
example : NetKAT := .id

/-- A test: tpSrc = 8. -/
def tpSrc8 : NetKAT := .fieldTest .tpSrc FieldValue.v8

/-- Sequencing: (tpSrc = 8) ; drop -/
def examplePolicy : NetKAT := .seq tpSrc8 .drop

/-- Choice: id + drop -/
def exampleChoice : NetKAT := .plus .id .drop

/-- Star: id* -/
def exampleStar : NetKAT := .star .id

end DyNetKAT.NetKAT
