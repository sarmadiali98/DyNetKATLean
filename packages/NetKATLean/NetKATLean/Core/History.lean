------------------------------------------------------------------------
-- Canonical nonempty packet histories
--
-- Per the DyNetKAT paper (arXiv:2102.10035v4), Figure 3 (p. 5) evaluates
-- NetKAT policies over packet histories:
--
--   ⟦f=n⟧(σ::h) = {σ::h} if σ(f)=n, {} otherwise
--   ⟦f←n⟧(σ::h) = {σ[f:=n]::h}
--   ⟦dup⟧(σ::h) = {σ::(σ::h)}
--
-- Definition 1 (p. 5) defines histories as (possibly empty) packet lists;
-- the test, assignment and dup clauses are only defined on nonempty
-- histories σ::h.  This module introduces the canonical nonempty history
-- representation `History` (head packet + tail list), mirroring the
-- paper's σ::h.
--
-- This type is distinct from the pending/handled packet queues of
-- DyNetKAT configurations (`DyNetKAT.Config.pending`/`handled`), which
-- are plain `List CtxPkt` queues, not NetKAT histories.
--
-- No `Fintype History` instance is registered: the set of finite nonempty
-- histories is countably infinite (tails are unbounded), so it cannot be
-- enumerated.  Enumeration stays at packet level.
------------------------------------------------------------------------

import NetKATLean.Core.Packet
import NetKATLean.Core.AST

namespace DyNetKAT.NetKAT

/-- A nonempty packet history: the paper's `σ :: h` (Definition 1, p. 5).

    `head` is the most recent packet σ; `tail` is the rest h (possibly
    empty).  The empty history ⟨⟩ of the paper is deliberately not
    representable: every history has a head, so tests and assignments are
    total on `History`, removing the paper's clause partiality on ⟨⟩. -/
structure History (P : Type := CtxPkt) where
  head : P
  tail : List P

namespace History

variable {P : Type}

------------------------------------------------------------------------
-- Basic structural operations
------------------------------------------------------------------------

/-- The singleton history `σ :: ⟨⟩` - the evaluation input of the SOS
    premise of rule `(cpolX;)` (Figure 8, p. 10). -/
def singleton (σ : P) : History P := ⟨σ, []⟩

/-- The packet list of a history: `σ :: h ↦ σ :: h` as a `List P`.
    Always nonempty. -/
def toList (h : History P) : List P := h.head :: h.tail

/-- Prepend a packet to a history: `σ :: (τ :: h)`.

    This is the history-building step of the paper's `dup` clause,
    `⟦dup⟧(σ::h) = {σ::(σ::h)}`. -/
def prepend (σ : P) (h : History P) : History P := ⟨σ, h.toList⟩

------------------------------------------------------------------------
-- Basic structural properties
------------------------------------------------------------------------

/-- Converting a singleton history to a list yields `[σ]`. -/
theorem toList_singleton (σ : P) : (singleton σ).toList = [σ] := rfl

/-- Prepending a packet produces the expected list:
    `(prepend σ h).toList = σ :: h.toList`. -/
theorem toList_prepend (σ : P) (h : History P) :
    (prepend σ h).toList = σ :: h.toList := rfl

/-- Every converted history is nonempty. -/
theorem toList_ne_nil (h : History P) : h.toList ≠ [] := by
  cases h
  intro hcon
  exact absurd hcon (List.cons_ne_nil _ _)

/-- The list representation is injective. -/
theorem toList_injective : Function.Injective (@toList P) := by
  rintro ⟨σ₁, t₁⟩ ⟨σ₂, t₂⟩ h
  have h' : σ₁ :: t₁ = σ₂ :: t₂ := h
  injection h' with e₁ e₂
  rw [e₁, e₂]

/-- Singleton histories have empty tails. -/
theorem singleton_tail (σ : P) : (singleton σ).tail = [] := rfl

------------------------------------------------------------------------
-- Decidable equality
------------------------------------------------------------------------

/-- Decidable equality on the concrete packet space, via the explicit
    field enumeration (same construction as the instances in
    `Evaluator.lean` and `Decision.lean`).  Kept as a private definition
    so that no second global `DecidableEq CtxPkt` instance is registered
    (the existing global instance lives in `Decision.lean`). -/
private def decidableEqCtxPkt : DecidableEq CtxPkt := ctxSchema.packetEq

/-- Decidable equality on histories, via the injective list encoding
    (`toList_injective`). -/
instance instDecidableEqHistory : DecidableEq History := by
  haveI := decidableEqCtxPkt
  intro h₁ h₂
  exact decidable_of_iff (h₁.toList = h₂.toList)
    ⟨fun heq => toList_injective heq, fun h => congrArg toList h⟩

end History

end DyNetKAT.NetKAT
