import DyNetKAT

------------------------------------------------------------------------
-- Executable checks for the canonical nonempty packet history
-- (`DyNetKAT.NetKAT.History`).
--
-- Run with:  lake env lean test_history.lean   (from lean/)
--
-- Verifies singleton construction and prepending, plus the structural
-- lemmas of `History.lean`, on the concrete packet space.
------------------------------------------------------------------------

open DyNetKAT.NetKAT

------------------------------------------------------------------------
-- Singleton construction
------------------------------------------------------------------------

-- `singleton σ` is the paper's `σ :: ⟨⟩`: head σ, empty tail.
example (σ : CtxPkt) : (History.singleton σ).head = σ := rfl

example (σ : CtxPkt) : (History.singleton σ).tail = [] :=
  History.singleton_tail σ

example (σ : CtxPkt) : (History.singleton σ).toList = [σ] :=
  History.toList_singleton σ

------------------------------------------------------------------------
-- Prepending
------------------------------------------------------------------------

-- `prepend σ h` puts σ in front of the history's packet list.
example (σ : CtxPkt) (h : History) :
    (History.prepend σ h).toList = σ :: h.toList :=
  History.toList_prepend σ h

-- Concretely: prepending to a singleton yields a two-packet history.
example (σ τ : CtxPkt) :
    (History.prepend σ (History.singleton τ)).toList = [σ, τ] := rfl

-- The tail of the original history is preserved under prepend.
example (σ : CtxPkt) (h : History) :
    (History.prepend σ h).tail = h.toList := rfl

------------------------------------------------------------------------
-- Structural lemmas
------------------------------------------------------------------------

-- Every converted history is nonempty.
example (h : History) : h.toList ≠ [] := History.toList_ne_nil h

-- The list representation is injective.
example : Function.Injective (@History.toList CtxPkt) := History.toList_injective

------------------------------------------------------------------------
-- Executable checks (decidable equality computes)
------------------------------------------------------------------------

#eval History.singleton examplePacket == History.singleton examplePacket  -- true
#eval History.singleton examplePacket == History.singleton examplePacket9 -- false
#eval (History.prepend examplePacket9 (History.singleton examplePacket)).toList.length -- 2
#eval decide ((History.prepend examplePacket9 (History.singleton examplePacket)).toList
  = [examplePacket9, examplePacket]) -- true
