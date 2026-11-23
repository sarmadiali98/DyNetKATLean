import NetKATLean

namespace DyNetKAT.NetKAT

private def port0 := NetKAT.fieldTest .port .v0

-- PA-CONTRA and PA-MATCH-ALL, the bottom two packet equations.
example : Derives (.seq port0 (.fieldTest .port .v9)) .drop :=
  .paContra (schema := ctxSchema) .port .v0 .v9 (by decide)

example : Derives (matchAll .port) .id := .paMatchAll .port

private theorem portAbsorbed : Derives (.union port0 .id) .id :=
  .baPlusOne (schema := ctxSchema) (.pFieldEq ⟨.port, .v0⟩)

-- The left and right induction premises use the equational KAT order.
example : Derives (.union (.seq (.star port0) .id) .id) .id := by
  apply Derives.lfpL
  exact .trans (.unionCongr
    (.trans (.unionCongr (.refl _) (.seqOne _))
      (.trans (.plusComm _ _) portAbsorbed)) (.refl _)) (.plusIdem _)

example : Derives (.union (.seq .id (.star port0)) .id) .id := by
  apply Derives.lfpR
  exact .trans (.unionCongr
    (.trans (.unionCongr (.refl _) (.oneSeq _))
      (.trans (.plusComm _ _) portAbsorbed)) (.refl _)) (.plusIdem _)

#guard netkatIsZero (.seq port0 (.fieldTest .port .v9))
#guard netkatEquiv (matchAll .port) .id

#print axioms starLfpLeft
#print axioms starLfpRight
#print axioms paContra_sem
#print axioms paMatchAll_sem
#print axioms Derives.sound
#print axioms Derives.historySound

end DyNetKAT.NetKAT
