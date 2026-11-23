import NetKATLean.Core.Symbolic
import NetKATLean.Core.Normalization

/-! The proof-only bridge to E_NK. Symbolic closure supplies the star
certificates. The star-free comparison uses the existing field partition
and pair-sum laws. -/

namespace DyNetKAT.NetKAT

/-- Packet-specific completeness through symbolic star closure and the
star-free field-partition laws. -/
theorem netkatNativeEquiv_iff_derives {schema : PacketSchema} [DiagramLayout schema]
    (p q : NetKAT schema) :
    netkatNativeEquiv p q = true ↔ Derives p q := by
  rw [netkatNativeEquiv_correct]
  constructor
  · intro h
    obtain ⟨r, hf, hr⟩ := exists_derives_starFree_symbolic p
    obtain ⟨t, hg, ht⟩ := exists_derives_starFree_symbolic q
    exact hr.trans ((derives_of_equiv_starFree hf hg (fun σ τ =>
      (hr.sound σ τ).symm.trans ((h σ τ).trans (ht.sound σ τ)))).trans ht.symm)
  · exact Derives.sound

theorem netkatNativeEquiv_false_not_derives {schema : PacketSchema} [DiagramLayout schema]
    {p q : NetKAT schema}
    (h : netkatNativeEquiv p q = false) : ¬ Derives p q := by
  intro d
  have htrue := netkatNativeEquiv_complete d.sound
  rw [h] at htrue
  contradiction

theorem netkatNativeEquivFinite_iff_derives {schema : PacketSchema} (p q : NetKAT schema) :
    netkatNativeEquivFinite p q = true ↔ Derives p q := by
  letI := schema.diagramLayouts.out
  rw [netkatNativeEquivFinite_correct, ← netkatNativeEquiv_correct, netkatNativeEquiv_iff_derives]

end DyNetKAT.NetKAT
