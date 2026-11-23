import NetKATLean.Core.Denotation
import NetKATLean.Core.Decision

/-! Compatibility surface for concrete evaluation and KATLean denotation. -/

namespace DyNetKAT.NetKAT

/-- The executable finite result set is exactly the KATLean relation. -/
theorem execute_katInterp (policy : NetKAT) (p : CtxPkt) :
    ∃ outputs : Finset CtxPkt, execute policy p = .supported outputs ∧
      ∀ q, q ∈ outputs ↔ (katInterp policy).holds p q := by
  obtain ⟨outputs, executed, correct⟩ := execute_correct policy p
  exact ⟨outputs, executed, fun q => (correct q).symm.trans (katInterp_correct policy p q).symm⟩

end DyNetKAT.NetKAT
