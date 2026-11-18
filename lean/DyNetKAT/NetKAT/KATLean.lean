import DyNetKAT.NetKAT.Interpretation
import DyNetKAT.NetKAT.Normalization

/-! Compatibility import surface for the NetKAT interpretation and the
normalization bridge. Derivation soundness is defined in Axioms. -/
namespace DyNetKAT.NetKAT

/-- Lemma 5's existing normalization has the same KATLean interpretation. -/
theorem normalize_katInterp (policy : NetKAT) : katInterp policy = katInterp (normalize policy) :=
  (normalize_derives policy).katSound

end DyNetKAT.NetKAT
