import DyNetKAT.NetKAT.BackendCertificate

namespace DyNetKAT.NetKAT

/-- A deliberately incomplete algebraic reduction. Its size depends on the
policy syntax, with no enumeration of the packet universe. -/
def reduceEquational : NetKAT → NetKAT
  | .seq p q =>
    let p' := reduceEquational p
    let q' := reduceEquational q
    if p' = .id then q' else if q' = .id then p' else .seq p' q'
  | .union p q =>
    let p' := reduceEquational p
    let q' := reduceEquational q
    if p' = .drop then q' else if q' = .drop then p' else .union p' q'
  | .star p => .star (reduceEquational p)
  | p => p

theorem reduceEquational_sound (p : NetKAT) : Derives p (reduceEquational p) := by
  induction p with
  | seq p q hp hq =>
    apply (Derives.seqCongr hp hq).trans
    simp only [reduceEquational]
    split
    · rename_i h
      rw [h]
      exact .oneSeq _
    · split
      · rename_i h
        rw [h]
        exact .seqOne _
      · exact .refl _
  | union p q hp hq =>
    apply (Derives.unionCongr hp hq).trans
    simp only [reduceEquational]
    split
    · rename_i h
      rw [h]
      exact (Derives.plusComm _ _).trans (Derives.plusZero _)
    · split
      · rename_i h
        rw [h]
        exact .plusZero _
      · exact .refl _
  | star _ ih => exact .starCongr ih
  | _ => exact .refl _

/-- A common reduced term is a compact certificate for this rewrite fragment. -/
def checkEquationalCertificate (p q common : NetKAT) : Bool :=
  decide (reduceEquational p = common ∧ reduceEquational q = common)

theorem checkEquationalCertificate_sound {p q common : NetKAT}
    (h : checkEquationalCertificate p q common = true) : Derives p q := by
  have he : reduceEquational p = common ∧ reduceEquational q = common := of_decide_eq_true h
  exact (reduceEquational_sound p).trans
    ((he.1.trans he.2.symm) ▸ (reduceEquational_sound q).symm)

/-- Candidate rejection falls through to the existing checked decision API. -/
def decideWithEquationalCertificate (p q : NetKAT) (common : NetKAT)
    (fallback : Option BackendCandidate := none) : BackendDecision p q :=
  if h : checkEquationalCertificate p q common then
    ⟨true, .checkedEquational,
      ((netkatEquiv_correct _ _).mpr (checkEquationalCertificate_sound h).sound).symm⟩
  else decideWithBackend p q fallback

theorem decideWithEquationalCertificate_correct (p q common : NetKAT)
    (fallback : Option BackendCandidate) :
    (decideWithEquationalCertificate p q common fallback).equivalent = true ↔
      ∀ σ τ, Semantics p σ τ ↔ Semantics q σ τ := by
  rw [(decideWithEquationalCertificate p q common fallback).correct, netkatEquiv_correct]

end DyNetKAT.NetKAT
