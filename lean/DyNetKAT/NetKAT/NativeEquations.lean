import KATLean.Native.Equations
import DyNetKAT.NetKAT.Axioms

namespace DyNetKAT.NetKAT

/-- Algebraic substitution into the existing syntax. This is not a packet-aware
frontend from NetKAT into the solver. Atomic actions may be arbitrary policies. -/
def nativeTest (tests : T → Predicate) : KATLean.Native.Test T → Predicate
  | .bot => .pFalse
  | .top => .pTrue
  | .atom t => tests t
  | .neg p => .pNot (nativeTest tests p)
  | .conj p q => .pAnd (nativeTest tests p) (nativeTest tests q)
  | .disj p q => .pOr (nativeTest tests p) (nativeTest tests q)

def nativeEmbed (actions : A → NetKAT) (tests : T → Predicate) : KATLean.Native.Expr T A → NetKAT
  | .zero => .drop
  | .one => .id
  | .action a => actions a
  | .test p => .test (nativeTest tests p)
  | .plus p q => .union (nativeEmbed actions tests p) (nativeEmbed actions tests q)
  | .seq p q => .seq (nativeEmbed actions tests p) (nativeEmbed actions tests q)
  | .star p => .star (nativeEmbed actions tests p)

/-- Every pure KAT derivation maps to the existing E_NK proof system, without
using a packet evaluator, equivalence oracle or normalization theorem. -/
theorem nativeEquational_derives {p q : KATLean.Native.Expr T A}
    (h : KATLean.Native.Equational p q) (actions : A → NetKAT) (tests : T → Predicate) :
    Derives (nativeEmbed actions tests p) (nativeEmbed actions tests q) := by
  induction h with
  | refl p => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ihp ihq => exact .trans ihp ihq
  | plusCongr _ _ ihp ihq => exact .unionCongr ihp ihq
  | seqCongr _ _ ihp ihq => exact .seqCongr ihp ihq
  | starCongr _ ih => exact .starCongr ih
  | notCongr _ ih => exact .notCongr ih
  | testFalse => exact .testFalse
  | testTrue => exact .testTrue
  | testOr a b => exact .testOr _ _
  | testAnd a b => exact .testAnd _ _
  | plusAssoc p q r => exact .plusAssoc _ _ _
  | plusComm p q => exact .plusComm _ _
  | plusZero p => exact .plusZero _
  | plusIdem p => exact .plusIdem _
  | seqAssoc p q r => exact .seqAssoc _ _ _
  | oneSeq p => exact .oneSeq _
  | seqOne p => exact .seqOne _
  | seqDistL p q r => exact .seqDistL _ _ _
  | seqDistR p q r => exact .seqDistR _ _ _
  | zeroSeq p => exact .zeroSeq _
  | seqZero p => exact .seqZero _
  | unrollL p => exact .unrollL _
  | unrollR p => exact .unrollR _
  | lfpL _ ih => exact .lfpL ih
  | lfpR _ ih => exact .lfpR ih
  | baPlusDist a b c => exact .baPlusDist _ _ _
  | baPlusOne a => exact .baPlusOne _
  | baExclMid a => exact .baExclMid _
  | baSeqComm a b => exact .baSeqComm _ _
  | baContra a => exact .baContra _
  | baSeqIdem a => exact .baSeqIdem _

end DyNetKAT.NetKAT
