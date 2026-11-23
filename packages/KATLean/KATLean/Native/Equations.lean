import KATLean.Native.Correctness

namespace KATLean.Native

/-- Pure two-sorted KAT axioms, without NetKAT packet equations. This relation
is not defined by the solver or by relational validity. -/
inductive Equational {T A : Type} : Expr T A → Expr T A → Prop
  | refl (p) : Equational p p
  | symm : Equational p q → Equational q p
  | trans : Equational p q → Equational q r → Equational p r
  | plusCongr : Equational p p' → Equational q q' → Equational (.plus p q) (.plus p' q')
  | seqCongr : Equational p p' → Equational q q' → Equational (.seq p q) (.seq p' q')
  | starCongr : Equational p q → Equational (.star p) (.star q)
  | notCongr : Equational (.test a) (.test b) → Equational (.test (.neg a)) (.test (.neg b))
  | testFalse : Equational (.test .bot) .zero
  | testTrue : Equational (.test .top) .one
  | testOr (a b) : Equational (.test (.disj a b)) (.plus (.test a) (.test b))
  | testAnd (a b) : Equational (.test (.conj a b)) (.seq (.test a) (.test b))
  | plusAssoc (p q r) : Equational (.plus p (.plus q r)) (.plus (.plus p q) r)
  | plusComm (p q) : Equational (.plus p q) (.plus q p)
  | plusZero (p) : Equational (.plus p .zero) p
  | plusIdem (p) : Equational (.plus p p) p
  | seqAssoc (p q r) : Equational (.seq p (.seq q r)) (.seq (.seq p q) r)
  | oneSeq (p) : Equational (.seq .one p) p
  | seqOne (p) : Equational (.seq p .one) p
  | seqDistL (p q r) : Equational (.seq p (.plus q r)) (.plus (.seq p q) (.seq p r))
  | seqDistR (p q r) : Equational (.seq (.plus p q) r) (.plus (.seq p r) (.seq q r))
  | zeroSeq (p) : Equational (.seq .zero p) .zero
  | seqZero (p) : Equational (.seq p .zero) .zero
  | unrollL (p) : Equational (.plus .one (.seq p (.star p))) (.star p)
  | unrollR (p) : Equational (.plus .one (.seq (.star p) p)) (.star p)
  | lfpL : Equational (.plus (.plus q (.seq p r)) r) r →
      Equational (.plus (.seq (.star p) q) r) r
  | lfpR : Equational (.plus (.plus p (.seq q r)) q) q →
      Equational (.plus (.seq p (.star r)) q) q
  | baPlusDist (a b c) : Equational (.plus (.test a) (.seq (.test b) (.test c)))
      (.seq (.plus (.test a) (.test b)) (.plus (.test a) (.test c)))
  | baPlusOne (a) : Equational (.plus (.test a) .one) .one
  | baExclMid (a) : Equational (.plus (.test a) (.test (.neg a))) .one
  | baSeqComm (a b) : Equational (.seq (.test a) (.test b)) (.seq (.test b) (.test a))
  | baContra (a) : Equational (.seq (.test a) (.test (.neg a))) .zero
  | baSeqIdem (a) : Equational (.seq (.test a) (.test a)) (.test a)

/-- Validity in every abstract KATLean KAT, not just relational instances. -/
def AlgebraicallyEquivalent (p q : Expr T A) : Prop :=
  ∀ (K B : Type) [KleeneAlgebra K] [BooleanAlgebra B] (kat : KAT K B)
    (actions : A → K) (tests : T → B), p.interp kat actions tests = q.interp kat actions tests

/-- Pure KAT axioms are justified directly by the KATLean/Mathlib algebra. -/
theorem Equational.algebraic_sound {p q : Expr T A} (proof : Equational p q) :
    AlgebraicallyEquivalent p q := by
  intro K B _ _ kat actions tests
  induction proof with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ihp ihq => exact ihp.trans ihq
  | plusCongr _ _ ihp ihq => exact congrArg₂ (· + ·) ihp ihq
  | seqCongr _ _ ihp ihq => exact congrArg₂ (· * ·) ihp ihq
  | starCongr _ ih => exact congrArg KStar.kstar ih
  | notCongr _ ih => exact congrArg (fun t : B => kat.embed tᶜ) (kat.injective ih)
  | testFalse => exact kat.map_bot
  | testTrue => exact kat.map_top
  | testOr a b => exact kat.map_sup _ _
  | testAnd a b => exact kat.map_inf _ _
  | plusAssoc p q r => exact (add_assoc _ _ _).symm
  | plusComm p q => exact add_comm _ _
  | plusZero p => exact add_zero _
  | plusIdem p => exact add_idem _
  | seqAssoc p q r => exact (mul_assoc _ _ _).symm
  | oneSeq p => exact one_mul _
  | seqOne p => exact mul_one _
  | seqDistL p q r => exact mul_add _ _ _
  | seqDistR p q r => exact add_mul _ _ _
  | zeroSeq p => exact zero_mul _
  | seqZero p => exact mul_zero _
  | unrollL p => exact star_unfold_left _
  | unrollR p => exact star_unfold_right _
  | lfpL _ ih => exact star_induction_left_add ih
  | lfpR _ ih => exact star_induction_right_add ih
  | baPlusDist a b c => exact kat.plus_distrib _ _ _
  | baPlusOne a => exact kat.plus_one _
  | baExclMid a => exact kat.excluded_middle _
  | baSeqComm a b => exact kat.test_commute _ _
  | baContra a => exact kat.contradiction _
  | baSeqIdem a => exact kat.test_idempotent _

theorem AlgebraicallyEquivalent.relational {p q : Expr T A} (h : AlgebraicallyEquivalent p q) :
    RelationalEquivalent p q := fun P actions tests => h (Rel P) (Set P) Rel.tests actions tests

/-- Sound derivations are accepted by the symbolic solver. -/
theorem Equational.solver_positive [BooleanAlphabet T] [Encodable T] [Encodable A]
    [Fintype A] [DecidableEq T] [DecidableEq A] {p q : Expr T A} (h : Equational p q) :
    decideEquiv p q = true := decideEquiv_complete p q h.algebraic_sound.relational

end KATLean.Native
