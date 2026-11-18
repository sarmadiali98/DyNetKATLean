import KATLean.Native.Equations

/-! The syntactic KAT model, obtained by quotienting both sorts by derivability. -/

namespace KATLean.Native
namespace TermModel

open scoped Computability

variable {T A : Type}

private def programSetoid (T A : Type) : Setoid (Expr T A) where
  r := Equational
  iseqv := ⟨Equational.refl, Equational.symm, Equational.trans⟩

/-- Program expressions modulo the inductive KAT proof rules. -/
def Program (T A : Type) := Quotient (programSetoid T A)

private def program (p : Expr T A) : Program T A := Quotient.mk _ p

private theorem program_eq {p q : Expr T A} : program p = program q ↔ Equational p q :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound (s := programSetoid T A) h⟩

instance : Zero (Program T A) := ⟨program .zero⟩
instance : One (Program T A) := ⟨program .one⟩
instance : Add (Program T A) :=
  ⟨Quotient.map₂ (sa := programSetoid T A) (sb := programSetoid T A)
    (sc := programSetoid T A) Expr.plus (fun _ _ h₁ _ _ h₂ => Equational.plusCongr h₁ h₂)⟩
instance : Mul (Program T A) :=
  ⟨Quotient.map₂ (sa := programSetoid T A) (sb := programSetoid T A)
    (sc := programSetoid T A) Expr.seq (fun _ _ h₁ _ _ h₂ => Equational.seqCongr h₁ h₂)⟩
instance : KStar (Program T A) := ⟨Quotient.map (sa := programSetoid T A) (sb := programSetoid T A)
    Expr.star (fun _ _ h => Equational.starCongr h)⟩

private instance : Semiring (Program T A) where
  add_assoc := by
    rintro ⟨p⟩ ⟨q⟩ ⟨r⟩
    exact program_eq.mpr (Equational.plusAssoc p q r).symm
  zero_add := by
    rintro ⟨p⟩
    exact program_eq.mpr ((Equational.plusComm .zero p).trans (.plusZero p))
  add_zero := by
    rintro ⟨p⟩
    exact program_eq.mpr (.plusZero p)
  add_comm := by
    rintro ⟨p⟩ ⟨q⟩
    exact program_eq.mpr (.plusComm p q)
  nsmul := nsmulRec
  mul_assoc := by
    rintro ⟨p⟩ ⟨q⟩ ⟨r⟩
    exact program_eq.mpr (Equational.seqAssoc p q r).symm
  one_mul := by
    rintro ⟨p⟩
    exact program_eq.mpr (.oneSeq p)
  mul_one := by
    rintro ⟨p⟩
    exact program_eq.mpr (.seqOne p)
  zero_mul := by
    rintro ⟨p⟩
    exact program_eq.mpr (.zeroSeq p)
  mul_zero := by
    rintro ⟨p⟩
    exact program_eq.mpr (.seqZero p)
  left_distrib := by
    rintro ⟨p⟩ ⟨q⟩ ⟨r⟩
    exact program_eq.mpr (.seqDistL p q r)
  right_distrib := by
    rintro ⟨p⟩ ⟨q⟩ ⟨r⟩
    exact program_eq.mpr (.seqDistR p q r)

private instance : IdemSemiring (Program T A) :=
  IdemSemiring.ofSemiring (by rintro ⟨p⟩; exact program_eq.mpr (.plusIdem p))

instance : KleeneAlgebra (Program T A) where
  one_le_kstar a := by
    obtain ⟨p⟩ := a
    have h : (1 : Program T A) + program (p.seq p.star) = program p.star :=
      program_eq.mpr (.unrollL p)
    exact le_self_add.trans_eq h
  mul_kstar_le_kstar a := by
    obtain ⟨p⟩ := a
    have h : (1 : Program T A) + program (p.seq p.star) = program p.star :=
      program_eq.mpr (.unrollL p)
    exact le_add_self.trans_eq h
  kstar_mul_le_kstar a := by
    obtain ⟨p⟩ := a
    have h : (1 : Program T A) + program (p.star.seq p) = program p.star :=
      program_eq.mpr (.unrollR p)
    exact le_add_self.trans_eq h
  mul_kstar_le_self := by
    rintro ⟨p⟩ ⟨q⟩ h
    apply add_eq_right_iff_le.mp
    apply program_eq.mpr
    have h' : Equational (.plus (.seq q p) q) q := program_eq.mp h
    have premise : Equational (.plus (.plus q (.seq q p)) q) q :=
      (Equational.plusCongr (.plusComm q (.seq q p)) (.refl q)).trans
        ((Equational.plusAssoc (.seq q p) q q).symm.trans
          ((Equational.plusCongr (.refl _) (.plusIdem q)).trans h'))
    exact .lfpR premise
  kstar_mul_le_self := by
    rintro ⟨p⟩ ⟨q⟩ h
    apply add_eq_right_iff_le.mp
    apply program_eq.mpr
    have h' : Equational (.plus (.seq p q) q) q := program_eq.mp h
    have premise : Equational (.plus (.plus q (.seq p q)) q) q :=
      (Equational.plusCongr (.plusComm q (.seq p q)) (.refl q)).trans
        ((Equational.plusAssoc (.seq p q) q q).symm.trans
          ((Equational.plusCongr (.refl _) (.plusIdem q)).trans h'))
    exact .lfpL premise

private def testSetoid (T A : Type) : Setoid (Test T) where
  r p q := Equational (.test p : Expr T A) (.test q)
  iseqv := ⟨fun _ => .refl _, Equational.symm, Equational.trans⟩

/-- Boolean tests modulo the pure KAT proof rules on embedded tests. -/
def Tests (T A : Type) := Quotient (testSetoid T A)

private def test (A : Type) (p : Test T) : Tests T A := Quotient.mk _ p

private def embed : Tests T A → Program T A :=
  Quotient.map (sa := testSetoid T A) (sb := programSetoid T A) Expr.test (fun _ _ h => h)

private theorem embed_injective : Function.Injective (embed : Tests T A → Program T A) := by
  rintro ⟨p⟩ ⟨q⟩ h
  exact Quotient.sound (s := testSetoid T A) (program_eq.mp h)

private instance : Top (Tests T A) := ⟨test A .top⟩
private instance : Bot (Tests T A) := ⟨test A .bot⟩
private instance : Max (Tests T A) :=
  ⟨Quotient.map₂ (sa := testSetoid T A) (sb := testSetoid T A)
    (sc := testSetoid T A) Test.disj (fun p p' hp q q' hq =>
      (Equational.testOr p q).trans
        ((Equational.plusCongr hp hq).trans (Equational.testOr p' q').symm))⟩
private instance : Min (Tests T A) :=
  ⟨Quotient.map₂ (sa := testSetoid T A) (sb := testSetoid T A)
    (sc := testSetoid T A) Test.conj (fun p p' hp q q' hq =>
      (Equational.testAnd p q).trans
        ((Equational.seqCongr hp hq).trans (Equational.testAnd p' q').symm))⟩
private instance : HasCompl (Tests T A) :=
  ⟨Quotient.map (sa := testSetoid T A) (sb := testSetoid T A)
    Test.neg (fun _ _ h => Equational.notCongr h)⟩

@[simp] private theorem embed_top : embed (⊤ : Tests T A) = 1 :=
  program_eq.mpr .testTrue

@[simp] private theorem embed_bot : embed (⊥ : Tests T A) = 0 :=
  program_eq.mpr .testFalse

@[simp] private theorem embed_sup (x y : Tests T A) : embed (x ⊔ y) = embed x + embed y := by
  obtain ⟨p⟩ := x
  obtain ⟨q⟩ := y
  exact program_eq.mpr (.testOr p q)

@[simp] private theorem embed_inf (x y : Tests T A) : embed (x ⊓ y) = embed x * embed y := by
  obtain ⟨p⟩ := x
  obtain ⟨q⟩ := y
  exact program_eq.mpr (.testAnd p q)

private theorem embed_le_one (x : Tests T A) : embed x ≤ 1 := by
  obtain ⟨p⟩ := x
  exact add_eq_right_iff_le.mp (program_eq.mpr (.baPlusOne p))

private theorem embed_idem (x : Tests T A) : embed x * embed x = embed x := by
  obtain ⟨p⟩ := x
  exact program_eq.mpr (.baSeqIdem p)

private instance : Lattice (Tests T A) where
  sup := (· ⊔ ·)
  inf := (· ⊓ ·)
  le x y := embed x ≤ embed y
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ h k := embed_injective (le_antisymm h k)
  le_sup_left x y := by
    rw [embed_sup]
    exact le_self_add
  le_sup_right x y := by
    rw [embed_sup]
    exact le_add_self
  sup_le x y z h k := by
    rw [embed_sup]
    exact add_le h k
  inf_le_left x y := by
    rw [embed_inf]
    simpa using mul_le_mul_left' (embed_le_one y) (embed x)
  inf_le_right x y := by
    rw [embed_inf]
    simpa using mul_le_mul_right' (embed_le_one x) (embed y)
  le_inf x y z h k := by
    rw [embed_inf, ← embed_idem x]
    exact (mul_le_mul_right' h _).trans (mul_le_mul_left' k _)

private instance : BooleanAlgebra (Tests T A) where
  __ := DistribLattice.ofInfSupLe (by
    intro x y z
    change embed (x ⊓ (y ⊔ z)) ≤ embed ((x ⊓ y) ⊔ (x ⊓ z))
    rw [embed_inf, embed_sup, embed_sup, embed_inf, embed_inf, mul_add])
  inf_compl_le_bot := by
    rintro ⟨p⟩
    change embed (test A p ⊓ (test A p)ᶜ) ≤ embed (⊥ : Tests T A)
    rw [embed_inf, embed_bot]
    exact (program_eq.mpr (.baContra p)).le
  top_le_sup_compl := by
    rintro ⟨p⟩
    change embed (⊤ : Tests T A) ≤ embed (test A p ⊔ (test A p)ᶜ)
    rw [embed_top, embed_sup]
    exact (program_eq.mpr (.baExclMid p)).symm.le
  le_top x := by
    change embed x ≤ embed (⊤ : Tests T A)
    rw [embed_top]
    exact embed_le_one x
  bot_le x := by
    change embed (⊥ : Tests T A) ≤ embed x
    rw [embed_bot]
    exact zero_le _

private def kat : KAT (Program T A) (Tests T A) where
  embed := embed
  injective := embed_injective
  map_bot := embed_bot
  map_top := embed_top
  map_sup := embed_sup
  map_inf := embed_inf

private theorem interpTest (p : Test T) :
    p.interp (fun t => test A (.atom t)) = test A p := by
  induction p <;> simp only [Test.interp, *] <;> rfl

private theorem interpProgram (p : Expr T A) :
    p.interp kat (fun a => program (.action a)) (fun t => test A (.atom t)) = program p := by
  induction p <;> simp only [Expr.interp, interpTest, *] <;> rfl

end TermModel

/-- The quotient by derivability is itself an abstract KAT. Evaluating at its
  generators reflects universal algebraic equality back into a derivation. -/
theorem AlgebraicallyEquivalent.equational {p q : Expr T A}
    (h : AlgebraicallyEquivalent p q) : Equational p q := by
  have eq := h (TermModel.Program T A) (TermModel.Tests T A) TermModel.kat
    (fun a => TermModel.program (.action a)) (fun t => TermModel.test A (.atom t))
  rw [TermModel.interpProgram, TermModel.interpProgram] at eq
  exact TermModel.program_eq.mp eq

theorem algebraicallyEquivalent_iff_equational (p q : Expr T A) :
    AlgebraicallyEquivalent p q ↔ Equational p q :=
  ⟨AlgebraicallyEquivalent.equational, Equational.algebraic_sound⟩

end KATLean.Native
