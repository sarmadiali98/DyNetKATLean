import DyNetKAT.NetKAT.Interpretation

namespace DyNetKAT.NetKAT

local infixl:65 " ⊕ " => NetKAT.union
local infixl:70 " ⨟ " => NetKAT.seq

/-- The sum of all field tests in PA-MATCH-ALL for the concrete value domain. -/
def matchAll (f : FieldName) : NetKAT :=
  ([.v0, .v1, .v8, .v9] : List FieldValueEnum).foldr
    (fun v rest => NetKAT.fieldTest f v ⊕ rest) .drop

/-- DyNetKAT Figure 4 restricted to the dup-free syntax. The KAT order
    p ≤ q is encoded as derivability of p + q ≡ q. The test embeddings
    identify the separate Lean predicate syntax with the paper's shared
    test/program operations. -/
inductive Derives : NetKAT → NetKAT → Prop
  | refl (p) : Derives p p
  | symm : Derives p q → Derives q p
  | trans : Derives p q → Derives q r → Derives p r
  | unionCongr : Derives p p' → Derives q q' → Derives (p ⊕ q) (p' ⊕ q')
  | seqCongr : Derives p p' → Derives q q' → Derives (p ⨟ q) (p' ⨟ q')
  | starCongr : Derives p q → Derives (.star p) (.star q)
  | notCongr : Derives (.test a) (.test b) → Derives (.test (.pNot a)) (.test (.pNot b))
  | testFalse : Derives (.test .pFalse) .drop
  | testTrue : Derives (.test .pTrue) .id
  | testOr (a b) : Derives (.test (.pOr a b)) (.test a ⊕ .test b)
  | testAnd (a b) : Derives (.test (.pAnd a b)) (.test a ⨟ .test b)
  | completeTestExpand (α) : Derives (.completeTest α) (completeTestExpr α)
  | plusAssoc (p q r) : Derives (p ⊕ (q ⊕ r)) ((p ⊕ q) ⊕ r)
  | plusComm (p q) : Derives (p ⊕ q) (q ⊕ p)
  | plusZero (p) : Derives (p ⊕ .drop) p
  | plusIdem (p) : Derives (p ⊕ p) p
  | seqAssoc (p q r) : Derives (p ⨟ (q ⨟ r)) ((p ⨟ q) ⨟ r)
  | oneSeq (p) : Derives (.id ⨟ p) p
  | seqOne (p) : Derives (p ⨟ .id) p
  | seqDistL (p q r) : Derives (p ⨟ (q ⊕ r)) ((p ⨟ q) ⊕ (p ⨟ r))
  | seqDistR (p q r) : Derives ((p ⊕ q) ⨟ r) ((p ⨟ r) ⊕ (q ⨟ r))
  | zeroSeq (p) : Derives (.drop ⨟ p) .drop
  | seqZero (p) : Derives (p ⨟ .drop) .drop
  | unrollL (p) : Derives (.id ⊕ (p ⨟ .star p)) (.star p)
  | unrollR (p) : Derives (.id ⊕ (.star p ⨟ p)) (.star p)
  | lfpL : Derives ((q ⊕ (p ⨟ r)) ⊕ r) r → Derives ((.star p ⨟ q) ⊕ r) r
  | lfpR : Derives ((p ⊕ (q ⨟ r)) ⊕ q) q → Derives ((p ⨟ .star r) ⊕ q) q
  | baPlusDist (a b c : Predicate) :
      Derives (.test a ⊕ (.test b ⨟ .test c)) ((.test a ⊕ .test b) ⨟ (.test a ⊕ .test c))
  | baPlusOne (a : Predicate) : Derives (.test a ⊕ .id) .id
  | baExclMid (a : Predicate) : Derives (.test a ⊕ .test (.pNot a)) .id
  | baSeqComm (a b : Predicate) : Derives (.test a ⨟ .test b) (.test b ⨟ .test a)
  | baContra (a : Predicate) : Derives (.test a ⨟ .test (.pNot a)) .drop
  | baSeqIdem (a : Predicate) : Derives (.test a ⨟ .test a) (.test a)
  | paModModComm (f g v w) (h : f ≠ g) :
      Derives (.assign1 f v ⨟ .assign1 g w) (.assign1 g w ⨟ .assign1 f v)
  | paModFilterComm (f g v w) (h : f ≠ g) :
      Derives (.assign1 f v ⨟ NetKAT.fieldTest g w) (NetKAT.fieldTest g w ⨟ .assign1 f v)
  | paModFilter (f v) :
      Derives (.assign1 f v ⨟ NetKAT.fieldTest f v) (.assign1 f v)
  | paFilterMod (f v) :
      Derives (NetKAT.fieldTest f v ⨟ .assign1 f v) (NetKAT.fieldTest f v)
  | paModMod (f v w) : Derives (.assign1 f v ⨟ .assign1 f w) (.assign1 f w)
  | paContra (f v w) (h : v ≠ w) :
      Derives (NetKAT.fieldTest f v ⨟ NetKAT.fieldTest f w) .drop
  | paMatchAll (f) : Derives (matchAll f) .id

/-- The syntax-level PA-MATCH-ALL list denotes the finite algebraic sum. -/
theorem matchAll_katInterp (f : FieldName) :
    katInterp (matchAll f) = ∑ v : FieldValueEnum, ctxPacketModel.filter f v := by
  have values : (Finset.univ : Finset FieldValueEnum) = {.v0, .v1, .v8, .v9} := by
    ext v
    cases v <;> simp
  rw [values]
  simp [matchAll, katInterp, NetKAT.fieldTest, predicateInterp,
    KATLean.Rel.tests, KATLean.NetKAT.PacketModel.filter]

/-- Rule-by-rule algebraic soundness in KATLean. This proof does not use
Derives.sound. Mathlib's KA laws act on the KATLean relation instance. -/
theorem Derives.katSound {p q : NetKAT} (proof : Derives p q) :
    katInterp p = katInterp q := by
  induction proof with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ihp ihq => exact ihp.trans ihq
  | unionCongr _ _ ihp ihq => exact congrArg₂ (· + ·) ihp ihq
  | seqCongr _ _ ihp ihq => exact congrArg₂ (· * ·) ihp ihq
  | starCongr _ ih => exact congrArg KStar.kstar ih
  | notCongr _ ih =>
    exact congrArg (fun test : Set CtxPkt => KATLean.Rel.tests.embed testᶜ)
      (KATLean.Rel.tests.injective ih)
  | testFalse => exact KATLean.Rel.tests.map_bot
  | testTrue => exact KATLean.Rel.tests.map_top
  | testOr a b => exact KATLean.Rel.tests.map_sup (predicateInterp a) (predicateInterp b)
  | testAnd a b => exact KATLean.Rel.tests.map_inf (predicateInterp a) (predicateInterp b)
  | completeTestExpand alpha =>
    apply katInterp_eq_iff.mpr
    exact fun x y => (completeTestExpr_correct alpha x y).symm
  | plusAssoc p q r => exact (add_assoc (katInterp p) (katInterp q) (katInterp r)).symm
  | plusComm p q => exact add_comm (katInterp p) (katInterp q)
  | plusZero p => exact add_zero (katInterp p)
  | plusIdem p => exact add_idem (katInterp p)
  | seqAssoc p q r => exact (mul_assoc (katInterp p) (katInterp q) (katInterp r)).symm
  | oneSeq p => exact one_mul (katInterp p)
  | seqOne p => exact mul_one (katInterp p)
  | seqDistL p q r => exact mul_add (katInterp p) (katInterp q) (katInterp r)
  | seqDistR p q r => exact add_mul (katInterp p) (katInterp q) (katInterp r)
  | zeroSeq p => exact zero_mul (katInterp p)
  | seqZero p => exact mul_zero (katInterp p)
  | unrollL p => exact KATLean.star_unfold_left (katInterp p)
  | unrollR p => exact KATLean.star_unfold_right (katInterp p)
  | lfpL _ ih => exact KATLean.star_induction_left_add ih
  | lfpR _ ih => exact KATLean.star_induction_right_add ih
  | baPlusDist a b c =>
    exact KATLean.Rel.tests.plus_distrib (predicateInterp a) (predicateInterp b) (predicateInterp c)
  | baPlusOne a => exact KATLean.Rel.tests.plus_one (predicateInterp a)
  | baExclMid a => exact KATLean.Rel.tests.excluded_middle (predicateInterp a)
  | baSeqComm a b => exact KATLean.Rel.tests.test_commute (predicateInterp a) (predicateInterp b)
  | baContra a => exact KATLean.Rel.tests.contradiction (predicateInterp a)
  | baSeqIdem a => exact KATLean.Rel.tests.test_idempotent (predicateInterp a)
  | paModModComm f g v w different => exact ctxPacketModel.assign_commute f g v w different
  | paModFilterComm f g v w different => exact ctxPacketModel.assign_filter_commute f g v w different
  | paModFilter f v => exact ctxPacketModel.assign_filter f v
  | paFilterMod f v => exact ctxPacketModel.filter_assign f v
  | paModMod f v w => exact ctxPacketModel.overwrite f v w
  | paContra f v w different => exact ctxPacketModel.filter_contradiction f v w different
  | paMatchAll f => exact (matchAll_katInterp f).trans (ctxPacketModel.match_all f)

/-- Every derivation is sound for the existing finite packet semantics,
by algebraic soundness in KATLean and interpretation correctness. -/
theorem Derives.sound (h : Derives p q) : ∀ σ τ, Semantics p σ τ ↔ Semantics q σ τ :=
  katInterp_eq_iff.mp h.katSound

/-- Compatibility wrapper for the paper's left induction rule. -/
theorem starLfpLeft {p q r : NetKAT}
    (h : ∀ σ τ, Semantics (q ⊕ (p ⨟ r)) σ τ → Semantics r σ τ) :
    ∀ σ τ, Semantics (.star p ⨟ q) σ τ → Semantics r σ τ := by
  have stable : katInterp q + katInterp p * katInterp r ≤ katInterp r :=
    KATLean.Rel.le_iff.mpr (fun x y step => (katInterp_correct r x y).mpr
      (h x y ((katInterp_correct _ x y).mp step)))
  have bound := KATLean.star_induction_left stable
  intro x y step
  exact (katInterp_correct r x y).mp
    (KATLean.Rel.le_iff.mp bound x y ((katInterp_correct _ x y).mpr step))

/-- Compatibility wrapper for the paper's right induction rule. -/
theorem starLfpRight {p q r : NetKAT}
    (h : ∀ σ τ, Semantics (p ⊕ (q ⨟ r)) σ τ → Semantics q σ τ) :
    ∀ σ τ, Semantics (p ⨟ .star r) σ τ → Semantics q σ τ := by
  have stable : katInterp p + katInterp q * katInterp r ≤ katInterp q :=
    KATLean.Rel.le_iff.mpr (fun x y step => (katInterp_correct q x y).mpr
      (h x y ((katInterp_correct _ x y).mp step)))
  have bound := KATLean.star_induction_right stable
  intro x y step
  exact (katInterp_correct q x y).mp
    (KATLean.Rel.le_iff.mp bound x y ((katInterp_correct _ x y).mpr step))

/-- Compatibility wrapper for PA-CONTRA. -/
theorem paContra_sem (f : FieldName) {v w : FieldValueEnum} (h : v ≠ w) (σ τ : CtxPkt) :
    ¬ Semantics (NetKAT.fieldTest f v ⨟ NetKAT.fieldTest f w) σ τ := by
  have equivalent := (Derives.paContra f v w h).sound σ τ
  exact fun step => (equivalent.mp step).elim

/-- Compatibility wrapper for the finite syntax-level PA-MATCH-ALL sum. -/
theorem paMatchAll_sem (f : FieldName) (σ τ : CtxPkt) :
    Semantics (matchAll f) σ τ ↔ σ = τ :=
  (Derives.paMatchAll f).sound σ τ

theorem Derives.historySound (h : Derives p q) :
    ∀ σ τ, HistorySemantics p σ τ ↔ HistorySemantics q σ τ :=
  (netkatEquiv_history_correct p q).mp ((netkatEquiv_correct p q).mpr h.sound)

end DyNetKAT.NetKAT
