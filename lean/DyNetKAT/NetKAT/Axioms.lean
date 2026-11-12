import DyNetKAT.NetKAT.Decision

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

private theorem StarClosure.map {P Q : CtxPkt → CtxPkt → Prop}
    (h : ∀ σ τ, P σ τ → Q σ τ) {σ τ} (hp : StarClosure P σ τ) :
    StarClosure Q σ τ := by
  induction hp with
  | refl => exact .refl _
  | step hp _ ih => exact .step (h _ _ hp) ih

private theorem StarClosure.snoc {P : CtxPkt → CtxPkt → Prop}
    {σ ρ τ} (h : StarClosure P σ ρ) (last : P ρ τ) : StarClosure P σ τ := by
  induction h with
  | refl => exact .step last (.refl _)
  | step first _ ih => exact .step first (ih last)

private theorem StarClosure.last {P : CtxPkt → CtxPkt → Prop}
    {σ τ} (h : StarClosure P σ τ) : σ = τ ∨ ∃ ρ, StarClosure P σ ρ ∧ P ρ τ := by
  induction h with
  | refl => exact Or.inl rfl
  | step first _ ih =>
      rcases ih with rfl | ⟨ρ, h, last⟩
      · exact Or.inr ⟨_, .refl _, first⟩
      · exact Or.inr ⟨ρ, .step first h, last⟩

/-- KA-LFP-L, where inclusion is the relational interpretation of KAT order. -/
theorem starLfpLeft {p q r : NetKAT}
    (h : ∀ σ τ, Semantics (q ⊕ (p ⨟ r)) σ τ → Semantics r σ τ) :
    ∀ σ τ, Semantics (.star p ⨟ q) σ τ → Semantics r σ τ := by
  rintro σ τ ⟨ρ, hStar, hq⟩
  change StarClosure (Semantics p) σ ρ at hStar
  induction hStar with
  | refl => exact h _ _ (Or.inl hq)
  | step hp _ ih => exact h _ _ (Or.inr ⟨_, hp, ih hq⟩)

/-- KA-LFP-R, where inclusion is the relational interpretation of KAT order. -/
theorem starLfpRight {p q r : NetKAT}
    (h : ∀ σ τ, Semantics (p ⊕ (q ⨟ r)) σ τ → Semantics q σ τ) :
    ∀ σ τ, Semantics (p ⨟ .star r) σ τ → Semantics q σ τ := by
  rintro σ τ ⟨ρ, hp, hStar⟩
  change StarClosure (Semantics r) ρ τ at hStar
  have hq := h σ ρ (Or.inl hp)
  clear hp
  induction hStar with
  | refl => exact hq
  | step hr _ ih => exact ih (h _ _ (Or.inr ⟨_, hq, hr⟩))

theorem paContra_sem (f : FieldName) {v w : FieldValueEnum} (h : v ≠ w) (σ τ : CtxPkt) :
    ¬ Semantics (NetKAT.fieldTest f v ⨟ NetKAT.fieldTest f w) σ τ := by
  simp only [seq_sem, fieldTest_sem]
  rintro ⟨ρ, ⟨hv, rfl⟩, hw, _⟩
  exact h (hv.symm.trans hw)

theorem paMatchAll_sem (f : FieldName) (σ τ : CtxPkt) :
    Semantics (matchAll f) σ τ ↔ σ = τ := by
  simp only [matchAll, List.foldr_cons, List.foldr_nil, union_sem, fieldTest_sem,
    sem_drop_false, or_false]
  cases σ f <;> simp [eq_comm]

private theorem update_same_of_eq {σ : CtxPkt} {f : FieldName} {v : FieldValueEnum}
    (h : σ f = v) : Packet.update σ f v = σ := by
  funext g
  by_cases hg : g = f
  · subst g
    simp [Packet.update, h]
  · simp [Packet.update, Ne.symm hg]

/-- Every derivation is sound for the project's finite packet semantics. -/
theorem Derives.sound (h : Derives p q) : ∀ σ τ, Semantics p σ τ ↔ Semantics q σ τ := by
  induction h with
  | refl => intros; rfl
  | symm _ ih => exact fun σ τ => (ih σ τ).symm
  | trans _ _ ih₁ ih₂ => exact fun σ τ => (ih₁ σ τ).trans (ih₂ σ τ)
  | unionCongr _ _ ih₁ ih₂ => simp only [union_sem, ih₁, ih₂, implies_true]
  | seqCongr _ _ ih₁ ih₂ => simp only [seq_sem, ih₁, ih₂, implies_true]
  | starCongr _ ih =>
      exact fun _ _ => ⟨StarClosure.map (fun σ τ => (ih σ τ).mp),
        StarClosure.map (fun σ τ => (ih σ τ).mpr)⟩
  | notCongr _ ih =>
      intro σ τ
      have hh := ih σ σ
      simp only [Semantics, and_true] at hh
      simp only [notTest_sem, hh]
  | testFalse => simp [Semantics, Predicate.holds, Predicate.eval]
  | testTrue => simp [Semantics, Predicate.holds, Predicate.eval]
  | testOr => simp [Semantics, Predicate.holds, Predicate.eval, or_and_right]
  | testAnd => simp [Semantics, Predicate.holds, Predicate.eval, and_assoc]
  | completeTestExpand α => exact fun σ τ => (completeTestExpr_correct α σ τ).symm
  | plusAssoc p q r => exact fun σ τ => (union_assoc p q r σ τ).symm
  | plusComm p q => exact union_comm p q
  | plusZero => simp [Semantics]
  | plusIdem p => exact union_idem p
  | seqAssoc =>
      intro σ τ
      simp only [seq_sem]
      constructor
      · rintro ⟨ρ, hp, κ, hq, hr⟩
        exact ⟨κ, ⟨ρ, hp, hq⟩, hr⟩
      · rintro ⟨κ, ⟨ρ, hp, hq⟩, hr⟩
        exact ⟨ρ, hp, κ, hq, hr⟩
  | oneSeq p => exact seq_id_left p
  | seqOne p => exact seq_id_right p
  | seqDistL p q r => exact seq_distrib_left p q r
  | seqDistR p q r => exact seq_distrib_right p q r
  | zeroSeq p => simpa only [sem_drop_false, iff_false] using seq_drop_left p
  | seqZero p => simpa only [sem_drop_false, iff_false] using seq_drop_right p
  | unrollL p =>
      intro σ τ
      constructor
      · rintro (rfl | ⟨ρ, hp, hs⟩)
        · exact .refl _
        · exact .step hp hs
      · intro hs
        change StarClosure (Semantics p) σ τ at hs
        cases hs with
        | refl => exact Or.inl rfl
        | step hp hs => exact Or.inr ⟨_, hp, hs⟩
  | unrollR p =>
      intro σ τ
      constructor
      · rintro (rfl | ⟨ρ, hs, hp⟩)
        · exact .refl _
        · exact StarClosure.snoc hs hp
      · exact StarClosure.last
  | lfpL _ ih =>
      intro σ τ
      exact ⟨fun h => h.elim (starLfpLeft (fun _ _ h => (ih _ _).mp (Or.inl h)) σ τ) id,
        Or.inr⟩
  | lfpR _ ih =>
      intro σ τ
      exact ⟨fun h => h.elim (starLfpRight (fun _ _ h => (ih _ _).mp (Or.inl h)) σ τ) id,
        Or.inr⟩
  | baPlusDist =>
      intro σ τ
      simp only [Semantics, ← or_and_right, exists_eq_left, and_assoc]
      aesop
  | baPlusOne => simp [Semantics]
  | baExclMid a =>
      intro σ τ
      cases hEval : a.eval σ <;> simp [Semantics, Predicate.holds, Predicate.eval, hEval]
  | baSeqComm => simp [Semantics, and_left_comm, and_assoc]
  | baContra => simp [Semantics, Predicate.holds, Predicate.eval]
  | baSeqIdem => simp [Semantics, and_assoc]
  | paModModComm f g v w h =>
      simp [seq_sem, assign1_sem, assign_comm_diff f g v w h]
  | paModFilterComm f g v w h =>
      intro σ τ
      simp only [seq_sem, assign1_sem, fieldTest_sem]
      constructor
      · rintro ⟨ρ, rfl, htest, rfl⟩
        exact ⟨σ, ⟨by simpa [Packet.update, h] using htest, rfl⟩, rfl⟩
      · rintro ⟨ρ, ⟨htest, rfl⟩, rfl⟩
        exact ⟨_, rfl, by simpa [Packet.update, h] using htest, rfl⟩
  | paModFilter => simp [seq_sem, assign1_sem, fieldTest_sem, assign_test_same_field]
  | paFilterMod =>
      intro σ τ
      simp only [seq_sem, fieldTest_sem, assign1_sem]
      constructor
      · rintro ⟨ρ, ⟨h, rfl⟩, rfl⟩
        exact ⟨h, update_same_of_eq h⟩
      · rintro ⟨h, rfl⟩
        exact ⟨_, ⟨h, rfl⟩, (update_same_of_eq h).symm⟩
  | paModMod => simp [seq_sem, assign1_sem, Packet.update_update_same]
  | paContra f v w h => exact fun σ τ => iff_false_intro (paContra_sem f h σ τ)
  | paMatchAll f => exact paMatchAll_sem f

theorem Derives.historySound (h : Derives p q) :
    ∀ σ τ, HistorySemantics p σ τ ↔ HistorySemantics q σ τ :=
  (netkatEquiv_history_correct p q).mp ((netkatEquiv_correct p q).mpr h.sound)

end DyNetKAT.NetKAT
