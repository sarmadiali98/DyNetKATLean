import DyNetKAT.NetKAT.Decision

namespace DyNetKAT.NetKAT

/-- Numeric encoding of the finite values for the common KATch fragment. -/
def katchValue : FieldValueEnum ↪ Int where
  toFun
    | .v0 => 0
    | .v1 => 1
    | .v8 => 8
    | .v9 => 9
  inj' := by
    intro a b
    cases a <;> cases b <;> decide

abbrev KatchPacket := Packet FieldName Int

def katchPacket : CtxPkt ↪ KatchPacket where
  toFun σ f := katchValue (σ f)
  inj' := by
    intro σ τ h
    exact funext fun f => katchValue.injective (congrFun h f)

private def katchPredicate : Predicate → KatchPacket → Bool
  | .pFalse, _ => false
  | .pTrue, _ => true
  | .pFieldEq ⟨f, v⟩, σ => decide (σ f = katchValue v)
  | .pAnd p q, σ => katchPredicate p σ && katchPredicate q σ
  | .pOr p q, σ => katchPredicate p σ || katchPredicate q σ
  | .pNot p, σ => !katchPredicate p σ

private theorem katchPredicate_encode (p : Predicate) (σ : CtxPkt) :
    katchPredicate p (katchPacket σ) = p.eval σ := by
  induction p with
  | pFalse | pTrue => rfl
  | pFieldEq eq =>
      cases eq
      simp [katchPredicate, Predicate.eval, katchPacket, katchValue.injective.eq_iff]
  | pAnd _ _ ih₁ ih₂ => simp only [katchPredicate, Predicate.eval, ih₁, ih₂]
  | pOr _ _ ih₁ ih₂ => simp only [katchPredicate, Predicate.eval, ih₁, ih₂]
  | pNot _ ih => simp only [katchPredicate, Predicate.eval, ih]

private theorem katchPacket_update (σ : CtxPkt) (f : FieldName) (v : FieldValueEnum) :
    Packet.update (katchPacket σ) f (katchValue v) = katchPacket (Packet.update σ f v) := by
  funext g
  by_cases h : f = g <;> simp [Packet.update, h, katchPacket]

/-- The packet relation from KATch's NetKAT semantics on the common,
    dup-free fragment. Complete tests abbreviate conjunctions of all
    field tests. Integer fields here also admit packets outside CtxPkt. -/
def katchSemantics : NetKAT → KatchPacket → KatchPacket → Prop
  | .drop, _, _ => False
  | .id, σ, τ => σ = τ
  | .test p, σ, τ => katchPredicate p σ = true ∧ σ = τ
  | .completeTest α, σ, τ => katchPacket α = σ ∧ σ = τ
  | .assign1 f v, σ, τ => τ = Packet.update σ f (katchValue v)
  | .union p q, σ, τ => katchSemantics p σ τ ∨ katchSemantics q σ τ
  | .seq p q, σ, τ => ∃ ρ, katchSemantics p σ ρ ∧ katchSemantics q ρ τ
  | .star p, σ, τ => StarClosure (katchSemantics p) σ τ

/-- From an encoded input, every execution remains in the encoded domain
    and gives exactly the encoded outputs of the existing Lean semantics. -/
theorem katchSemantics_encode (p : NetKAT) (σ : CtxPkt) (out : KatchPacket) :
    katchSemantics p (katchPacket σ) out ↔
      ∃ τ, out = katchPacket τ ∧ Semantics p σ τ := by
  induction p generalizing σ out with
  | drop => simp [katchSemantics, Semantics]
  | id =>
      change katchPacket σ = out ↔ ∃ τ, out = katchPacket τ ∧ σ = τ
      exact ⟨fun h => ⟨σ, h.symm, rfl⟩, fun ⟨τ, h, hτ⟩ => hτ ▸ h.symm⟩
  | test a =>
      simp only [katchSemantics, Semantics, katchPredicate_encode, Predicate.holds]
      constructor
      · rintro ⟨h, rfl⟩
        exact ⟨σ, rfl, h, rfl⟩
      · rintro ⟨τ, rfl, h, rfl⟩
        exact ⟨h, rfl⟩
  | completeTest α =>
      simp only [katchSemantics, Semantics, holdsComplete_iff_eq,
        katchPacket.injective.eq_iff]
      constructor
      · rintro ⟨rfl, rfl⟩
        exact ⟨_, rfl, rfl, rfl⟩
      · rintro ⟨τ, rfl, rfl, rfl⟩
        exact ⟨rfl, rfl⟩
  | assign1 f v => simp [katchSemantics, Semantics, katchPacket_update]
  | union p q ih₁ ih₂ =>
      simp only [katchSemantics, Semantics, ih₁, ih₂]
      constructor
      · rintro (⟨τ, rfl, h⟩ | ⟨τ, rfl, h⟩)
        · exact ⟨τ, rfl, Or.inl h⟩
        · exact ⟨τ, rfl, Or.inr h⟩
      · rintro ⟨τ, rfl, h | h⟩
        · exact Or.inl ⟨τ, rfl, h⟩
        · exact Or.inr ⟨τ, rfl, h⟩
  | seq p q ih₁ ih₂ =>
      constructor
      · rintro ⟨m, hm, hOut⟩
        obtain ⟨ρ, rfl, hρ⟩ := (ih₁ σ m).mp hm
        obtain ⟨τ, rfl, hτ⟩ := (ih₂ ρ out).mp hOut
        exact ⟨τ, rfl, ρ, hρ, hτ⟩
      · rintro ⟨τ, rfl, ρ, hρ, hτ⟩
        exact ⟨katchPacket ρ, (ih₁ σ _).mpr ⟨ρ, rfl, hρ⟩, (ih₂ ρ _).mpr ⟨τ, rfl, hτ⟩⟩
  | star p ih =>
      have forward {s t : KatchPacket} (h : StarClosure (katchSemantics p) s t) :
          ∀ ρ, s = katchPacket ρ → ∃ τ, t = katchPacket τ ∧ StarClosure (Semantics p) ρ τ := by
        induction h with
        | refl => exact fun ρ hr => ⟨ρ, hr, .refl ρ⟩
        | @step s u t hp _ ihStar =>
            intro ρ hr
            subst s
            obtain ⟨κ, hk, hρκ⟩ := (ih ρ u).mp hp
            obtain ⟨τ, ht, hκτ⟩ := ihStar κ hk
            exact ⟨τ, ht, .step hρκ hκτ⟩
      have backward {ρ τ} (h : StarClosure (Semantics p) ρ τ) :
          StarClosure (katchSemantics p) (katchPacket ρ) (katchPacket τ) := by
        induction h with
        | refl => exact .refl _
        | step hp _ ihStar => exact .step ((ih _ _).mpr ⟨_, rfl, hp⟩) ihStar
      exact ⟨fun h => forward h σ rfl, fun ⟨τ, ht, h⟩ => ht ▸ backward h⟩

/-- The domain restriction can be expressed as a test of the four
    allowed integer values at each field. -/
theorem katchPacket_range_iff (σ : KatchPacket) :
    σ ∈ Set.range katchPacket ↔ ∀ f, σ f = 0 ∨ σ f = 1 ∨ σ f = 8 ∨ σ f = 9 := by
  constructor
  · rintro ⟨p, rfl⟩ f
    change katchValue (p f) = 0 ∨ katchValue (p f) = 1 ∨
      katchValue (p f) = 8 ∨ katchValue (p f) = 9
    cases p f <;> decide
  · intro h
    refine ⟨fun f => if σ f = 0 then .v0 else if σ f = 1 then .v1
      else if σ f = 8 then .v8 else .v9, ?_⟩
    funext f
    rcases h f with hf | hf | hf | hf <;> simp [katchPacket, katchValue, hf]

/-- Equivalence of the common-fragment policies on KATch's packet
    relation with the input restricted to the finite domain. Outputs
    range over all packets because closure is proved by the embedding. -/
theorem netkatEquiv_katch_restricted (p q : NetKAT) :
    netkatEquiv p q = true ↔
      ∀ σ ∈ Set.range katchPacket, ∀ τ, katchSemantics p σ τ ↔ katchSemantics q σ τ := by
  rw [netkatEquiv_correct]
  constructor
  · rintro h σ ⟨s, rfl⟩ τ
    simp only [katchSemantics_encode, h s]
  · intro h σ τ
    simpa only [katchSemantics_encode, katchPacket.injective.eq_iff, exists_eq_left'] using
      h (katchPacket σ) ⟨σ, rfl⟩ (katchPacket τ)

theorem netkatIsZero_katch_restricted (p : NetKAT) :
    netkatIsZero p = true ↔
      ∀ σ ∈ Set.range katchPacket, ∀ τ, ¬ katchSemantics p σ τ := by
  rw [netkatIsZero, netkatEquiv_katch_restricted]
  simp only [katchSemantics, iff_false]

end DyNetKAT.NetKAT
