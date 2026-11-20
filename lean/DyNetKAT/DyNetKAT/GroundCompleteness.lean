import DyNetKAT.DyNetKAT.HeadNormalForm
import DyNetKAT.DyNetKAT.EquationsAIP
import DyNetKAT.DyNetKAT.NetKATBridge

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

variable {schema : PacketSchema}

open DyNetKAT.NetKAT Equations

variable [DiagramLayout schema]

namespace Equations.AtomicPrefix

theorem packet_label_eq {z : NetKAT schema} {σ τ : schema.Packet}
    (h : AtomicPrefix (.visible (.packet z)))
    (hs : HistorySemantics z (History.singleton σ) (History.singleton τ)) :
    z = packetSummand (σ, τ) := by
  cases h with
  | packet α π =>
    have eq := (packetSummand_sem σ τ (α, π)).mp
      ((historySemantics_singleton_iff_packetSemantics ..).mp hs)
    rw [← eq]

theorem packet_realizes {z : NetKAT schema} {σ τ : schema.Packet}
    {pt hl pt' hl' : List schema.Packet}
    (h : AtomicPrefix (.visible (.packet z)))
    (hs : MoveLabel.Realizes (.visible (.packet z)) pt hl (.packet σ τ) pt' hl') :
    z = packetSummand (σ, τ) := by
  cases hs with
  | packet hsem => exact h.packet_label_eq hsem

/-- An atomic label realizing an observation is uniquely determined by it. -/
theorem label_eq_of_realizes {l k : MoveLabel schema} {a : Action schema}
    {pt hl pt' hl' : List schema.Packet}
    (hl₀ : AtomicPrefix l) (hk₀ : AtomicPrefix k)
    (hl₁ : l.Realizes pt hl a pt' hl') (hk₁ : k.Realizes pt hl a pt' hl') :
    l = k := by
  cases hl₁ with
  | packet h =>
    cases hk₁ with
    | packet h' =>
      rw [hl₀.packet_label_eq h, hk₀.packet_label_eq h']
  | recv => cases hk₁; rfl
  | send => cases hk₁; rfl
  | rcfg => cases hk₁; rfl

/-- Each atomic label has a concrete enabled transition, including packet heads. -/
theorem exists_realizes {l : MoveLabel schema} (h : AtomicPrefix l) :
    ∃ pt hl a pt' hl', l.Realizes pt hl a pt' hl' := by
  cases h with
  | packet α π =>
    exact ⟨[α], [], .packet α π, [], [π], .packet
      ((historySemantics_singleton_iff_packetSemantics ..).mpr
        ((packetSummand_sem α π (α, π)).mpr rfl))⟩
  | recv x z => exact ⟨[], [], .recv x z, [], [], .recv⟩
  | send x z => exact ⟨[], [], .send x z, [], [], .send⟩
  | rcfg x z => exact ⟨[], [], .rcfg x z, [], [], .rcfg⟩

end Equations.AtomicPrefix

namespace HeadNormalForm

theorem ground_render_iff (xs : HeadNormalForm schema) :
    Ground xs.render ↔ ∀ b ∈ xs, Ground b.continuation := by
  have prefix_ground (b : HeadSummand schema) : Ground b.render ↔ Ground b.continuation := by
    rcases b with ⟨_, h, _⟩
    cases h <;> rfl
  induction xs with
  | nil => simp [Ground]
  | cons b xs ih =>
    have split : Ground (DyNetKAT.choice b.render (render xs)) ↔
        Ground b.render ∧ Ground (render xs) := Finset.union_eq_empty
    rw [render_cons, split, prefix_ground]
    constructor
    · rintro ⟨hb, hxs⟩ c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hb
      · exact ih.mp hxs c hc
    · intro h
      exact ⟨h b List.mem_cons_self, ih.mpr
        (fun c hc => h c (List.mem_cons_of_mem _ hc))⟩

theorem match_head {env : RecEnv schema} {xs ys : HeadNormalForm schema}
    (h : Bisimilar env xs.render ys.render) {a : HeadSummand schema} (ha : a ∈ xs) :
    ∃ b ∈ ys, a.label = b.label ∧ Bisimilar env a.continuation b.continuation := by
  obtain ⟨pt, hl, act, pt', hl', realizes⟩ := a.atomic.exists_realizes
  have step := (step_iff env xs pt hl act a.continuation pt' hl').mpr ⟨a, ha, rfl, realizes⟩
  obtain ⟨R, hR, hxy⟩ := h
  obtain ⟨q, hs, related⟩ := hR.2 _ _ hxy _ _ _ _ _ _ step
  obtain ⟨b, hb, rfl, realizes'⟩ := (step_iff env ys ..).mp hs
  exact ⟨b, hb, a.atomic.label_eq_of_realizes b.atomic realizes realizes', ⟨R, hR, related⟩⟩

theorem eq_nil_of_bisimilar_nil {env : RecEnv schema} {xs : HeadNormalForm schema}
    (h : Bisimilar env xs.render (render [])) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    obtain ⟨b, hb, _⟩ := match_head h (List.mem_cons_self (a := a) (l := xs))
    simp at hb

/-- Absorb a list whose summands all match derivably in the receiving list. -/
theorem absorb (env : RecEnv schema) {xs ys : HeadNormalForm schema}
    (h : ∀ a ∈ xs, ∃ b ∈ ys, a.label = b.label ∧
      DerivesNoAIP env a.continuation b.continuation) :
    DerivesNoAIP env (.choice xs.render ys.render) ys.render := by
  have one (b : HeadSummand schema) (zs : HeadNormalForm schema) (hb : b ∈ zs) :
      DerivesNoAIP env (.choice b.render zs.render) zs.render := by
    have same (c : HeadSummand schema) : c ∈ b :: zs ↔ c ∈ zs := by
      simp only [List.mem_cons]
      exact ⟨fun hc => hc.elim (fun e => e.symm ▸ hb) id, Or.inr⟩
    exact render_derives_of_mem_iff env same
  induction xs with
  | nil => exact .trans (.a2 _ _) (.a5 _)
  | cons a xs ih =>
    obtain ⟨b, hb, lab, d⟩ := h a List.mem_cons_self
    have head : DerivesNoAIP env a.render b.render := by
      unfold HeadSummand.render
      rw [← lab]
      exact .prefixCongr _ d
    exact .trans (.a3 _ _ _) (.trans
      (.choiceCongr head (ih (fun c hc => h c (List.mem_cons_of_mem _ hc))))
      (one b ys hb))

/-- Reduce equality of bisimilar head forms to equality of matched residuals. -/
theorem complete_of_continuations {env : RecEnv schema} {xs ys : HeadNormalForm schema}
    (h : Bisimilar env xs.render ys.render)
    (complete : ∀ a ∈ xs, ∀ b ∈ ys, Bisimilar env a.continuation b.continuation →
      DerivesNoAIP env a.continuation b.continuation) :
    DerivesNoAIP env xs.render ys.render := by
  have left : DerivesNoAIP env (.choice xs.render ys.render) ys.render := by
    apply absorb env
    intro a ha
    obtain ⟨b, hb, hl, hbis⟩ := match_head h ha
    exact ⟨b, hb, hl, complete a ha b hb hbis⟩
  have right : DerivesNoAIP env (.choice ys.render xs.render) xs.render := by
    apply absorb env
    intro b hb
    obtain ⟨a, ha, hl, hbis⟩ := match_head (h.symm env) hb
    exact ⟨a, ha, hl, (complete a ha b hb (hbis.symm env)).symm⟩
  exact .trans right.symm (.trans (.a2 _ _) left)

end HeadNormalForm

/-- The completeness direction of Theorem 1 for ground terms, without AIP. -/
theorem ground_complete {env : RecEnv schema} {p q : DyNetKAT schema}
    (hp : Ground p) (hq : Ground q) (h : Bisimilar env p q) :
    DerivesNoAIP env p q := by
  suffices aux : ∀ n (s t : DyNetKAT schema), prefixCount s + prefixCount t = n →
      Ground s → Ground t → Bisimilar env s t → DerivesNoAIP env s t from
    aux _ p q rfl hp hq h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s t hn gs gt hs
    obtain ⟨xs, dx, bx⟩ := gs.exists_headNormalForm (env := env)
    obtain ⟨ys, dy, bys⟩ := gt.exists_headNormalForm (env := env)
    have hnf := (dx.sound.symm env).trans env (hs.trans env dy.sound)
    refine .trans dx (.trans (HeadNormalForm.complete_of_continuations hnf ?_) dy.symm)
    intro a ha b hb hab
    obtain ⟨ga, la⟩ := bx a ha
    obtain ⟨gb, lb⟩ := bys b hb
    exact ih _ (hn ▸ Nat.add_lt_add la lb) _ _ rfl ga gb hab

theorem HeadNormalForm.ground_complete {env : RecEnv schema} {xs ys : HeadNormalForm schema}
    (hx : Ground xs.render) (hy : Ground ys.render)
    (h : Bisimilar env xs.render ys.render) : DerivesNoAIP env xs.render ys.render :=
  DyNetKAT.DyNetKAT.ground_complete hx hy h

/-- Theorem 1 on the typed ground domain. Soundness holds without the ground hypotheses. -/
theorem ground_derives_iff_bisimilar {env : RecEnv schema} {p q : DyNetKAT schema}
    (hp : Ground p) (hq : Ground q) :
    Derives env p q ↔ Bisimilar env p q :=
  ⟨Derives.sound, fun h => .ofNoAIP (ground_complete hp hq h)⟩

end DyNetKAT.DyNetKAT
