import KATLean.Native.Decision

namespace KATLean.Native

variable {T A P : Type}

/-- Test observations at a relational state. Classical decidability is used
only in this semantic bridge, never by the executable solver. -/
noncomputable def observe (tests : T → Set P) (state : P) : Atom T :=
  fun name => @decide (state ∈ tests name) (Classical.propDecidable _)

theorem test_observe (predicate : Test T) (tests : T → Set P) (state : P) :
    predicate.eval (observe tests state) = true ↔ state ∈ predicate.interp tests := by
  classical
  induction predicate <;> simp_all [Test.eval, Test.interp, observe]
  case neg predicate ih =>
    cases value : predicate.eval (observe tests state) <;> simp_all

/-- A guarded word is realized by a sequence of relational action steps
whose states have exactly its recorded Boolean observations. -/
def Realizes (actions : A → Rel P) (tests : T → Set P) :
    Atom T → Word T A → P → P → Prop
  | atom, [], source, target => atom = observe tests source ∧ source = target
  | atom, (action, next) :: rest, source, target =>
      atom = observe tests source ∧
        ∃ middle, (actions action).holds source middle ∧ Realizes actions tests next rest middle target

theorem Realizes.start {actions : A → Rel P} {tests : T → Set P} {atom word source target}
    (h : Realizes actions tests atom word source target) : atom = observe tests source := by
  cases word <;> exact h.1

theorem Realizes.finish {actions : A → Rel P} {tests : T → Set P} {atom word source target}
    (h : Realizes actions tests atom word source target) : finish atom word = observe tests target := by
  induction word generalizing atom source with
  | nil => exact h.2 ▸ h.1
  | cons first rest ih => exact ih h.2.choose_spec.2

theorem realizes_append (actions : A → Rel P) (tests : T → Set P)
    (atom : Atom T) (u v : Word T A) (source target : P) :
    Realizes actions tests atom (u ++ v) source target ↔
      ∃ middle, Realizes actions tests atom u source middle ∧
        Realizes actions tests (finish atom u) v middle target := by
  induction u generalizing atom source with
  | nil =>
    constructor
    · intro h
      exact ⟨source, ⟨h.start, rfl⟩, h⟩
    · rintro ⟨middle, ⟨_, rfl⟩, h⟩
      exact h
  | cons first rest ih =>
    change (_ ∧ ∃ middle, _ ∧ _) ↔ ∃ middle, (_ ∧ ∃ next, _ ∧ _) ∧ _
    constructor
    · rintro ⟨observed, middle, step, tail⟩
      obtain ⟨endPrefix, firstPart, suffix⟩ := (ih first.2 middle).mp tail
      exact ⟨endPrefix, ⟨observed, middle, step, firstPart⟩, suffix⟩
    · rintro ⟨endPrefix, ⟨observed, middle, step, firstPart⟩, suffix⟩
      exact ⟨observed, middle, step, (ih first.2 middle).mpr ⟨endPrefix, firstPart, suffix⟩⟩

/-- Every accepted guarded word is sound in every KATLean relational model. -/
theorem Accept.relational_sound {e : Expr T A} {atom : Atom T} {word : Word T A}
    (accepted : Accept e atom word) (actions : A → Rel P) (tests : T → Set P) :
    ∀ source target, Realizes actions tests atom word source target →
      (e.interp Rel.tests actions tests).holds source target := by
  induction accepted with
  | one => exact fun _ _ h => h.2
  | test atom predicate checked =>
    intro source target realized
    have test := (test_observe predicate tests source).mp (realized.start ▸ checked)
    exact ⟨test, realized.2⟩
  | action atom next name =>
    rintro source target ⟨_, middle, step, _, rfl⟩
    exact step
  | plusLeft _ ih => exact fun source target h => Or.inl (ih source target h)
  | plusRight _ ih => exact fun source target h => Or.inr (ih source target h)
  | @seq p atom u q v _ _ ihp ihq =>
    intro source target h
    obtain ⟨middle, firstPart, suffix⟩ := (realizes_append actions tests atom u v source target).mp h
    exact ⟨middle, ihp source middle firstPart, ihq middle target suffix⟩
  | starNil => exact fun _ _ h => h.2 ▸ Relation.ReflTransGen.refl
  | @starCons p atom u v _ _ ihp ihq =>
    intro source target h
    obtain ⟨middle, firstPart, suffix⟩ := (realizes_append actions tests atom u v source target).mp h
    exact (ihq middle target suffix).head (ihp source middle firstPart)

/-- The guarded-string semantics is exact for arbitrary relational
interpretations, not merely a packet regression model. -/
theorem interp_iff_accept (e : Expr T A) (actions : A → Rel P) (tests : T → Set P)
    (source target : P) :
    (e.interp Rel.tests actions tests).holds source target ↔
      ∃ atom word, Accept e atom word ∧ Realizes actions tests atom word source target := by
  constructor
  · intro run
    induction e generalizing source target with
    | zero => exact run.elim
    | one => exact ⟨observe tests source, [], .one _, rfl, run⟩
    | action name =>
      exact ⟨observe tests source, [(name, observe tests target)], .action _ _ _,
        rfl, target, run, rfl, rfl⟩
    | test predicate =>
      exact ⟨observe tests source, [], .test _ _ ((test_observe predicate tests source).mpr run.1),
        rfl, run.2⟩
    | plus p q ihp ihq =>
      rcases run with hp | hq
      · obtain ⟨atom, word, accepted, realized⟩ := ihp source target hp
        exact ⟨atom, word, .plusLeft accepted, realized⟩
      · obtain ⟨atom, word, accepted, realized⟩ := ihq source target hq
        exact ⟨atom, word, .plusRight accepted, realized⟩
    | seq p q ihp ihq =>
      obtain ⟨middle, hp, hq⟩ := run
      obtain ⟨atom, u, acceptedP, realizedP⟩ := ihp source middle hp
      obtain ⟨next, v, acceptedQ, realizedQ⟩ := ihq middle target hq
      have equal : next = finish atom u := realizedQ.start.trans realizedP.finish.symm
      subst next
      exact ⟨atom, u ++ v, .seq acceptedP acceptedQ,
        (realizes_append actions tests atom u v source target).mpr ⟨middle, realizedP, realizedQ⟩⟩
    | star p ih =>
      change Relation.ReflTransGen (p.interp Rel.tests actions tests).holds source target at run
      induction run using Relation.ReflTransGen.head_induction_on with
      | refl => exact ⟨observe tests target, [], .starNil _ _, rfl, rfl⟩
      | @head source middle step tail rest =>
        obtain ⟨atom, u, acceptedP, realizedP⟩ := ih source middle step
        obtain ⟨next, v, acceptedStar, realizedStar⟩ := rest
        have equal : next = finish atom u := realizedStar.start.trans realizedP.finish.symm
        subst next
        exact ⟨atom, u ++ v, .starCons acceptedP acceptedStar,
          (realizes_append actions tests atom u v source target).mpr ⟨middle, realizedP, realizedStar⟩⟩
  · rintro ⟨atom, word, accepted, realized⟩
    exact accepted.relational_sound actions tests source target realized

/-- Equality in every relational KATLean interpretation. The scope is
explicit; no abstract KAT completeness theorem is assumed. -/
def RelationalEquivalent (p q : Expr T A) : Prop :=
  ∀ (P : Type) (actions : A → Rel P) (tests : T → Set P),
    p.interp Rel.tests actions tests = q.interp Rel.tests actions tests

theorem LanguageEquivalent.relational_sound {p q : Expr T A} (equal : LanguageEquivalent p q) :
    RelationalEquivalent p q := by
  intro P actions tests
  unfold LanguageEquivalent at equal
  apply Rel.ext_holds
  intro source target
  simp only [interp_iff_accept, equal]

end KATLean.Native
