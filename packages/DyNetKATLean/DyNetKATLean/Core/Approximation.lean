import DyNetKATLean.Core.RestrictionProjection

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

variable {schema : PacketSchema}

open DyNetKAT.NetKAT

/-- The finite image needed to match a single SOS transition. Both the
initial and final packet lists and the action are fixed. -/
def ImageFiniteAt (env : RecEnv schema) (p : DyNetKAT schema) : Prop :=
  ∀ (pt hl : List schema.Packet) (a : Action schema) (pt' hl' : List schema.Packet),
    {q : (DyNetKAT schema) | Step env ⟨p, pt, hl⟩ a ⟨q, pt', hl'⟩}.Finite

def ImageFiniteFrom (env : RecEnv schema) (p : DyNetKAT schema) : Prop :=
  ∀ q, Relation.ReflTransGen (ProcessStep env) p q → ImageFiniteAt env q

theorem ImageFiniteFrom.step {env : RecEnv schema} {p q : DyNetKAT schema}
    (h : ImageFiniteFrom env p) (hs : ProcessStep env p q) : ImageFiniteFrom env q :=
  fun r hr => h r ((Relation.ReflTransGen.single hs).trans hr)

/-- The successor uses precisely one less level, with identical packet effects. -/
theorem project_step_exact_iff {env : RecEnv schema} {p q : DyNetKAT schema} {n : Nat}
    {pt hl pt' hl' : List schema.Packet} {a : Action schema} :
    Step env ⟨.project (n + 1) p, pt, hl⟩ a ⟨.project n q, pt', hl'⟩ ↔
      Step env ⟨p, pt, hl⟩ a ⟨q, pt', hl'⟩ := by
  constructor
  · intro h
    obtain ⟨r, he, hs⟩ := project_step_inv env n p pt hl a _ pt' hl' h
    cases he
    exact hs
  · exact Step.cpol_project n p q a pt pt' hl hl'

/-- Projecting an already projected process to a smaller budget. -/
theorem project_truncate (env : RecEnv schema) (p : DyNetKAT schema) {m n : Nat} (hmn : m ≤ n) :
    Bisimilar env (.project m (.project n p)) (.project m p) := by
  let R (x y : DyNetKAT schema) : Prop :=
    ∃ m n p, m ≤ n ∧ x = .project m (.project n p) ∧ y = .project m p
  refine ⟨fun x y => R x y ∨ R y x, ⟨fun _ _ h => h.symm, ?_⟩,
    Or.inl ⟨m, n, p, hmn, rfl, rfl⟩⟩
  intro x y h pt hl a x' pt' hl' hs
  rcases h with ⟨m, n, p, hmn, rfl, rfl⟩ | ⟨m, n, p, hmn, rfl, rfl⟩
  · cases m with
    | zero => cases hs
    | succ m =>
      cases n with
      | zero => omega
      | succ n =>
        obtain ⟨u, rfl, hu⟩ := project_step_inv env m _ pt hl a _ pt' hl' hs
        obtain ⟨v, rfl, hv⟩ := project_step_inv env n _ pt hl a _ pt' hl' hu
        exact ⟨.project m v, project_step_exact_iff.mpr hv,
          Or.inl ⟨m, n, v, Nat.le_of_succ_le_succ hmn, rfl, rfl⟩⟩
  · cases m with
    | zero => cases hs
    | succ m =>
      cases n with
      | zero => omega
      | succ n =>
        obtain ⟨v, rfl, hv⟩ := project_step_inv env m _ pt hl a _ pt' hl' hs
        exact ⟨.project m (.project n v),
          project_step_exact_iff.mpr (project_step_exact_iff.mpr hv),
          Or.inr ⟨m, n, v, Nat.le_of_succ_le_succ hmn, rfl, rfl⟩⟩

theorem project_bisimilar_of_le {env : RecEnv schema} {p q : DyNetKAT schema} {m n : Nat}
    (hmn : m ≤ n) (h : Bisimilar env (.project n p) (.project n q)) :
    Bisimilar env (.project m p) (.project m q) :=
  Bisimilar.trans env (Bisimilar.symm env (project_truncate env p hmn))
    (Bisimilar.trans env (Bisimilar.project env (n := m) h) (project_truncate env q hmn))

/-- A finite candidate set cannot have a failure depth for every candidate
while still admitting a match at every depth. -/
private theorem finite_depth_match {α : Type} {s : Set α} (hf : s.Finite)
    {accepts : Nat → α → Prop}
    (hmono : ∀ {m n x}, m ≤ n → accepts n x → accepts m x)
    (h : ∀ n, ∃ x ∈ s, accepts n x) :
    ∃ x ∈ s, ∀ n, accepts n x := by
  classical
  by_contra! hnone
  have failures : ∀ x : s, ∃ n, ¬ accepts n x := fun x => hnone x x.property
  choose depth hdepth using failures
  letI := hf.fintype
  have bounded (xs : Finset s) : ∃ n, ∀ x ∈ xs, depth x ≤ n := by
    induction xs using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | @insert x xs _ ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨max (depth x) n, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Nat.le_max_left _ _
      · exact (hn y hy).trans (Nat.le_max_right _ _)
  obtain ⟨n, hn⟩ := bounded Finset.univ
  obtain ⟨x, hx, hm⟩ := h n
  exact hdepth ⟨x, hx⟩ (hmono (hn ⟨x, hx⟩ (Finset.mem_univ _)) hm)

/-- Only the matching side needs an image-finite state for this direction. -/
theorem approximation_match {env : RecEnv schema} {p q p' : DyNetKAT schema}
    (hf : ImageFiniteAt env q)
    (h : ∀ n, Bisimilar env (.project n p) (.project n q))
    {pt hl pt' hl' : List schema.Packet} {a : Action schema}
    (hp : Step env ⟨p, pt, hl⟩ a ⟨p', pt', hl'⟩) :
    ∃ q', Step env ⟨q, pt, hl⟩ a ⟨q', pt', hl'⟩ ∧
      ∀ n, Bisimilar env (.project n p') (.project n q') := by
  apply finite_depth_match (hf pt hl a pt' hl')
  · exact fun hle he => project_bisimilar_of_le hle he
  · intro n
    obtain ⟨R, hR, hRelated⟩ := h (n + 1)
    obtain ⟨target, hs, hr⟩ := hR.2 _ _ hRelated pt hl a (.project n p') pt' hl'
      (project_step_exact_iff.mpr hp)
    obtain ⟨q', rfl, hq⟩ := project_step_inv env n q pt hl a target pt' hl' hs
    exact ⟨q', hq, R, hR, hr⟩

/-- Semantic AIP for processes whose reachable states are image finite. -/
theorem approximation_induction {env : RecEnv schema} {p q : DyNetKAT schema}
    (hp : ImageFiniteFrom env p) (hq : ImageFiniteFrom env q)
    (h : ∀ n, Bisimilar env (.project n p) (.project n q)) : Bisimilar env p q := by
  let R (p q : DyNetKAT schema) : Prop := ImageFiniteFrom env p ∧ ImageFiniteFrom env q ∧
    ∀ n, Bisimilar env (.project n p) (.project n q)
  refine ⟨R, ⟨?_, ?_⟩, hp, hq, h⟩
  · rintro p q ⟨hp, hq, he⟩
    exact ⟨hq, hp, fun n => Bisimilar.symm env (he n)⟩
  · rintro p q ⟨hp, hq, he⟩ pt hl a p' pt' hl' hs
    obtain ⟨q', hq', ha⟩ := approximation_match (hq q .refl) he hs
    exact ⟨q', hq', hp.step ⟨pt, hl, a, pt', hl', hs⟩,
      hq.step ⟨pt, hl, a, pt', hl', hq'⟩, ha⟩

/-- On image-finite reachable states, finite projections characterize
strong source bisimilarity. -/
theorem approximation_induction_iff {env : RecEnv schema} {p q : DyNetKAT schema}
    (hp : ImageFiniteFrom env p) (hq : ImageFiniteFrom env q) :
    Bisimilar env p q ↔ ∀ n, Bisimilar env (.project n p) (.project n q) :=
  ⟨project_bisim_all_depths env, approximation_induction hp hq⟩

end DyNetKAT.DyNetKAT
