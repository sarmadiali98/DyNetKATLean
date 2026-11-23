import DyNetKATLean.Core.FiniteClosure

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

variable {schema : NetKAT.PacketSchema}

open DyNetKAT.NetKAT

/-- Executable candidate data. The node index supplies finite decidable identity. -/
structure AbstractTable (n : Nat) (schema : NetKAT.PacketSchema := NetKAT.ctxSchema) where
  initial : Fin n
  row : Fin n → List ((MoveLabel schema) × Fin n)

namespace AbstractTable

def Observes {n : Nat} (T : (AbstractTable n (schema := schema))) (i j : Fin n)
    (pt hl : List schema.Packet) (a : Action schema) (pt' hl' : List schema.Packet) : Prop :=
  ∃ l, (l, j) ∈ T.row i ∧ l.Realizes pt hl a pt' hl'

def Edge {n : Nat} (T : (AbstractTable n (schema := schema))) (i j : Fin n) : Prop :=
  ∃ pt hl a pt' hl', T.Observes i j pt hl a pt' hl'

def Reaches {n : Nat} (T : (AbstractTable n (schema := schema))) :=
  Relation.ReflTransGen T.Edge T.initial

def nodeName (i : Nat) : String := String.mk (List.replicate i 'q')

def process {n : Nat} (_ : (AbstractTable n (schema := schema))) (i : Fin n) : DyNetKAT schema :=
  .var (nodeName i.val)

def body {n : Nat} (T : (AbstractTable n (schema := schema))) (i : Fin n) : DyNetKAT schema :=
  choiceOf ((T.row i).map fun (l, j) => l.prefix (T.process j))

/-- Any environment with these definitions can execute the rendered model. -/
def Implements {n : Nat} (T : (AbstractTable n (schema := schema))) (env : RecEnv schema) : Prop :=
  ∀ i, env.lookup (nodeName (i : Fin n).val) = some (T.body i)

def environment {n : Nat} (T : (AbstractTable n (schema := schema))) : RecEnv schema := fun name =>
  (List.finRange n).findSome? fun i => if name = nodeName i.val then some (T.body i) else none

theorem environment_implements {n : Nat} (T : (AbstractTable n (schema := schema))) : T.Implements T.environment := by
  intro i
  unfold environment RecEnv.lookup
  apply List.findSome?_eq_some_iff.mpr
  have hm : i ∈ List.finRange n := by simp
  -- All entries with the requested name have the same body.
  generalize List.finRange n = indices at hm ⊢
  induction indices with
  | nil => simp at hm
  | cons j js ih =>
    by_cases h : nodeName i.val = nodeName j.val
    · have hj : i = j := Fin.ext (by simpa [nodeName, String.length] using congrArg String.length h)
      subst j
      exact ⟨[], i, js, rfl, by simp, by simp⟩
    · obtain ⟨as, b, bs, he, hb, ha⟩ := ih ((List.mem_cons.mp hm).resolve_left (fun e => h (congrArg (fun k : Fin n => nodeName k.val) e)))
      exact ⟨j :: as, b, bs, by simp [he], hb, by simpa [h] using ha⟩

theorem step_iff {n : Nat} (T : (AbstractTable n (schema := schema))) {env : RecEnv schema}
    (he : T.Implements env) (i : Fin n) (pt hl : List schema.Packet) (a : Action schema)
    (q : DyNetKAT schema) (pt' hl' : List schema.Packet) :
    Step env ⟨T.process i, pt, hl⟩ a ⟨q, pt', hl'⟩ ↔
      ∃ j, q = T.process j ∧ T.Observes i j pt hl a pt' hl' := by
  have unfoldStep :
      Step env ⟨T.process i, pt, hl⟩ a ⟨q, pt', hl'⟩ ↔
      Step env ⟨T.body i, pt, hl⟩ a ⟨q, pt', hl'⟩ := by
    constructor
    · intro h
      cases h with
      | cpol_var _ _ _ _ _ _ _ _ lookup hs =>
        cases Option.some.inj (lookup.symm.trans (he i))
        exact hs
    · exact fun h => .cpol_var _ _ _ _ _ _ _ _ (he i) h
  rw [unfoldStep, body, choiceOf_step_iff]
  constructor
  · rintro ⟨b, hb, hs⟩
    obtain ⟨⟨l, j⟩, hm, rfl⟩ := List.mem_map.mp hb
    obtain ⟨rfl, hr⟩ := (l.prefix_step_iff env _ _ _ _ _ _ _).mp hs
    exact ⟨j, rfl, l, hm, hr⟩
  · rintro ⟨j, rfl, l, hm, hr⟩
    exact ⟨_, List.mem_map.mpr ⟨(l,j), hm, rfl⟩,
      (l.prefix_step_iff env _ _ _ _ _ _ _).mpr ⟨rfl, hr⟩⟩

end AbstractTable

structure SimulationAbstraction {schema : NetKAT.PacketSchema} {n : Nat} (G : ProcessGraph schema) (root : GProc schema)
    (T : (AbstractTable n (schema := schema))) where
  represents : Fin n → GProc schema → Prop
  initial : represents T.initial root
  forward : ∀ {i p q pt hl a pt' hl'}, represents i p →
    GStep G ⟨p, pt, hl⟩ a ⟨q, pt', hl'⟩ →
    ∃ j, T.Observes i j pt hl a pt' hl' ∧ represents j q

namespace SimulationAbstraction

theorem allReachable {n G root} {T : (AbstractTable n (schema := schema))} (C : SimulationAbstraction G root T)
    {q : GProc schema} (h : Relation.ReflTransGen (ConcreteStep G) root q) :
    ∃ j, T.Reaches j ∧ C.represents j q := by
  induction h with
  | refl => exact ⟨_, .refl, C.initial⟩
  | tail _ hs ih =>
    obtain ⟨i, hi, hr⟩ := ih
    obtain ⟨pt, hl, a, pt', hl', hs⟩ := hs
    obtain ⟨j, hj, hq⟩ := C.forward hr hs
    exact ⟨j, hi.tail ⟨pt, hl, a, pt', hl', hj⟩, hq⟩

theorem liftProperty {n G root} {T : (AbstractTable n (schema := schema))} (C : SimulationAbstraction G root T)
    {Inv : Fin n → Prop} {Safe : GProc schema → Prop}
    (invariant : ∀ i, T.Reaches i → Inv i)
    (transfer : ∀ i p, Inv i → C.represents i p → Safe p)
    {q : GProc schema} (reach : Relation.ReflTransGen (ConcreteStep G) root q) : Safe q := by
  obtain ⟨i, hi, hr⟩ := C.allReachable reach
  exact transfer i q (invariant i hi) hr

theorem coversSource {n G root} {T : (AbstractTable n (schema := schema))} (C : SimulationAbstraction G root T)
    {env : RecEnv schema} {c d : Config schema} {acts : List (Action schema)} (corr : Corr G env c.proc root)
    (steps : Steps env c acts d) :
    ∃ j q, T.Reaches j ∧ C.represents j q ∧ Corr G env d.proc q := by
  obtain ⟨q, hs, hc⟩ := steps_to_gsteps G env c d acts steps root corr
  obtain ⟨j, hj, hr⟩ := C.allReachable hs.concreteReachable
  exact ⟨j, q, hj, hr, hc⟩

end SimulationAbstraction

structure BisimulationQuotient {schema : NetKAT.PacketSchema} {n : Nat} (G : ProcessGraph schema) (root : GProc schema)
    (T : (AbstractTable n (schema := schema))) extends SimulationAbstraction G root T where
  backward : ∀ {i j p pt hl a pt' hl'}, represents i p →
    T.Observes i j pt hl a pt' hl' →
    ∃ q, GStep G ⟨p, pt, hl⟩ a ⟨q, pt', hl'⟩ ∧ represents j q

namespace BisimulationQuotient

theorem sameClass {n G root} {T : (AbstractTable n (schema := schema))} (C : BisimulationQuotient G root T)
    {i p q} (hp : C.represents i p) (hq : C.represents i q) : GBisimilar G p q := by
  refine ⟨fun p q => ∃ i, C.represents i p ∧ C.represents i q, ⟨?_, ?_⟩, i, hp, hq⟩
  · rintro _ _ ⟨j, h₁, h₂⟩
    exact ⟨j, h₂, h₁⟩
  · rintro _ _ ⟨j, h₁, h₂⟩ pt hl a p' pt' hl' hs
    obtain ⟨k, he, hp'⟩ := C.forward h₁ hs
    obtain ⟨q', ht, hq'⟩ := C.backward h₂ he
    exact ⟨q', ht, k, hp', hq'⟩

theorem sourceModel {n G root} {T : (AbstractTable n (schema := schema))} (C : BisimulationQuotient G root T)
    {env model : RecEnv schema} {p : DyNetKAT schema} (hc : Corr G env p root) (hm : T.Implements model) :
    ∃ R, IsBisimulation2 env model R ∧ R p (T.process T.initial) := by
  refine ⟨fun p q => ∃ i g, q = T.process i ∧ Corr G env p g ∧ C.represents i g,
    ⟨?_, ?_⟩, T.initial, root, rfl, hc, C.initial⟩
  · rintro p _ ⟨i, g, rfl, hc, hr⟩ pt hl a p' pt' hl' hs
    obtain ⟨g', hg, hc'⟩ := step_to_gstep G env ⟨p, pt, hl⟩ ⟨p', pt', hl'⟩ a hs g hc
    obtain ⟨j, hj, hr'⟩ := C.forward hr hg
    exact ⟨_, (T.step_iff hm i pt hl a _ pt' hl').mpr ⟨j, rfl, hj⟩, j, g', rfl, hc', hr'⟩
  · rintro p _ ⟨i, g, rfl, hc, hr⟩ pt hl a q' pt' hl' hs
    obtain ⟨j, rfl, hj⟩ := (T.step_iff hm i pt hl a q' pt' hl').mp hs
    obtain ⟨g', hg, hr'⟩ := C.backward hr hj
    obtain ⟨p', hp', hc'⟩ := gstep_to_step G env ⟨g, pt, hl⟩ ⟨g', pt', hl'⟩ a hg p hc
    exact ⟨p', hp', j, g', rfl, hc', hr'⟩

theorem bisimilar {n G root} {T : (AbstractTable n (schema := schema))} (C : BisimulationQuotient G root T)
    {env : RecEnv schema} {p : DyNetKAT schema} (hc : Corr G env p root) (hm : T.Implements env) :
    Bisimilar env p (T.process T.initial) := by
  obtain ⟨_, h, hp⟩ := C.sourceModel hc hm
  exact bisimilar_of_isBisimulation2_same_env h hp

end BisimulationQuotient

end DyNetKAT.DyNetKAT
