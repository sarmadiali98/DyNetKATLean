import DyNetKAT

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.FiniteAbstractionTests

open DyNetKAT.NetKAT

private def tick : MoveLabel := .visible (.rcfg "tick" .id)
private def table : AbstractTable 1 := ⟨0, fun _ => [(tick, 0)]⟩
private def node := varNode (AbstractTable.nodeName 1)
private def root : GProc := .ref node

-- One tick adds a deadlocked parallel component.
private def grow : Nat → GProc
  | 0 => root
  | n + 1 => .parallel (grow n) .deadlock

private def commonEnv : RecEnv :=
  table.environment.define (AbstractTable.nodeName 1) (.rcfgPrefix "tick" .id
    (.parallel (.var (AbstractTable.nodeName 1)) .deadlock))

private def growSource : DyNetKAT := .var (AbstractTable.nodeName 1)

private theorem growSupport : FiniteSupport commonEnv growSource {AbstractTable.nodeName 1} := by
  refine ⟨by simp [growSource], ?_⟩
  intro x hx
  obtain rfl := Finset.mem_singleton.mp hx
  exact ⟨_, rfl, by simp [recursiveVars, growSource]⟩

private def growing : ProcessGraph := toGraph commonEnv growSource _ growSupport

private theorem growing_label : growing.label node = .rcfgPrefix "tick" .id (grow 1) := by
  rw [growing, node, toGraph_label_varNode growSupport (by simp [node])]
  rfl

private theorem grow_step (n : Nat) (pt hl : List CtxPkt) :
    GStep growing ⟨grow n, pt, hl⟩ (.rcfg "tick" .id) ⟨grow (n + 1), pt, hl⟩ := by
  induction n with
  | zero =>
    apply GStep.var
    rw [growing_label]
    exact .rcfg _ _ _ _ _
  | succ n ih => exact .par_l _ _ _ _ _ _ _ _ ih

private theorem grow_exact (n : Nat) : MovesExact growing (grow n) [(tick, grow (n + 1))] := by
  intro pt hl a q pt' hl'
  constructor
  · intro hs
    induction n generalizing q a pt hl pt' hl' with
    | zero =>
      have h := gstep_ref_inv hs
      rw [growing_label] at h
      cases h
      exact ⟨tick, by simp, .rcfg⟩
    | succ n ih =>
      cases hs with
      | par_l _ _ _ _ _ _ _ _ hs =>
        obtain ⟨l, hm, hr⟩ := ih _ _ _ _ _ _ hs
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp hm)
        exact ⟨tick, by simp [grow], hr⟩
      | par_r _ _ _ _ _ _ _ _ hs => cases hs
      | sync_recv_send _ _ _ _ _ _ _ _ _ hs => cases hs
      | sync_send_recv _ _ _ _ _ _ _ _ _ hs => cases hs
  · rintro ⟨l, hm, hr⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp hm)
    cases hr
    exact grow_step n pt hl

private def quotient : BisimulationQuotient growing root table where
  represents _ p := ∃ n, p = grow n
  initial := ⟨0, rfl⟩
  forward := by
    rintro i p q pt hl a pt' hl' ⟨n, rfl⟩ hs
    obtain ⟨l, hm, hr⟩ := (grow_exact n pt hl a q pt' hl').mp hs
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp hm)
    exact ⟨0, ⟨tick, by simp [table], hr⟩, n + 1, rfl⟩
  backward := by
    rintro i j p pt hl a pt' hl' ⟨n, rfl⟩ ⟨l, hm, hr⟩
    obtain ⟨rfl, _⟩ := Prod.mk.inj (List.mem_singleton.mp hm)
    cases hr
    exact ⟨_, grow_step n pt hl, n + 1, rfl⟩

private theorem grow_injective : Function.Injective grow := by
  intro n
  induction n with
  | zero => intro m h; cases m <;> cases h; rfl
  | succ n ih =>
    intro m h
    cases m with
    | zero => cases h
    | succ m => exact congrArg Nat.succ (ih (GProc.parallel.inj h).1)

theorem infinite_concrete_one_state_quotient :
    {p | Relation.ReflTransGen (ConcreteStep growing) root p}.Infinite ∧
      Nonempty (BisimulationQuotient growing root table) := by
  refine ⟨(Set.infinite_range_of_injective grow_injective).mono ?_, ⟨quotient⟩⟩
  rintro p ⟨n, rfl⟩
  induction n with
  | zero => exact .refl
  | succ n ih => exact ih.tail ⟨[], [], _, [], [], grow_step n [] []⟩

theorem growing_source_bisimilar_to_one_state :
    Bisimilar commonEnv growSource (table.process table.initial) := by
  apply quotient.bisimilar (toGraph_corr commonEnv growSource _ growSupport)
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

private def looping : ProcessGraph where
  root := root
  nodes := {node}
  label := fun _ => .rcfgPrefix "tick" .id root
  root_closed := by simp [root, gprocRefs]
  closed := by simp [root, gprocRefs]

private def identityLoop : BisimulationQuotient looping root table where
  represents _ p := p = root
  initial := rfl
  forward := by
    rintro i p q pt hl a pt' hl' rfl hs
    have h := gstep_ref_inv hs
    cases h
    exact ⟨0, ⟨tick, by simp [table], .rcfg⟩, rfl⟩
  backward := by
    rintro i j p pt hl a pt' hl' rfl ⟨l, hm, hr⟩
    obtain ⟨rfl, _⟩ := Prod.mk.inj (List.mem_singleton.mp hm)
    cases hr
    exact ⟨root, .var _ _ _ _ _ _ _ (.rcfg _ _ _ _ _), rfl⟩

private def missing : AbstractTable 1 := ⟨0, fun _ => []⟩

example : IsEmpty (SimulationAbstraction growing root missing) := by
  constructor
  intro cert
  obtain ⟨_, l, hm, _⟩ := (cert.forward cert.initial (grow_step 0 [] [])).imp
    (fun _ h => h.1)
  simp [missing] at hm

private def wrongTarget : AbstractTable 2 := ⟨0, fun i => if i = 0 then [(tick, 1)] else []⟩

example : IsEmpty (SimulationAbstraction growing root wrongTarget) := by
  constructor
  intro cert
  obtain ⟨j, ⟨l, hm, _⟩, hj⟩ := cert.forward cert.initial (grow_step 0 [] [])
  have he : j = (1 : Fin 2) := congrArg Prod.snd (List.mem_singleton.mp hm)
  subst j
  obtain ⟨_, ⟨_, hm, _⟩, _⟩ := cert.forward hj (grow_step 1 [] [])
  simp [wrongTarget] at hm

private def invented : AbstractTable 1 :=
  ⟨0, fun _ => [(tick, 0), (.visible (.rcfg "extra" .id), 0)]⟩

example : IsEmpty (BisimulationQuotient growing root invented) := by
  constructor
  intro cert
  obtain ⟨q, hs, _⟩ := cert.backward cert.initial
    (show invented.Observes 0 0 [] [] (.rcfg "extra" .id) [] [] from
      ⟨_, by simp [invented], .rcfg⟩)
  obtain ⟨l, hm, hr⟩ := (grow_exact 0 [] [] _ q [] []).mp hs
  obtain ⟨rfl, _⟩ := Prod.mk.inj (List.mem_singleton.mp hm)
  have bad : ∀ a, MoveLabel.Realizes tick [] [] a [] [] → a ≠ .rcfg "extra" .id := by
    intro a h
    cases h
    intro he
    have := Action.rcfg.inj he
    simp at this
  exact bad _ hr rfl

private def wrongPayload : AbstractTable 1 :=
  ⟨0, fun _ => [(.send "update" (.seq .id .id), 0)]⟩

-- Equal packet policies do not make literal communication payloads equal.
example : ¬ wrongPayload.Observes 0 0 [] [] (.send "update" .id) [] [] := by
  rintro ⟨l, hm, h⟩
  obtain ⟨rfl, _⟩ := Prod.mk.inj (List.mem_singleton.mp hm)
  cases h

private def packetLoop : AbstractTable 1 :=
  ⟨0, fun _ => [(.visible (.packet .id), 0)]⟩

-- A table edge cannot leave the handled list unchanged on a packet step.
example (σ τ : CtxPkt) : ¬ packetLoop.Observes 0 0 [σ] [] (.packet σ τ) [] [] := by
  rintro ⟨l, hm, h⟩
  obtain ⟨rfl, _⟩ := Prod.mk.inj (List.mem_singleton.mp hm)
  cases h

-- An opaque blocked set needs no identity test at the abstraction boundary.
private def noMoves : AbstractTable 1 := ⟨0, fun _ => []⟩

def opaqueRestriction (L : Set CommunicationAction) :
    BisimulationQuotient looping (.restrict L .deadlock) noMoves where
  represents _ p := p = .restrict L .deadlock
  initial := rfl
  forward := by
    rintro i p q pt hl a pt' hl' rfl hs
    cases hs with
    | restrict _ _ _ _ _ _ _ _ _ hs => cases hs
  backward := by
    rintro i j p pt hl a pt' hl' _ ⟨l, hm, _⟩
    simp [noMoves] at hm

#print axioms SimulationAbstraction.forward
#print axioms SimulationAbstraction.liftProperty
#print axioms BisimulationQuotient.backward
#print axioms BisimulationQuotient.sourceModel
#print axioms BisimulationQuotient.bisimilar
#print axioms infinite_concrete_one_state_quotient
#print axioms growing_source_bisimilar_to_one_state


private def quotientChecks : RestrictionChecks := fun _ _ => false

private theorem quotientSupport : ProjectionSupport growing (fun _ => quotientChecks)
    (fun i => i = node) := by
  constructor
  · rintro i rfl j hj
    simpa [growing_label, grow, root, gprocRefs] using hj
  · rintro i rfl
    rw [growing_label]
    exact ⟨trivial, ⟨trivial, trivial⟩⟩

private def quotientStrategy :=
  analyzeCompiledSource growSupport quotientChecks quotientSupport
    ⟨by simp [growSource, node, toGProc, gprocRefs], trivial⟩ .structural ⟨3, 8, 8⟩
    (.exactModel none) (some (.quotient table quotient))

#guard quotientStrategy.guarantee == .strongQuotient 1

example : ∃ R, IsBisimulation2 commonEnv table.environment R ∧
    R growSource (table.process table.initial) :=
  AnalysisResult.quotientModel quotient (toGraph_corr commonEnv growSource _ growSupport)

end DyNetKAT.DyNetKAT.FiniteAbstractionTests
