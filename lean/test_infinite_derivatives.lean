import DyNetKAT

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.InfiniteDerivativesTests

open DyNetKAT.NetKAT

private def blocker : GProc := .rcfgPrefix "b" .id .deadlock

private def spawnEnv : RecEnv :=
  RecEnv.empty.define "X" (.rcfgPrefix "a" .id
    (.parallel (.var "X") (.rcfgPrefix "b" .id .deadlock)))

private theorem spawnSupported : FiniteSupport spawnEnv (.var "X") {"X"} := by
  refine ⟨by simp [recursiveVars], ?_⟩
  intro x hx
  have hx' : x = "X" := Finset.mem_singleton.mp hx
  subst x
  simp [spawnEnv, recursiveVars]

private def graph : ProcessGraph := toGraph spawnEnv (.var "X") {"X"} spawnSupported

private def spawnState : Nat → GProc
  | 0 => .ref (varNode "X")
  | n + 1 => .parallel (spawnState n) blocker

private theorem spawnStep (n : Nat) :
    GStep graph ⟨spawnState n, [], []⟩ (.rcfg "a" .id) ⟨spawnState (n + 1), [], []⟩ := by
  induction n with
  | zero =>
      exact .var _ _ _ _ _ _ _ (by
        have hLabel : graph.label (varNode "X") =
            .rcfgPrefix "a" .id (.parallel (.ref (varNode "X")) blocker) := by
          simp [graph, spawnEnv, toGProc, blocker]
        change GStep graph ⟨graph.label (varNode "X"), [], []⟩ _ _
        rw [hLabel]
        exact .rcfg _ _ _ _ _)
  | succ n ih =>
      exact .par_l _ _ _ _ _ _ _ _ ih

/-- One-step enumeration succeeds at every growing derivative. -/
theorem spawn_guardedMoves_exact (n : Nat) :
    ∃ row, guardedMoves graph (spawnState n) = some row ∧ MovesExact graph (spawnState n) row := by
  have supportedRow : ∃ row, guardedMoves graph (spawnState n) = some row := by
    apply (guardedMoves_exists_iff graph _).mpr
    induction n with
    | zero =>
        change MoveAdmissible (fun _ => False) (graph.label (varNode "X"))
        simp [graph, spawnEnv, toGProc, MoveAdmissible]
    | succ n ih =>
        exact ⟨ih, trivial⟩
  obtain ⟨row, h⟩ := supportedRow
  exact ⟨row, h, guardedMoves_exact h⟩

private theorem spawnReach (n : Nat) : ReachableDerivative graph (spawnState n) := by
  induction n with
  | zero => exact .refl
  | succ n ih => exact ih.tail ⟨[], [], .rcfg "a" .id, [], [], trivial, spawnStep n⟩

private theorem spawnInjective : Function.Injective spawnState := by
  intro n
  induction n with
  | zero =>
      intro m h
      cases m
      · rfl
      · cases h
  | succ n ih =>
      intro m h
      cases m
      · cases h
      · exact congrArg Nat.succ (ih (GProc.parallel.inj h).1)

/-- One recursive definition gives infinitely many distinct process
    derivatives under the restricted SOS, with both packet lists empty. -/
theorem spawn_no_finite_derivatives : ¬ HasFiniteDerivatives graph := by
  rintro ⟨S, hFinite, hClosure⟩
  apply (Set.infinite_range_of_injective spawnInjective) (hFinite.subset ?_)
  rintro _ ⟨n, rfl⟩
  exact (hClosure.mem_iff _).mpr (spawnReach n)

theorem spawn_rejects_every_candidate {n : Nat} (C : NormalizationCandidate n) :
    normalizeGraph graph C = .error .invalidCertificate := by
  apply (normalizeGraph_invalid_iff graph C).mpr
  cases h : checkNormalization graph C with
  | false => rfl
  | true => exact (spawn_no_finite_derivatives (checkNormalization_finite h)).elim

private def checks : RestrictionChecks := fun _ _ => false

private theorem spawnWellFormed : WellFormed spawnEnv (.var "X") := by
  have body (x : Var) (hx : ReachableVar spawnEnv (.var "X") x) :
      x = "X" := Finset.mem_singleton.mp
    (reachableVars_subset_of_finiteSupport spawnEnv _ _ spawnSupported x hx)
  constructor
  · intro x hx
    rw [body x hx]
    rfl
  · intro x hx
    rw [body x hx]
    exact ⟨_, rfl, trivial⟩

private theorem spawnPaperAdmissible : PaperAdmissible true spawnEnv (.var "X") := by
  refine ⟨spawnWellFormed, trivial, ?_⟩
  intro x body hx lookup
  obtain rfl := Finset.mem_singleton.mp
    (reachableVars_subset_of_finiteSupport spawnEnv _ _ spawnSupported x hx)
  have definition := RecEnv.lookup_unique lookup
    (show spawnEnv.lookup "X" = some _ from rfl)
  simpa [definition, PaperSyntax]

example : ¬ BaseAdmissible spawnEnv (.var "X") := by
  intro base
  have body := base.2.2 "X" _ (.direct (by simp)) (show spawnEnv.lookup "X" = some _ from rfl)
  simp [PaperSyntax] at body

example (n : Nat) : ∃ p, PaperAdmissible true spawnEnv p ∧ Corr graph spawnEnv p (spawnState n) := by
  have trace (start count : Nat) : ∃ actions,
      GSteps graph ⟨spawnState start, [], []⟩ actions ⟨spawnState (start + count), [], []⟩ := by
    induction count generalizing start with
    | zero => exact ⟨[], .nil _⟩
    | succ count ih =>
      obtain ⟨actions, tail⟩ := ih (start + 1)
      rw [show start + 1 + count = start + (count + 1) by omega] at tail
      exact ⟨_ :: actions, .cons _ _ _ _ _ (spawnStep start) tail⟩
  obtain ⟨actions, steps⟩ := trace 0 n
  rw [Nat.zero_add] at steps
  exact steps.preserves_paperAdmissible (toGraph_corr spawnEnv _ _ spawnSupported)
    spawnPaperAdmissible

-- Environment closure and guardedness do not make the spawning root ground.
example : WellFormed spawnEnv (.var "X") ∧ ¬ Ground (.var "X") :=
  ⟨spawnWellFormed, by simp [Ground]⟩

example : WellFormed spawnEnv (.var "X") ∧ ¬ TypedPaperGuarded (.var "X") :=
  ⟨spawnWellFormed, fun h => h "X" .here⟩

private def spawnDependencies :=
  DependencyGraph.build spawnEnv (.var "X") {"X"} spawnSupported

#guard spawnDependencies.edges == {("X", "X")}
#guard spawnDependencies.sccs == {{"X"}}
#guard spawnDependencies.cyclicSccs == {{"X"}}

example {C : Finset Var} (hC : C ∈ spawnDependencies.sccs) {x : Var} (hx : x ∈ C) :
    (∃ b, spawnEnv.lookup x = some b ∧ TypedPaperGuarded b) ∧ ¬ HasFiniteDerivatives graph :=
  ⟨DependencyGraph.guarded_scc spawnSupported spawnWellFormed hC hx,
    spawn_no_finite_derivatives⟩

private theorem spawnBodyChecks (x : Var) (b : DyNetKAT)
    (hx : ReachableVar spawnEnv (.var "X") x) (hb : spawnEnv.lookup x = some b) :
    AllRestrictionChecksCorrect (toGProc b) checks := by
  have he : x = "X" := Finset.mem_singleton.mp
    (reachableVars_subset_of_finiteSupport spawnEnv _ _ spawnSupported x hx)
  subst x
  simp only [spawnEnv, RecEnv.lookup_define_same, Option.some.injEq] at hb
  subst b
  exact ⟨trivial, trivial⟩

theorem spawn_projection (n : Nat) : ∃ q,
    renderProjection graph (fun _ => checks) n ⟨graph.root, checks⟩ = some q ∧
      Bisimilar spawnEnv q (.project n (.var "X")) :=
  renderProjection_source spawnSupported spawnWellFormed checks (fun _ => checks) trivial
    spawnBodyChecks n

-- The global graph derivative family is infinite, and each member has a
-- finite row. The source theorem covers every reachable residual as well.
theorem spawn_memo_projection (n : Nat) : ∃ q stats,
    renderProjectionMemo graph (fun _ => checks) n ⟨graph.root, checks⟩ = some (q, stats) ∧
      Bisimilar spawnEnv q (.project n (.var "X")) :=
  renderProjectionMemo_source spawnSupported spawnWellFormed checks (fun _ => checks)
    trivial spawnBodyChecks n

private def spawnMemo (n : Nat) :=
  renderProjectionMemo graph (fun _ => checks) n ⟨graph.root, checks⟩

#guard ([1, 2, 4] : List Nat).map (fun n => (spawnMemo n).map Prod.snd) ==
  [some ⟨0, 2, 1⟩, some ⟨0, 4, 1⟩, some ⟨0, 18, 1⟩]

example (n : Nat) : (spawnMemo n).map Prod.fst =
    renderProjection graph (fun _ => checks) n ⟨graph.root, checks⟩ :=
  renderProjectionMemo_eq _ _ _ _

theorem spawn_finite_branching (n : Nat) :
    {q : GProc | ∃ pt hl a pt' hl', GStep graph ⟨spawnState n, pt, hl⟩ a
      ⟨q, pt', hl'⟩}.Finite := by
  obtain ⟨_, _, h⟩ := spawn_guardedMoves_exact n
  exact h.finite_graph_targets

theorem spawn_imageFinite : ImageFiniteFrom spawnEnv (.var "X") :=
  imageFinite_supported spawnSupported spawnWellFormed checks (fun _ => checks) trivial
    spawnBodyChecks

#guard ([1, 2, 4] : List Nat).all fun n =>
  (renderProjection graph (fun _ => checks) n ⟨graph.root, checks⟩).isSome

-- The same specification has image-finite reachable processes even
-- though spawn_no_finite_derivatives rules out a finite derivative space.
example : ImageFiniteFrom spawnEnv (.var "X") := spawnWellFormed.imageFiniteFrom

example : Bisimilar spawnEnv (.var "X")
    (.rcfgPrefix "a" .id (.parallel (.var "X") (.rcfgPrefix "b" .id .deadlock))) := by
  let body := DyNetKAT.rcfgPrefix "a" .id (.parallel (.var "X") (.rcfgPrefix "b" .id .deadlock))
  have lookup : spawnEnv.lookup "X" = some body := rfl
  have hw := WellFormed.body spawnEnv (.var "X") "X" body spawnWellFormed
    (.direct (by simp)) lookup
  exact Derives.aip_guarded_sound spawnWellFormed hw
    (fun n => .ofNoAIP (.projectCongr n (.unfold lookup)))

-- A single algebraic head retains the growing recursive continuation.
example : DerivesNoAIP spawnEnv (.var "X")
    (HeadNormalForm.render [HeadSummand.rcfg "a" .id
      (.parallel (.var "X") (.rcfgPrefix "b" .id .deadlock))]) :=
  .trans (.unfold rfl) (HeadNormalForm.render_singleton spawnEnv (HeadSummand.rcfg "a" .id
    (.parallel (.var "X") (.rcfgPrefix "b" .id .deadlock)))).symm

example : ∃ q, IsDNKNormalForm q ∧ DerivesNoAIP spawnEnv (.var "X") q :=
  spawnWellFormed.normalizes

#print axioms spawn_no_finite_derivatives
#print axioms spawn_rejects_every_candidate


private def spawnClosure :=
  discoverClosure
    (toGraph_projectionSupport spawnSupported spawnWellFormed (fun _ => checks)
      (fun x b hx hb => spawnBodyChecks x b hx hb))
    .structural ⟨4, 32, 8⟩ ⟨graph.root, checks⟩
    (toGProc_projectionValid (env := spawnEnv) (root := .var "X") trivial)

private def spawnClosureFailure : Option DiscoveryFailure :=
  match spawnClosure with
  | .ok _ => none
  | .error e => some e

#eval spawnClosureFailure
#guard (spawnClosureFailure == some .resourceLimit)

example (n : Nat) : ∃ q,
    renderProjection graph (fun _ => checks) n ⟨graph.root, checks⟩ = some q ∧
      Bisimilar spawnEnv q (.project n (.var "X")) := spawn_projection n

theorem spawn_no_valid_closure (rows : ClosureCandidate graph) :
    ¬ ValidClosure graph.root rows := by
  intro cert
  apply (Set.infinite_range_of_injective spawnInjective) (cert.reachableFinite.subset ?_)
  rintro _ ⟨n, rfl⟩
  apply Relation.ReflTransGen.mono ?_ (spawnReach n)
  rintro _ _ ⟨pt, hl, a, pt', hl', _, hs⟩
  exact ⟨pt, hl, a, pt', hl', hs⟩

-- Spent components remain as deadlocks. The index counts unspent blockers.
private inductive SpawnResidual : Nat → GProc → Prop
  | root : SpawnResidual 0 graph.root
  | live : SpawnResidual n p → SpawnResidual (n + 1) (.parallel p blocker)
  | spent : SpawnResidual n p → SpawnResidual n (.parallel p .deadlock)

private theorem SpawnResidual.step {n p} (h : SpawnResidual n p) {pt hl a q pt' hl'}
    (hs : GStep graph ⟨p, pt, hl⟩ a ⟨q, pt', hl'⟩) :
    pt' = pt ∧ hl' = hl ∧
      ((a = .rcfg "a" .id ∧ SpawnResidual (n + 1) q) ∨
       (a = .rcfg "b" .id ∧ ∃ k, n = k + 1 ∧ SpawnResidual k q)) := by
  induction h generalizing pt hl a q pt' hl' with
  | root =>
    change GStep graph ⟨.ref (varNode "X"), pt, hl⟩ a ⟨q, pt', hl'⟩ at hs
    have hh := gstep_ref_inv hs
    have label : graph.label (varNode "X") = .rcfgPrefix "a" .id (.parallel graph.root blocker) := by
      simp [graph, spawnEnv, toGProc, blocker]
      rfl
    rw [label] at hh
    cases hh
    exact ⟨rfl, rfl, Or.inl ⟨rfl, .live .root⟩⟩
  | live h ih =>
    cases hs with
    | par_l _ _ _ _ _ _ _ _ hs =>
      obtain ⟨rfl, rfl, ⟨rfl, hq⟩ | ⟨rfl, k, rfl, hq⟩⟩ := ih hs
      · exact ⟨rfl, rfl, Or.inl ⟨rfl, .live hq⟩⟩
      · exact ⟨rfl, rfl, Or.inr ⟨rfl, _, rfl, .live hq⟩⟩
    | par_r _ _ _ _ _ _ _ _ hs =>
      cases hs
      exact ⟨rfl, rfl, Or.inr ⟨rfl, _, rfl, .spent h⟩⟩
    | sync_recv_send _ _ _ _ _ _ _ _ hs _ => obtain ⟨_, _, ⟨he, _⟩ | ⟨he, _⟩⟩ := ih hs <;> cases he
    | sync_send_recv _ _ _ _ _ _ _ _ hs _ => obtain ⟨_, _, ⟨he, _⟩ | ⟨he, _⟩⟩ := ih hs <;> cases he
  | spent _ ih =>
    cases hs with
    | par_l _ _ _ _ _ _ _ _ hs =>
      obtain ⟨rfl, rfl, ⟨rfl, hq⟩ | ⟨rfl, k, rfl, hq⟩⟩ := ih hs
      · exact ⟨rfl, rfl, Or.inl ⟨rfl, .spent hq⟩⟩
      · exact ⟨rfl, rfl, Or.inr ⟨rfl, _, rfl, .spent hq⟩⟩
    | par_r _ _ _ _ _ _ _ _ hs => cases hs
    | sync_recv_send _ _ _ _ _ _ _ _ _ hs => cases hs
    | sync_send_recv _ _ _ _ _ _ _ _ _ hs => cases hs

private theorem SpawnResidual.consume {n p} (h : SpawnResidual n p) (hp : 0 < n) :
    ∃ q, GStep graph ⟨p, [], []⟩ (.rcfg "b" .id) ⟨q, [], []⟩ ∧
      SpawnResidual (n - 1) q := by
  induction h with
  | root => omega
  | live h => exact ⟨_, .par_r _ _ _ _ _ _ _ _ (.rcfg _ _ _ _ _), .spent h⟩
  | spent h ih =>
    obtain ⟨q, hs, hq⟩ := ih hp
    exact ⟨_, .par_l _ _ _ _ _ _ _ _ hs, .spent hq⟩

private theorem SpawnResidual.bisim_count {n m p q} (hp : SpawnResidual n p)
    (hq : SpawnResidual m q) (hb : GBisimilar graph p q) : n = m := by
  have le {n m p q} (hp : SpawnResidual n p) (hq : SpawnResidual m q)
      (hb : GBisimilar graph p q) : n ≤ m := by
    induction n generalizing m p q with
    | zero => omega
    | succ n ih =>
      obtain ⟨p', hs, hp'⟩ := hp.consume (by omega)
      obtain ⟨q', ht, hb'⟩ := (gbisimilar_isGBisimulation graph).2 p q hb [] [] _ p' [] [] hs
      obtain ⟨_, _, ⟨he, _⟩ | ⟨_, k, rfl, hq'⟩⟩ := hq.step ht
      · exact (show Action.rcfg "b" .id ≠ .rcfg "a" .id by intro h; have := Action.rcfg.inj h; simp at this) he |>.elim
      · have := ih hp' hq' hb'
        omega
  exact Nat.le_antisymm (le hp hq hb) (le hq hp (hb.symm graph))

private theorem spawnResidual (n : Nat) : SpawnResidual n (spawnState n) := by
  induction n with
  | zero => exact .root
  | succ _ ih => exact .live ih

theorem spawn_bisimilar_only_if_equal_count {j k : Nat}
    (h : GBisimilar graph (spawnState j) (spawnState k)) : j = k :=
  (spawnResidual j).bisim_count (spawnResidual k) h

theorem spawn_no_finite_quotient {n} (T : AbstractTable n) :
    IsEmpty (BisimulationQuotient graph graph.root T) := by
  classical
  constructor
  intro cert
  have covered (k : Nat) : ∃ i, T.Reaches i ∧ cert.represents i (spawnState k) :=
    cert.toSimulationAbstraction.allReachable
      ((spawnReach k).mono (by rintro _ _ ⟨pt, hl, a, pt', hl', _, hs⟩
                               exact ⟨pt, hl, a, pt', hl', hs⟩))
  let index (k : Nat) := (covered k).choose
  apply not_injective_infinite_finite index
  intro j k he
  have hj := (covered j).choose_spec.2
  have hk := (covered k).choose_spec.2
  change index j = index k at he
  change cert.represents (index k) (spawnState k) at hk
  rw [← he] at hk
  exact spawn_bisimilar_only_if_equal_count (cert.sameClass hj hk)

private def spawnTable : AbstractTable 2 :=
  ⟨0, fun i => if i = 0 then [(.visible (.rcfg "a" .id), 0), (.visible (.rcfg "b" .id), 0)]
               else []⟩

private def spawnSimulation : SimulationAbstraction graph graph.root spawnTable where
  represents i p := i = 0 ∧ ∃ n, SpawnResidual n p
  initial := ⟨rfl, 0, .root⟩
  forward := by
    rintro i p q pt hl a pt' hl' ⟨rfl, n, hr⟩ hs
    obtain ⟨rfl, rfl, ⟨rfl, hq⟩ | ⟨rfl, k, _, hq⟩⟩ := hr.step hs
    · exact ⟨0, ⟨_, by simp [spawnTable], .rcfg⟩, rfl, _, hq⟩
    · exact ⟨0, ⟨_, by simp [spawnTable], .rcfg⟩, rfl, k, hq⟩

theorem spawn_all_depth_no_packet_or_communication {p}
    (reach : Relation.ReflTransGen (ConcreteStep graph) graph.root p) :
    ∀ {pt hl a q pt' hl'}, GStep graph ⟨p, pt, hl⟩ a ⟨q, pt', hl'⟩ →
      pt' = pt ∧ hl' = hl ∧ (a = .rcfg "a" .id ∨ a = .rcfg "b" .id) := by
  apply spawnSimulation.liftProperty (Inv := fun i => i = 0) ?_ ?_ reach
  · intro i h
    induction h with
    | refl => rfl
    | tail _ hs ih =>
      obtain ⟨pt, hl, a, pt', hl', l, hm, _⟩ := hs
      rw [ih] at hm
      simp [spawnTable] at hm
      rcases hm with h | h <;> exact h.2
  · rintro _ _ _ ⟨_, n, hr⟩ _ _ _ _ _ _ hs
    obtain ⟨hp, hh, ha | hb⟩ := hr.step hs
    exacts [⟨hp, hh, Or.inl ha.1⟩, ⟨hp, hh, Or.inr hb.1⟩]

#print axioms spawn_no_finite_quotient
#print axioms spawn_all_depth_no_packet_or_communication


private def spawnProgram : Program true spawnEnv := ⟨.var "X", spawnPaperAdmissible⟩
private def compiledSpawn : spawnProgram.Compiled := ⟨_, spawnSupported⟩

private def spawnStrategy (request : AnalysisRequest) :=
  compiledSpawn.analyze checks
    (toGraph_projectionSupport spawnSupported spawnWellFormed (fun _ => checks)
      (fun x b hx hb => spawnBodyChecks x b hx hb))
    (toGProc_projectionValid (env := spawnEnv) (root := .var "X") trivial)
    .structural ⟨4, 32, 8⟩ request (some (.simulation spawnTable spawnSimulation))

#guard (spawnStrategy (.allDepth none)).guarantee == .simulationAbstraction 2
#guard (spawnStrategy (.bounded 2)).guarantee == .boundedProjection 2
#guard (spawnStrategy (.exactModel (some 2))).guarantee == .boundedProjection 2
#guard (spawnStrategy (.exactModel (some 2))).closureFailure == some .resourceLimit
#guard (spawnStrategy (.exactModel none)).guarantee == .unknown

private def spawnPropertyResult :
    StatePropertyVerdict graph graph.root
      (fun p => ∀ {pt hl a q pt' hl'}, GStep graph ⟨p, pt, hl⟩ a ⟨q, pt', hl'⟩ →
        pt' = pt ∧ hl' = hl ∧ (a = .rcfg "a" .id ∨ a = .rcfg "b" .id)) := by
  exact match spawnStrategy (.allDepth none) with
  | .simulation _ _ _ =>
    .provedAllDepth (.simulationAbstraction 2)
      (fun _ reach => spawn_all_depth_no_packet_or_communication reach)
  | result => .unknown result.guarantee result.closureFailure

#guard (match spawnPropertyResult with
  | .provedAllDepth (.simulationAbstraction 2) _ => true
  | _ => false)

end DyNetKAT.DyNetKAT.InfiniteDerivativesTests
