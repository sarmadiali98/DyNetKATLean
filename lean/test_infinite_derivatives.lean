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

end DyNetKAT.DyNetKAT.InfiniteDerivativesTests
