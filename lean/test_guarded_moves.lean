import DyNetKAT

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.GuardedMovesTests

open DyNetKAT.NetKAT

private def host : DyNetKAT := .var "Host"
private def switch : DyNetKAT := .var "Switch"
private def root : DyNetKAT := .parallel host switch
private def hostBody : DyNetKAT := .send "update" .id switch
private def switchBody : DyNetKAT := .recv "update" .id host

private def env : RecEnv :=
  (RecEnv.empty.define "Host" hostBody).define "Switch" switchBody

private def support : Finset Var := {"Host", "Switch"}

private theorem supported : FiniteSupport env root support := by
  refine ⟨by simp [root, host, switch, recursiveVars, support, Finset.union_subset_iff], ?_⟩
  intro x hx
  simp [support] at hx
  rcases hx with rfl | rfl
  · exact ⟨hostBody, rfl, by simp [hostBody, switch, recursiveVars, support]⟩
  · exact ⟨switchBody, rfl, by simp [switchBody, host, recursiveVars, support]⟩

private theorem wellFormed : WellFormed env root := by
  have bodies : ∀ x, ReachableVar env root x →
      ∃ b, env.lookup x = some b ∧ GuardedOccurrences b := by
    intro x hx
    have hm := reachableVars_subset_of_finiteSupport env root support supported x hx
    simp [support] at hm
    rcases hm with rfl | rfl
    · exact ⟨hostBody, rfl, trivial⟩
    · exact ⟨switchBody, rfl, trivial⟩
  refine ⟨?_, bodies⟩
  intro x hx
  obtain ⟨b, hb, _⟩ := bodies x hx
  simp [hb]

example : WellFormed env root ∧ TypedPaperGuarded hostBody ∧
    TypedPaperGuarded switchBody ∧ ¬ TypedPaperGuarded root := by
  refine ⟨wellFormed, ?_, ?_, fun h => h "Host" (.parallelLeft .here)⟩
  · intro _ h
    cases h
  · intro _ h
    cases h

-- Unfold both references inside parallel without spending projection depth.
example :
    Bisimilar env (.project 1 root) (.project 1 (.parallel hostBody switchBody)) := by
  have hh : Bisimilar env host hostBody := Equations.unfold_sound env rfl
  have hs : Bisimilar env switch switchBody := Equations.unfold_sound env rfl
  obtain ⟨_, _, _, _, _, _, _, hp, _, _⟩ := paperLemma3 env hh hs .id "update" ∅ 1
  obtain ⟨_, _, _, _, _, projected, _⟩ := paperLemma3 env hp hp .id "update" ∅ 1
  exact projected

#print axioms paperLemma3
#print axioms Equations.unfold_sound

private def dependencies := DependencyGraph.build env root support supported

#guard dependencies.entries == {"Host", "Switch"}
#guard dependencies.edges == {("Host", "Switch"), ("Switch", "Host")}
#guard dependencies.sccs == {{"Host", "Switch"}}
#guard dependencies.cyclicSccs == dependencies.sccs

example {C : Finset Var} (hC : C ∈ dependencies.sccs) {x : Var} (hx : x ∈ C) :
    ∃ b, env.lookup x = some b ∧ TypedPaperGuarded b :=
  DependencyGraph.guarded_scc supported wellFormed hC hx

private def graph : ProcessGraph := toGraph env root support supported

example : ∃ row, guardedMoves graph (toGProc root)
    (some (fun _ _ => false)) (fun _ => some (fun _ _ => false)) = some row :=
  guardedMoves_toGraph_exists supported wellFormed _ _

private def row : List SymbolicMove :=
  [(.send "update" .id, toGProc (.parallel switch switch)),
   (.recv "update" .id, toGProc (.parallel host host)),
   (.visible (.rcfg "update" .id), toGProc (.parallel switch host))]

private theorem computed : guardedMoves graph (toGProc root) = some row := by
  have hh : graph.label (varNode "Host") = toGProc hostBody := by
    rw [graph, toGraph_label_varNode supported (by simp [support])]
    rfl
  have hs : graph.label (varNode "Switch") = toGProc switchBody := by
    rw [graph, toGraph_label_varNode supported (by simp [support])]
    rfl
  simp only [guardedMoves, root, host, switch, toGProc, localMoves, hh, hs,
    hostBody, switchBody, Option.some_bind]
  rfl

-- A body row is used directly as the reference row, with the same residual.
example : guardedMoves graph (toGProc host) =
    localMoves (fun _ => none) (graph.label (varNode "Host")) := rfl

-- Two reference lookups and a handshake appear as one source transition.
example (pt hl : List CtxPkt) :
    ∃ p', Step env ⟨root, pt, hl⟩ (.rcfg "update" .id) ⟨p', pt, hl⟩ ∧
      Corr graph env p' (toGProc (.parallel switch host)) := by
  have exactRow := (guardedMoves_exact computed).source_steps
    (toGraph_corr env root support supported) pt hl (.rcfg "update" .id) pt hl
  exact exactRow.1 _ _ (by simp [row]) .rcfg

private def restrictedRoot : DyNetKAT := .restrict Set.univ root

private theorem restrictedSupport : FiniteSupport env restrictedRoot support := supported

private theorem restrictedWellFormed : WellFormed env restrictedRoot := by
  have liftReach : ∀ x, ReachableVar env restrictedRoot x → ReachableVar env root x := by
    intro x hx
    induction hx with
    | direct h => exact .direct h
    | throughDefinition _ hBody hOccurs ih => exact .throughDefinition ih hBody hOccurs
  exact ⟨fun x hx => wellFormed.1 x (liftReach x hx), fun x hx => wellFormed.2 x (liftReach x hx)⟩

private def restrictedGraph := toGraph env restrictedRoot support restrictedSupport
private def rootChecks : RestrictionChecks := fun _ _ => true
private def bodyChecks : NodeId → RestrictionChecks := fun _ _ _ => false

private theorem checked :
    GuardedRestrictionChecksCorrect restrictedGraph (toGProc restrictedRoot)
      (some rootChecks) (fun i => some (bodyChecks i)) := by
  have hh : restrictedGraph.label (varNode "Host") = toGProc hostBody := by
    rw [restrictedGraph, toGraph_label_varNode restrictedSupport (by simp [support])]
    rfl
  have hs : restrictedGraph.label (varNode "Switch") = toGProc switchBody := by
    rw [restrictedGraph, toGraph_label_varNode restrictedSupport (by simp [support])]
    rfl
  simp [GuardedRestrictionChecksCorrect, RestrictionChecksCorrect, restrictedRoot,
    root, host, switch, toGProc, rootChecks, hh, hs, hostBody, switchBody]

-- Both unilateral actions are blocked after the two references synchronize.
example : guardedMoves restrictedGraph (toGProc restrictedRoot)
    (some rootChecks) (fun i => some (bodyChecks i)) =
    some [(.visible (.rcfg "update" .id), toGProc (.restrict Set.univ (.parallel switch host)))] := by
  have hh : restrictedGraph.label (varNode "Host") = toGProc hostBody := by
    rw [restrictedGraph, toGraph_label_varNode restrictedSupport (by simp [support])]
    rfl
  have hs : restrictedGraph.label (varNode "Switch") = toGProc switchBody := by
    rw [restrictedGraph, toGraph_label_varNode restrictedSupport (by simp [support])]
    rfl
  simp only [guardedMoves, localMoves, toGProc, restrictedRoot, root, host, switch,
    hh, hs, hostBody, switchBody, Option.some_bind]
  rfl

example : ∃ result,
    guardedMoves restrictedGraph (toGProc restrictedRoot)
      (some rootChecks) (fun i => some (bodyChecks i)) = some result ∧
      SourceMovesExact restrictedGraph env restrictedRoot result :=
  guardedMoves_toGraph_source_exact restrictedSupport restrictedWellFormed _ _ checked

private theorem projectionBodyChecks (x : Var) (b : DyNetKAT)
    (hx : ReachableVar env root x) (hb : env.lookup x = some b) :
    AllRestrictionChecksCorrect (toGProc b) (bodyChecks (varNode x)) := by
  have hm := reachableVars_subset_of_finiteSupport env root support supported x hx
  simp [support] at hm
  rcases hm with rfl | rfl
  · have he : env.lookup "Host" = some hostBody := rfl
    rw [he] at hb
    cases hb
    trivial
  · have he : env.lookup "Switch" = some switchBody := rfl
    rw [he] at hb
    cases hb
    trivial

-- The unrestricted compound root and its mutual definitions render at every depth.
example (n : Nat) : ∃ q,
    renderProjection graph bodyChecks n ⟨toGProc root, rootChecks⟩ = some q ∧
      Bisimilar env q (.project n root) :=
  renderProjection_source supported wellFormed rootChecks bodyChecks
    ⟨trivial, trivial⟩ projectionBodyChecks n

example (n : Nat) : ∃ q,
    renderProjection graph bodyChecks n
      ((CheckedResidual.mk (toGProc root) rootChecks).restrict Set.univ (fun _ => true)) = some q ∧
      Bisimilar env q (.restrict Set.univ (.project n root)) :=
  renderProjection_restricted supported wellFormed rootChecks bodyChecks
    ⟨trivial, trivial⟩ projectionBodyChecks Set.univ (fun _ => true) (by simp) n

-- Both mutually guarded definitions are consulted for the compound root.
example (n : Nat) : ∃ q stats,
    renderProjectionMemo graph bodyChecks n ⟨toGProc root, rootChecks⟩ = some (q, stats) ∧
      Bisimilar env q (.project n root) :=
  renderProjectionMemo_source supported wellFormed rootChecks bodyChecks
    ⟨trivial, trivial⟩ projectionBodyChecks n

#guard ([0, 1, 2, 4] : List Nat).all fun n =>
  (renderProjectionMemo graph bodyChecks n ⟨toGProc root, rootChecks⟩).isSome

-- Lookup of a root reference costs zero depth.
example : renderProjection graph bodyChecks 1 ⟨toGProc host, rootChecks⟩ =
    some (choiceOf [.send "update" .id .deadlock]) := by
  have hh : graph.label (varNode "Host") = toGProc hostBody := by
    rw [graph, toGraph_label_varNode supported (by simp [support])]
    rfl
  simp only [renderProjection, checkedMoves, host, toGProc, localCheckedMoves, hh, hostBody]
  rfl

#guard ([1, 2, 3] : List Nat).all fun n =>
  (renderProjection graph bodyChecks n ⟨toGProc root, rootChecks⟩).isSome

-- The compound root and all derivatives of the mutual recursion have finite images.
example : ImageFiniteFrom env root :=
  imageFinite_supported supported wellFormed rootChecks bodyChecks
    ⟨trivial, trivial⟩ projectionBodyChecks

example : {q | ProcessStep env (.parallel switch host) q}.Finite := by
  have hs : Step env ⟨root, [], []⟩ (.rcfg "update" .id)
      ⟨.parallel switch host, [], []⟩ :=
    .cpol_sync_send_recv _ _ _ _ _ _ _ _
      (.cpol_var _ _ _ _ _ _ _ _ rfl (.cpol_send _ _ _ _ _))
      (.cpol_var _ _ _ _ _ _ _ _ rfl (.cpol_recv _ _ _ _ _))
  exact finite_branching_supported supported wellFormed rootChecks bodyChecks
    ⟨trivial, trivial⟩ projectionBodyChecks _
    (Relation.ReflTransGen.single ⟨[], [], _, [], [], hs⟩)

-- The guarded AIP rule needs neither the graph support nor the classifiers.
example : Bisimilar env (.choice restrictedRoot restrictedRoot) restrictedRoot := by
  have reach (x : Var) (h : ReachableVar env (.choice restrictedRoot restrictedRoot) x) :
      ReachableVar env restrictedRoot x := by
    induction h with
    | direct h => exact .direct (by simpa using h)
    | throughDefinition _ hBody hOccurs ih => exact .throughDefinition ih hBody hOccurs
  have hw : WellFormed env (.choice restrictedRoot restrictedRoot) :=
    ⟨fun x hx => restrictedWellFormed.1 x (reach x hx),
     fun x hx => restrictedWellFormed.2 x (reach x hx)⟩
  exact Derives.aip_guarded_sound hw restrictedWellFormed
    (fun n => .ofNoAIP (.projectCongr n (.a4 restrictedRoot)))

-- The algebraic witness for Host || Switch has the two interleavings and
-- one handshake, with both mutually recursive references still in scope.
example : DerivesNoAIP env root (HeadNormalForm.render
    [.send "update" .id (.parallel switch switch),
     .recv "update" .id (.parallel host host),
     .rcfg "update" .id (.parallel switch host)]) := by
  have left : DerivesNoAIP env host (HeadNormalForm.render [.send "update" .id switch]) :=
    .trans (.unfold rfl) (HeadNormalForm.render_singleton env (HeadSummand.send "update" .id switch)).symm
  have right : DerivesNoAIP env switch (HeadNormalForm.render [.recv "update" .id host]) :=
    .trans (.unfold rfl) (HeadNormalForm.render_singleton env (HeadSummand.recv "update" .id host)).symm
  exact HeadNormalForm.parallel_correct env left right

example : ∃ q, IsDNKNormalForm q ∧ DerivesNoAIP env restrictedRoot q :=
  restrictedWellFormed.normalizes

#print axioms guardedMoves_toGraph_exists
#print axioms guardedMoves_toGraph_source_exact
#print axioms guardedMoves_exact_with
#print axioms guardedMoves_exact
#print axioms MovesExact.source_steps


private def closureChecks : RestrictionChecks := fun _ _ => false

private theorem closureSupport :
    ProjectionSupport graph (fun _ => closureChecks) (ProjectionLive env root) := by
  apply toGraph_projectionSupport supported wellFormed
  intro x b hx hb
  have hm := reachableVars_subset_of_finiteSupport env root support supported x hx
  simp [support] at hm
  rcases hm with rfl | rfl
  · have he : b = hostBody := Option.some.inj (hb.symm.trans rfl)
    subst b
    trivial
  · have he : b = switchBody := Option.some.inj (hb.symm.trans rfl)
    subst b
    trivial

private def hostClosure :=
  discoverClosure closureSupport .structural ⟨8, 32, 8⟩ ⟨graph.root, closureChecks⟩
    (toGProc_projectionValid (env := env) (root := root) ⟨trivial, trivial⟩)

#guard (match hostClosure with
  | .ok rows => rows.length == 4 && (rows.map fun r => r.moves.length).sum == 10
  | .error _ => false)


private def hostStrategy :=
  Internal.analyzeCompiledSource supported closureChecks closureSupport
    (toGProc_projectionValid (env := env) (root := root) ⟨trivial, trivial⟩)
    .structural ⟨8, 32, 8⟩ (.allDepth none)

#guard hostStrategy.guarantee == .finiteClosure 4

end DyNetKAT.DyNetKAT.GuardedMovesTests
