import DyNetKATLean

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.FiniteCertificateTests

open DyNetKAT.NetKAT

private def x := auxNode 0
private def y := auxNode 1
private def z := auxNode 2
private def a (p : GProc) := GProc.rcfgPrefix "a" .id p

-- X has two same-observation successors with different future behavior.
-- Y has the same alternatives in reverse order and cycles through Z.
private def body : NodeId → GProc
  | .inr 0 => .choice (a .deadlock) (a (.ref x))
  | .inr 1 => .choice (a (.ref z)) (a .deadlock)
  | .inr 2 => .choice (a (.ref y)) (a .deadlock)
  | _ => .deadlock

private def graph : ProcessGraph where
  nodes := {x, y, z}
  root := .ref x
  label := body
  root_closed := by simp [gprocRefs]
  closed := by
    intro i _
    match i with
    | .inr 0 | .inr 1 | .inr 2 | .inr (_ + 3) | .inl _ =>
      simp [body, gprocRefs, a, Finset.union_subset_iff]

-- Keep both same-observation successors, including the deadlocking branch.
private def nondeterministicTable : AbstractTable 2 :=
  ⟨0, fun i => if i = 0 then [(.visible (.rcfg "a" .id), 1), (.visible (.rcfg "a" .id), 0)] else []⟩

private theorem nondeterministicExact :
    MovesExact graph (.ref x) [(.visible (.rcfg "a" .id), .deadlock),
      (.visible (.rcfg "a" .id), .ref x)] :=
  guardedMoves_exact (by rfl)

private def nondeterministicQuotient :
    BisimulationQuotient graph (.ref x) nondeterministicTable where
  represents i p := p = (if i = 0 then .ref x else .deadlock)
  initial := rfl
  forward := by
    rintro i p q pt hl act pt' hl' rfl hs
    by_cases hi : i = 0
    · subst i
      change GStep graph ⟨.ref x, pt, hl⟩ act ⟨q, pt', hl'⟩ at hs
      obtain ⟨l, hm, hr⟩ := (nondeterministicExact pt hl act q pt' hl').mp hs
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨1, ⟨_, by simp [nondeterministicTable], hr⟩, rfl⟩
      · exact ⟨0, ⟨_, by simp [nondeterministicTable], hr⟩, rfl⟩
    · simp only [if_neg hi] at hs
      cases hs
  backward := by
    rintro i j p pt hl act pt' hl' rfl ⟨l, hm, hr⟩
    by_cases hi : i = 0
    · subst i
      change (l, j) ∈ [(.visible (.rcfg "a" .id), 1), (.visible (.rcfg "a" .id), 0)] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨.deadlock, (nondeterministicExact pt hl act _ pt' hl').mpr
          ⟨_, by simp, hr⟩, rfl⟩
      · exact ⟨.ref x, (nondeterministicExact pt hl act _ pt' hl').mpr
          ⟨_, by simp, hr⟩, rfl⟩
    · simp [nondeterministicTable, hi] at hm

private def checks : RestrictionChecks := fun _ _ => false

private theorem supported : ProjectionSupport graph (fun _ => checks) (fun _ => True) := by
  refine ⟨by simp, ?_⟩
  intro i _
  change MoveAdmissible _ (body i) true ∧ AllRestrictionChecksCorrect (body i) checks
  match i with
  | .inr 0 | .inr 1 | .inr 2 | .inr (_ + 3) | .inl _ =>
    simp [body, a, MoveAdmissible, AllRestrictionChecksCorrect]

private def closure (p : GProc) (valid : AllRestrictionChecksCorrect p checks) :=
  discoverClosure supported .structural ⟨8, 16, 8⟩ ⟨p, checks⟩ ⟨by simp, valid⟩

private def stats (result : Except DiscoveryFailure (ClosureCandidate graph)) :=
  result.map fun rows => (rows.length, (rows.map fun r => r.moves.length).sum)

private def left := closure (.ref x) trivial
private def right := closure (.ref y) trivial

example : stats left = .ok (2, 2) := rfl
example : stats right = .ok (3, 4) := rfl

private def compare (p q : GProc) (l r : Except DiscoveryFailure (ClosureCandidate graph)) := do
  discoverBisimulation .structural 32 32 p q (← l) (← r)

private def found (result : Except DiscoveryFailure (BisimCandidate graph)) : Bool :=
  match result with
  | .ok _ => true
  | .error _ => false

#guard found (compare (.ref x) (.ref y) left right)
#guard found (compare (.ref y) (.ref y) right right)
#guard !(found (compare (.ref x) .deadlock left (closure .deadlock trivial)))

private def combined :=
  discoverResidualBisimulation supported .structural ⟨8, 16, 8⟩ 32 32
    ⟨.ref x, checks⟩ ⟨.ref y, checks⟩ ⟨by simp, trivial⟩ ⟨by simp, trivial⟩

example : GBisimilar graph (.ref x) (.ref y) := by
  have success : ∃ pairs, combined = .ok pairs := ⟨_, rfl⟩
  obtain ⟨pairs, he⟩ := success
  have cert := discoverResidualBisimulation_sound he
  exact ⟨pairs.Relates, cert.bisimulation, cert.roots⟩

-- One state and one transition. The root returns to itself.
private def loopGraph : ProcessGraph where
  nodes := {x}
  root := .ref x
  label := fun _ => a (.ref x)
  root_closed := by simp [gprocRefs]
  closed := by simp [gprocRefs, a]

private theorem loopSupport :
    ProjectionSupport loopGraph (fun _ => checks) (fun _ => True) :=
  ⟨by simp, fun _ _ => ⟨trivial, trivial⟩⟩

private def loop := discoverClosure loopSupport .structural ⟨1, 1, 1⟩
  ⟨loopGraph.root, checks⟩ ⟨by simp, trivial⟩

example : (loop.map fun rows => (rows.length, (rows.map fun r => r.moves.length).sum)) = .ok (1, 1) := rfl

example {q : GProc} (h : Relation.ReflTransGen (ConcreteStep loopGraph) loopGraph.root q) :
    q = loopGraph.root := by
  have hc : ∃ rows, loop = .ok rows ∧ ∀ p, rows.Represents p → p = loopGraph.root := by
    refine ⟨_, rfl, ?_⟩
    rintro p ⟨r, hr, rfl⟩
    obtain rfl := List.mem_singleton.mp hr
    rfl
  obtain ⟨rows, he, onlyRoot⟩ := hc
  exact (discoverClosure_sound he).liftProperty onlyRoot h

private def mismatch : Bool :=
  match left, closure .deadlock trivial with
  | .ok (l :: _), .ok (r :: _) => checkReconfigurationMismatch l r "a" .id
  | _, _ => false

#guard mismatch

example : ¬ GBisimilar graph (.ref x) .deadlock := by
  have witness : ∃ l r : ConcreteRow graph, l.proc = .ref x ∧ r.proc = .deadlock ∧
      checkReconfigurationMismatch l r "a" .id = true := by
    have rows : ∃ l r : ConcreteRow graph, ∃ ls rs,
        left = .ok (l :: ls) ∧ closure .deadlock trivial = .ok (r :: rs) ∧
        l.proc = .ref x ∧ r.proc = .deadlock ∧ checkReconfigurationMismatch l r "a" .id = true :=
      ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨l, r, _, _, _, _, hl, hr, hc⟩ := rows
    exact ⟨l, r, hl, hr, hc⟩
  obtain ⟨l, r, hl, hr, hm⟩ := witness
  simpa only [hl, hr] using checkReconfigurationMismatch_sound hm

example : discoverClosure loopSupport .structural ⟨1, 0, 1⟩
    ⟨loopGraph.root, checks⟩ ⟨by simp, trivial⟩ = .error .resourceLimit := rfl

example : discoverClosure loopSupport .structural ⟨1, 1, 0⟩
    ⟨loopGraph.root, checks⟩ ⟨by simp, trivial⟩ = .error .resourceLimit := rfl

#print axioms checkClosure_sound
#print axioms ValidClosure.allReachable
#print axioms ValidClosure.liftProperty
#print axioms ValidClosure.coversSource
#print axioms discoverClosure_sound
#print axioms checkBisimulation_sound
#print axioms ValidBisimCertificate.bisimilar
#print axioms discoverBisimulation_sound
#print axioms checkReconfigurationMismatch_sound
#print axioms discoverResidualBisimulation_sound
#print axioms analyzeRecursive_ground
#print axioms analyzeRecursive_closure


private def strategyEnv : RecEnv :=
  (RecEnv.empty.define "X" (.choice (.rcfgPrefix "a" .id .deadlock)
    (.rcfgPrefix "a" .id (.var "X")))).define "Y" (.choice
      (.rcfgPrefix "a" .id (.var "Z")) (.rcfgPrefix "a" .id .deadlock))
    |>.define "Z" (.choice (.rcfgPrefix "a" .id (.var "Y")) (.rcfgPrefix "a" .id .deadlock))

private def strategyRoot : DyNetKAT := .choice (.var "X") (.var "Y")
private def strategyNames : Finset Var := {"X", "Y", "Z"}
private theorem strategyFinite : FiniteSupport strategyEnv strategyRoot strategyNames := by
  refine ⟨by simp [strategyRoot, strategyNames, recursiveVars, Finset.union_subset_iff], ?_⟩
  intro v hv
  simp [strategyNames] at hv
  rcases hv with rfl | rfl | rfl <;>
    exact ⟨_, rfl, by simp [recursiveVars, strategyNames, Finset.union_subset_iff]⟩

private def strategyGraph := toGraph strategyEnv strategyRoot strategyNames strategyFinite

private theorem strategySupported : ProjectionSupport strategyGraph (fun _ => checks)
    (fun i => i = varNode "X" ∨ i = varNode "Y" ∨ i = varNode "Z") := by
  have label (v : Var) (hv : v ∈ strategyNames) :=
    toGraph_label_varNode strategyFinite hv
  constructor
  · rintro i (rfl | rfl | rfl) j hj
    all_goals
      rw [strategyGraph, label _ (by simp [strategyNames])] at hj
      simp [strategyEnv, RecEnv.lookup, RecEnv.define, toGProc, gprocRefs] at hj
      subst j
      simp
  · rintro i (rfl | rfl | rfl)
    all_goals
      rw [strategyGraph, label _ (by simp [strategyNames])]
      exact ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

private theorem strategyCorr (p : DyNetKAT) (h : recursiveVars p ⊆ strategyNames) :
    Corr strategyGraph strategyEnv p (toGProc p) :=
  toGraph_corr_of_subset _ _ _ strategyFinite p h

private def mutualStrategy :=
  Internal.analyzeResidual strategySupported
    (state := ⟨toGProc (.var "Y"), checks⟩) ⟨by simp [toGProc, gprocRefs], trivial⟩
    (strategyCorr (.var "Y") (by simp [strategyNames])) .structural ⟨8, 16, 8⟩ (.allDepth none)

#guard mutualStrategy.guarantee == .finiteClosure 3

private def equivalentStrategy :=
  Internal.analyzeEquivalence strategySupported
    (left := ⟨toGProc (.var "X"), checks⟩) (right := ⟨toGProc (.var "Y"), checks⟩)
    ⟨by simp [toGProc, gprocRefs], trivial⟩ ⟨by simp [toGProc, gprocRefs], trivial⟩
    (strategyCorr (.var "X") (by simp [strategyNames]))
    (strategyCorr (.var "Y") (by simp [strategyNames])) .structural ⟨8, 16, 8⟩ 32 32

#guard (match equivalentStrategy.guarantee with
  | .finiteBisimulation _ => true
  | _ => false)

private def mismatchStrategy :=
  Internal.analyzeEquivalence strategySupported
    (left := ⟨toGProc (.var "X"), checks⟩) (right := ⟨.deadlock, checks⟩)
    ⟨by simp [toGProc, gprocRefs], trivial⟩ ⟨by simp [gprocRefs], trivial⟩
    (strategyCorr (.var "X") (by simp [strategyNames]))
    (corr_deadlock_intro strategyGraph strategyEnv) .structural ⟨8, 16, 8⟩ 32 32
    (some ("a", .id))

#guard mismatchStrategy.guarantee == .distinguishingWitness

private def exhaustedEquivalence (supplied : Option (SuppliedEquivalence strategyEnv
    (.var "X") (.var "X"))) :=
  Internal.analyzeEquivalence strategySupported
    (left := ⟨toGProc (.var "X"), checks⟩) (right := ⟨toGProc (.var "X"), checks⟩)
    ⟨by simp [toGProc, gprocRefs], trivial⟩ ⟨by simp [toGProc, gprocRefs], trivial⟩
    (strategyCorr (.var "X") (by simp [strategyNames]))
    (strategyCorr (.var "X") (by simp [strategyNames])) .structural ⟨0, 0, 0⟩ 0 0 none supplied

#guard (exhaustedEquivalence none).guarantee == .unknown
#guard (exhaustedEquivalence (some (.direct (Bisimilar.refl _ _)))).guarantee ==
  .directEquivalence

#print axioms Internal.boundedAnalysis
#print axioms Internal.analyzeResidual
#print axioms AnalysisResult.proveStateProperty
#print axioms AnalysisResult.quotientModel
#print axioms EquivalenceResult.proof?
#print axioms Internal.analyzeEquivalence

end DyNetKAT.DyNetKAT.FiniteCertificateTests
