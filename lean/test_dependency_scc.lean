import DyNetKAT

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.DependencySCCTests

open DyNetKAT.NetKAT
open DependencyGraph

private def emptyGraph : DependencyGraph :=
  build RecEnv.empty .deadlock ∅ ⟨by simp, by simp⟩

#guard emptyGraph.nodes == ∅ && emptyGraph.entries == ∅ && emptyGraph.sccs == ∅

private def singletonEnv : RecEnv := RecEnv.empty.define "X" .deadlock
private def singletonGraph : DependencyGraph :=
  build singletonEnv (.var "X") {"X"} (by
    refine ⟨by simp, ?_⟩
    intro x hx
    obtain rfl := Finset.mem_singleton.mp hx
    exact ⟨.deadlock, rfl, by simp⟩)

#guard singletonGraph.sccs == {{"X"}} && singletonGraph.cyclicSccs == ∅

private def chainEnv : RecEnv :=
  let e := RecEnv.empty.define "X" (.rcfgPrefix "tick" .id (.var "Y"))
  let e := e.define "Y" (.var "Z")
  let e := e.define "Z" .deadlock
  e.define "Irrelevant" (.var "Irrelevant")

private def chainSupport : Finset Var := {"X", "Y", "Z", "Irrelevant"}
private theorem chainFinite : FiniteSupport chainEnv (.var "X") chainSupport := by
  refine ⟨by simp [chainSupport], ?_⟩
  intro x hx
  simp only [chainSupport, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨.rcfgPrefix "tick" .id (.var "Y"), rfl, by simp [recursiveVars, chainSupport]⟩
  · exact ⟨.var "Z", rfl, by simp [chainSupport]⟩
  · exact ⟨.deadlock, rfl, by simp⟩
  · exact ⟨.var "Irrelevant", rfl, by simp [chainSupport]⟩

private def chain := build chainEnv (.var "X") chainSupport chainFinite

#guard chain.entries == {"X"}
#guard chain.nodes == {"X", "Y", "Z"}
#guard chain.edges == {("X", "Y"), ("Y", "Z")}
#guard chain.sccs == {{"X"}, {"Y"}, {"Z"}}
#guard chain.cyclicSccs == ∅
#guard chain.condensationEdges == {({"X"}, {"Y"}), ({"Y"}, {"Z"})}

example : chain.Path "X" "Z" :=
  (Relation.ReflTransGen.single (r := chain.Edge) (a := "X") (b := "Y") (by decide)).tail (by decide)

example : ¬ ReachableVar chainEnv (.var "X") "Irrelevant" := by
  intro h
  exact (show "Irrelevant" ∉ chain.nodes by decide) ((mem_build_nodes chainFinite).mpr h)

example : ∃ q, Ground q ∧ DerivesNoAIP chainEnv (.var "X") q :=
  acyclic_unfolds_ground chainFinite ((cyclicSccs_eq_empty_iff chain).mp (by decide))

private def loopBody (guarded : Bool) : DyNetKAT :=
  if guarded then .rcfgPrefix "tick" .id (.var "X") else .var "X"

private def loopEnv (guarded : Bool) : RecEnv := RecEnv.empty.define "X" (loopBody guarded)

private theorem loopFinite (guarded : Bool) : FiniteSupport (loopEnv guarded) (.var "X") {"X"} := by
  refine ⟨by simp, ?_⟩
  intro x hx
  obtain rfl := Finset.mem_singleton.mp hx
  exact ⟨loopBody guarded, rfl, by cases guarded <;> simp [loopBody, recursiveVars]⟩

private def loop (guarded : Bool) :=
  build (loopEnv guarded) (.var "X") {"X"} (loopFinite guarded)

#guard (loop true).cyclicSccs == {{"X"}} && (loop false).cyclicSccs == {{"X"}}
#guard (loop true).condensationEdges == ∅ && (loop false).condensationEdges == ∅

example : TypedPaperGuarded (loopBody true) :=
  (typedPaperGuarded_iff_guardedOccurrences _).mpr trivial

example : ¬ WellFormed (loopEnv false) (.var "X") := by
  intro h
  exact not_guardedOccurrences_var "X"
    (h.reachable_guarded (loopEnv false) (.var "X") "X" (.var "X") (.direct (by simp)) rfl)

#print axioms DependencyGraph.build_edge_iff
#print axioms DependencyGraph.mem_build_nodes
#print axioms DependencyGraph.reachableVar_iff_entry_path
#print axioms DependencyGraph.path_iff_reachable_from_var
#print axioms DependencyGraph.scc_partition
#print axioms DependencyGraph.same_scc_iff
#print axioms DependencyGraph.cyclic_scc_iff_cycle
#print axioms DependencyGraph.condensation_acyclic
#print axioms DependencyGraph.dependency_decreases
#print axioms DependencyGraph.guarded_scc
#print axioms DependencyGraph.acyclic_unfolds_ground

-- The acyclic route needs no projection support or restriction classifiers.
private def noClosureAttempt {G : ProcessGraph} (_ : Unit) :
    Except DiscoveryFailure (ClosureCandidate G) := .error .resourceLimit

example : analyzeRecursive chainFinite .structural noClosureAttempt = .ground := rfl

example : ∃ q, Ground q ∧ DerivesNoAIP chainEnv (.var "X") q :=
  analyzeRecursive_ground (hs := chainFinite) (id := .structural) (attempt := noClosureAttempt) rfl


private theorem noRec : FiniteSupport RecEnv.empty .deadlock ∅ := ⟨by simp, by simp⟩

#guard (analyzeSource noRec (fun () => .unknown .unknown)).guarantee == .ground
#guard (analyzeSource chainFinite (fun () => .unknown .resourceLimit)).guarantee == .ground

private def loopChecks : RestrictionChecks := fun _ _ => false
private def loopGraph := toGraph (loopEnv true) (.var "X") _ (loopFinite true)

private theorem loopLabel :
    loopGraph.label (varNode "X") = .rcfgPrefix "tick" .id (.ref (varNode "X")) := by
  rw [loopGraph, toGraph_label_varNode (loopFinite true) (by simp)]
  rfl

private theorem loopSupported : ProjectionSupport loopGraph (fun _ => loopChecks)
    (fun i => i = varNode "X") := by
  constructor
  · rintro i rfl j hj
    simpa [loopLabel, gprocRefs] using hj
  · rintro i rfl
    rw [loopLabel]
    exact ⟨trivial, trivial⟩

private def loopResult (limit : Nat) :=
  analyzeCompiledSource (loopFinite true) loopChecks loopSupported ⟨by simp [toGProc, gprocRefs],
    trivial⟩ .structural ⟨limit, 2, 2⟩ (.allDepth none)

#guard (loopResult 1).guarantee == .finiteClosure 1
#guard (loopResult 0).guarantee == .unknown
#guard (loopResult 0).closureFailure == some .resourceLimit

#print axioms analyzeSource_acyclic
#print axioms analyzeCompiledSource
#print axioms AnalysisResult.groundModel

end DyNetKAT.DyNetKAT.DependencySCCTests
