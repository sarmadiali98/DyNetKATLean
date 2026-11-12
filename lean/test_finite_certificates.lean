import DyNetKAT

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

end DyNetKAT.DyNetKAT.FiniteCertificateTests
