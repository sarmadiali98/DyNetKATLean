import DyNetKAT

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.ReachabilityTests

open DyNetKAT.NetKAT

private def finite (term : DyNetKAT) (sorted : PaperSyntax true term)
    (closed : recursiveVars term = ∅) : Program true RecEnv.empty :=
  ⟨term, (paperAdmissible_iff ..).mpr ⟨sorted, fun _ reach => by
    cases reach with
    | direct mem => simp [closed] at mem
    | throughDefinition _ lookup _ => simp at lookup⟩⟩

private def compileClosed (p : Program true RecEnv.empty) (closed : recursiveVars p.term = ∅) :
    p.Compiled :=
  ⟨∅, ⟨by rw [closed], by simp⟩⟩

private def checks : RestrictionChecks := fun _ _ => false
private def blockChecks : RestrictionChecks := fun _ _ => true

private def enter := NetKAT.fieldTest .port .v0
private def exit := NetKAT.fieldTest .port .v1
private def packetFlow := NetKAT.assign1 (schema := ctxSchema) .port .v1
private def one := finite (.nSeq packetFlow .deadlock) trivial rfl
private def two := finite (.nSeq .id one.term) trivial rfl

private def start : ReconfigSet := {("start", .id)}
private def finish : ReconfigSet := {("finish", .id)}
private def nested := finite (.rcfgPrefix "start" .id (.rcfgPrefix "finish" .id two.term))
  ⟨rfl, rfl, trivial⟩ rfl

private def check (p : Program true RecEnv.empty) (closed : recursiveVars p.term = ∅)
    (cls : RestrictionChecks) (n : Nat) (stages : List ReconfigSet) : Option Bool :=
  projectedReachability (compileClosed p closed) cls (fun _ => checks) n stages enter exit

#guard check one rfl checks 1 [] == some true
#guard check two rfl checks 1 [] == some false
#guard check two rfl checks 2 [] == some true
#guard check nested rfl checks 4 [start, finish] == some true
#guard check nested rfl checks 3 [start, finish] == some false
#guard check nested rfl checks 4 [finish, start] == some false

private theorem nestedSupport :
    ProjectionSupport (compileClosed nested rfl).graph (fun _ => checks) (fun _ => False) :=
  ⟨fun _ h => h.elim, fun _ h => h.elim⟩

private theorem nestedValid : ((compileClosed nested rfl).initial checks).checked.Valid
    (fun _ => False) := by
  constructor
  · simp [compileClosed, Program.Compiled.initial, Program.Compiled.graph, toGraph,
      nested, two, one, finite, toGProc, gprocRefs]
  · trivial

example (verdict : check nested rfl checks 4 [start, finish] = some true) :
    EndpointReachable nested (some 4) [start, finish] enter exit :=
  (projectedReachability_correct (compileClosed nested rfl) checks nestedSupport nestedValid
    4 [start, finish] enter exit).mp verdict

example (verdict : check nested rfl checks 3 [start, finish] = some false) :
    ¬ EndpointReachable nested (some 3) [start, finish] enter exit := by
  intro reachable
  have yes := (projectedReachability_correct (compileClosed nested rfl) checks nestedSupport
    nestedValid 3 [start, finish] enter exit).mpr reachable
  change check nested rfl checks 3 [start, finish] = some true at yes
  rw [verdict] at yes
  cases yes

-- A syntactic head can see the second policy through an impossible first step.
private def impossible := finite (.nSeq .drop one.term) trivial rfl
#guard (head impossible.term).map (fun H => !netkatIsZero (reachabilityPolicy enter H exit)) == some true
#guard check impossible rfl checks 2 [] == some false

-- An active restriction blocks the only transition that could expose the continuation.
private def blocked := finite (.restrict Set.univ (.send "start" .id one.term))
  ⟨rfl, trivial⟩ rfl
#guard check blocked rfl blockChecks 3 [start] == some false

#print axioms GraphHeadSpec.iff_feasible
#print axioms graphTail_path_iff
#print axioms graphTail_feasible_iff
#print axioms graphTails_feasible_iff
#print axioms graphTails_head_iff
#print axioms graphTails_source_iff
#print axioms graphHead_source_iff
#print axioms compiledSafety_source_correct
#print axioms projectedReachability_correct
#print axioms normalizedReachability_correct
#print axioms TraceSafety.positiveAbsorption_iff_traces
#print axioms TraceSafety.checkPositive_correct

end DyNetKAT.DyNetKAT.ReachabilityTests
