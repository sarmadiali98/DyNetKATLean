import DyNetKAT

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.TraceSafetyTests

open DyNetKAT.NetKAT TraceSafety

private def tick : Letter := .rcfg "tick" .id
private def fault : Letter := .rcfg "fault" .id
private def alphabet := [tick, fault]

private def finite (term : DyNetKAT) (sorted : PaperSyntax true term)
    (closed : recursiveVars term = ∅) : Program true RecEnv.empty :=
  ⟨term, (paperAdmissible_iff ..).mpr ⟨sorted, fun _ reach => by
    cases reach with
    | direct mem => simp [closed] at mem
    | throughDefinition _ lookup _ => simp at lookup⟩⟩

private def oneTick := finite (.rcfgPrefix "tick" .id .deadlock) ⟨rfl, trivial⟩ (by rfl)

private theorem finite_support :
    FiniteSupport RecEnv.empty oneTick.term ∅ := by
  refine ⟨?_, ?_⟩
  · simp [oneTick, finite, recursiveVars]
  · simp

private def compiled : oneTick.Compiled := ⟨∅, finite_support⟩
private def noChecks : RestrictionChecks := fun _ _ => false
private theorem supported :
    ProjectionSupport compiled.graph (fun _ => noChecks) (fun _ => False) :=
  ⟨fun _ h => h.elim, fun _ h => h.elim⟩

private theorem valid : (compiled.initial noChecks).checked.Valid (fun _ => False) := by
  constructor
  · simp [compiled, Program.Compiled.initial, Program.Compiled.graph, toGraph,
      oneTick, finite, toGProc, gprocRefs]
  · trivial

#guard check compiled noChecks supported valid [[fault]]
#guard !(check compiled noChecks supported valid [[tick]])

example : Safe oneTick [[fault]] :=
  (check_correct compiled noChecks supported valid _).mp rfl

example : ¬ Safe oneTick [[tick]] := by
  intro h
  have contradicts := (check_correct compiled noChecks supported valid _).mpr h
  cases contradicts

-- A guarded recursive universal process over one reconfiguration letter.
private def loop := translate [tick] []
private def twoTicks := [tick, tick]

private theorem loop_ticks : loop.Trace (twoTicks.map Letter.action) :=
  (translate_trace_iff [tick] [] (by simp) _).mpr
    ⟨twoTicks, rfl, by simp [InAlphabet, twoTicks], by simp [Avoids]⟩

example : ¬ Safe loop [twoTicks] :=
  fun safe => safe _ (by simp) loop_ticks

example : ¬ SourceTrace (translationEnv [tick]) (.project 1 loop.term) (twoTicks.map Letter.action) := by
  rw [sourceTrace_project_iff]
  simp [twoTicks]

example : SourceTrace (translationEnv [tick]) (.project 2 loop.term) (twoTicks.map Letter.action) :=
  sourceTrace_project_iff.mpr ⟨loop_ticks, by decide⟩

private theorem loop_noFault : ¬ loop.Trace [fault.action] := by
  intro h
  obtain ⟨w, eq, inA, _⟩ := (translate_trace_iff [tick] [] (by simp) _).mp h
  have same : w = [fault] := (List.map_injective_iff.mpr Letter.action_injective) eq
  rw [same] at inA
  have mem := inA fault (by simp)
  simp [fault, tick] at mem

example : Safe loop [[fault]] := by
  apply (safe_iff_all_projections ..).mpr
  intro n bad mem h
  obtain rfl : bad = [fault] := by simpa using mem
  exact loop_noFault (sourceTrace_project_iff.mp h).1

example : EquationalSafety loop [tick, fault] [[fault]] := by
  apply (equationalSafety_iff_safe loop _ _ (by simp) ?_).mpr
  · intro bad mem h
    obtain rfl : bad = [fault] := by simpa using mem
    exact loop_noFault h
  · intro t h
    obtain ⟨w, word, inA, _⟩ := (translate_trace_iff [tick] [] (by simp) t).mp h
    refine ⟨w, word, fun a ha => ?_⟩
    have same : a = tick := by simpa using inA a ha
    simp [same]

private def sending := finite (.send "request" .id .deadlock) trivial rfl
private def blocked := finite (.restrict Set.univ sending.term) ⟨rfl, trivial⟩ rfl

example : sending.Trace [.send "request" .id] :=
  sourceTrace_cons_actionStep.mpr ⟨.deadlock, .cpol_send _ _ _ [] [], sourceTrace_nil ..⟩

example : ¬ blocked.Trace [.send "request" .id] := by
  change ¬ SourceTrace _ (.restrict Set.univ sending.term) [.send "request" .id]
  rw [sourceTrace_restrict_iff]
  simp [actionAllowed]

private def σ : CtxPkt := fun _ => .v0
private def packet : Letter := .packet σ (Packet.update σ .port .v1)

-- A mixed packet/reconfiguration word exercises the base-continuation sort.
example : (translate [packet, tick] [[tick]]).Trace [packet.action, tick.action] := by
  apply (translate_trace_iff _ _ (by simp) _).mpr
  refine ⟨[packet, tick], rfl, by simp [InAlphabet], ?_⟩
  simp [Avoids, List.cons_prefix_cons, packet, tick]

#guard (ExtendedRegexp.any.desugar alphabet).length == 2
#guard (ExtendedRegexp.except tick |>.desugar [tick, fault, packet]) == [[fault]]
#guard (ExtendedRegexp.repeat (.letter tick) 1).desugar alphabet == [twoTicks]
#guard (Regexp.concat (.union (.letter tick) (.letter fault)) (.letter tick)).hnf ==
  [twoTicks, [fault, tick]]

#print axioms sourceTrace_iff_packetLists
#print axioms Program.trace_iff_reaches_residual
#print axioms Program.Compiled.trace_iff
#print axioms Program.inLeft_trace
#print axioms trace_a16
#print axioms TraceDerives.sound
#print axioms TraceDerives.complete
#print axioms translate_trace_iff
#print axioms safe_iff_trace_inclusion
#print axioms safe_iff_project_maxLength
#print axioms Formula.equational_iff
#print axioms check_correct
#print axioms check_iff_equationalSafety

end DyNetKAT.DyNetKAT.TraceSafetyTests
