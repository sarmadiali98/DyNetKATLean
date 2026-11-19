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

-- Definition 17 uses one plus the stored count.
#guard (ExtendedRegexp.letter tick).desugar alphabet == [[tick]]
#guard (ExtendedRegexp.repeat (.letter tick) 0).desugar alphabet == [[tick]]
#guard (ExtendedRegexp.repeat (.letter tick) 2).desugar alphabet == [[tick, tick, tick]]
#guard ((Regexp.letter tick).repeatPositive 2).hnf == [[tick, tick, tick]]

-- Nested expressions elaborate when their action clauses are defined.
example : (PrintedRegexp.repeat
    (.concat (.action (.neg (.literal tick))) (.union .any (.action (.literal fault)))) 0
    |>.elaborate) =
    some (.repeat (.concat (.except tick) (.union .any (.letter fault))) 0) := rfl

example : (PrintedRegexp.union .any (.action (.neg (.neg (.literal tick))))).elaborate =
    none := rfl

#guard (ExtendedRegexp.except tick).desugar [tick, packet] == []
#guard (padded fault 0).desugar alphabet == [[fault]]
#guard (padded fault 1).desugar alphabet == [[tick, fault], [fault, fault]]
#guard (padded fault 2).desugar alphabet ==
  [[tick, tick, fault], [tick, fault, fault], [fault, tick, fault], [fault, fault, fault]]

-- Padding expands to different core syntax with the same position-specific property.
private def explicitFirstPadding : Formula alphabet :=
  ⟨.union (.concat (.letter tick) (.letter fault)) (.concat (.letter fault) (.letter fault)),
    by simp [Regexp.Over, alphabet]⟩

example : EquationalSafety oneTick alphabet ((padded fault 1).desugar alphabet) ↔
    EquationalSafety oneTick alphabet explicitFirstPadding.val.hnf := Iff.rfl

private theorem loop_uses_alphabet : UsesAlphabet loop alphabet := by
  intro actions run
  obtain ⟨w, eq, inA, _⟩ := (translate_trace_iff [tick] [] (by simp) _).mp run
  refine ⟨w, eq, fun a mem => ?_⟩
  have same : a = tick := by simpa using inA a mem
  simp [alphabet, same]

example : ∀ n, EquationalSafety loop alphabet ((padded fault n).desugar alphabet) := by
  apply (eq28_iff_no_occurrence loop alphabet loop_uses_alphabet fault).mpr
  intro actions run occurs
  obtain ⟨w, rfl, inA, _⟩ := (translate_trace_iff [tick] [] (by simp) _).mp run
  obtain ⟨a, mem, equalAction⟩ := List.mem_map.mp occurs
  have eqTick : a = tick := by simpa using inA a mem
  have eqFault := Letter.action_injective equalAction
  simp [eqTick, tick, fault] at eqFault

-- The first position is safe, but the next position violates safety.
private def delayed := finite (.rcfgPrefix "tick" .id (.rcfgPrefix "fault" .id .deadlock))
  ⟨rfl, rfl, trivial⟩ rfl

example : Safe delayed ((padded fault 0).desugar alphabet) := by
  rw [safe_padded_iff]
  intro u len _ run
  have empty := List.length_eq_zero_iff.mp len
  subst u
  obtain ⟨_, step, _⟩ := sourceTrace_cons_actionStep.mp run
  have action := (rcfgPrefix_step_inv _ _ _ _ _ _ _ _ _ _ step).1
  simp [fault, Letter.action] at action

example : ¬ Safe delayed ((padded fault 1).desugar alphabet) := by
  intro safe
  apply (safe_padded_iff delayed alphabet fault 1).mp safe [tick] rfl (by simp [InAlphabet, alphabet])
  exact sourceTrace_cons_actionStep.mpr ⟨_, .cpol_rcfg _ _ _ [] [],
    sourceTrace_cons_actionStep.mpr ⟨_, .cpol_rcfg _ _ _ [] [], sourceTrace_nil ..⟩⟩

private def positiveTick : Formula alphabet := ⟨.letter tick, by simp [Regexp.Over, alphabet]⟩
private def positiveEither : Formula alphabet :=
  ⟨.union (.letter tick) (.letter fault), by simp [Regexp.Over, alphabet]⟩

#guard checkPositive compiled noChecks supported valid positiveTick
#guard !(checkPositive compiled noChecks supported valid positiveEither)

example : PositiveAbsorption oneTick positiveTick :=
  (checkPositive_correct compiled noChecks supported valid positiveTick).mp rfl

example : ¬ PositiveAbsorption oneTick positiveEither := by
  intro h
  have verdict := (checkPositive_correct compiled noChecks supported valid positiveEither).mpr h
  cases verdict

#print axioms ExtendedRegexp.desugar_correct
#print axioms Regexp.matches_repeatPositive
#print axioms ExtendedRegexp.equational_iff_core
#print axioms padded_exists_coreFormula
#print axioms mem_padded
#print axioms safe_padded_iff_project
#print axioms padded_equational_iff
#print axioms eq28_iff_no_occurrence

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
