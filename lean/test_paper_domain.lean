import DyNetKAT

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.PaperDomainTests

private def entry : DyNetKAT := .var "X"

private theorem oneEquation {body : DyNetKAT}
    (vars : recursiveVars body ⊆ {"X"}) (guarded : GuardedOccurrences body)
    (base : BaseSyntax body) :
    BaseAdmissible (RecEnv.empty.define "X" body) entry := by
  let env := RecEnv.empty.define "X" body
  have support : FiniteSupport env entry {"X"} := by
    refine ⟨by simp [entry], ?_⟩
    intro x hx
    obtain rfl := Finset.mem_singleton.mp hx
    exact ⟨body, rfl, vars⟩
  apply (baseAdmissible_iff env entry).2
  refine ⟨trivial, fun x hx => ?_⟩
  obtain rfl := Finset.mem_singleton.mp
    (reachableVars_subset_of_finiteSupport env entry _ support x hx)
  exact ⟨body, ⟨rfl, base, (typedPaperGuarded_iff_guardedOccurrences body).2 guarded⟩,
    fun _ other => RecEnv.lookup_unique other.1 rfl⟩

private theorem deadlockAdmissible : BaseAdmissible RecEnv.empty .deadlock :=
  (baseAdmissible_iff _ _).2 ⟨trivial, fun x hx => by
    have impossible : x ∈ (∅ : Finset Var) := by
      cases hx with
      | direct occurs => exact occurs
      | throughDefinition _ lookup _ => cases lookup
    simp at impossible⟩

private def loopBody : DyNetKAT := .send "a" .id entry
private def loopEnv := RecEnv.empty.define "X" loopBody

private theorem loopAdmissible : BaseAdmissible loopEnv entry :=
  oneEquation (by simp [loopBody, entry, recursiveVars]) trivial trivial

private def mutualX : DyNetKAT := .send "a" .id (.var "Y")
private def mutualY : DyNetKAT := .recv "b" .id entry
private def mutualEnv := (RecEnv.empty.define "X" mutualX).define "Y" mutualY

example : BaseAdmissible mutualEnv entry := by
  have support : FiniteSupport mutualEnv entry {"X", "Y"} := by
    refine ⟨by simp [entry], ?_⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨mutualX, rfl, by simp [mutualX, recursiveVars]⟩
    · exact ⟨mutualY, rfl, by simp [mutualY, entry, recursiveVars]⟩
  apply (baseAdmissible_iff _ _).2
  refine ⟨trivial, fun x hx => ?_⟩
  have mem := reachableVars_subset_of_finiteSupport mutualEnv entry _ support x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at mem
  rcases mem with rfl | rfl
  · exact ⟨mutualX, ⟨rfl, trivial, fun _ h => by cases h⟩,
      fun _ other => RecEnv.lookup_unique other.1 rfl⟩
  · exact ⟨mutualY, ⟨rfl, trivial, fun _ h => by cases h⟩,
      fun _ other => RecEnv.lookup_unique other.1 rfl⟩

private def unguardedBody : DyNetKAT :=
  .parallel (.send "a" .id .deadlock) entry

-- a.0 stands for a!1; ⊥. The parallel right branch has no prefix on its path.
example : BaseSyntax unguardedBody := ⟨trivial, trivial⟩

theorem rejects_unguarded_parallel :
    ¬ WellFormed (RecEnv.empty.define "X" unguardedBody) entry := by
  intro wf
  have guarded := wf.reachable_guarded _ _ "X" unguardedBody (.direct (by simp [entry])) rfl
  exact (typedPaperGuarded_iff_guardedOccurrences _).2 guarded "X" (.parallelRight .here)

example (wf : WellFormed loopEnv entry) : WellFormed loopEnv loopBody :=
  wf.body _ _ "X" loopBody (.direct (by simp [entry])) rfl

-- One derivation exercises lookup, choice, parallel synchronization, restriction
-- and projection. The residual exposes X outside a prefix.
private def compound : DyNetKAT :=
  .project 1 (.restrict Set.univ
    (.parallel (.choice entry .deadlock) (.recv "a" .id .deadlock)))

private def result : DyNetKAT :=
  .project 0 (.restrict Set.univ (.parallel entry .deadlock))

private theorem compoundStep : Step loopEnv ⟨compound, [], []⟩
    (.rcfg "a" .id) ⟨result, [], []⟩ := by
  apply Step.cpol_project
  apply Step.cpol_restrict
  · trivial
  apply Step.cpol_sync_send_recv
  · apply Step.cpol_choice_l
    exact .cpol_var _ _ _ _ _ _ _ _ rfl (.cpol_send _ _ _ _ _)
  · exact .cpol_recv _ _ _ _ _

example (source : PaperAdmissible true loopEnv compound) :
    PaperAdmissible true loopEnv result :=
  compoundStep.preserves_paperAdmissible source

-- The printed extended grammar requires an Eq. (1) packet continuation.
example : ¬ PaperSyntax true (.nSeq .id (.project 0 .deadlock)) := by
  simp [PaperSyntax]

example (wf : WellFormed loopEnv compound) : WellFormed loopEnv result :=
  compoundStep.preserves_wellFormed wf

example (wf : WellFormed loopEnv compound) : WellFormed loopEnv result :=
  (Steps.cons _ _ _ _ _ compoundStep (.nil _)).preserves_wellFormed wf

example : ¬ TypedPaperGuarded result :=
  fun guarded => guarded "X" (.project (.restrict (.parallelLeft .here)))

example : BaseAdmissible infEnv entry := by
  apply (baseAdmissible_iff _ _).2
  refine ⟨trivial, fun x _ => ?_⟩
  exact ⟨_, ⟨infEnv_lookup x, trivial, fun _ occ => by cases occ⟩,
    fun _ other => RecEnv.lookup_unique other.1 (infEnv_lookup x)⟩

-- Base-language growth also works with empty packet lists and a single equation.
private def growBody : DyNetKAT := .send "a" .id (.parallel entry .deadlock)
private def growEnv := RecEnv.empty.define "X" growBody

private def grow : Nat → DyNetKAT
  | 0 => entry
  | n + 1 => .parallel (grow n) .deadlock

private theorem grow_step (n : Nat) :
    Step growEnv ⟨grow n, [], []⟩ (.send "a" .id) ⟨grow (n + 1), [], []⟩ := by
  induction n with
  | zero => exact .cpol_var _ _ _ _ _ _ _ _ rfl (.cpol_send _ _ _ _ _)
  | succ n ih => exact .cpol_par_l _ _ _ _ _ _ _ _ ih

private theorem grow_injective : Function.Injective grow := by
  intro n
  induction n with
  | zero =>
    intro m eq
    cases m
    · rfl
    · cases eq
  | succ n ih =>
    intro m eq
    cases m with
    | zero => cases eq
    | succ m => exact congrArg Nat.succ (ih (DyNetKAT.parallel.inj eq).1)

theorem base_admissible_infinite_derivatives :
    {p | BaseAdmissible growEnv p ∧ ∃ actions,
      Steps growEnv ⟨entry, [], []⟩ actions ⟨p, [], []⟩}.Infinite := by
  apply (Set.infinite_range_of_injective grow_injective).mono
  rintro p ⟨n, rfl⟩
  have reach (start count : Nat) : ∃ actions,
      Steps growEnv ⟨grow start, [], []⟩ actions ⟨grow (start + count), [], []⟩ := by
    induction count generalizing start with
    | zero => exact ⟨[], .nil _⟩
    | succ count ih =>
      obtain ⟨actions, tail⟩ := ih (start + 1)
      rw [show start + 1 + count = start + (count + 1) by omega] at tail
      exact ⟨_ :: actions, .cons _ _ _ _ _ (grow_step start) tail⟩
  obtain ⟨actions, steps⟩ := reach 0 n
  rw [Nat.zero_add] at steps
  have source : BaseAdmissible growEnv entry :=
    oneEquation (by simp [growBody, entry, recursiveVars]) trivial ⟨trivial, trivial⟩
  exact ⟨steps.preserves_paperAdmissible source, actions, steps⟩

private def sourceLoop : Program false loopEnv := ⟨entry, loopAdmissible⟩

example : BaseAdmissible (RecEnv.empty.define "X" (.nSeq .id entry)) entry :=
  oneEquation (by simp [entry, recursiveVars]) trivial trivial

-- A reachable bare reference may be an entry or residual. The same
-- occurrence in a defining body cannot supply an admitted program.
example : ¬ ∃ p : Program false (RecEnv.empty.define "X" unguardedBody), p.term = entry := by
  rintro ⟨⟨_, admitted⟩, rfl⟩
  exact rejects_unguarded_parallel admitted.1

example : ¬ ∃ p : Program true (RecEnv.empty.define "X" (.var "X")), p.term = entry := by
  rintro ⟨⟨_, admitted⟩, rfl⟩
  exact (admitted.1.reachable_guarded _ _ "X" entry (.direct (by simp [entry])) rfl)

-- Finite support and an acyclic dependency graph cannot admit an
-- unguarded defining alias to the certified strategy.
example : ¬ ∃ p : Program false
    ((RecEnv.empty.define "Y" .deadlock).define "X" (.var "Y")), p.term = entry := by
  rintro ⟨⟨_, admitted⟩, rfl⟩
  exact (admitted.1.reachable_guarded _ _ "X" (.var "Y") (.direct (by simp [entry])) rfl)

example (p : Program false loopEnv) :
    ¬ ∃ r : p.Residual, r.term = .project 0 .deadlock := by
  rintro ⟨r, eq⟩
  have formed := r.admissible.2.1
  simp [eq, PaperSyntax] at formed

example (p : Program true RecEnv.empty) (h : p.term = .deadlock) :
    ¬ ∃ r : p.Residual, r.term = .restrict ∅ .deadlock := by
  rintro ⟨r, eq⟩
  have reachable := r.reachable
  rw [h, eq] at reachable
  cases reachable with
  | tail before step =>
    have onlyDeadlock : ∀ q, Relation.ReflTransGen (ProcessStep RecEnv.empty) .deadlock q →
        q = .deadlock := by
      intro q path
      induction path with
      | refl => rfl
      | tail _ edge ih =>
        obtain ⟨pt, hl, a, pt', hl', hs⟩ := edge
        rw [ih] at hs
        cases hs
    obtain ⟨pt, hl, a, pt', hl', hs⟩ := step
    rw [onlyDeadlock _ before] at hs
    cases hs

example {d : Config} {acts : List Action} (trace : Steps loopEnv ⟨entry, [], []⟩ acts d) :
    BaseAdmissible loopEnv (sourceLoop.afterTrace trace).term :=
  (sourceLoop.afterTrace trace).admissible

private theorem loopStep : Step loopEnv ⟨entry, [], []⟩ (.send "a" .id) ⟨entry, [], []⟩ :=
  .cpol_var _ _ _ _ _ _ _ _ rfl (.cpol_send _ _ _ _ _)

example : BaseAdmissible loopEnv
    (sourceLoop.initial.advance (d := ⟨entry, [], []⟩) loopStep).term :=
  (sourceLoop.initial.advance loopStep).admissible

example : BaseAdmissible loopEnv
    (sourceLoop.afterTrace (.cons _ _ _ _ _ loopStep (.cons _ _ _ _ _ loopStep (.nil _)))).term :=
  (sourceLoop.afterTrace (.cons _ _ _ _ _ loopStep (.cons _ _ _ _ _ loopStep (.nil _)))).admissible

private def groundProgram : Program false RecEnv.empty := ⟨.deadlock, deadlockAdmissible⟩
private def groundCompiled : groundProgram.Compiled := ⟨∅, by
  constructor
  · simp [groundProgram]
  · simp⟩

private def checks : RestrictionChecks := fun _ _ => false
private def groundSupport : ProjectionSupport groundCompiled.graph (fun _ => checks) (fun _ => False) :=
  ⟨by simp, by simp⟩

private def groundState := groundCompiled.initial checks
private theorem groundValid : groundState.checked.Valid (fun _ => False) :=
  ⟨by simp [groundState, Program.Compiled.initial, Program.Compiled.graph, groundCompiled,
    groundProgram, toGraph, toGProc, gprocRefs], trivial⟩

#guard (groundState.moves groundSupport groundValid).val.isEmpty
#guard (groundCompiled.analyze checks groundSupport groundValid .structural ⟨2, 4, 4⟩
  (.exactModel none)).guarantee == .ground
#guard (groundState.analyze groundSupport groundValid .structural ⟨2, 4, 4⟩
  (.bounded 1)).guarantee == .boundedProjection 1
#guard ((groundState.equivalence groundState groundSupport groundValid groundValid .structural
  ⟨2, 4, 4⟩ 8 8).proof?).isSome

#print axioms Program.Residual.admissible
#print axioms Program.Residual.advance
#print axioms Program.Residual.finite_targets
#print axioms Program.afterTrace
#print axioms Program.Compiled.source_reachable
#print axioms Program.Compiled.State.moves_exact
#print axioms Program.Compiled.State.successor
#print axioms Program.Compiled.analyze
#print axioms Program.equivalence
#print axioms Program.Compiled.safety_correct
#print axioms Program.Compiled.normalizedSafety_correct
#print axioms Program.normalizes
#print axioms Program.ground_complete
#print axioms Program.approximation
#print axioms wellFormed_iff_closedDefined_and_typedPaperGuarded
#print axioms paperAdmissible_iff
#print axioms baseAdmissible_iff
#print axioms Step.reachableVar_mono
#print axioms Step.preserves_wellFormed
#print axioms Step.preserves_paperAdmissible
#print axioms Steps.preserves_wellFormed
#print axioms Steps.preserves_paperAdmissible
#print axioms PaperAdmissible.reachable
#print axioms GSteps.preserves_paperAdmissible
#print axioms rejects_unguarded_parallel
#print axioms base_admissible_infinite_derivatives

end DyNetKAT.DyNetKAT.PaperDomainTests
