import DyNetKATLean.Core.RecEnv

namespace DyNetKAT.DyNetKAT

open DyNetKAT.NetKAT

variable {schema : PacketSchema}

/-- The recursive-variable names occurring directly in a process term. -/
def recursiveVars : DyNetKAT schema → Finset Var
  | .deadlock => ∅
  | .nSeq _ continuation => recursiveVars continuation
  | .recv _ _ continuation => recursiveVars continuation
  | .send _ _ continuation => recursiveVars continuation
  | .rcfgPrefix _ _ continuation => recursiveVars continuation
  | .parallel left right => recursiveVars left ∪ recursiveVars right
  | .choice left right => recursiveVars left ∪ recursiveVars right
  | .leftMerge left right => recursiveVars left ∪ recursiveVars right
  | .commMerge left right => recursiveVars left ∪ recursiveVars right
  | .restrict _ process => recursiveVars process
  | .project _ process => recursiveVars process
  | .var name => {name}

/-- Every recursive variable occurring directly in `process` has a definition
    in `env`.  This predicate does not inspect the bodies of those definitions. -/
def Defined (env : RecEnv schema) (process : DyNetKAT schema) : Prop :=
  ∀ name ∈ recursiveVars process, (env.lookup name).isSome

/-- A recursive variable is reachable from a process when it occurs directly,
    or occurs directly in the body of an already reachable variable. -/
inductive ReachableVar {schema : PacketSchema} (env : RecEnv schema) : DyNetKAT schema → Var → Prop
  | direct {process : (DyNetKAT schema)} {name : Var} :
      name ∈ recursiveVars process → ReachableVar env process name
  | throughDefinition {process : (DyNetKAT schema)} {source target : Var} {body : (DyNetKAT schema)} :
      ReachableVar env process source → env.lookup source = some body →
      target ∈ recursiveVars body → ReachableVar env process target

/-- Every recursively reachable variable has a definition in `env`. -/
def ClosedDefined (env : RecEnv schema) (process : DyNetKAT schema) : Prop :=
  ∀ name, ReachableVar env process name → (env.lookup name).isSome

theorem reachableVar_direct (env : RecEnv schema) (process : DyNetKAT schema) (name : Var)
    (occurs : name ∈ recursiveVars process) :
    ReachableVar env process name :=
  .direct occurs

theorem reachableVar_through_definition (env : RecEnv schema) (process : DyNetKAT schema)
    (source target : Var) (body : DyNetKAT schema)
    (source_reachable : ReachableVar env process source)
    (definition : env.lookup source = some body)
    (occurs : target ∈ recursiveVars body) :
    ReachableVar env process target :=
  .throughDefinition source_reachable definition occurs

theorem ClosedDefined.defined (env : RecEnv schema) (process : DyNetKAT schema)
    (closed : ClosedDefined env process) :
    Defined env process := by
  intro name occurs
  exact closed name (.direct occurs)

theorem ReachableVar.body (env : RecEnv schema) (process : DyNetKAT schema) (source target : Var)
    (body : DyNetKAT schema) (source_reachable : ReachableVar env process source)
    (definition : env.lookup source = some body)
    (occurs : target ∈ recursiveVars body) :
    ReachableVar env process target := by
  exact .throughDefinition source_reachable definition occurs

theorem reachableVar_of_reachable_body (env : RecEnv schema) (process : DyNetKAT schema)
    (source : Var) (body : DyNetKAT schema)
    (source_reachable : ReachableVar env process source)
    (definition : env.lookup source = some body) (target : Var)
    (target_reachable : ReachableVar env body target) :
    ReachableVar env process target := by
  induction target_reachable with
  | direct occurs =>
      exact .throughDefinition source_reachable definition occurs
  | throughDefinition source_reachable' definition' occurs' ih =>
      exact .throughDefinition ih definition' occurs'

@[simp] theorem recursiveVars_deadlock :
    recursiveVars (.deadlock : DyNetKAT schema) = ∅ := rfl

@[simp] theorem recursiveVars_var (name : Var) :
    recursiveVars (.var name : DyNetKAT schema) = {name} := rfl

@[simp] theorem recursiveVars_choice (left right : DyNetKAT schema) :
    recursiveVars (.choice left right) = recursiveVars left ∪ recursiveVars right := rfl

/-- All recursive-variable occurrences in a process are guarded according to
    Definition 7.  A NetKAT sequencing, communication, or reconfiguration
    prefix guards every occurrence in its continuation.  The remaining
    operators only contain subexpressions and therefore preserve guardedness
    exactly when all of their process arguments are guarded. -/
def GuardedOccurrences : DyNetKAT schema → Prop
  | .deadlock => True
  | .nSeq _ _ => True
  | .recv _ _ _ => True
  | .send _ _ _ => True
  | .rcfgPrefix _ _ _ => True
  | .parallel left right => GuardedOccurrences left ∧ GuardedOccurrences right
  | .choice left right => GuardedOccurrences left ∧ GuardedOccurrences right
  | .leftMerge left right => GuardedOccurrences left ∧ GuardedOccurrences right
  | .commMerge left right => GuardedOccurrences left ∧ GuardedOccurrences right
  | .restrict _ process => GuardedOccurrences process
  | .project _ process => GuardedOccurrences process
  | .var _ => False

/-- Name used by the guarded-recursion specification in the paper. -/
abbrev IsGuarded := @GuardedOccurrences schema

@[simp] theorem guardedOccurrences_deadlock :
    GuardedOccurrences (.deadlock : DyNetKAT schema) := by
  trivial

theorem guardedOccurrences_deadlock_iff :
    GuardedOccurrences (.deadlock : DyNetKAT schema) ↔ True := by
  rfl

@[simp] theorem not_guardedOccurrences_var (name : Var) :
    ¬ GuardedOccurrences (.var name : DyNetKAT schema) := by
  simp [GuardedOccurrences]

theorem guardedOccurrences_var_iff (name : Var) :
    GuardedOccurrences (.var name : DyNetKAT schema) ↔ False := by
  rfl

@[simp] theorem guardedOccurrences_choice_iff (left right : DyNetKAT schema) :
    GuardedOccurrences (.choice left right) ↔
      GuardedOccurrences left ∧ GuardedOccurrences right := by
  rfl

@[simp] theorem guardedOccurrences_nSeq
    (policy : NetKAT schema) (continuation : DyNetKAT schema) :
    GuardedOccurrences (.nSeq policy continuation) := by
  trivial

theorem guardedOccurrences_nSeq_iff
    (policy : NetKAT schema) (continuation : DyNetKAT schema) :
    GuardedOccurrences (.nSeq policy continuation) ↔ True := by
  rfl

/-/ A recursive specification is well formed when every recursively reachable
    variable is defined and its defining body is guarded. -/
def WellFormed (env : RecEnv schema) (process : DyNetKAT schema) : Prop :=
  ClosedDefined env process ∧
    ∀ name, ReachableVar env process name →
      ∃ body, env.lookup name = some body ∧ GuardedOccurrences body

theorem WellFormed.closedDefined (env : RecEnv schema) (process : DyNetKAT schema)
    (well_formed : WellFormed env process) :
    ClosedDefined env process :=
  well_formed.1

theorem WellFormed.reachable_definition (env : RecEnv schema) (process : DyNetKAT schema)
    (well_formed : WellFormed env process) (name : Var)
    (reachable : ReachableVar env process name) :
    ∃ body, env.lookup name = some body := by
  rcases well_formed.2 name reachable with ⟨body, definition, _⟩
  exact ⟨body, definition⟩

theorem WellFormed.reachable_guarded (env : RecEnv schema) (process : DyNetKAT schema)
    (well_formed : WellFormed env process) (name : Var) (body : DyNetKAT schema)
    (reachable : ReachableVar env process name)
    (definition : env.lookup name = some body) :
    GuardedOccurrences body := by
  rcases well_formed.2 name reachable with ⟨defined_body, defined, guarded⟩
  have same_body : defined_body = body := by
    exact (Option.some.inj (definition.symm.trans defined)).symm
  simpa [same_body] using guarded

theorem WellFormed.body (env : RecEnv schema) (process : DyNetKAT schema) (source : Var)
    (body : DyNetKAT schema) (well_formed : WellFormed env process)
    (source_reachable : ReachableVar env process source)
    (definition : env.lookup source = some body) :
    WellFormed env body := by
  have reachable_from_process : ∀ target,
      ReachableVar env body target → ReachableVar env process target := by
    intro target target_reachable
    exact reachableVar_of_reachable_body env process source body source_reachable
      definition target target_reachable
  constructor
  · intro target target_reachable
    exact well_formed.1 target (reachable_from_process target target_reachable)
  · intro target target_reachable
    exact well_formed.2 target (reachable_from_process target target_reachable)

theorem wellFormed_var_iff (env : RecEnv schema) (name : Var) :
    WellFormed env (.var name) ↔
      (∃ body, env.lookup name = some body ∧ GuardedOccurrences body) ∧
      (∀ target, target ≠ name →
        ReachableVar env (.var name) target →
          ∃ body, env.lookup target = some body ∧ GuardedOccurrences body) := by
  constructor
  · intro well_formed
    have root_reachable : ReachableVar env (.var name) name :=
      .direct (by simp)
    obtain ⟨body, definition, guarded⟩ := well_formed.2 name root_reachable
    constructor
    · exact ⟨body, definition, guarded⟩
    · intro target different reachable
      obtain ⟨body, definition, guarded⟩ :=
        well_formed.2 target reachable
      exact ⟨body, definition, guarded⟩
  · rintro ⟨⟨root_body, root_definition, root_guarded⟩, other⟩
    constructor
    · intro target reachable
      obtain rfl | different := eq_or_ne target name
      · simpa [root_definition] using (show (env.lookup name).isSome from by
          simp [root_definition])
      · obtain ⟨body, definition, _⟩ := other target different reachable
        simpa [definition]
    · intro target reachable
      obtain rfl | different := eq_or_ne target name
      · exact ⟨root_body, root_definition, root_guarded⟩
      · exact other target different reachable

end DyNetKAT.DyNetKAT
