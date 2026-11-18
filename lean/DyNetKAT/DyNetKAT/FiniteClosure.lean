import DyNetKAT.DyNetKAT.GraphNormalization
import DyNetKAT.DyNetKAT.FiniteProjection
import DyNetKAT.DyNetKAT.DependencySCC

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

open DyNetKAT.NetKAT

/-- A partial identity test. False gives no evidence of inequality. -/
structure ConcreteIdentity where
  same : GProc → GProc → Bool
  sound : ∀ {p q}, same p q = true → p = q

def ConcreteIdentity.structural : ConcreteIdentity :=
  ⟨sameProcess, sameProcess_sound⟩

def MoveLabel.enabled : MoveLabel → Bool
  | .visible l => l.enabled
  | .recv .. | .send .. => true

theorem MoveLabel.Realizes.enabled {l pt hl a pt' hl'}
    (h : MoveLabel.Realizes l pt hl a pt' hl') : l.enabled = true := by
  cases l with
  | visible k => exact realizes_enabled h
  | recv | send => rfl

def ConcreteStep (G : ProcessGraph) (p q : GProc) : Prop :=
  ∃ pt hl a pt' hl', GStep G ⟨p, pt, hl⟩ a ⟨q, pt', hl'⟩

/-- A row uses the same exactness contract as projection, after discarding
packet labels with no SOS instance. The residual classifiers are needed only
when computing further rows. -/
structure ConcreteRow (G : ProcessGraph) where
  proc : GProc
  moves : List SymbolicMove
  exactRow : MovesExact G proc moves

namespace ConcreteRow

def load {G : ProcessGraph} {bodyChecks : NodeId → RestrictionChecks}
    {live : NodeId → Prop} (support : ProjectionSupport G bodyChecks live)
    (p : {p : CheckedResidual // p.Valid live}) :
    Option (ConcreteRow G × List {q : CheckedResidual // q.Valid live}) := do
  match he : checkedMoves G bodyChecks p.val with
  | none => none
  | some row =>
    let spec := checkedMoves_spec support p.property he
    let enabled := row.attach.filter fun m => m.val.1.enabled
    have memEnabled (l : MoveLabel) (q : GProc) :
        (l, q) ∈ enabled.map (CheckedMove.erase ∘ Subtype.val) ↔
          (l, q) ∈ row.map CheckedMove.erase ∧ l.enabled = true := by
      simp only [enabled, List.mem_map, List.mem_filter, List.mem_attach, true_and,
        Function.comp_apply, Subtype.exists]
      constructor
      · rintro ⟨m, hm, hen, he⟩
        have eq : m.1 = l := congrArg Prod.fst he
        exact ⟨⟨m, hm, he⟩, eq ▸ hen⟩
      · rintro ⟨⟨m, hm, he⟩, hen⟩
        have eq : m.1 = l := congrArg Prod.fst he
        exact ⟨m, hm, eq.symm ▸ hen, he⟩
    return (⟨p.val.proc, enabled.map (CheckedMove.erase ∘ Subtype.val), by
      intro pt hl a q pt' hl'
      rw [spec.1 pt hl a q pt' hl']
      constructor
      · rintro ⟨l, hm, hr⟩
        exact ⟨l, (memEnabled l q).mpr ⟨hm, hr.enabled⟩, hr⟩
      · rintro ⟨l, hm, hr⟩
        exact ⟨l, ((memEnabled l q).mp hm).1, hr⟩⟩,
      enabled.map fun m => ⟨m.val.2, spec.2 _ m.property⟩)

end ConcreteRow

abbrev ClosureCandidate (G : ProcessGraph) := List (ConcreteRow G)

def ClosureCandidate.Represents {G : ProcessGraph} (rows : ClosureCandidate G) (p : GProc) :
    Prop := ∃ r ∈ rows, r.proc = p

def ClosureCandidate.contains {G : ProcessGraph} (rows : ClosureCandidate G)
    (id : ConcreteIdentity) (p : GProc) : Bool :=
  rows.any fun r => id.same p r.proc

theorem ClosureCandidate.contains_sound {G : ProcessGraph} {rows : ClosureCandidate G}
    {id : ConcreteIdentity} {p : GProc} (h : rows.contains id p = true) :
    rows.Represents p := by
  obtain ⟨r, hr, he⟩ := List.any_eq_true.mp h
  exact ⟨r, hr, (id.sound he).symm⟩

structure ValidClosure {G : ProcessGraph} (root : GProc) (rows : ClosureCandidate G) : Prop where
  root_mem : rows.Represents root
  closed : ∀ {p q}, rows.Represents p → ConcreteStep G p q → rows.Represents q

def checkClosure {G : ProcessGraph} (id : ConcreteIdentity) (root : GProc)
    (rows : ClosureCandidate G) : Bool :=
  rows.contains id root &&
    rows.all fun r => r.moves.all fun m => rows.contains id m.2

theorem checkClosure_sound {G : ProcessGraph} {id : ConcreteIdentity} {root : GProc}
    {rows : ClosureCandidate G} (h : checkClosure id root rows = true) :
    ValidClosure root rows := by
  obtain ⟨hroot, hrows⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨ClosureCandidate.contains_sound hroot, ?_⟩
  rintro _ q ⟨r, hr, rfl⟩ ⟨pt, hl, a, pt', hl', hs⟩
  obtain ⟨l, hm, _⟩ := (r.exactRow pt hl a q pt' hl').mp hs
  exact ClosureCandidate.contains_sound
    (List.all_eq_true.mp (List.all_eq_true.mp hrows r hr) (l, q) hm)

theorem ValidClosure.allReachable {G : ProcessGraph} {root : GProc} {rows : ClosureCandidate G}
    (h : ValidClosure root rows) {q : GProc}
    (reach : Relation.ReflTransGen (ConcreteStep G) root q) : rows.Represents q := by
  induction reach with
  | refl => exact h.root_mem
  | tail _ step ih => exact h.closed ih step

theorem ClosureCandidate.finite {G : ProcessGraph} (rows : ClosureCandidate G) :
    {p | rows.Represents p}.Finite := by
  classical
  apply ((rows.map ConcreteRow.proc).toFinset.finite_toSet).subset
  rintro p ⟨r, hr, rfl⟩
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨r, hr, rfl⟩)

theorem ValidClosure.reachableFinite {G : ProcessGraph} {root : GProc}
    {rows : ClosureCandidate G} (h : ValidClosure root rows) :
    {q | Relation.ReflTransGen (ConcreteStep G) root q}.Finite :=
  rows.finite.subset fun _ reach => h.allReachable reach

theorem ValidClosure.liftProperty {G : ProcessGraph} {root : GProc} {rows : ClosureCandidate G}
    (h : ValidClosure root rows) {Safe : GProc → Prop}
    (safe : ∀ p, rows.Represents p → Safe p) {q : GProc}
    (reach : Relation.ReflTransGen (ConcreteStep G) root q) : Safe q :=
  safe q (h.allReachable reach)

theorem GSteps.concreteReachable {G : ProcessGraph} {c d : GConfig} {acts : List Action}
    (h : GSteps G c acts d) : Relation.ReflTransGen (ConcreteStep G) c.proc d.proc := by
  induction h with
  | nil => exact .refl
  | cons _ _ _ a _ step _ ih => exact (Relation.ReflTransGen.single (r := ConcreteStep G) ⟨_, _, a, _, _, step⟩).trans ih

theorem ValidClosure.coversSource {G : ProcessGraph} {env : RecEnv} {root : GProc}
    {rows : ClosureCandidate G} {c d : Config} {acts : List Action}
    (h : ValidClosure root rows) (corr : Corr G env c.proc root) (steps : Steps env c acts d) :
    ∃ q, rows.Represents q ∧ Corr G env d.proc q := by
  obtain ⟨q, hsteps, hc⟩ := steps_to_gsteps G env c d acts steps root corr
  exact ⟨q, h.allReachable hsteps.concreteReachable, hc⟩

structure ClosureLimits where
  states : Nat
  transitions : Nat
  iterations : Nat
  deriving Repr

inductive DiscoveryFailure where
  | resourceLimit
  | cannotIdentifyState
  | unknown
  deriving DecidableEq, Repr

private def enqueue {live : NodeId → Prop} (id : ConcreteIdentity) (maxStates : Nat)
    (targets seen pending : List {p : CheckedResidual // p.Valid live}) :
    Except DiscoveryFailure (List {p : CheckedResidual // p.Valid live} ×
      List {p : CheckedResidual // p.Valid live}) := do
  match targets with
  | [] => return (seen, pending)
  | q :: rest =>
    if seen.any (fun p => id.same q.val.proc p.val.proc) then
      enqueue id maxStates rest seen pending
    else if !id.same q.val.proc q.val.proc then
      throw .cannotIdentifyState
    else if seen.length ≥ maxStates then
      throw .resourceLimit
    else
      enqueue id maxStates rest (q :: seen) (pending ++ [q])

private def explore {G : ProcessGraph} {bodyChecks : NodeId → RestrictionChecks}
    {live : NodeId → Prop} (support : ProjectionSupport G bodyChecks live)
    (id : ConcreteIdentity) (maxStates : Nat) :
    Nat → Nat → List {p : CheckedResidual // p.Valid live} →
    List {p : CheckedResidual // p.Valid live} → ClosureCandidate G →
    Except DiscoveryFailure (ClosureCandidate G)
  | _, _, [], _, rows => .ok rows.reverse
  | 0, _, _ :: _, _, _ => .error .resourceLimit
  | fuel + 1, transitions, p :: pending, seen, rows => do
    let some (row, targets) := ConcreteRow.load support p | throw .unknown
    if row.moves.length > transitions then throw .resourceLimit
    let (seen, pending) ← enqueue id maxStates targets seen pending
    explore support id maxStates fuel (transitions - row.moves.length) pending seen (row :: rows)

def discoverClosure {G : ProcessGraph} {bodyChecks : NodeId → RestrictionChecks}
    {live : NodeId → Prop} (support : ProjectionSupport G bodyChecks live)
    (id : ConcreteIdentity) (limits : ClosureLimits)
    (root : CheckedResidual) (valid : root.Valid live) :
    Except DiscoveryFailure (ClosureCandidate G) :=
  if limits.states = 0 then .error .resourceLimit
  else if !id.same root.proc root.proc then .error .cannotIdentifyState
  else
    match explore support id limits.states limits.iterations limits.transitions
        [⟨root, valid⟩] [⟨root, valid⟩] [] with
    | .error e => .error e
    | .ok rows => if checkClosure id root.proc rows then .ok rows else .error .unknown

theorem discoverClosure_sound {G : ProcessGraph} {bodyChecks : NodeId → RestrictionChecks}
    {live : NodeId → Prop} {support : ProjectionSupport G bodyChecks live}
    {id limits root valid rows}
    (h : discoverClosure support id limits root valid = .ok rows) :
    ValidClosure (G := G) root.proc rows := by
  unfold discoverClosure at h
  split at h
  · cases h
  split at h
  · cases h
  cases he : explore support id limits.states limits.iterations limits.transitions
      [⟨root, valid⟩] [⟨root, valid⟩] [] with
  | error e => rw [he] at h
               cases h
  | ok candidate =>
    rw [he] at h
    by_cases hc : checkClosure id root.proc candidate = true
    · simp [hc] at h
      subst rows
      exact checkClosure_sound hc
    · simp [hc] at h

/-- Route selection leaves semantic evidence in the corresponding theorems.
The fallback has the same preconditions as exact finite projection. -/
inductive RecursiveAnalysis (G : ProcessGraph) where
  | ground
  | finiteClosure (rows : ClosureCandidate G)
  | projection (reason : DiscoveryFailure)

def Internal.analyzeRecursive {env : RecEnv} {root : DyNetKAT} {S : Finset Var}
    (hs : FiniteSupport env root S) (id : ConcreteIdentity)
    (attempt : Unit → Except DiscoveryFailure (ClosureCandidate (toGraph env root S hs))) :
    RecursiveAnalysis (toGraph env root S hs) :=
  if (DependencyGraph.build env root S hs).cyclicSccs = ∅ then .ground
  else
    match attempt () with
    | .ok rows =>
      if checkClosure id (toGraph env root S hs).root rows then .finiteClosure rows
      else .projection .unknown
    | .error reason => .projection reason

theorem analyzeRecursive_ground {env root S hs id attempt}
    (h : Internal.analyzeRecursive (env := env) (root := root) (S := S) hs id attempt = .ground) :
    ∃ q, Ground q ∧ DerivesNoAIP env root q := by
  unfold Internal.analyzeRecursive at h
  split at h
  · exact DependencyGraph.acyclic_unfolds_ground hs
      ((DependencyGraph.cyclicSccs_eq_empty_iff _).mp (by assumption))
  · split at h
    · split at h <;> contradiction
    · contradiction

theorem analyzeRecursive_closure {env root S hs id attempt rows}
    (h : Internal.analyzeRecursive (env := env) (root := root) (S := S) hs id attempt =
        .finiteClosure rows) :
    ValidClosure (toGraph env root S hs).root rows := by
  unfold Internal.analyzeRecursive at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
        exact checkClosure_sound (by assumption)
      · contradiction
    · contradiction

end DyNetKAT.DyNetKAT
