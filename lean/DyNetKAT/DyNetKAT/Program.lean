import DyNetKAT.DyNetKAT.PaperDomain
import DyNetKAT.DyNetKAT.AnalysisStrategy
import DyNetKAT.DyNetKAT.SafetyCheck
import DyNetKAT.DyNetKAT.HeadNormalForm
import DyNetKAT.DyNetKAT.GroundCompleteness

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

/-- Eq. (1) when `extended = false`, printed Eq. (6) when it is true. -/
structure Program (extended : Bool) (env : RecEnv) where
  term : DyNetKAT
  admissible : PaperAdmissible extended env term

namespace Program

variable {extended : Bool} {env : RecEnv}

/-- A residual is indexed by its source program. Each edge is a paper SOS
step with packet lists, in the stateless sense used by bisimilarity. -/
structure Residual (program : Program extended env) where
  term : DyNetKAT
  reachable : Relation.ReflTransGen (ProcessStep env) program.term term

namespace Residual

variable {program : Program extended env}

theorem admissible (state : program.Residual) : PaperAdmissible extended env state.term :=
  program.admissible.reachable state.reachable

def advance (state : program.Residual) {d : Config} {a : Action} {pt hl : List DyNetKAT.NetKAT.CtxPkt}
    (step : Step env ⟨state.term, pt, hl⟩ a d) : program.Residual :=
  ⟨d.proc, state.reachable.tail ⟨pt, hl, a, d.pending, d.handled, step⟩⟩

theorem finite_targets (state : program.Residual) :
    {q | ProcessStep env state.term q}.Finite :=
  state.admissible.1.finite_targets

end Residual

def initial (program : Program extended env) : program.Residual :=
  ⟨program.term, .refl⟩

/-- Concrete execution with consistent packet lists also supplies a residual. -/
def afterTrace (program : Program extended env) {pt hl : List DyNetKAT.NetKAT.CtxPkt}
    {d : Config} {acts : List Action} (trace : Steps env ⟨program.term, pt, hl⟩ acts d) :
    program.Residual := ⟨d.proc, toReach trace .refl⟩
where
  toReach {c d : Config} {acts : List Action} (trace : Steps env c acts d)
      (initial : Relation.ReflTransGen (ProcessStep env) program.term c.proc) :
      Relation.ReflTransGen (ProcessStep env) program.term d.proc := by
    induction trace with
    | nil => exact initial
    | cons c next _ a _ step _ ih =>
      exact ih (initial.tail ⟨c.pending, c.handled, a, next.pending, next.handled, step⟩)

theorem approximation (p q : Program extended env) :
    Bisimilar env p.term q.term ↔ ∀ n, Bisimilar env (.project n p.term) (.project n q.term) :=
  approximation_induction_iff p.admissible.1.imageFiniteFrom q.admissible.1.imageFiniteFrom

theorem ground_complete (p q : Program extended env) (hp : Ground p.term) (hq : Ground q.term) :
    Derives env p.term q.term ↔ Bisimilar env p.term q.term :=
  ground_derives_iff_bisimilar hp hq

/-- Head normal forms are algebraic representations. The witness need not
be an SOS residual. -/
theorem normalizes (program : Program extended env) :
    ∃ q, IsDNKNormalForm q ∧ DerivesNoAIP env program.term q :=
  program.admissible.1.normalizes

/-- Finite support is a compiler requirement. Admissibility itself has no
finite-support requirement. The graph is derived from the admitted source. -/
structure Compiled (program : Program extended env) where
  names : Finset Var
  support : FiniteSupport env program.term names

namespace Compiled

variable {program : Program extended env}

def graph (compiled : program.Compiled) : ProcessGraph :=
  toGraph env program.term compiled.names compiled.support

theorem corr (compiled : program.Compiled) :
    Corr compiled.graph env program.term compiled.graph.root :=
  toGraph_corr env program.term compiled.names compiled.support

/-- Reachability in a compiled graph witnesses source SOS reachability. -/
theorem source_reachable (compiled : program.Compiled) {q : GProc}
    (reachable : Relation.ReflTransGen (ConcreteStep compiled.graph) compiled.graph.root q) :
    ∃ p : program.Residual, Corr compiled.graph env p.term q := by
  induction reachable with
  | refl => exact ⟨program.initial, compiled.corr⟩
  | tail _ edge ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨pt, hl, a, pt', hl', step⟩ := edge
    obtain ⟨target, hs, hc⟩ := gstep_to_step _ env _ _ a step p.term hp
    exact ⟨p.advance (d := ⟨target, pt', hl'⟩) hs, hc⟩

/-- A source residual and its graph representative, with executable
restriction checks attached to the graph syntax. -/
structure State (compiled : program.Compiled) where
  source : program.Residual
  checked : CheckedResidual
  corr : Corr compiled.graph env source.term checked.proc
  reachable : Relation.ReflTransGen (ConcreteStep compiled.graph) compiled.graph.root checked.proc

def initial (compiled : program.Compiled) (checks : RestrictionChecks) : compiled.State :=
  ⟨program.initial, ⟨compiled.graph.root, checks⟩, compiled.corr, .refl⟩

/-- Exact symbolic enumeration on a reachable compiled state. The proof
field is erased and makes row membership available to `successor`. -/
def State.moves {compiled : program.Compiled} (state : compiled.State)
    {bodyChecks live} (support : ProjectionSupport compiled.graph bodyChecks live)
    (valid : state.checked.Valid live) :
    { row : List CheckedMove //
      MovesExact compiled.graph state.checked.proc (row.map CheckedMove.erase) ∧
        ∀ move ∈ row, move.2.Valid live } :=
  match h : checkedMoves compiled.graph bodyChecks state.checked with
  | some row => ⟨row, checkedMoves_spec support valid h⟩
  | none => False.elim (by obtain ⟨row, hs⟩ := checkedMoves_exists support valid
                           rw [h] at hs
                           cases hs)

theorem State.moves_exact {compiled : program.Compiled} (state : compiled.State)
    {bodyChecks live} (support : ProjectionSupport compiled.graph bodyChecks live)
    (valid : state.checked.Valid live) :
    SourceMovesExact compiled.graph env state.source.term
      ((state.moves support valid).val.map CheckedMove.erase) :=
  (state.moves support valid).property.1.source_steps state.corr

/-- A realized symbolic move produces a reachable admissible residual.
Packet moves require a realization witness, since their NetKAT guard may
fail for the chosen packet. -/
theorem State.successor {compiled : program.Compiled} (state : compiled.State)
    {bodyChecks live} (support : ProjectionSupport compiled.graph bodyChecks live)
    (valid : state.checked.Valid live) {move : CheckedMove}
    (member : move ∈ (state.moves support valid).val)
    {pt hl a pt' hl'} (realizes : MoveLabel.Realizes move.1 pt hl a pt' hl') :
    ∃ target : compiled.State, target.checked = move.2 ∧
      Step env ⟨state.source.term, pt, hl⟩ a ⟨target.source.term, pt', hl'⟩ := by
  have graphStep := ((state.moves support valid).property.1 pt hl a move.2.proc pt' hl').2
    ⟨move.1, List.mem_map.mpr ⟨move, member, rfl⟩, realizes⟩
  obtain ⟨p, step, corr⟩ := gstep_to_step _ env _ _ a graphStep state.source.term state.corr
  exact ⟨⟨state.source.advance (d := ⟨p, pt', hl'⟩) step, move.2, corr,
    state.reachable.tail ⟨pt, hl, a, pt', hl', graphStep⟩⟩, rfl, step⟩

/-- Restrict a certificate's concrete side to SOS states reachable from
the analyzed root. Abstract table indices are model states. -/
private def reachableSimulation {n G root} {table : AbstractTable n}
    (cert : SimulationAbstraction G root table) : SimulationAbstraction G root table where
  represents i p := cert.represents i p ∧ Relation.ReflTransGen (ConcreteStep G) root p
  initial := ⟨cert.initial, .refl⟩
  forward := by
    intro i p q pt hl a pt' hl' hp step
    obtain ⟨j, edge, hq⟩ := cert.forward hp.1 step
    exact ⟨j, edge, hq, hp.2.tail ⟨pt, hl, a, pt', hl', step⟩⟩

private def reachableQuotient {n G root} {table : AbstractTable n}
    (cert : BisimulationQuotient G root table) : BisimulationQuotient G root table where
  toSimulationAbstraction := reachableSimulation cert.toSimulationAbstraction
  backward := by
    intro i j p pt hl a pt' hl' hp edge
    obtain ⟨q, step, hq⟩ := cert.backward hp.1 edge
    exact ⟨q, step, hq, hp.2.tail ⟨pt, hl, a, pt', hl', step⟩⟩

private def restrictModel {G : ProcessGraph} {root : GProc} :
    SuppliedModel G root → SuppliedModel G root
  | .simulation table cert => .simulation table (reachableSimulation cert)
  | .quotient table cert => .quotient table (reachableQuotient cert)

/-- Analyze a residual with source reachability and graph correspondence.
All internal discovery starts at the checked representative. -/
def State.analyze {compiled : program.Compiled} (state : compiled.State)
    {bodyChecks live} (support : ProjectionSupport compiled.graph bodyChecks live)
    (valid : state.checked.Valid live) (id : ConcreteIdentity) (limits : ClosureLimits)
    (request : AnalysisRequest) (model : Option (SuppliedModel compiled.graph state.checked.proc) := none) :
    AnalysisResult compiled.graph state.checked.proc env state.source.term :=
  Internal.analyzeResidual support valid state.corr id limits request (model.map restrictModel)

/-- Analyze an admitted source. Administrative unfolding can return an
algebraic model. That model is not used as a new source or residual. -/
def analyze (compiled : program.Compiled) (checks : RestrictionChecks)
    {bodyChecks live} (support : ProjectionSupport compiled.graph bodyChecks live)
    (valid : (compiled.initial checks).checked.Valid live)
    (id : ConcreteIdentity) (limits : ClosureLimits) (request : AnalysisRequest)
    (model : Option (SuppliedModel compiled.graph compiled.graph.root) := none) :
    AnalysisResult compiled.graph compiled.graph.root env program.term :=
  let run := fun () => (compiled.initial checks).analyze support valid id limits request model
  match request with
  | .bounded _ => run ()
  | _ => Internal.analyzeSource compiled.support run

/-- The original firewall query pipeline on an admitted source. Preprocessing
uses internal graph representations of head and tail. -/
def safety (compiled : program.Compiled) (R : ReconfigSet)
    (ingress egress : DyNetKAT.NetKAT.NetKAT) : SafetyCheckResult :=
  Internal.safetyCheckRestrictedGraph compiled.graph R ingress egress

theorem safety_correct (compiled : program.Compiled) {Q : ProcessGraph}
    (preprocessed : preprocessGraph compiled.graph = some Q)
    (R : ReconfigSet) (ingress egress : DyNetKAT.NetKAT.NetKAT) :
    ((compiled.safety R ingress egress).initialCondition = .isZero true ↔
      ¬ flowVia ingress egress (GraphHeadSpec Q Q.root)) ∧
    ((compiled.safety R ingress egress).postReconfigurationCondition = .nonzero true ↔
      flowVia ingress egress (GraphTailSpec Q R Q.root)) := by
  obtain ⟨_, _, _, _, _, _, initial, post⟩ :=
    safetyCheckRestrictedGraph_correct (R := R) (ingress := ingress) (egress := egress)
      preprocessed
  exact ⟨initial, post⟩

/-- Check queries on the finite reachable derivative table of the source
under communication restriction. The normalized graph is a query model. -/
def normalizedSafety (compiled : program.Compiled) {n : Nat}
    (candidate : NormalizationCandidate n) (R : ReconfigSet)
    (ingress egress : DyNetKAT.NetKAT.NetKAT) : Except NormalizationError SafetyCheckResult :=
  Internal.normalizeAndSafetyCheckGraph compiled.graph candidate R ingress egress

theorem normalizedSafety_correct (compiled : program.Compiled)
    {n : Nat} {candidate : NormalizationCandidate n} {Q : ProcessGraph}
    (normalized : normalizeGraph compiled.graph candidate = .ok Q)
    (R : ReconfigSet) (ingress egress : DyNetKAT.NetKAT.NetKAT) :
    (∀ i, ∃ p : program.Residual, Corr compiled.graph env p.term (candidate.state i)) ∧
      GraphBisimilarBetween compiled.graph Q (.restrict Set.univ compiled.graph.root) Q.root ∧
      ∃ result, compiled.normalizedSafety candidate R ingress egress = .ok result ∧
        (result.initialCondition = .isZero true ↔
          ¬ flowVia ingress egress (GraphHeadSpec Q Q.root)) ∧
        (result.postReconfigurationCondition = .nonzero true ↔
          flowVia ingress egress (GraphTailSpec Q R Q.root)) := by
  refine ⟨?_, normalizeAndSafetyCheckGraph_correct normalized R ingress egress⟩
  intro i
  have reachable := (normalizeGraph_correct normalized).1.reachable ⟨i, rfl⟩
  apply compiled.source_reachable
  exact reachable.mono (by
    rintro _ _ ⟨pt, hl, a, pt', hl', _, step⟩
    exact ⟨pt, hl, a, pt', hl', step⟩)

end Compiled

private def restrictEquivalence {p q : DyNetKAT} :
    SuppliedEquivalence env p q → SuppliedEquivalence env p q
  | .direct proof => .direct proof
  | .quotient cert corr target implements =>
    .quotient (Compiled.reachableQuotient cert) corr target implements

/-- Compare two independently admitted sources in a shared graph. The
correspondences certify the meaning of both graph entry points. -/
def equivalence (p q : Program extended env)
    {G : ProcessGraph} {left right : CheckedResidual} {bodyChecks live}
    (support : ProjectionSupport G bodyChecks live)
    (lv : left.Valid live) (rv : right.Valid live)
    (lc : Corr G env p.term left.proc) (rc : Corr G env q.term right.proc)
    (id : ConcreteIdentity) (limits : ClosureLimits) (maxPairs rounds : Nat)
    (mismatch : Option (Channel × DyNetKAT.NetKAT.NetKAT) := none)
    (supplied : Option (SuppliedEquivalence env p.term q.term) := none) :
    EquivalenceResult env p.term q.term :=
  Internal.analyzeEquivalence support lv rv lc rc id limits maxPairs rounds mismatch
    (supplied.map restrictEquivalence)

/-- Both operands must be reachable and share the same compiled graph. -/
def Compiled.State.equivalence {program : Program extended env} {compiled : program.Compiled} (left right : compiled.State)
    {bodyChecks live} (support : ProjectionSupport compiled.graph bodyChecks live)
    (lv : left.checked.Valid live) (rv : right.checked.Valid live)
    (id : ConcreteIdentity) (limits : ClosureLimits) (maxPairs rounds : Nat)
    (mismatch : Option (Channel × DyNetKAT.NetKAT.NetKAT) := none)
    (supplied : Option (SuppliedEquivalence env left.source.term right.source.term) := none) :
    EquivalenceResult env left.source.term right.source.term :=
  Internal.analyzeEquivalence support lv rv left.corr right.corr id limits maxPairs rounds mismatch
    (supplied.map restrictEquivalence)

end Program
end DyNetKAT.DyNetKAT
