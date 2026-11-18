import DyNetKAT.DyNetKAT.FiniteAbstraction
import DyNetKAT.DyNetKAT.FiniteBisimulation
import DyNetKAT.DyNetKAT.MemoProjection

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

inductive AnalysisGuarantee where
  | ground
  | boundedProjection (depth : Nat)
  | finiteClosure (states : Nat)
  | simulationAbstraction (states : Nat)
  | strongQuotient (states : Nat)
  | finiteBisimulation (pairs : Nat)
  | directEquivalence
  | distinguishingWitness
  | unknown
  deriving DecidableEq, Repr

/-- Requests for a single root. Pairwise equivalence is a separate entry point. -/
inductive AnalysisRequest where
  | bounded (depth : Nat)
  | allDepth (fallback : Option Nat := none)
  | exactModel (fallback : Option Nat := none)

inductive SuppliedModel (G : ProcessGraph) (root : GProc) where
  | simulation {n} (table : AbstractTable n) (cert : SimulationAbstraction G root table)
  | quotient {n} (table : AbstractTable n) (cert : BisimulationQuotient G root table)

inductive AnalysisResult (G : ProcessGraph) (root : GProc) (env : RecEnv) (source : DyNetKAT) where
  | ground (proof : ∃ q, Ground q ∧ DerivesNoAIP env source q)
  | closure (rows : ClosureCandidate G) (proof : ValidClosure root rows)
  | simulation {n} (table : AbstractTable n) (cert : SimulationAbstraction G root table)
      (closureFailure : DiscoveryFailure)
  | quotient {n} (table : AbstractTable n) (cert : BisimulationQuotient G root table)
      (closureFailure : DiscoveryFailure)
  | bounded (depth : Nat) (term : DyNetKAT) (proof : Bisimilar env term (.project depth source))
      (closureFailure : Option DiscoveryFailure)
  | unknown (closureFailure : DiscoveryFailure)

def AnalysisResult.guarantee {G root env source} :
    AnalysisResult G root env source → AnalysisGuarantee
  | .ground _ => .ground
  | .closure rows _ => .finiteClosure rows.length
  | .simulation (n := n) .. => .simulationAbstraction n
  | .quotient (n := n) .. => .strongQuotient n
  | .bounded depth .. => .boundedProjection depth
  | .unknown _ => .unknown

def AnalysisResult.closureFailure {G root env source} :
    AnalysisResult G root env source → Option DiscoveryFailure
  | .bounded _ _ _ reason => reason
  | .simulation _ _ reason | .quotient _ _ reason | .unknown reason => some reason
  | _ => none

/-- A property verdict distinguishes a certified all-depth fact from the
available analysis model. Failure to discharge an invariant is inconclusive. -/
inductive StatePropertyVerdict (G : ProcessGraph) (root : GProc) (Safe : GProc → Prop) where
  | provedAllDepth (method : AnalysisGuarantee)
      (proof : ∀ p, Relation.ReflTransGen (ConcreteStep G) root p → Safe p)
  | unknown (available : AnalysisGuarantee) (closureFailure : Option DiscoveryFailure)

namespace AnalysisResult

/-- Extract an exact model for the requested depth only. -/
def projection? {G root env source} (depth : Nat) :
    AnalysisResult G root env source →
      Option {term : DyNetKAT // Bisimilar env term (.project depth source)}
  | .bounded n term sound _ =>
    if h : n = depth then some ⟨term, h ▸ sound⟩ else none
  | _ => none

theorem closureProperty {G root rows} (cert : ValidClosure (G := G) root rows)
    {Safe : GProc → Prop} (safe : ∀ p, rows.Represents p → Safe p) :
    ∀ p, Relation.ReflTransGen (ConcreteStep G) root p → Safe p :=
  fun _ reach => cert.liftProperty safe reach

theorem simulationProperty {G root n} {table : AbstractTable n}
    (cert : SimulationAbstraction G root table) {Inv : Fin n → Prop} {Safe : GProc → Prop}
    (inv : ∀ i, table.Reaches i → Inv i)
    (safe : ∀ i p, Inv i → cert.represents i p → Safe p) :
    ∀ p, Relation.ReflTransGen (ConcreteStep G) root p → Safe p :=
  fun _ reach => cert.liftProperty inv safe reach

theorem quotientModel {G root n env source} {table : AbstractTable n}
    (cert : BisimulationQuotient G root table) (corr : Corr G env source root) :
    ∃ R, IsBisimulation2 env table.environment R ∧ R source (table.process table.initial) :=
  cert.sourceModel corr table.environment_implements

theorem groundModel {env source : _}
    (proof : ∃ q, Ground q ∧ DerivesNoAIP env source q) :
    ∃ q, Ground q ∧ Bisimilar env source q := by
  obtain ⟨q, hg, hd⟩ := proof
  exact ⟨q, hg, hd.sound⟩

/-- The callbacks prove the requested property on the selected certificate.
An abstract callback may discharge an invariant via `simulationProperty`. -/
def proveStateProperty {G root env source} {Safe : GProc → Prop}
    (result : AnalysisResult G root env source)
    (concrete : ∀ rows : ClosureCandidate G, Option (PLift (∀ p, rows.Represents p → Safe p)))
    (abstract : ∀ {n} {table : AbstractTable n} (cert : SimulationAbstraction G root table),
      Option (PLift (∀ i p, table.Reaches i → cert.represents i p → Safe p))) :
    StatePropertyVerdict G root Safe :=
  let unknown := StatePropertyVerdict.unknown result.guarantee result.closureFailure
  match result with
  | .closure rows cert =>
    match concrete rows with
    | some h => .provedAllDepth result.guarantee (closureProperty cert h.down)
    | none => unknown
  | .simulation _ cert _ =>
    match abstract cert with
    | some h => .provedAllDepth result.guarantee (simulationProperty cert (fun _ h => h) h.down)
    | none => unknown
  | .quotient _ cert _ =>
    match abstract cert.toSimulationAbstraction with
    | some h => .provedAllDepth result.guarantee
        (simulationProperty cert.toSimulationAbstraction (fun _ h => h) h.down)
    | none => unknown
  | _ => unknown

end AnalysisResult

def Internal.boundedAnalysis {G env source bodyChecks live} {state : CheckedResidual}
    (support : ProjectionSupport G bodyChecks live) (valid : state.Valid live)
    (corr : Corr G env source state.proc) (depth : Nat) (reason : Option DiscoveryFailure := none) :
    AnalysisResult G state.proc env source :=
  .bounded depth (renderProjectionTotal support depth state valid)
    (renderProjection_bisimilar support valid corr
      (renderProjectionTotal_eq_some support depth state valid)) reason

/-- Run discovery for an already compiled residual. Explicit bounded requests
use projection directly. A simulation candidate serves only all-depth properties. -/
def Internal.analyzeResidual {G env source bodyChecks live} {state : CheckedResidual}
    (support : ProjectionSupport G bodyChecks live) (valid : state.Valid live)
    (corr : Corr G env source state.proc) (id : ConcreteIdentity) (limits : ClosureLimits)
    (request : AnalysisRequest) (model : Option (SuppliedModel G state.proc) := none) :
    AnalysisResult G state.proc env source :=
  match request with
  | .bounded depth => Internal.boundedAnalysis support valid corr depth
  | .allDepth depth | .exactModel depth =>
    match h : discoverClosure support id limits state valid with
    | .ok rows => .closure rows (discoverClosure_sound h)
    | .error reason =>
      match request, model with
      | _, some (.quotient table cert) => .quotient table cert reason
      | .allDepth _, some (.simulation table cert) => .simulation table cert reason
      | _, _ =>
        match depth with
        | some n => Internal.boundedAnalysis support valid corr n (some reason)
        | none => .unknown reason

/-- Check dependency metadata before evaluating a residual-analysis thunk.
The thunk can carry the guardedness and classifier evidence for cyclic analysis. -/
def Internal.analyzeSource {env root S} (hs : FiniteSupport env root S)
    (otherwise : Unit → AnalysisResult (toGraph env root S hs) (toGProc root) env root) :
    AnalysisResult (toGraph env root S hs) (toGProc root) env root :=
  if acyclic : (DependencyGraph.build env root S hs).cyclicSccs = ∅ then
    .ground (DependencyGraph.acyclic_unfolds_ground hs
      ((DependencyGraph.cyclicSccs_eq_empty_iff _).mp acyclic))
  else otherwise ()

theorem Internal.analyzeSource_acyclic {env root S} (hs : FiniteSupport env root S) {otherwise}
    (h : (DependencyGraph.build env root S hs).cyclicSccs = ∅) :
    (Internal.analyzeSource hs otherwise).guarantee = .ground := by
  simp [Internal.analyzeSource, h, AnalysisResult.guarantee]

def Internal.analyzeCompiledSource {env root S bodyChecks live} (hs : FiniteSupport env root S)
    (checks : RestrictionChecks)
    (support : ProjectionSupport (toGraph env root S hs) bodyChecks live)
    (valid : (CheckedResidual.mk (toGProc root) checks).Valid live)
    (id : ConcreteIdentity) (limits : ClosureLimits) (request : AnalysisRequest)
    (model : Option (SuppliedModel (toGraph env root S hs) (toGProc root)) := none) :
    AnalysisResult (toGraph env root S hs) (toGProc root) env root :=
  let run := fun () =>
    Internal.analyzeResidual support valid (toGraph_corr env root S hs) id limits request model
  match request with
  | .bounded _ => run ()
  | _ => Internal.analyzeSource hs run

/-- Pairwise equivalence has a distinct result type. In particular its
constructors cannot accept a bounded projection or a forward simulation. -/
inductive EquivalenceResult (env : RecEnv) (p q : DyNetKAT) where
  | finite {G gp gq} (pairs : BisimCandidate G) (cert : ValidBisimCertificate gp gq pairs)
      (left : Corr G env p gp) (right : Corr G env q gq)
  | quotient {G root n} {table : AbstractTable n} (cert : BisimulationQuotient G root table)
      (left : Corr G env p root) (right : q = table.process table.initial)
      (implements : table.Implements env)
  | direct (proof : Bisimilar env p q)
  | disproved (channel : Channel) (policy : DyNetKAT.NetKAT.NetKAT)
      (proof : ¬ Bisimilar env p q)
  | unknown (reason : DiscoveryFailure)

def EquivalenceResult.guarantee {env p q} : EquivalenceResult env p q → AnalysisGuarantee
  | .finite pairs .. => .finiteBisimulation pairs.length
  | .quotient (n := n) .. => .strongQuotient n
  | .direct _ => .directEquivalence
  | .disproved .. => .distinguishingWitness
  | .unknown _ => .unknown

def EquivalenceResult.proof? {env p q} : EquivalenceResult env p q → Option (PLift (Bisimilar env p q))
  | .finite _ cert hp hq => some ⟨cert.bisimilar hp hq⟩
  | .quotient cert hp hq hm => some ⟨hq.symm ▸ cert.bisimilar hp hm⟩
  | .direct h => some ⟨h⟩
  | .disproved .. | .unknown _ => none

/-- Exact evidence for a pair can be supplied if finite discovery is inconclusive. -/
inductive SuppliedEquivalence (env : RecEnv) (p q : DyNetKAT) where
  | direct (proof : Bisimilar env p q)
  | quotient {G root n} {table : AbstractTable n}
      (cert : BisimulationQuotient G root table)
      (left : Corr G env p root) (right : q = table.process table.initial)
      (implements : table.Implements env)

/-- Optional checked mismatch first, followed by finite concrete search.
If the search is inconclusive, use supplied exact evidence for the pair. -/
def Internal.analyzeEquivalence {G env p q bodyChecks live} {left right : CheckedResidual}
    (support : ProjectionSupport G bodyChecks live)
    (lv : left.Valid live) (rv : right.Valid live)
    (lc : Corr G env p left.proc) (rc : Corr G env q right.proc)
    (id : ConcreteIdentity) (limits : ClosureLimits) (maxPairs rounds : Nat)
    (mismatch : Option (Channel × DyNetKAT.NetKAT.NetKAT) := none)
    (supplied : Option (SuppliedEquivalence env p q) := none) :
    EquivalenceResult env p q := Id.run do
  if let some (channel, policy) := mismatch then
    if let some (l, _) := ConcreteRow.load support ⟨left, lv⟩ then
      if let some (r, _) := ConcreteRow.load support ⟨right, rv⟩ then
        -- The row loader carries exactness, and its process identity is checked below.
        if he : checkReconfigurationMismatch l r channel policy &&
            id.same l.proc left.proc && id.same r.proc right.proc then
          have ⟨⟨hm, hl⟩, hr⟩ := Bool.and_eq_true_iff.mp he |>.imp_left Bool.and_eq_true_iff.mp
          have hl' := id.sound hl
          have hr' := id.sound hr
          return .disproved channel policy (fun h => checkReconfigurationMismatch_sound hm
            (hl'.symm ▸ hr'.symm ▸ (gbisimilar_iff_bisimilar G env lc rc).mpr h))
  match h : discoverResidualBisimulation support id limits maxPairs rounds left right lv rv with
  | .ok pairs => return .finite pairs (discoverResidualBisimulation_sound h) lc rc
  | .error reason =>
    match supplied with
    | some (.direct proof) => return .direct proof
    | some (.quotient cert left right implements) => return .quotient cert left right implements
    | none => return .unknown reason

end DyNetKAT.DyNetKAT
