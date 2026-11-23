import DyNetKATLean.Core.TightReachability
import DyNetKAT.Frontend.V11Loader
import DyNetKATLean.Core.Reachability

namespace DyNetKAT.Frontend.V11

open _root_.DyNetKAT.NetKAT _root_.DyNetKAT.DyNetKAT

private def checks {s : PacketSchema} : RestrictionChecks s := fun _ _ => false

private def checkRestrictions {s : PacketSchema} (p : GProc s) (c : RestrictionChecks s) :
    Option { _u : Unit // AllRestrictionChecksCorrect p c } :=
  match p with
  | .restrict .. => none
  | .nSeq _ p | .recv _ _ p | .send _ _ p | .rcfgPrefix _ _ p | .project _ p =>
      checkRestrictions p (c.child false)
  | .choice p q | .parallel p q | .leftMerge p q | .commMerge p q => do
      let l ← checkRestrictions p (c.child false)
      let r ← checkRestrictions q (c.child true)
      return ⟨(), l.property, r.property⟩
  | .deadlock | .ref _ => some ⟨(), trivial⟩

private def checkDefinitions {s : PacketSchema} :
    (ds : List (String × _root_.DyNetKAT.DyNetKAT.DyNetKAT s)) →
    Option { _u : Unit // ∀ pair ∈ ds, AllRestrictionChecksCorrect (toGProc pair.2) checks }
  | [] => some ⟨(), by simp⟩
  | pair :: rest => do
      let h ← checkRestrictions (toGProc pair.2) checks
      let t ← checkDefinitions rest
      return ⟨(), by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact h.property
        · exact t.property p hp⟩

structure BoundedQuery (s : PacketSchema) where
  packetKey : String
  index : Nat
  expression : String
  depth : Nat
  nonzero : Bool
  stages : List (ReconfigSet s)
  ingress : Predicate s
  egress : Predicate s

def BoundedQuery.reachable (job : Loaded) (q : BoundedQuery job.domains.schema) : Prop :=
  EndpointReachable job.program (some q.depth) q.stages (.test q.ingress) (.test q.egress)

def BoundedQuery.elaborate (job : Loaded) (q :
    Query (Reconfiguration job.domains.schema) (Predicate job.domains.schema)) :
    Except String (BoundedQuery job.domains.schema) := do
  let .reachability polarity := q.kind | throw "expected a reachability query"
  let some ingress := job.ingress.lookup q.packetKey | throw "missing ingress predicate"
  let some egress := job.egress.lookup q.packetKey | throw "missing egress predicate"
  let stages := q.stages.map fun stage =>
    (stage.map fun event => (event.channel, event.payload)).toFinset
  return ⟨q.packetKey, q.index, q.expression, q.depth, polarity, stages, ingress, egress⟩

structure BoundedVerdict (job : Loaded) (query : BoundedQuery job.domains.schema) where
  nonempty : Bool
  correct : nonempty = true ↔ query.reachable job

def BoundedVerdict.satisfied {job : Loaded} {q : BoundedQuery job.domains.schema}
    (v : BoundedVerdict job q) : Bool :=
  v.nonempty == q.nonzero

theorem BoundedVerdict.empty {job : Loaded} {q : BoundedQuery job.domains.schema}
    (v : BoundedVerdict job q) (h : v.nonempty = false) : ¬ q.reachable job :=
  fun reach => Bool.false_ne_true (h.symm.trans (v.correct.mpr reach))

structure Prepared (job : Loaded) where
  rootChecks : RestrictionChecks job.domains.schema
  bodyChecks : NodeId → RestrictionChecks job.domains.schema
  live : NodeId → Prop
  support : ProjectionSupport job.support.graph bodyChecks live
  valid : (job.support.initial rootChecks).checked.Valid live

/-- Check reusable classifiers once for the exact admitted loaded program. -/
def prepare (job : Loaded) : Except String (Prepared job) := do
  let some root := checkRestrictions (toGProc job.program.term) checks |
    throw "explicit root restriction needs a certified classifier"
  let some bodies := checkDefinitions job.definitions |
    throw "explicit declaration restriction needs a certified classifier"
  have support := toGraph_projectionSupport job.support.support job.program.admissible.1
    (fun _ => checks) (by
      intro x b _ found
      change job.definitions.lookup x = some b at found
      obtain ⟨left, right, eq, _⟩ := List.lookup_eq_some_iff.mp found
      exact bodies.property (x, b) (by rw [eq]; simp))
  have valid := toGProc_projectionValid (env := fun name => job.definitions.lookup name) root.property
  return ⟨checks, fun _ => checks, _, support, valid⟩

def checkPrepared (job : Loaded) (prepared : Prepared job) (q : BoundedQuery job.domains.schema) :
    Except String (BoundedVerdict job q) := do
  if depth : q.depth = q.stages.length + 1 then
    if let some i := pinnedIngress q.ingress then
      let v := tightReachability job.support prepared.rootChecks prepared.support prepared.valid q.stages q.ingress q.egress i
      return ⟨v.val, by unfold BoundedQuery.reachable; rw [depth]; exact v.property⟩
  match h : projectedReachability job.support prepared.rootChecks prepared.bodyChecks q.depth q.stages
      (.test q.ingress) (.test q.egress) with
  | none => throw "bounded projection or selector did not produce a verdict"
  | some result =>
      have exactResult := projectedReachability_correct job.support prepared.rootChecks prepared.support prepared.valid
        q.depth q.stages (.test q.ingress) (.test q.egress)
      return ⟨result, by rw [h] at exactResult; simpa only [Option.some.injEq] using exactResult⟩

def checkBounded (job : Loaded) (q : BoundedQuery job.domains.schema) :
    Except String (BoundedVerdict job q) := do
  checkPrepared job (← prepare job) q

end DyNetKAT.Frontend.V11
