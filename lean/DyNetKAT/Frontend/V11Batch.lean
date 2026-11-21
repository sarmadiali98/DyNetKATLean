import DyNetKAT.Frontend.V11Waypoint
import Lean.Data.Json

namespace DyNetKAT.Frontend.V11

open _root_.DyNetKAT.NetKAT _root_.DyNetKAT.DyNetKAT

abbrev InputQuery (job : Loaded) :=
  Query (Reconfiguration job.domains.schema) (Predicate job.domains.schema)

structure QueryReport where
  moduleName : String
  packetKey : String
  index : Nat
  expression : String
  depth : Nat
  kind : String
  polarity : Option Bool
  verdict : Option Bool
  diagnostic : Option String
  deriving BEq, Repr

def QueryReport.expectation (r : QueryReport) : Option Bool := do
  let actual ← r.verdict
  let expected ← r.polarity
  return actual == expected

def QueryReport.json (r : QueryReport) : Lean.Json :=
  Lean.Json.mkObj [
    ("module", toJson r.moduleName), ("packet", toJson r.packetKey), ("index", toJson r.index),
    ("expression", toJson r.expression), ("depth", toJson r.depth), ("kind", toJson r.kind),
    ("polarity", toJson (r.polarity.map fun p => if p then "!0" else "=0")),
    ("verdict", toJson r.verdict), ("expectation_agrees", toJson r.expectation),
    ("diagnostic", toJson r.diagnostic)]
where
  toJson {α : Type} [Lean.ToJson α] (a : α) := Lean.toJson a

def QueryReport.exitCode (r : QueryReport) : UInt32 :=
  if r.diagnostic.isSome then 4 else if r.expectation == some false then 1 else 0

def QueryReport.display (r : QueryReport) : String :=
  let label := s!"{r.moduleName} {r.packetKey} {r.index} {r.kind} depth={r.depth}"
  match r.diagnostic, r.verdict with
  | some reason, _ => s!"{label} non-verdict: {reason}"
  | _, some b =>
    let status := match r.expectation with
      | none => ""
      | some true => " expectation agrees"
      | some false => " checked verdict disagrees with fixture expectation"
    s!"{label} verdict={b}{status}"
  | _, _ => s!"{label} non-verdict"

def evaluate (job : Loaded) (prepared : Prepared job) (q : InputQuery job) : Except String Bool := do
  match q.kind with
  | .reachability _ =>
    let b ← BoundedQuery.elaborate job q
    return (← checkPrepared job prepared b).nonempty
  | .waypoint via =>
    let some ing := job.ingress.lookup q.packetKey | throw "missing ingress predicate"
    let some out := job.egress.lookup q.packetKey | throw "missing egress predicate"
    let head ← selectHead job prepared q.depth (stagesOf q.stages)
    let rhs ← waypointRelation head.val ing out via
    return (checkWaypointInclusion (List.finRange job.domains.size) ing out head.val rhs).val

def reportQuery (job : Loaded) (prepared : Except String (Prepared job))
    (q : InputQuery job) : QueryReport :=
  let (kind, polarity) := match q.kind with
    | .reachability p => ("reachability", some p)
    | .waypoint _ => ("waypoint", none)
  let (result, problem) := match prepared >>= fun p => evaluate job p q with
    | .ok answer => (some answer, none)
    | .error message => (none, some message)
  ⟨job.moduleName, q.packetKey, q.index, q.expression, q.depth, kind, polarity, result, problem⟩

def batch (job : Loaded) : List QueryReport :=
  let prepared := prepare job
  job.queries.map (reportQuery job prepared)

end DyNetKAT.Frontend.V11
