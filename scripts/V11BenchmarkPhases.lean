import DyNetKAT.Frontend.V11Batch

open DyNetKAT.Frontend.V11
open _root_.DyNetKAT.DyNetKAT

private def route (job : Loaded) (q : InputQuery job) : String :=
  match q.kind with
  | .reachability _ =>
    match BoundedQuery.elaborate job q with
    | .ok b =>
      if b.depth == b.stages.length + 1 && (pinnedIngress b.ingress).isSome then
        "tight_reachability"
      else
        "projected_reachability"
    | .error _ => "elaboration_error"
  | .waypoint _ =>
    if q.depth == q.stages.length + 1 then "tight_waypoint_head" else "projected_waypoint_head"

private def phase (name : String) (start : Nat) : IO Unit := do
  let stop ← IO.monoNanosNow
  IO.eprintln s!"{name} {stop - start}"

def main (args : List String) : IO UInt32 := do
  let [path] := args | return 2
  let start ← IO.monoNanosNow
  IO.eprintln s!"entry_clock {start}"
  let reading ← IO.monoNanosNow
  let text ← IO.FS.readFile path
  phase "read" reading
  let loading ← IO.monoNanosNow
  -- These are the same public operations composed by V11.load.
  let parsed ← match decode text >>= parseInput with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  phase "decode_and_parse" loading
  let validation ← IO.monoNanosNow
  let job ← match elaborate parsed (inferDomains parsed) with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  phase "infer_domains_elaborate_validate" validation
  let preparing ← IO.monoNanosNow
  let prepared ← match prepare job with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  phase "prepare" preparing
  let out ← IO.getStdout
  let mut code : UInt32 := 0
  for query in job.queries do
    let checking ← IO.monoNanosNow
    let report := reportQuery job (.ok prepared) query
    phase s!"check/{query.packetKey}/{query.index}" checking
    let reporting ← IO.monoNanosNow
    out.putStrLn ((Lean.Json.mkObj [("input", .str path), ("result", report.json)]).compress)
    out.flush
    phase s!"output/{query.packetKey}/{query.index}" reporting
    IO.eprintln s!"route/{query.packetKey}/{query.index} {route job query}"
    code := max code report.exitCode
  let finish ← IO.monoNanosNow
  IO.eprintln s!"exit_clock {finish}"
  IO.eprintln s!"internal_total {finish - start}"
  return code
