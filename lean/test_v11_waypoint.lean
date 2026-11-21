import DyNetKAT.Frontend.V11Batch

open DyNetKAT.Frontend.V11

private def fixture := r#"{
  "module_name":"Waypoints",
  "program":"\"pt <- 1\" ; bot",
  "recursive_variables":{},
  "channels":[],
  "in_packets":{"p":"pt = 0"},
  "out_packets":{"p":"pt = 1"},
  "properties":{"p":[["r","head(@Program)","!0",1],
                      ["w","head(@Program)","pt = 1",1],
                      ["w","head(@Program)","zero",2]]}
}"#

private def checkFixture (text : String) : Except String Bool := do
  let job ← load text
  let results := batch job
  let fresh := job.queries.map fun q => reportQuery job (prepare job) q
  let some waypoint := job.queries[1]? | return false
  let some report := results[1]? | return false
  let session := prepare job
  let bad := reportQuery job session { waypoint with packetKey := "missing" }
  return results == fresh &&
     (results.map (·.index)) == [0, 1, 2] &&
     (results.map (·.kind)) == ["reachability", "waypoint", "waypoint"] &&
     (results.map (·.verdict)) == [some true, some true, some false] &&
     (results.map (·.expectation)) == [some true, none, none] &&
     (results.map (·.exitCode)) == [0, 0, 0] && bad.exitCode == 4 &&
     reportQuery job session waypoint == report

#guard (checkFixture fixture).toOption == some true
#guard (checkFixture (fixture.replace "pt <- 1" "(pt <- 1)*")).toOption == some true

-- A second field introduces an ingress fiber and exercises its fast checker.
#guard (checkFixture (fixture.replace r#""out_packets":{"p":"pt = 1"}"#
  r#""out_packets":{"p":"pt = 1 . flag = 0"}"#)).toOption == some true

#guard (do
  let job ← load fixture
  let some report := (batch job)[0]? | return false
  return report.json.compress ==
    "{\"verdict\":true,\"polarity\":\"!0\",\"packet\":\"p\",\"module\":\"Waypoints\",\"kind\":\"reachability\",\"index\":0,\"expression\":\"head(@Program)\",\"expectation_agrees\":true,\"diagnostic\":null,\"depth\":1}"
  : Except String Bool).toOption == some true

private def corpusReport (line : String) :
    Except String (String × String × String × Nat × Nat × Bool × Option Bool) := do
  let envelope ← Lean.Json.parse line
  let file ← envelope.getObjValAs? String "input"
  let r ← envelope.getObjVal? "result"
  unless (← r.getObjVal? "diagnostic") == .null do throw s!"non-verdict: {line}"
  return (file, ← r.getObjValAs? String "kind", ← r.getObjValAs? String "packet",
    ← r.getObjValAs? Nat "index", ← r.getObjValAs? Nat "depth",
    ← r.getObjValAs? Bool "verdict", ← r.getObjValAs? (Option Bool) "expectation_agrees")

-- Pass the JSONL outputs of the native reused and fresh batch runs.
def main (args : List String) : IO Unit := do
  let [reuse, fresh] := args | throw (IO.userError "expected reused and fresh JSONL files")
  let reused ← IO.FS.readFile reuse
  unless reused == (← IO.FS.readFile fresh) do
    throw (IO.userError "fresh and reused batch records differ")
  let lines := (reused.splitOn "\n").filter (!·.isEmpty)
  let rows ← IO.ofExcept (lines.mapM corpusReport)
  let inputs := (rows.map fun row => row.1).eraseDups
  let waypoints := rows.filter fun row => row.2.1 == "waypoint"
  let reach := rows.filter fun row => row.2.1 == "reachability"
  unless inputs.length == 27 && reach.length == 108 && waypoints.length == 12 do
    throw (IO.userError "unexpected pinned corpus totals")
  for (_, _, _, _, _, verdict, expectation) in waypoints do
    unless verdict && expectation.isNone do throw (IO.userError "unexpected waypoint result")
  let disagreements := reach.filterMap fun (file, _, packet, index, depth, verdict, expectation) =>
    if expectation == some false then
      some ((System.FilePath.mk file).fileName, packet, index, depth, verdict)
    else none
  unless disagreements == [
      (some "distributed_controller_independent.json", "H3_to_H2", 1, 3, true),
      (some "distributed_controller_independent.json", "H1_to_H4", 1, 3, true)] do
    throw (IO.userError s!"unexpected fixture expectation disagreements {repr disagreements}")
  IO.println "27 inputs, 120 identical records, 12 true waypoint verdicts, 2 fixture disagreements"
