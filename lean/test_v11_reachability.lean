import DyNetKAT.Frontend.V11Reachability

open DyNetKAT.Frontend.V11

private def input := r#"{
  "module_name":"Bounded",
  "program":"Start",
  "recursive_variables":{
    "Start":"rcfg(a, \"one\") ; Next o+ \"pt <- 1\" ; bot",
    "Next":"rcfg(b, \"one\") ; \"~ (pt = 1) . pt <- 1\" ; bot"
  },
  "channels":["a","b"],
  "in_packets":{"p":"~ (pt = 1)"},
  "out_packets":{"p":"pt = 1"},
  "properties":{"p":[
    ["r","head(@Program)","!0",1],
    ["r","head(@Program)","=0",0],
    ["r","head(tail(tail(@Program,{rcfg(a,\"one\")}),{rcfg(b,\"one\")}))","!0",3],
    ["r","head(tail(tail(@Program,{rcfg(a,\"one\")}),{rcfg(b,\"one\")}))","=0",2],
    ["r","head(tail(@Program,{rcfg(a,\"one + zero\")}))","=0",3]
  ]}
}"#

private def verdicts (job : Loaded) : Except String (List (String × Nat × Nat × Bool × Bool)) :=
  job.queries.filterMapM fun q => do
    match q.kind with
    | .waypoint _ => return none
    | .reachability _ =>
      let b ← BoundedQuery.elaborate job q
      let v ← checkBounded job b
      return some (b.packetKey, b.index, b.depth, v.nonempty, v.satisfied)

private def check (text : String) : Except String (List (String × Nat × Nat × Bool × Bool)) :=
  load text >>= verdicts

private def widen (d : Domains) : Domains :=
  d.map fun f => { f with cardinality := f.cardinality + 2 }

#guard (check input).toOption == some
  [("p", 0, 1, true, true), ("p", 1, 0, false, true), ("p", 2, 3, true, true),
   ("p", 3, 2, false, true), ("p", 4, 3, false, true)]

#guard (do
  let parsed ← decode input >>= parseInput
  elaborate parsed (widen (inferDomains parsed)) >>= verdicts).toOption == (check input).toOption

-- This conjunctive ingress triggers the tight-depth specialization.
#guard (check (input.replace "~ (pt = 1)" "pt = 0")).toOption == (check input).toOption

#guard (check (input.replace "head(@Program)" "tail(@Program,{})")).isOk == false
#guard (check (input.replace "\"program\":\"Start\"" "\"program\":\"delta{}(Start)\"")).isOk == false

def main (args : List String) : IO Unit := do
  for path in args do
    let parsed ← IO.ofExcept (decode (← IO.FS.readFile path) >>= parseInput)
    let d := inferDomains parsed
    let result ← IO.ofExcept (elaborate parsed d >>= verdicts)
    let extended ← IO.ofExcept (elaborate parsed (widen d) >>= verdicts)
    unless result == extended do
      throw (IO.userError s!"{path}: verdict changed after domain extension")
    -- The two independent-controller post-update queries express isolation
    -- claims that the admitted source model disproves.
    let independent := (System.FilePath.mk path).fileName ==
      some "distributed_controller_independent.json"
    for (_, index, _, _, satisfied) in result do
      unless satisfied == !(independent && index == 1) do
        throw (IO.userError s!"{path}: unexpected checked outcome at index {index}")
    IO.println s!"{path}: checked {result.length} verdicts and domain extension"
