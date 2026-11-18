import DyNetKAT.Experimental

/- Generate the differential corpus with
   lake env lean --run test_katch_differential.lean > common.nkpl
   Run the KATch reference on common.nkpl. Each expected comparison is
   computed by Lean and checked by the reference implementation. -/
open DyNetKAT.NetKAT
open DyNetKAT.NetKAT.KatchExport

private def src := NetKAT.fieldTest .tpSrc .v8
private def setPort := NetKAT.assign1 .port .v1
private def path := NetKAT.union
  (.seq (.fieldTest .port .v0) (.assign1 .port .v8))
  (.seq (.fieldTest .port .v8) (.assign1 .port .v9))
private def viaStar := NetKAT.seq (.fieldTest .port .v0)
  (.seq (.star path) (.fieldTest .port .v9))

private def corpus : List (String × NetKAT × NetKAT) :=
  [ ("zero and false", .drop, .test .pFalse)
  , ("identity and true", .id, .test .pTrue)
  , ("identity and zero differ", .id, .drop)
  , ("predicate contradiction", .test (.pAnd .tpSrc8 (.pNot .tpSrc8)), .drop)
  , ("predicate excluded middle", .test (.pOr .tpSrc8 (.pNot .tpSrc8)), .id)
  , ("consecutive contradictory tests", .seq src (.fieldTest .tpSrc .v9), .drop)
  , ("assignment and test on distinct fields", .seq src setPort, .seq setPort src)
  , ("assignment and test on the same field", .seq setPort (.fieldTest .port .v1), setPort)
  , ("complete test expansion", .completeTest examplePacket, completeTestExpr examplePacket)
  , ("complete test admits a packet", .completeTest examplePacket, .drop)
  , ("PA-MATCH-ALL on the restricted domain", matchAll .port, .id)
  , ("two-step reachability", viaStar, .seq (.fieldTest .port .v0) (.assign1 .port .v9))
  , ("two-step reachability differs from zero", viaStar, .drop)
  , ("one step cannot reach", .seq (.fieldTest .port .v0)
      (.seq path (.fieldTest .port .v9)), .drop)
  , ("nested star", .star (.star path), .star path)
  , ("reflexive case", .star .drop, .id)
  , ("star unrolls right", .union .id (.seq (.star path) path), .star path) ]

def main : IO Unit := do
  IO.println s!"domain = {domain}"
  for (name, p, q) in corpus do
    let op := if netkatEquiv p q then "≡" else "≢"
    IO.println s!"-- {name}"
    IO.println s!"check (domain ⋅ ({policy p})) {op} (domain ⋅ ({policy q}))"
  IO.println "-- Removing the domain restriction exposes additional port values."
  IO.println s!"check {policy (matchAll .port)} ≢ ⊤"
