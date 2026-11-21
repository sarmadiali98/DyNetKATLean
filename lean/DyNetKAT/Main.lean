import DyNetKAT.Frontend.V11Batch
import DyNetKAT.Frontend.V11Reachability
import DyNetKAT.Basic
import DyNetKAT.Frontend.V11Loader

open DyNetKAT.Frontend.V11

private def validate (path : String) : IO Bool := do
  try
    match load (← IO.FS.readFile path) with
    | .error message =>
        IO.eprintln s!"{path}: {message}"
        return false
    | .ok input =>
        IO.println s!"{path}: accepted {input.moduleName}, {input.definitions.length} declarations, {input.domains.size} fields, {input.queries.length} queries"
        return true
  catch err =>
    IO.eprintln s!"{path}: {err}"
    return false

private def reach (path : String) : IO Bool := do
  try
    match load (← IO.FS.readFile path) with
    | .error message =>
        IO.eprintln s!"{path}: {message}"
        return false
    | .ok job =>
        let mut ok := true
        for q in job.queries do
          if let .reachability _ := q.kind then
            let out ← IO.getStdout
            let id := s!"{path} {q.packetKey} {q.index} depth={q.depth}"
            match BoundedQuery.elaborate job q >>= (fun b => (checkBounded job b).map fun v => (v.nonempty, v.satisfied)) with
            | .error why =>
                out.putStrLn s!"{id} non-verdict: {why}"
                ok := false
            | .ok (nonempty, satisfied) =>
                out.putStrLn s!"{id} nonempty={nonempty} satisfied={satisfied}"
            out.flush
        return ok
  catch err =>
    IO.eprintln s!"{path}: {err}"
    return false

private def runQueries (path : String) (json fresh : Bool)
    (selected : Option (String × Nat)) : IO UInt32 := do
  try
    let job ← match load (← IO.FS.readFile path) with
      | .ok job => pure job
      | .error e => throw (IO.userError e)
    let queries := match selected with
      | none => job.queries
      | some (key, index) => job.queries.filter fun q => q.packetKey == key && q.index == index
    if selected.isSome && queries.isEmpty then
      IO.eprintln s!"{path}: no query with that packet key and index"
      return 2
    let prepared := if fresh then none else some (prepare job)
    let out ← IO.getStdout
    let mut code : UInt32 := 0
    for query in queries do
      let report := reportQuery job (match prepared with | some p => p | none => prepare job) query
      if json then
        out.putStrLn ((Lean.Json.mkObj [("input", .str path), ("result", report.json)]).compress)
      else
        out.putStrLn s!"{path} {report.display}"
      out.flush
      code := max code report.exitCode
    return code
  catch err =>
    IO.eprintln s!"{path}: {err}"
    return 2

private def usage : IO UInt32 := do
  IO.eprintln "Usage: dynetkat (validate|reach) FILE... | batch [--json] [--fresh] FILE... | query [--json] FILE PACKET INDEX"
  return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.println s!"DyNetKAT formalization: {DyNetKAT.projectName}"
      return 0
  | "reach" :: path :: paths =>
      let results ← (path :: paths).mapM reach
      return if results.all id then 0 else 1
  | "validate" :: path :: paths =>
      let results ← (path :: paths).mapM validate
      return if results.all id then 0 else 1
  | "batch" :: rest =>
      let json := rest.head? == some "--json"
      let rest := if json then rest.drop 1 else rest
      let fresh := rest.head? == some "--fresh"
      let paths := if fresh then rest.drop 1 else rest
      if paths.isEmpty then return ← usage
      let codes ← paths.mapM (fun path => runQueries path json fresh none)
      return codes.foldl max 0
  | "query" :: rest =>
      let json := rest.head? == some "--json"
      match (if json then rest.drop 1 else rest) with
      | [path,key,index] =>
          let some n := index.toNat? | usage
          runQueries path json false (some (key,n))
      | _ => usage
  | _ => usage
