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

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.println s!"DyNetKAT formalization: {DyNetKAT.projectName}"
      return 0
  | "validate" :: path :: paths =>
      let results ← (path :: paths).mapM validate
      return if results.all id then 0 else 1
  | _ =>
      IO.eprintln "Usage: dynetkat validate FILE.json [FILE.json ...]"
      return 2
