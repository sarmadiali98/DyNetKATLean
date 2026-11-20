import Lean.Data.Json.Parser
import DyNetKAT.Frontend.V11Syntax

namespace DyNetKAT.Frontend.V11

open Lean Std.Internal.Parsec Std.Internal.Parsec.String

-- Retain object order and reject duplicate keys before a map can overwrite them.
private inductive InputJson where
  | object (fields : List (String × InputJson))
  | array (items : Array InputJson)
  | scalar (value : Json)
  deriving Inhabited

mutual
  private partial def jsonValue : Parser InputJson := do
    ws
    match ← peek! with
    | '{' =>
        skip
        ws
        if (← peek!) == '}' then
          skip
          return .object []
        jsonObject []
    | '[' =>
        skip
        ws
        if (← peek!) == ']' then
          skip
          return .array #[]
        jsonArray #[]
    | _ => return .scalar (← Json.Parser.anyCore)

  private partial def jsonObject (acc : List (String × InputJson)) : Parser InputJson := do
    if (← any) != '"' then fail "expected a JSON object key"
    let key ← Json.Parser.str
    if (acc.lookup key).isSome then fail s!"duplicate JSON key '{key}'"
    ws
    if (← any) != ':' then fail "expected ':' after JSON key"
    let value ← jsonValue
    ws
    match ← any with
    | '}' => return .object ((key, value) :: acc).reverse
    | ',' =>
        ws
        jsonObject ((key, value) :: acc)
    | _ => fail "expected ',' or '}' after JSON field"

  private partial def jsonArray (acc : Array InputJson) : Parser InputJson := do
    let value ← jsonValue
    ws
    match ← any with
    | ']' => return .array (acc.push value)
    | ',' => jsonArray (acc.push value)
    | _ => fail "expected ',' or ']' after JSON item"
end

private def jsonDocument : Parser InputJson := do
  let value ← jsonValue
  ws
  eof
  return value

private def object (path : String) : InputJson → Except String (List (String × InputJson))
  | .object fields => pure fields
  | _ => throw s!"{path}: expected an object"

private def string (path : String) : InputJson → Except String String
  | .scalar (.str s) => pure s
  | _ => throw s!"{path}: expected a string"

private def strings (path : String) (j : InputJson) : Except String (List (String × String)) := do
  (← object path j).mapM fun (k, v) => return (k, ← string s!"{path}.{k}" v)

private def array (path : String) : InputJson → Except String (Array InputJson)
  | .array values => pure values
  | _ => throw s!"{path}: expected an array"

structure RawQuery where
  kind : String
  expression : String
  operand : String
  depth : Nat
  deriving Inhabited, Repr

structure RawInput where
  moduleName : String
  root : String
  definitions : List (String × String)
  channels : List String
  ingress : List (String × String)
  egress : List (String × String)
  queries : List (String × List RawQuery)
  deriving Inhabited, Repr

def decode (text : String) : Except String RawInput := do
  let json ← (Parser.run jsonDocument text).mapError ("JSON: " ++ ·)
  let fields ← object "input" json
  let get := fun name => match fields.lookup name with
    | some field => Except.ok field
    | none => Except.error s!"missing field '{name}'"
  if (fields.lookup "comm").isSome || (fields.lookup "file_name").isSome then
    throw "preprocessed input is not supported by the raw v1.1 loader"
  let moduleName ← string "module_name" (← get "module_name")
  let root ← string "program" (← get "program")
  let definitions ← strings "recursive_variables" (← get "recursive_variables")
  let channels ← (← array "channels" (← get "channels")).toList.mapM (string "channels")
  let ingress ← strings "in_packets" (← get "in_packets")
  let egress ← strings "out_packets" (← get "out_packets")
  let properties ← object "properties" (← get "properties")
  let queries ← properties.mapM fun (key, entry) => do
    let path := s!"properties.{key}"
    let result ← (← array path entry).toList.zipIdx.mapM fun (item, index) => do
      let loc := s!"{path}[{index}]"
      match (← array loc item).toList with
      | [kind, selector, operand, .scalar depth] =>
          return ⟨← string loc kind, ← string loc selector, ← string loc operand,
            ← depth.getNat?.mapError (fun _ => s!"{loc}: expected a natural depth")⟩
      | _ => throw s!"{loc}: expected [kind, selector, operand, depth]"
    return (key, result)
  return ⟨moduleName, root, definitions, channels, ingress, egress, queries⟩

end DyNetKAT.Frontend.V11
