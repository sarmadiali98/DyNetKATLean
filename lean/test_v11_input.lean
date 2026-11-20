import DyNetKAT.Frontend.V11Loader

open DyNetKAT.Frontend.V11

private def input := r#"{
  "module_name":"Example",
  "program":"(c ! \"zero + zero\") ; X || Y",
  "recursive_variables":{"X":"(c ? \"zero\") ; Y","Y":"\"sw = 7 . sw <- 1344\" ; X"},
  "channels":["c"],
  "in_packets":{"z":"~ (sw = 1344)", "a":"one"},
  "out_packets":{"a":"one", "z":"sw = 7"},
  "properties":{"a":[["w","head(@Program)","sw = 7",4]],
    "z":[["r","head(tail(tail(@Program, {rcfg(c, \"zero\")}), {}))","=0",5],
         ["r","(head(@Program))","!0",2]]}
}"#

private def checkLoaded : Except String Bool := do
  let job ← load input
  let .parallel (.send "c" (.union .drop .drop) (.var "X")) (.var "Y") := job.program.term
    | return false
  let some (.recv "c" .drop (.var "Y")) := job.definitions.lookup "X" | return false
  let [a, b, c] := job.queries | return false
  let .reachability false := a.kind | return false
  let .reachability true := b.kind | return false
  let .waypoint _ := c.kind | return false
  let [[event], []] := a.stages | return false
  let .drop := event.payload | return false
  return job.channels == ["c"] &&
    (job.definitions.map Prod.fst) == ["X", "Y"] &&
    (job.domains.toList.map fun d => (d.name, d.cardinality)) == [("sw", 1346)] &&
    a.packetKey == "z" && a.index == 0 && a.depth == 5 && event.channel == "c" &&
    b.packetKey == "z" && b.index == 1 && b.depth == 2 &&
    c.packetKey == "a" && c.index == 0 && c.depth == 4

private def accepted (result : Except String Bool) : Bool :=
  match result with
  | .ok true => true
  | _ => false

#guard accepted checkLoaded

private def rejected (result : Except String α) (fragment : String) : Bool :=
  match result with
  | .error e => (e.splitOn fragment).length > 1
  | .ok _ => false

#guard rejected (load "{") "JSON:"
#guard rejected (load (input.replace "\"channels\":" "\"channels\":[],\"channels\":")) "duplicate JSON key"
#guard rejected (load (input.replace "[\"c\"]" "[\"c\",\"c\"]")) "duplicate name"
#guard rejected (load (input.replace "|| Y" "|| Missing")) "Missing"
#guard rejected (load (input.replace r#"(c ? \"zero\") ; Y"# "Y")) "unguarded"
#guard rejected (load (input.replace "|| Y" r#"|| delta{rcfg(c,\"zero\")}(Y)"#)) "delta restricts"
#guard rejected (load (input.replace "|| Y" r#"|| \"one\" ; pi{2}(Y)"#)) "base continuations"
#guard rejected (load (input.replace "|| Y" "||")) "expected a process"
#guard rejected (load (input.replace "|| Y" r#"|| (u ? \"one\") ; Y"#)) "undeclared channel"
#guard rejected (load (input.replace "\"=0\"" "\"maybe\"")) "expects '!0' or '=0'"
#guard rejected (load (input.replace "head(@Program)" "tail(@Program,{})")) "expected head"
#guard rejected (load (input.replace "sw = 7\",4" "sw <- 7\",4")) "expected a predicate"
#guard rejected (elaboratePolicy #[⟨"sw", 2⟩] (.test "pt" 1)) "unknown packet field"
#guard rejected (elaboratePolicy #[⟨"sw", 2⟩] (.assign "sw" 2)) "outside domain"

#guard accepted ((parsePolicy "~ (sw = 1 + sw = 2) . (pt <- 8)* + one").map
  (· == .union (.seq (.neg (.union (.test "sw" 1) (.test "sw" 2))) (.star (.assign "pt" 8))) .one))

#guard accepted ((parseProcess "delta{(c ! \"one\")}(pi{2}(X ||< Y | bot))").map fun
  | .restrict [e] (.project 2 (.commMerge (.leftMerge (.ref "X") (.ref "Y")) .bot)) =>
      e.channel == "c" && e.direction == .send
  | _ => false)

private def checkFixture (dir : System.FilePath) (name : String) (count : Nat)
    (isFatTree : Bool) : IO Unit := do
  let text ← IO.FS.readFile (dir / name)
  match decode text, load text with
  | .ok raw, .ok job =>
      unless job.definitions.map Prod.fst == raw.definitions.map Prod.fst &&
          job.channels == raw.channels && job.queries.length == count do
        throw (IO.userError s!"{name}: lost declarations, channels or queries")
      let expected := raw.ingress.flatMap fun (key, _) =>
        ((raw.queries.lookup key).getD []).zipIdx.map fun (q, i) =>
          (key, i, q.depth, q.expression, q.operand)
      unless job.queries.map (fun q => (q.packetKey, q.index, q.depth, q.expression, q.operand)) ==
          expected do
        throw (IO.userError s!"{name}: changed query identity, order or depth")
      if isFatTree then
        unless (job.domains.toList.map FieldDomain.name) == ["dst", "pt", "src", "sw", "typ"] do
          throw (IO.userError s!"{name}: unexpected packet fields")
        for q in job.queries do
          unless q.stages.length + 1 == q.depth do
            throw (IO.userError s!"{name}: incorrect selector nesting")
      IO.println s!"accepted {name} ({count} queries)"
  | .error e, _ | _, .error e => throw (IO.userError s!"{name}: {e}")

-- Pass a directory containing the three pinned fixture files and the
-- unmodified outputs of the pinned FatTree generator.
def main (args : List String) : IO Unit := do
  match args with
  | [dir] =>
      for name in ["stateful_firewall.json", "distributed_controller_independent.json",
          "distributed_controller_synchronized.json"] do
        checkFixture dir name 4 false
      for pods in [6, 8, 10, 12, 14, 16] do
        for (group, count) in [("reachability_1", 4), ("reachability_2", 4),
            ("waypointing", 1), ("all_properties", 9)] do
          checkFixture dir s!"fattree_{pods}_pods_{group}.json" count true
  | _ => throw (IO.userError "expected one directory with the pinned corpus")
