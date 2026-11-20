import DyNetKAT.Frontend.V11Json
import DyNetKAT.DyNetKAT.Program

set_option linter.dupNamespace false

namespace DyNetKAT.Frontend.V11

open _root_.DyNetKAT.NetKAT _root_.DyNetKAT.DyNetKAT

private abbrev Proc (s : PacketSchema) := _root_.DyNetKAT.DyNetKAT.DyNetKAT s

private def atInput (loc : String) (result : Except String α) : Except String α :=
  result.mapError (fun msg => s!"{loc}: {msg}")

inductive QueryKind (P : Type) where
  | reachability (nonzero : Bool)
  | waypoint (test : P)

structure Query (E P : Type) where
  packetKey : String
  index : Nat
  stages : List (List E)
  depth : Nat
  kind : QueryKind P
  expression : String
  operand : String

structure ParsedInput where
  moduleName : String
  channels : List String
  root : Process
  definitions : List (String × Process)
  ingress : List (String × Policy)
  egress : List (String × Policy)
  queries : List (Query Event Policy)

private def checkNames (loc : String) (names : List String) : Except String Unit := do
  let mut seen : Std.HashSet String := {}
  for name in names do
    unless validName name do throw s!"{loc}: invalid name '{name}'"
    if seen.contains name then throw s!"{loc}: duplicate name '{name}'"
    seen := seen.insert name

def parseInput (raw : RawInput) : Except String ParsedInput := do
  checkNames "module_name" [raw.moduleName]
  checkNames "channels" raw.channels
  checkNames "recursive_variables" (raw.definitions.map Prod.fst)
  for (key, _) in raw.ingress do
    unless (raw.egress.lookup key).isSome do throw s!"out_packets: missing key '{key}'"
  for (key, _) in raw.egress do
    unless (raw.ingress.lookup key).isSome do throw s!"in_packets: missing key '{key}'"
  for (key, _) in raw.queries do
    unless (raw.ingress.lookup key).isSome do throw s!"properties: unknown packet key '{key}'"
  let root ← atInput "program" (parseProcess raw.root)
  let defs ← raw.definitions.mapM fun (name, text) =>
    return (name, ← atInput s!"recursive_variables.{name}" (parseProcess text))
  let ingress ← raw.ingress.mapM fun (key, text) =>
    return (key, ← atInput s!"in_packets.{key}" (parsePolicy text))
  let egress ← raw.egress.mapM fun (key, text) =>
    return (key, ← atInput s!"out_packets.{key}" (parsePolicy text))
  -- The reference dispatches in ingress-key order, then tuple order.
  let batches ← raw.ingress.mapM fun (key, _) => do
    let batch := (raw.queries.lookup key).getD []
    batch.zipIdx.mapM fun (q, index) => atInput s!"properties.{key}[{index}]" do
      let selector ← parseSelector q.expression
      let kind ← match q.kind, q.operand with
        | "r", "!0" => pure (.reachability true)
        | "r", "=0" => pure (.reachability false)
        | "r", _ => throw "reachability expects '!0' or '=0'"
        | "w", text => pure (.waypoint (← parsePolicy text))
        | _, _ => throw s!"unknown query kind '{q.kind}'"
      return ⟨key, index, selector.stages, q.depth, kind, q.expression, q.operand⟩
  return ⟨raw.moduleName, raw.channels, root, defs, ingress, egress, batches.flatten⟩

structure FieldDomain where
  name : String
  cardinality : Nat
  deriving Repr

abbrev Domains := Array FieldDomain

def Domains.schema (domains : Domains) : PacketSchema :=
  PacketSchema.ofFields (Fin domains.size) (fun f => Fin domains[f].cardinality)

private abbrev Maxima := Std.TreeMap String Nat

private def collectPolicy (p : Policy) (acc : Maxima) : Maxima :=
  match p with
  | .zero | .one => acc
  | .test field value | .assign field value =>
      acc.insert field (max value ((acc.get? field).getD 0))
  | .neg p | .star p => collectPolicy p acc
  | .union p q | .seq p q => collectPolicy q (collectPolicy p acc)

private def collectEvent (acc : Maxima) (e : Event) : Maxima :=
  collectPolicy e.payload acc

private def collectProcess (p : Process) (acc : Maxima) : Maxima :=
  match p with
  | .bot | .ref _ => acc
  | .packet n p => collectProcess p (collectPolicy n acc)
  | .comm e p => collectProcess p (collectEvent acc e)
  | .restrict events p => collectProcess p (events.foldl collectEvent acc)
  | .project _ p => collectProcess p acc
  | .choice p q | .parallel p q | .leftMerge p q | .commMerge p q =>
      collectProcess q (collectProcess p acc)

/-- Include every numeric value through the greatest literal and one more
    value, visible to complement tests. Field order is deterministic. -/
def inferDomains (input : ParsedInput) : Domains := Id.run do
  let mut maxima := collectProcess input.root {}
  for (_, p) in input.definitions do maxima := collectProcess p maxima
  for (_, p) in input.ingress ++ input.egress do maxima := collectPolicy p maxima
  for q in input.queries do
    for stage in q.stages do maxima := stage.foldl collectEvent maxima
    if let .waypoint p := q.kind then maxima := collectPolicy p maxima
  return maxima.toList.toArray.map fun (field, largest) => ⟨field, largest + 2⟩

private def resolveField (d : Domains) (name : String) :
    Except String d.schema.Field := do
  let i := d.findIdx (fun f => f.name == name)
  if h : i < d.size then return ⟨i, h⟩
  else throw s!"unknown packet field '{name}'"

private def resolveValue (d : Domains) (f : d.schema.Field) (value : Nat) :
    Except String (d.schema.Value f) := do
  let field := d[(show Fin d.size from f).val]
  if h : value < field.cardinality then return ⟨value, h⟩
  else throw s!"value {value} outside domain of '{field.name}'"

def elaborateTest (d : Domains) : Policy → Except String (Predicate d.schema)
  | .zero => pure .pFalse
  | .one => pure .pTrue
  | .test name value => do
      let f ← resolveField d name
      return .pFieldEq ⟨f, ← resolveValue d f value⟩
  | .neg p => return .pNot (← elaborateTest d p)
  | .union p q => return .pOr (← elaborateTest d p) (← elaborateTest d q)
  | .seq p q => return .pAnd (← elaborateTest d p) (← elaborateTest d q)
  | .assign .. | .star _ => throw "expected a predicate, found assignment or star"

def elaboratePolicy (d : Domains) : Policy → Except String (NetKAT d.schema)
  | .zero => pure .drop
  | .one => pure .id
  | .test name value => do
      let f ← resolveField d name
      return NetKAT.fieldTestFor f (← resolveValue d f value)
  | .assign name value => do
      let f ← resolveField d name
      return .assign1 f (← resolveValue d f value)
  | .neg p => return .test (.pNot (← elaborateTest d p))
  | .union p q => return .union (← elaboratePolicy d p) (← elaboratePolicy d q)
  | .seq p q => return .seq (← elaboratePolicy d p) (← elaboratePolicy d q)
  | .star p => return .star (← elaboratePolicy d p)

structure Reconfiguration (s : PacketSchema) where
  channel : Channel
  payload : NetKAT s

private def eventPolicy (d : Domains) (channels : Std.HashSet String) (e : Event) :
    Except String (NetKAT d.schema) := do
  unless channels.contains e.channel do throw s!"undeclared channel '{e.channel}'"
  elaboratePolicy d e.payload

private def restrictionAction (d : Domains) (channels : Std.HashSet String) (e : Event) :
    Except String (CommunicationAction d.schema) := do
  let p ← eventPolicy d channels e
  match e.direction with
  | .send => return .send e.channel p
  | .recv => return .recv e.channel p
  | .rcfg => throw "delta restricts send and receive actions only"

private def elaborateProcess (d : Domains) (channels : Std.HashSet String) :
    Process → Except String (Proc d.schema)
  | .bot => pure .deadlock
  | .ref name => pure (.var name)
  | .packet n p => return .nSeq (← elaboratePolicy d n) (← elaborateProcess d channels p)
  | .comm e p => do
      let n ← eventPolicy d channels e
      let next ← elaborateProcess d channels p
      return match e.direction with
        | .send => .send e.channel n next
        | .recv => .recv e.channel n next
        | .rcfg => .rcfgPrefix e.channel n next
  | .restrict es p => do
      let actions ← es.mapM (restrictionAction d channels)
      return .restrict (fun a => a ∈ actions) (← elaborateProcess d channels p)
  | .project depth p => return .project depth (← elaborateProcess d channels p)
  | .choice p q => return .choice (← elaborateProcess d channels p) (← elaborateProcess d channels q)
  | .parallel p q =>
      return .parallel (← elaborateProcess d channels p) (← elaborateProcess d channels q)
  | .leftMerge p q =>
      return .leftMerge (← elaborateProcess d channels p) (← elaborateProcess d channels q)
  | .commMerge p q =>
      return .commMerge (← elaborateProcess d channels p) (← elaborateProcess d channels q)

private def syntaxDec {s : PacketSchema} (extended : Bool) (p : Proc s) :
    Decidable (PaperSyntax extended p) :=
  match p with
  | .deadlock | .var _ => isTrue trivial
  | .nSeq _ p => syntaxDec false p
  | .recv _ _ p | .send _ _ p => syntaxDec extended p
  | .choice p q | .parallel p q =>
      @instDecidableAnd _ _ (syntaxDec extended p) (syntaxDec extended q)
  | .rcfgPrefix _ _ p | .restrict _ p | .project _ p =>
      @instDecidableAnd _ _ (inferInstance : Decidable (extended = true)) (syntaxDec extended p)
  | .leftMerge p q | .commMerge p q =>
      @instDecidableAnd _ _ (inferInstance : Decidable (extended = true))
        (@instDecidableAnd _ _ (syntaxDec extended p) (syntaxDec extended q))

private def guardedDec {s : PacketSchema} (p : Proc s) :
    Decidable (GuardedOccurrences p) :=
  match p with
  | .var _ => isFalse id
  | .deadlock | .nSeq .. | .send .. | .recv .. | .rcfgPrefix .. => isTrue trivial
  | .restrict _ p | .project _ p => guardedDec p
  | .choice p q | .parallel p q | .leftMerge p q | .commMerge p q =>
      @instDecidableAnd _ _ (guardedDec p) (guardedDec q)

private def missingReferences {s : PacketSchema} (env : RecEnv s) (p : Proc s) :
    List String :=
  match p with
  | .deadlock => []
  | .var name => if (env.lookup name).isNone then [name] else []
  | .nSeq _ p | .recv _ _ p | .send _ _ p | .rcfgPrefix _ _ p |
      .restrict _ p | .project _ p => missingReferences env p
  | .choice p q | .parallel p q | .leftMerge p q | .commMerge p q =>
      missingReferences env p ++ missingReferences env q

private def checkTerm {s : PacketSchema} (loc : String) (env : RecEnv s) (term : Proc s) :
    Except String { _u : Unit // Defined env term ∧ PaperSyntax true term } := do
  letI : Decidable (Defined env term) := by unfold Defined; infer_instance
  if h : Defined env term then
    letI := syntaxDec true term
    if formed : PaperSyntax true term then return ⟨(), h, formed⟩
    else throw s!"{loc}: continuation violates the paper grammar (packet prefixes require base continuations)"
  else
    let names := missingReferences env term
    throw s!"{loc}: unresolved process reference(s) {names}"

private def BodyOK {s : PacketSchema} (env : RecEnv s) (p : Proc s) : Prop :=
  Defined env p ∧ PaperSyntax true p ∧ GuardedOccurrences p

private def checkBodies {s : PacketSchema} (env : RecEnv s) :
    (defs : List (String × Proc s)) →
      Except String { _u : Unit // ∀ pair ∈ defs, BodyOK env pair.2 }
  | [] => pure ⟨(), by simp⟩
  | (name, body) :: rest => do
      let loc := s!"recursive_variables.{name}"
      let checked ← checkTerm loc env body
      let inst := guardedDec body
      match inst with
      | isTrue guarded =>
        let others ← checkBodies env rest
        return ⟨(), by
          intro pair mem
          rcases List.mem_cons.mp mem with exactName | inRest
          · subst pair
            exact ⟨checked.property.1, checked.property.2, guarded⟩
          · exact others.property pair inRest⟩
      | isFalse _ => throw s!"{loc}: unguarded recursive reference"

private theorem foundMem {s : PacketSchema} {defs : List (String × Proc s)}
    {name : String} {body : Proc s} (found : defs.lookup name = some body) :
    (name, body) ∈ defs := by
  obtain ⟨left, right, rfl, _⟩ := List.lookup_eq_some_iff.mp found
  simp

private structure Admitted {s : PacketSchema} (env : RecEnv s) where
  program : Program true env
  compiled : program.Compiled

private def admitProgram {s : PacketSchema} (defs : List (String × Proc s))
    (root : Proc s) :
    Except String (Admitted (fun name => defs.lookup name)) := do
  let env : RecEnv s := fun name => defs.lookup name
  let entry ← checkTerm "program" env root
  let bodies ← checkBodies env defs
  have bodyOK : ∀ x b, env.lookup x = some b → BodyOK env b :=
    fun x b h => bodies.property (x, b) (foundMem h)
  have closed : ClosedDefined env root := by
    intro x reachable
    induction reachable with
    | direct mem => exact entry.property.1 _ mem
    | throughDefinition _ found mem _ => exact (bodyOK _ _ found).1 _ mem
  let program : Program true env := ⟨root, ⟨⟨closed, by
    intro x reachable
    cases h : env.lookup x with
    | none => simpa [h] using closed x reachable
    | some b => exact ⟨b, rfl, (bodyOK x b h).2.2⟩⟩, entry.property.2,
    fun x b _ found => (bodyOK x b found).2.1⟩⟩
  let names := (defs.map Prod.fst).toFinset
  have inNames (x : String) : x ∈ names ↔ (env.lookup x).isSome := by
    change x ∈ (defs.map Prod.fst).toFinset ↔ (defs.lookup x).isSome
    simp only [List.mem_toFinset, List.mem_map, List.lookup_isSome_iff, beq_iff_eq]
    exact ⟨fun ⟨p, hp, eq⟩ => ⟨p, hp, eq.symm⟩, fun ⟨p, hp, eq⟩ => ⟨p, hp, eq.symm⟩⟩
  have subset (p : Proc s) (defined : Defined env p) : recursiveVars p ⊆ names :=
    fun x h => (inNames x).2 (defined x h)
  return ⟨program, ⟨names, subset root entry.property.1, by
    intro x mem
    have existsBody := (inNames x).1 mem
    cases h : env.lookup x with
    | none => simp [h] at existsBody
    | some b => exact ⟨b, rfl, subset b (bodyOK x b h).1⟩⟩⟩

structure Loaded where
  moduleName : String
  domains : Domains
  channels : List String
  definitions : List (String × Proc domains.schema)
  program : Program true (fun name => definitions.lookup name)
  support : program.Compiled
  ingress : List (String × Predicate domains.schema)
  egress : List (String × Predicate domains.schema)
  queries : List (Query (Reconfiguration domains.schema) (Predicate domains.schema))

def elaborate (input : ParsedInput) (domains : Domains) : Except String Loaded := do
  checkNames "recursive_variables" (input.definitions.map Prod.fst)
  checkNames "channels" input.channels
  checkNames "packet schema" (domains.toList.map FieldDomain.name)
  let channels := Std.HashSet.ofList input.channels
  let root ← atInput "program" (elaborateProcess domains channels input.root)
  let defs ← input.definitions.mapM fun (name, p) =>
    return (name, ← atInput s!"recursive_variables.{name}" (elaborateProcess domains channels p))
  let program ← admitProgram defs root
  let ingress ← input.ingress.mapM fun (key, p) =>
    return (key, ← atInput s!"in_packets.{key}" (elaborateTest domains p))
  let egress ← input.egress.mapM fun (key, p) =>
    return (key, ← atInput s!"out_packets.{key}" (elaborateTest domains p))
  let queries ← input.queries.mapM fun q => atInput s!"properties.{q.packetKey}[{q.index}]" do
    let stages ← q.stages.mapM fun stage => stage.mapM fun e => do
      unless e.direction == .rcfg do throw "tail expects reconfiguration actions"
      return ⟨e.channel, ← eventPolicy domains channels e⟩
    let kind ← match q.kind with
      | .reachability polarity => pure (.reachability polarity)
      | .waypoint p => pure (.waypoint (← elaborateTest domains p))
    return ⟨q.packetKey, q.index, stages, q.depth, kind, q.expression, q.operand⟩
  return ⟨input.moduleName, domains, input.channels, defs, program.program, program.compiled,
    ingress, egress, queries⟩

def load (text : String) : Except String Loaded := do
  let parsed ← parseInput (← decode text)
  elaborate parsed (inferDomains parsed)

end DyNetKAT.Frontend.V11
