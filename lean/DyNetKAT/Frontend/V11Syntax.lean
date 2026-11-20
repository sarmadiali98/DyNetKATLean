namespace DyNetKAT.Frontend.V11

inductive Policy where
  | zero | one
  | test (field : String) (value : Nat)
  | assign (field : String) (value : Nat)
  | neg (p : Policy)
  | union (p q : Policy)
  | seq (p q : Policy)
  | star (p : Policy)
  deriving Inhabited, Repr, BEq

inductive Direction where
  | send | recv | rcfg
  deriving Inhabited, Repr, BEq

structure Event where
  direction : Direction
  channel : String
  payload : Policy
  deriving Inhabited, Repr

inductive Process where
  | bot
  | ref (name : String)
  | packet (policy : Policy) (next : Process)
  | comm (event : Event) (next : Process)
  | choice (p q : Process)
  | parallel (p q : Process)
  | leftMerge (p q : Process)
  | commMerge (p q : Process)
  | restrict (events : List Event) (p : Process)
  | project (depth : Nat) (p : Process)
  deriving Inhabited, Repr

structure Selector where
  stages : List (List Event)
  deriving Inhabited, Repr

private inductive Token where
  | word (text : String)
  | quoted (text : String)
  | symbol (text : String)
  deriving Inhabited, Repr, BEq

private def wordStart (c : Char) : Bool := c.isAlpha || c == '_' || c == '@'
private def wordChar (c : Char) : Bool := wordStart c || c.isDigit || c == '-'

private partial def lex (acc : List Token) : List Char → Except String (List Token)
  | [] => pure acc.reverse
  | '"' :: cs => do
      let contents := cs.takeWhile (· != '"')
      match cs.drop contents.length with
      | [] => throw "unterminated quoted policy"
      | _ :: rest => lex (.quoted (String.mk contents) :: acc) rest
  | '|' :: '|' :: '<' :: cs => lex (.symbol "||<" :: acc) cs
  | '|' :: '|' :: cs => lex (.symbol "||" :: acc) cs
  | 'o' :: '+' :: cs => lex (.symbol "o+" :: acc) cs
  | '<' :: '-' :: cs => lex (.symbol "<-" :: acc) cs
  | c :: cs => do
      if c.isWhitespace then lex acc cs
      else if wordStart c || c.isDigit then
        let suffix := cs.takeWhile (if c.isDigit then Char.isDigit else wordChar)
        lex (.word (String.mk (c :: suffix)) :: acc) (cs.drop suffix.length)
      else if "(){};!?.,=~+*|".contains c then
        lex (.symbol (String.singleton c) :: acc) cs
      else throw s!"unexpected character {c}"

private abbrev Parser (α : Type) := List Token → Except String (α × List Token)

private def expect (s : String) : Parser Unit
  | .symbol t :: rest => if t == s then .ok ((), rest) else .error s!"expected '{s}', got '{t}'"
  | tokens => .error s!"expected '{s}', near {repr (tokens.take 3)}"

private def natural : Parser Nat
  | .word s :: rest =>
      match s.toNat? with
      | some n => .ok (n, rest)
      | none => .error s!"expected a natural number, got '{s}'"
  | _ => .error "expected a natural number"

def validName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => wordStart c && c != '@' && cs.all (fun x => wordChar x && x != '@')

private def finish (p : Parser α) (s : String) : Except String α := do
  let (value, remaining) ← p (← lex [] s.toList)
  unless remaining.isEmpty do throw s!"unexpected trailing tokens {repr (remaining.take 4)}"
  return value

mutual
  private partial def policyExpr (minimum : Nat) (tokens : List Token) :
      Except String (Policy × List Token) := do
    let (p, rest) ← policyAtom tokens
    policyRest minimum p rest

  private partial def policyAtom : Parser Policy
    | .symbol "(" :: rest => do
        let (p, rest) ← policyExpr 0 rest
        return (p, (← expect ")" rest).2)
    | .symbol "~" :: rest => do
        let (p, rest) ← policyExpr 3 rest
        return (.neg p, rest)
    | .word "zero" :: rest => pure (.zero, rest)
    | .word "one" :: rest => pure (.one, rest)
    | .word field :: .symbol op :: rest => do
        unless validName field && (op == "=" || op == "<-") do
          throw "expected a field test or assignment"
        let (value, rest) ← natural rest
        return (if op == "=" then .test field value else .assign field value, rest)
    | tokens => throw s!"expected a policy near {repr (tokens.take 3)}"

  private partial def policyRest (minimum : Nat) (p : Policy) :
      Parser Policy
    | .symbol "*" :: rest => policyRest minimum (.star p) rest
    | .symbol "+" :: rest => do
        if minimum > 1 then return (p, .symbol "+" :: rest)
        let (q, rest) ← policyExpr 2 rest
        policyRest minimum (.union p q) rest
    | .symbol "." :: rest => do
        if minimum > 2 then return (p, .symbol "." :: rest)
        let (q, rest) ← policyExpr 3 rest
        policyRest minimum (.seq p q) rest
    | rest => pure (p, rest)
end

def parsePolicy : String → Except String Policy := finish (policyExpr 0)

private partial def parseEvent : Parser Event
  | .symbol "(" :: rest => do
      let (e, rest) ← parseEvent rest
      return (e, (← expect ")" rest).2)
  | .word "rcfg" :: .symbol "(" :: .word ch :: .symbol "," :: .quoted p :: rest => do
      return (⟨.rcfg, ch, ← parsePolicy p⟩, (← expect ")" rest).2)
  | .word ch :: .symbol op :: .quoted p :: rest => do
      unless op == "!" || op == "?" do throw "expected ! or ?"
      return (⟨if op == "!" then .send else .recv, ch, ← parsePolicy p⟩, rest)
  | tokens => throw s!"expected communication action near {repr (tokens.take 3)}"

private partial def events (acc : List Event) : Parser (List Event)
  | .symbol "}" :: rest => pure (acc.reverse, rest)
  | tokens => do
      let (event, rest) ← parseEvent tokens
      match rest with
      | .symbol "," :: .symbol "}" :: _ => throw "trailing comma in action set"
      | .symbol "," :: tail => events (event :: acc) tail
      | _ => return ((event :: acc).reverse, (← expect "}" rest).2)

private def startsEvent : List Token → Bool
  | .word "rcfg" :: .symbol "(" :: _ => true
  | .word _ :: .symbol op :: _ => op == "!" || op == "?"
  | _ => false

mutual
  private partial def processExpr (minimum : Nat) (tokens : List Token) :
      Except String (Process × List Token) := do
    let (p, rest) ← processAtom tokens
    processRest minimum p rest

  private partial def processAtom (tokens : List Token) : Except String (Process × List Token) := do
    if startsEvent (tokens.dropWhile (· == .symbol "(")) then
      -- A parenthesized action and a grouped prefix differ at the closing token.
      match parseEvent tokens with
      | .ok (e, .symbol ";" :: rest) =>
          let (p, rest) ← processAtom rest
          return (.comm e p, rest)
      | _ => pure ()
    match tokens with
    | .symbol "(" :: rest =>
        let (p, rest) ← processExpr 0 rest
        return (p, (← expect ")" rest).2)
    | .quoted s :: .symbol ";" :: rest =>
        let (p, rest) ← processAtom rest
        return (.packet (← parsePolicy s) p, rest)
    | .word "zero" :: .symbol ";" :: rest =>
        let (p, rest) ← processAtom rest
        return (.packet .zero p, rest)
    | .word "delta" :: .symbol "{" :: rest =>
        let (set, rest) ← events [] rest
        let (p, rest) ← processExpr 0 (← expect "(" rest).2
        return (.restrict set p, (← expect ")" rest).2)
    | .word "pi" :: .symbol "{" :: rest =>
        let (depth, rest) ← natural rest
        let (_, rest) ← expect "}" rest
        let (p, rest) ← processExpr 0 (← expect "(" rest).2
        return (.project depth p, (← expect ")" rest).2)
    | .word "bot" :: rest => return (.bot, rest)
    | .word name :: rest =>
        if validName name then return (.ref name, rest)
        else throw s!"invalid process name '{name}'"
    | _ => throw s!"expected a process near {repr (tokens.take 3)}"

  private partial def processRest (minimum : Nat) (p : Process) (tokens : List Token) :
      Except String (Process × List Token) := do
    match tokens with
    | .symbol op :: rest =>
        let opInfo : Option (Nat × (Process → Process → Process)) :=
          match op with
          | "o+" => some (1, .choice)
          | "||" => some (2, .parallel)
          | "||<" => some (2, .leftMerge)
          | "|" => some (2, .commMerge)
          | _ => none
        let some (prec, combine) := opInfo | return (p, tokens)
        if minimum > prec then return (p, tokens)
        let (q, rest) ← processExpr (if op == "||<" then prec + 1 else prec) rest
        processRest minimum (combine p q) rest
    | _ => return (p, tokens)
end

def parseProcess : String → Except String Process := finish (processExpr 0)

private partial def selectorBody : Parser (List (List Event))
  | .word "@Program" :: rest => pure ([], rest)
  | .symbol "(" :: rest => do
      let (stages, rest) ← selectorBody rest
      return (stages, (← expect ")" rest).2)
  | .word "tail" :: .symbol "(" :: rest => do
      let (stages, rest) ← selectorBody rest
      let (_, rest) ← expect "," rest
      let (set, rest) ← events [] (← expect "{" rest).2
      unless set.all (fun e => e.direction == .rcfg) do
        throw "tail expects reconfiguration actions"
      return (stages ++ [set], (← expect ")" rest).2)
  | tokens => throw s!"expected @Program or tail near {repr (tokens.take 3)}"

private partial def selector : Parser Selector
  | .symbol "(" :: rest => do
      let (q, rest) ← selector rest
      return (q, (← expect ")" rest).2)
  | .word "head" :: .symbol "(" :: rest => do
      let (stages, rest) ← selectorBody rest
      return (⟨stages⟩, (← expect ")" rest).2)
  | _ => throw "expected head around the program selector"

def parseSelector : String → Except String Selector := finish selector

end DyNetKAT.Frontend.V11
