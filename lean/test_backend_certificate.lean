import DyNetKAT

open DyNetKAT.NetKAT

private def idRows : BackendRelation := fun p => {p}
private def emptyRows : BackendRelation := fun _ => ∅
private def ingress := NetKAT.fieldTest .port .v0
private def output := NetKAT.assign1 .port .v1
private def firewall := NetKAT.seq ingress output
private def firewallRows : BackendRelation := fun p =>
  if p .port = .v0 then {Packet.update p .port .v1} else ∅

#guard checkBackendRelation .id idRows
#guard checkBackendRelation .drop emptyRows
#guard checkBackendRelation ingress (fun p => if p .port = .v0 then {p} else ∅)
#guard checkBackendRelation output (fun p => {Packet.update p .port .v1})
#guard checkBackendEquivalent (.union .drop .id) (.test .pTrue) idRows
#guard checkBackendRelation firewall firewallRows
#guard checkBackendRelation (.star output) (fun p => {p, Packet.update p .port .v1})
#guard checkBackendCounterexample firewall .drop (Packet.update examplePacket .port .v0)

#guard !(checkBackendRelation .id emptyRows)
#guard !(checkBackendRelation .drop idRows)
#guard !(checkBackendRelation .id (fun p => {Packet.update p .port .v9}))
#guard !(checkBackendEquivalent .id .drop idRows)
#guard !(checkBackendCounterexample .id (.union .id .drop) examplePacket)
#guard (decodeBackendPacket [0, 1, 8]).isNone
#guard (decodeBackendRelation [([0, 1, 8, 9], [0, 1, 2, 9])]).isNone

private def wire := "{\"kind\":\"relation\",\"pairs\":[[[8,1,0,9],[0,1,0,9]]]}"

private def wirePolicy : NetKAT :=
  .seq (.completeTest (fun
      | .tpSrc => .v8 | .tpDst => .v1 | .swId => .v0 | .port => .v9))
    (.assign1 .tpSrc .v0)

#guard (decideWithBackend wirePolicy (.union wirePolicy .drop)
  (decodeBackendCandidate wire)).method == .checkedRelation
#guard (decideWithBackend .id .drop
  (decodeBackendCandidate "{\"kind\":\"counterexample\",\"input\":[8,1,0,9]}")).method == .checkedCounterexample
#guard (decodeBackendCandidate "{broken").isNone
#guard (decodeBackendCandidate "{\"kind\":\"equivalent\"}").isNone
#guard (decodeBackendCandidate "{\"kind\":\"relation\",\"pairs\":[[[8,1,0,9],[0,1,0,2]]]}").isNone
#guard (decideWithBackend .id .drop (some (.commonRelation idRows))).method == .exactFallback
#guard (decideWithBackend .id .id (some (.counterexample examplePacket))).method == .exactFallback
#guard (decideWithBackend .id .drop none).method == .exactFallback

example (h : (decideWithBackend wirePolicy (.union wirePolicy .drop)
    (decodeBackendCandidate wire)).equivalent = true) :
    ∀ σ τ, Semantics wirePolicy σ τ ↔ Semantics (.union wirePolicy .drop) σ τ :=
  (decideWithBackend_correct _ _ _).mp h

example (h : checkBackendCounterexample firewall .drop
    (Packet.update examplePacket .port .v0) = true) :
    ¬ ∀ σ τ, Semantics firewall σ τ ↔ Semantics .drop σ τ := by
  intro eq
  have no := checkBackendCounterexample_sound h
  rw [(netkatEquiv_correct _ _).mpr eq] at no
  cases no

-- Repeated compositions exercise the one-input witness path on larger syntax.
private def repeatedFirewall : Nat → NetKAT
  | 0 => firewall
  | n + 1 => .seq (.union .id .drop) (repeatedFirewall n)

private def benchmark : IO Unit := do
  let p := repeatedFirewall 96
  let q := NetKAT.star .drop
  let start ← IO.monoMsNow
  let checked := decideWithBackend p q
    (decodeBackendCandidate "{\"kind\":\"counterexample\",\"input\":[8,1,0,0]}")
  unless checked.method == .checkedCounterexample do throw (IO.userError "witness rejected")
  IO.println s!"one-input certificate: {(← IO.monoMsNow) - start} ms"
  let start ← IO.monoMsNow
  let exact := decideWithBackend p q none
  if exact.equivalent then throw (IO.userError "unexpected equivalence")
  IO.println s!"exact inequivalence fallback: {(← IO.monoMsNow) - start} ms"
  let start ← IO.monoMsNow
  unless netkatEquiv p firewall do throw (IO.userError "unexpected inequivalence")
  IO.println s!"exact equivalence: {(← IO.monoMsNow) - start} ms"
  let start ← IO.monoMsNow
  unless checkBackendEquivalent p firewall firewallRows do throw (IO.userError "relation rejected")
  IO.println s!"common relation check: {(← IO.monoMsNow) - start} ms"

/-- The optional backend round trip uses the same original policies on replay. -/
def main (args : List String) : IO Unit := do
  match args with
  | [] => benchmark
  | ["emit-witness"] => IO.println (KatchExport.counterexampleQuery firewall .drop)
  | ["emit-row"] => IO.println (KatchExport.relationRowQuery wirePolicy
      (fun | .tpSrc => .v8 | .tpDst => .v1 | .swId => .v0 | .port => .v9))
  | ["check-witness", file] =>
    let result := decideWithBackend firewall .drop
      (decodeBackendCandidate (← IO.FS.readFile file))
    IO.println s!"{repr result.method}: equivalent = {result.equivalent}"
  | ["check-relation", file] =>
    let result := decideWithBackend wirePolicy (.union wirePolicy .drop)
      (decodeBackendCandidate (← IO.FS.readFile file))
    IO.println s!"{repr result.method}: equivalent = {result.equivalent}"
  | _ => throw (IO.userError "expected emit-witness, emit-row, check-witness FILE, or check-relation FILE")

example {env : DyNetKAT.DyNetKAT.RecEnv} (rest : DyNetKAT.DyNetKAT.DyNetKAT)
    (h : (decideWithBackend firewall (.union .drop firewall) (some (.commonRelation firewallRows))).equivalent = true) :
    DyNetKAT.DyNetKAT.DerivesNoAIP env (.nSeq firewall rest) (.nSeq (.union .drop firewall) rest) :=
  .netkat rest (decideWithBackend_derives h)

/-- info: 'DyNetKAT.NetKAT.checkBackendRelation_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkBackendRelation_sound
/-- info: 'DyNetKAT.NetKAT.checkBackendRelation_normalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkBackendRelation_normalize
/-- info: 'DyNetKAT.NetKAT.checkBackendEquivalent_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkBackendEquivalent_sound
/-- info: 'DyNetKAT.NetKAT.checkBackendCounterexample_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkBackendCounterexample_sound
/-- info: 'DyNetKAT.NetKAT.decideWithBackend_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decideWithBackend_correct
/-- info: 'DyNetKAT.NetKAT.decideWithBackend_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decideWithBackend_history
/-- info: 'DyNetKAT.NetKAT.decideWithBackend_derives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decideWithBackend_derives
