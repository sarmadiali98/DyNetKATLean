import DyNetKAT
import Lean.Util.FoldConsts

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.PacketDependencyTests

open DyNetKAT.NetKAT

private def base : CtxPkt := fun _ => .v0
private def withPort (v : FieldValueEnum) : CtxPkt := Packet.update base .port v
private def setPort (v : FieldValueEnum) := NetKAT.assign1 (schema := ctxSchema) .port v
private def port (v : FieldValueEnum) := NetKAT.fieldTest .port v

private def path : NetKAT :=
  .union (.seq (port .v0) (setPort .v1)) (.seq (port .v1) (setPort .v8))

private def sparse : NetKAT := .seq (.completeTest base) (setPort .v1)

private def anyValue (f : FieldName) : NetKAT :=
  .union (.union (.assign1 f .v0) (.assign1 f .v1))
    (.union (.assign1 f .v8) (.assign1 f .v9))

-- Each input has four outputs, for 1,024 concrete pairs and one graph edge.
private def dense : NetKAT := anyValue .port

private def node := auxNode 0
private def loop : GProc := .ref node

private def graph (p : NetKAT) : ProcessGraph :=
  ⟨{node}, loop, fun _ => .nSeq p loop, by simp [loop, gprocRefs],
    by simp [loop, gprocRefs]⟩

private def candidate (p : NetKAT) : NormalizationCandidate 0 :=
  ⟨[node], fun _ => loop, fun _ => [(.packet p, 0)]⟩

private theorem graph_exact (p : NetKAT)
    (h : checkNormalization (graph p) (candidate p) = true) :
    ∃ (n : Nat) (C : NormalizationCandidate n), NormalizationExact (graph p) C :=
  (exists_exactNormalization_iff _).mpr (checkNormalization_finite h)

#guard checkNormalization (graph sparse) (candidate sparse)
#guard checkNormalization (graph dense) (candidate dense)

example (checked : checkNormalization (graph sparse) (candidate sparse) = true) :
    ∃ (n : Nat) (C : NormalizationCandidate n), NormalizationExact (graph sparse) C :=
  graph_exact sparse checked

example (checked : checkNormalization (graph dense) (candidate dense) = true) :
    ∃ (n : Nat) (C : NormalizationCandidate n), NormalizationExact (graph dense) C :=
  graph_exact dense checked

#guard match Internal.normalizeAndSafetyCheckGraph (graph sparse) (candidate sparse) ∅
    (.completeTest base) (port .v9) with
  | .ok result => result == ⟨.isZero true, .nonzero false⟩
  | .error _ => false

#guard match Internal.normalizeAndSafetyCheckGraph (graph dense) (candidate dense) ∅
    (.completeTest base) (port .v9) with
  | .ok result => result == ⟨.isZero false, .nonzero false⟩
  | .error _ => false

private def decisionNodes : KATLean.Native.Boolean.Diagram n → Nat
  | .leaf _ => 0
  | .skip rest => decisionNodes rest
  | .node low high => 1 + decisionNodes low + decisionNodes high

#eval show IO Unit from do
  for (name, p) in [("sparse", sparse), ("dense", dense)] do
    let diagram := symbolicNormalForm p
    let branches := ((candidate p).moves 0).length
    let size := KATLean.Native.Boolean.nodes diagram.1
    let decisions := decisionNodes diagram.1
    IO.println (s!"{name} graph: {size} diagram nodes, {decisions} decision nodes, " ++
      s!"{branches} packet-labelled edge")

#guard execute path base == .supported {withPort .v1}
#guard execute path (withPort .v8) == .supported ∅
#guard execute (.star path) base == .supported {base, withPort .v1, withPort .v8}
#guard execute (.star (.star path)) (withPort .v1) == .supported {withPort .v1, withPort .v8}

-- The pre-existing bounded evaluator is the concrete reference for a
-- supplied packet. Include the inner star separately from the nested case.
#eval show IO Unit from do
  for p in [path, .star path] do
    for σ in [base, withPort .v1, withPort .v8, withPort .v9, examplePacket] do
      unless execute (.star p) σ == boundedStar p (Fintype.card CtxPkt) σ do
        throw (IO.userError "supplied-packet execution disagrees with boundedStar")

-- Count rounds independently using the same one-step post operator. Include
-- the final round that observes equality, as the early-stop evaluator does.
private def countRounds (p : NetKAT) : Nat → Finset CtxPkt → Option Nat
  | 0, _ => none
  | fuel + 1, reached => do
      let next := reached ∪ (← (post p reached).outputs)
      if next = reached then some 1 else (countRounds p fuel next).map (· + 1)

#eval show IO Unit from do
  for (name, p, expected) in [("star", path, 3), ("nested star", .star path, 2)] do
    let start ← IO.monoNanosNow
    let result ← IO.mkRef (execute (.star p) base)
    let stop ← IO.monoNanosNow
    let some reached := (← result.get).outputs | throw (IO.userError "unsupported execution")
    let rounds := countRounds p 4 {base}
    unless reached.card == 3 && rounds == some expected do
      throw (IO.userError "unexpected reachable set or stabilization round")
    IO.println (s!"{name}: {reached.card} discovered packets, {expected} outer rounds, " ++
      s!"{stop - start} ns")

open Lean in
private partial def dependencies (env : Environment) (pending : List Name)
    (seen : Std.HashSet Name := {}) : Std.HashSet Name :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then dependencies env rest seen
    else
      let next := ((env.find? name).bind ConstantInfo.value? |>.map Expr.getUsedConstants)
        |>.getD #[] |>.toList.filter fun n =>
          let s := n.toString
          s.startsWith "KATLean." || s.startsWith "DyNetKAT." ||
            s.startsWith "_private.KATLean." || s.startsWith "_private.DyNetKAT." ||
            s.startsWith "_private.NetKATLean." || s.startsWith "_private.DyNetKATLean."
      dependencies env (next ++ rest) (seen.insert name)

open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if [`DyNetKAT.NetKAT.Legacy, `DyNetKAT.Experimental, `DyNetKAT.NetKAT.KATch,
        `DyNetKAT.NetKAT.BackendCertificate, `DyNetKAT.NetKAT.EquationalCertificate,
        `KATLean.Native.Explicit].contains mod then
      throwError "unexpected legacy or experimental module: {mod}"
  let executable := dependencies env [``execute]
  unless executable.toArray.any (fun n => n.toString.endsWith ".postWith") do
    throwError "missing supplied-packet post operator"
  -- The compiler-generated sizeOf instance mentions the syntax's default schema.
  for forbidden in [``ctxPkt_card, ``DyNetKAT.NetKAT.instFintypeCtxPkt] do
    if executable.contains forbidden then
      throwError "generic execute depends on the concrete schema via {forbidden}"
  let symbolicDecision := dependencies env [``netkatNativeEquivFinite]
  for required in [``PacketSchema.diagramLayouts, ``compileSymbolic] do
    unless symbolicDecision.contains required do
      throwError "missing finite-schema compiler dependency: {required}"
  for forbidden in [``ctxPkt_card, ``DyNetKAT.NetKAT.instFintypeCtxPkt, ``symbolicPairsFor,
      ``KATLean.NetKAT.Symbolic.Schema.acceptedPairs, ``execute] do
    if symbolicDecision.contains forbidden then
      throwError "finite-schema symbolic decision materializes packets via {forbidden}"
  let graphProof := dependencies env [``exists_exactNormalization_iff]
  for required in [``netkatIsZero, ``compileSymbolic] do
    unless graphProof.contains required do throwError "missing graph proof dependency: {required}"
  unless graphProof.toArray.any (fun n => n.toString.endsWith ".stepPacket_mem") do
    throwError "missing packet-prefix provenance proof"
  for forbidden in [``DyNetKAT.NetKAT.instFintypeCtxPkt, ``symbolicPairs, ``execute] do
    if graphProof.contains forbidden then
      throwError "graph proof materializes concrete packets via {forbidden}"
  let core := dependencies env [``netkatNativeEquiv_correct, ``exists_derives_pairSum,
    ``HeadNormalForm.packetHeads_correct, ``Program.normalizes, ``exists_exactNormalization_iff,
    ``exists_checkedNormalization_iff, ``normalizeCertifiedGraph_correct,
    ``Internal.normalizeAndSafetyCheckGraph, ``safetyCheckCertifiedGraph_correct,
    ``Program.Compiled.safety_correct, ``Program.Compiled.normalizedSafety_correct,
    ``execute_correct, ``reachableWithin_finite_stabilizes]
  if core.contains ``ctxPkt_card then throwError "core uses the concrete 256-packet cardinality lemma"
  let layering := dependencies env [``Equations.historySemantics_iff_nSeq_bisimilar,
    ``Program.historySemantics_iff_packetPrefix_bisimilar]
  for required in [``Step.cpol_seq_ok, ``nSeq_step_inv,
      ``historySemantics_iff_packetSemantics] do
    unless layering.contains required do
      throwError "missing semantic layering proof dependency: {required}"
  for forbidden in [``DyNetKAT.NetKAT.instFintypeCtxPkt, ``ctxPkt_card, ``symbolicPairs,
      ``execute, ``netkatNativeEquiv, ``compileSymbolic] do
    if layering.contains forbidden then
      throwError "semantic layering proof depends on {forbidden}"
  let traceTheory := dependencies env [``TraceSafety.Formula.equational_iff,
    ``TraceSafety.translate_trace_iff, ``Program.Compiled.trace_iff,
    ``TraceSafety.ExtendedRegexp.equational_iff_core, ``TraceSafety.eq28_iff_no_occurrence,
    ``TraceSafety.positiveAbsorption_iff_traces, ``graphTails_source_iff, ``graphHead_source_iff,
    ``projectedReachability_correct, ``normalizedReachability_correct]
  for required in [``TraceDerives.a16, ``TraceDerives.complete, ``TraceSafety.translate,
      ``Steps.cons] do
    unless traceTheory.contains required do
      throwError "missing trace safety proof dependency: {required}"
  let traceChecker := dependencies env [``TraceSafety.check, ``TraceSafety.checkPositive,
    ``projectedReachability]
  let traceCheckerProof := dependencies env [``TraceSafety.check_correct]
  for required in [``checkedMoves, ``execute] do
    unless traceChecker.contains required do
      throwError "missing trace checker dependency: {required}"
  for forbidden in [``DyNetKAT.NetKAT.instFintypeCtxPkt, ``ctxPkt_card] do
    if traceTheory.contains forbidden || traceChecker.contains forbidden then
      throwError "trace safety depends on the concrete packet universe via {forbidden}"
  -- Supplied-packet star correctness uses the abstract cardinality bound.
  unless traceCheckerProof.contains ``execute_correct do
    throwError "trace checker lacks the supplied-packet correctness proof"
  if traceCheckerProof.contains ``ctxPkt_card then
    throwError "trace checker proof uses the concrete 256-packet cardinality lemma"

  let projection := dependencies env [``WellFormed.project_exists_ground,
    ``renderProjection_derives, ``renderProjection_restricted_derives,
    ``Program.Compiled.renderProjection_derives, ``Program.Compiled.State.renderProjectionTotal_derives,
    ``Program.Compiled.State.renderProjectionMemo_derives]
  for required in [``DerivesNoAIP.projectZero, ``HeadNormalForm.project_correct,
      ``HeadNormalForm.packetHeads_correct, ``compileSymbolic, ``ground_complete,
      ``renderProjection_bisimilar, ``renderProjectionMemo_eq] do
    unless projection.contains required do
      throwError "missing projection derivation dependency: {required}"
  for forbidden in [``Derives.aip, ``approximation_induction,
      ``DyNetKAT.NetKAT.instFintypeCtxPkt, ``ctxPkt_card, ``execute, ``discoverClosure] do
    if projection.contains forbidden then
      throwError "projection derivation depends on {forbidden}"

#print axioms exists_exactNormalization_iff
#print axioms reachableWithin_finite_stabilizes
#print axioms execute_correct
#print axioms safetyCheckCertifiedGraph_correct
#print axioms Program.Compiled.safety_correct
#print axioms Program.Compiled.normalizedSafety_correct

end DyNetKAT.DyNetKAT.PacketDependencyTests
