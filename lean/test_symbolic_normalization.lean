import DyNetKAT.NetKAT.Legacy
import DyNetKAT
import Lean.Util.FoldConsts

namespace SymbolicNormalizationTests

open DyNetKAT.NetKAT

private def base : CtxPkt := fun _ => .v0
private def port0 := NetKAT.fieldTest .port .v0
private def port1 := NetKAT.fieldTest .port .v1
private def setPort1 := NetKAT.assign1 (schema := ctxSchema) .port .v1
private def setPort8 := NetKAT.assign1 (schema := ctxSchema) .port .v8
private def setSwitch9 := NetKAT.assign1 (schema := ctxSchema) .swId .v9
private def firewall := NetKAT.seq port0 setPort1
private def path := NetKAT.union firewall (.seq port1 setPort8)
private def sparse := NetKAT.seq (.completeTest base) setPort1

private def booleanHeavy : NetKAT := .test
  (.pAnd (.pFieldEq ⟨.tpSrc, .v8⟩)
    (.pNot (.pOr (.pFieldEq ⟨.swId, .v1⟩) (.pFieldEq ⟨.port, .v9⟩))))

private def corpus : List (String × NetKAT) :=
  [("drop", .drop), ("identity", .id), ("field test", port0),
   ("assignment", setPort1), ("contradiction", .seq port0 port1),
   ("overwrite", .seq setPort1 setPort8),
   ("distinct fields", .seq setSwitch9 setPort1), ("union", path),
   ("composition", .seq firewall (.seq port1 setPort8)),
   ("star", .star path), ("nested star", .star (.star path)),
   ("Boolean-heavy", booleanHeavy),
   ("assignment-heavy", .seq (.seq setSwitch9 setPort1) (.seq setPort8 (.assign1 .tpDst .v1))),
   ("firewall", firewall), ("sparse", sparse)]

#guard (symbolicPairs (.seq port0 port1)).isEmpty
#guard (symbolicPairs sparse).length == 1

-- Compare ordered field observations to avoid repeatedly comparing packet closures.
private def observePair (pair : CtxPkt × CtxPkt) :
    List FieldValueEnum × List FieldValueEnum :=
  (NetKAT.fieldEnum.map pair.1, NetKAT.fieldEnum.map pair.2)

-- Time materialization before checking agreement, including multiplicities.
#eval show IO Unit from do
  for (label, p) in corpus do
    let start ← IO.monoNanosNow
    let diagram := symbolicNormalForm p
    let branches := symbolicSchema.acceptedPairs (fun _ => .v0) diagram
    let symbolicResult ← IO.mkRef (KATLean.Native.Boolean.nodes diagram.1, branches.length, branches)
    let symbolicEnd ← IO.monoNanosNow
    let legacy := legacyNetkatNormalForm p
    let legacyResult ← IO.mkRef (legacy.card, legacy)
    let legacyEnd ← IO.monoNanosNow
    let (nodes, branchCount, branches) ← symbolicResult.get
    let (legacyCount, legacy) ← legacyResult.get
    let actual : Multiset _ := branches.map observePair
    let expected := legacy.val.map observePair
    unless decide (actual = expected) do
      throw (IO.userError s!"normal forms disagree or contain duplicate branches for {label}")
    IO.println s!"{label}: nodes={nodes}, branches={branchCount}/{legacyCount}, \
      symbolic={symbolicEnd - start} ns, legacy relation={legacyEnd - symbolicEnd} ns"
  let start ← IO.monoNanosNow
  let rendered ← IO.mkRef (legacyNetkatNormalForm sparse).orderedPairs.length
  let stop ← IO.monoNanosNow
  unless (← rendered.get) == 1 do throw (IO.userError "legacy sparse branch count disagrees")
  IO.println s!"sparse legacy relation and Cartesian render={stop - start} ns"

open Lean in
private partial def proofDependencies (env : Environment) (pending : List Name)
    (seen : Std.HashSet Name := {}) : Std.HashSet Name :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then proofDependencies env rest seen
    else
      -- PA-MATCH-ALL uses a finite sum of values of a single field.
      let fieldValueSums := [``Derives.katSound, ``matchAll_katInterp,
        ``KATLean.NetKAT.PacketModel.match_all]
      let next := ((env.find? name).bind ConstantInfo.value? |>.map Lean.Expr.getUsedConstants)
        |>.getD #[] |>.toList.filter fun n =>
          let s := n.toString
          s.startsWith "KATLean." || s.startsWith "DyNetKAT." ||
            s.startsWith "_private.KATLean." || s.startsWith "_private.DyNetKAT." ||
            s.startsWith "_private.NetKATLean." ||
            (n == ``Finset.univ && !fieldValueSums.contains name)
      proofDependencies env (next ++ rest) (seen.insert name)

open Lean in
run_cmd do
  let env ← getEnv
  let normalization := proofDependencies env
    [``symbolicNormalize, ``netkatNormalForm, ``exists_derives_pairSum]
  let heads := proofDependencies env [``DyNetKAT.DyNetKAT.HeadNormalForm.packetHeads,
    ``DyNetKAT.DyNetKAT.Ground.exists_headNormalForm,
    ``DyNetKAT.DyNetKAT.WellFormed.normalizes, ``DyNetKAT.DyNetKAT.Program.normalizes]
  for n in [``KATLean.NetKAT.Symbolic.Schema.mem_acceptedPairs, ``exists_derives_starFree_symbolic,
      ``KATLean.NetKAT.Symbolic.Schema.star_induction, ``Derives.paMatchAllFor, ``Derives.lfpR] do
    unless normalization.contains n && heads.contains n do
      throwError "missing symbolic normalization dependency: {n}"
  unless heads.contains ``DyNetKAT.DyNetKAT.HeadNormalForm.packetHeads_correct do
    throwError "missing packet-head correctness dependency"
  for used in [normalization, heads] do
    for n in used do
      if [``legacyNetkatNormalForm, ``legacyNetkatNormalForm_mem, ``legacyNormalize, ``legacyNormalize_correct,
          ``NormalForm.orderedPairs, ``legacyNetkatEquiv, ``execute, ``packetList,
          ``derives_starFree_of_complete,
          ``boundedPolicy, ``ctxPkt_card, `DyNetKAT.NetKAT.instFintypeCtxPkt,
          `KATLean.Native.Explicit.decideLanguageEquiv, ``Finset.univ].contains n ||
          n.toString.endsWith ".enumerateFields" ||
          n.toString.startsWith "KATLean.Native.Explicit." ||
          n.toString.startsWith "DyNetKAT.NetKAT.KATch" ||
          n.toString.startsWith "DyNetKAT.NetKAT.BackendCertificate" then
        throwError "exhaustive or experimental dependency: {n}"

#print axioms KATLean.NetKAT.Guard.acceptingReps_sound
#print axioms KATLean.NetKAT.Guard.acceptingReps_complete
#print axioms KATLean.NetKAT.Symbolic.Schema.mem_acceptedPairs
#print axioms symbolicNormalForm_correct
#print axioms symbolic_normalize_correct
#print axioms symbolic_normalize_pairSum
#print axioms normalize_starFree
#print axioms normalize_derives_of_starFree_complete
#print axioms netkatNormalForm_mem
#print axioms normalize_derives
#print axioms exists_derives_pairSum
#print axioms DyNetKAT.DyNetKAT.HeadNormalForm.packetHeads_correct
#print axioms DyNetKAT.DyNetKAT.Ground.exists_headNormalForm
#print axioms DyNetKAT.DyNetKAT.guarded_normalizes
#print axioms DyNetKAT.DyNetKAT.WellFormed.normalizes
#print axioms DyNetKAT.DyNetKAT.Program.normalizes

end SymbolicNormalizationTests
