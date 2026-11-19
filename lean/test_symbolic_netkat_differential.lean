import DyNetKAT.NetKAT.SymbolicDerives
import DyNetKAT.DyNetKAT.SafetyCheck
import Lean.Util.FoldConsts

namespace SymbolicNetKATDifferential

open DyNetKAT.NetKAT

private def p : NetKAT := .assign1 .port .v8
private def q : NetKAT := .assign1 .port .v9
private def t : NetKAT := NetKAT.fieldTest .port .v8

private def corpus : List (NetKAT × NetKAT) :=
  [(.drop, .drop), (.drop, .id), (.drop, .test .pFalse), (.id, .test .pTrue),
   (p, q), (p, .id), (p, .union p p), (t, .id),
   (.seq p q, q), (.seq p q, p), (.seq t p, t), (.seq p t, p),
   (.seq q t, .drop), (.union .id p, .star p), (.star p, .star q),
   (.star (.star p), .star p), (.union t p, p), (.seq .id t, t)]

#eval do
  for ((a, b), i) in corpus.zipIdx do
    let expected := legacyNetkatEquiv a b
    unless netkatEquiv a b == expected do
      throw (IO.userError s!"symbolic/legacy disagreement at case {i}")
  IO.println s!"{corpus.length} symbolic/legacy comparisons passed"

example (h : netkatNativeEquiv (.seq p q) q = true) : Derives (.seq p q) q :=
  (netkatNativeEquiv_iff_derives _ _).mp h

example (h : netkatNativeEquiv p q = false) : ¬ Derives p q :=
  netkatNativeEquiv_false_not_derives h

open Lean in
private partial def proofDependencies (env : Environment) (pending : List Name)
    (seen : Std.HashSet Name := {}) : Std.HashSet Name :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then proofDependencies env rest seen
    else
      let body := (env.find? name).bind ConstantInfo.value?
      let next := (body.map Lean.Expr.getUsedConstants).getD #[] |>.toList.filter fun n =>
        n.toString.startsWith "KATLean." || n.toString.startsWith "DyNetKAT." ||
        n.toString.startsWith "_private.KATLean." || n.toString.startsWith "_private.DyNetKAT."
      proofDependencies env (next ++ rest) (seen.insert name)

open Lean in
run_cmd do
  let env ← getEnv
  let used := proofDependencies env [``netkatNativeEquiv_iff_derives, ``netkatEquiv_correct,
    ``netkatIsZero, `DyNetKAT.DyNetKAT.netkatExistsNonempty]
  for n in [``derives_of_equiv_starFree, ``exists_derives_starFree_symbolic,
      ``KATLean.NetKAT.Symbolic.Schema.star_induction, ``Derives.paMatchAll, ``Derives.lfpR] do
    unless used.contains n do throwError "expected derivation dependency: {n}"
  for n in used do
    if [``legacyNetkatEquiv, ``netkatEquivAt, ``execute,
        ``packetList, ``normalize, ``normalize_derives, ``boundedPolicy,
        ``ctxPkt_card, `DyNetKAT.NetKAT.instFintypeCtxPkt,
        `KATLean.Native.Explicit.decideLanguageEquiv].contains n ||
        n.toString.endsWith ".enumerateFields" ||
        n.toString.startsWith "DyNetKAT.NetKAT.KATch" then
      throwError "exhaustive or experimental dependency: {n}"

#print axioms netkatEquiv_correct
#print axioms netkatIsZero_correct
#print axioms derives_of_equiv_starFree
#print axioms exists_derives_starFree_symbolic
#print axioms netkatNativeEquiv_iff_derives
#print axioms netkatNativeEquiv_false_not_derives

end SymbolicNetKATDifferential
