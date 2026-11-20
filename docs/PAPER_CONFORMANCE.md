# DyNetKAT paper conformance inventory

## Sources and edition crosswalk

The mathematical authority is [arXiv:2102.10035v4](https://arxiv.org/pdf/2102.10035v4),
22 May 2021, 38 pages. The comparison edition is the [Springer FoSSaCS 2022
chapter](https://link.springer.com/content/pdf/10.1007/978-3-030-99253-8_10.pdf),
LNCS 13242, pp. 184–204, DOI 10.1007/978-3-030-99253-8_10. The PDF bundled
with the v1.1 tool is a 22-page conference-style manuscript with its own
layout and examples. Use the Springer edition for published references.
Unqualified identifiers below refer to v4. Proposition 1, Lemma 3 and Theorem 1 retain their numbers. The other numbered definitions and lemmas follow the crosswalk.

| Subject | arXiv v4 | Springer chapter |
|---|---|---|
| Running examples | §I-A, Figs. 1–2, firewall and distributed controllers | §1 and Fig. 1, firewall |
| Packets and NetKAT | §II-A, Def. 1, Figs. 3–4 | §2.1, Def. 1, Fig. 2 for syntax and denotation. E_NK is referenced to Anderson et al. [3]. |
| Process syntax and examples | §II-C Eq. (1), Figs. 5–7 | §2.3 Eq. (1), Fig. 3 for firewall. Distributed-controller encodings are in v4. |
| Base SOS and example LTSs | §II-D Figs. 8–10 | §2.4 Fig. 4 gives packet, recursion, left choice/interleaving, a combined send/receive rule and both synchronization orientations. Right choice/interleaving are omitted. Fig. 5 is the firewall LTS. |
| Bisimilarity and layering | §III-A Def. 2, Prop. 1, Proof 1 | §3 Def. 2, Prop. 1, proof sketch |
| Extended SOS and grammar | Eqs. (2) δ, (3) π, (4) rcfg, (5) merges, (6) grammar | §3 gives extended operators, Eq. (2) is the extended grammar, and the separate formal SOS displays are omitted. |
| Congruence | Lemma 3, Proof 2 | Lemma 3, explicitly identifies the equivalence with stateless bisimilarity in the cited SOS format |
| Complete tests/assignments | Def. 4 | Unnumbered in §3 |
| NetKAT normalization | Lemma 5, Proof 3, Eqs. (7)–(8) | Lemma 4, proof sketch |
| DyNetKAT normal forms and guardedness | Defs. 6–7 | Defs. 5–6 |
| Finite branching | Lemma 8 | Unnumbered after Def. 6 |
| DyNetKAT normalization | Lemma 9, Proof 4 | Lemma 7 |
| Axioms and soundness | Fig. 11, Lemmas 10–11, Proofs 5–6, Eqs. (9)–(24), Appendix A Eqs. (36)–(129) | Fig. 6, Lemmas 8–9, short sketches. The extended proof appendix and numbered proof equations are omitted. |
| Soundness and ground-completeness | Theorem 1, Proof 7, Eq. (25) | Theorem 1, §3 proof |
| Safety syntax, hnf, translation | Defs. 12–14 and 17, §IV–IV-A | Def. 10 folds in sugars, Def. 11 folds in hnf and gives the translation as Eq. (3). The chapter presents one-letter negation by alphabet complement and refers to the longer desugaring definition. |
| Trace extension and safety | Defs. 15–16, Eqs. (26)–(27); Eq. (28) distributed controllers | Def. 12 combines trace extension and safety, then gives a firewall formula family |
| Extraction equations | §V Eqs. (29)–(33) | §5, unnumbered equations with the same cases |
| Extraction queries | Eqs. (34)–(35) are firewall initial zero and post-event **nonzero** | §5 Eqs. (4)–(5) use explicit π_n and **zero in both**, illustrating forbidden flow with all synchronization events. The later positive firewall example uses nonzero after the request, as in v4 (35). |
| FatTree | §V, Figs. 12–13 | §6, Figs. 7–8, same three property groups and scale |

There are technical issues in the source wording. The [proof ledger](PROOF_OBLIGATIONS.md)
records source wording and its Lean interpretation. The typed guardedness
audit below accounts for Definition 7's variable-in-payload clause. Other
issues include the printed merge and tail label metavariables,
the repeated term in one hnf equation, Definition 17's negation, and the
induction for Theorem 1 on recursive continuations. The FoSSaCS chapter
shortens several arguments and therefore does not resolve all of these.

## Core scope and import boundary

The paper-facing architecture follows the source grammar, `Program` /
reachable `Residual`, SOS, KATLean over Mathlib KA, dup-free NetKAT E_NK,
DyNetKAT E_DNK and certified analysis. `import DyNetKAT` exposes that core.
Its transitive source imports exclude KATch comparison and backend
certificate modules. `import DyNetKAT.Experimental` adds the preserved
optional exports. KATch supports external experiments, comparisons and
possible future acceleration. Core theorems and release criteria have no
KATch availability or replay requirement.

Full NetKAT with `dup` and its history-changing semantics is a supporting
extension outside current DyNetKAT scope. Existing dup-free history lemmas
still justify the packet-policy invocation in the SOS. Open full NetKAT
items in the inventory below are extension coverage gaps.

## Historical repository evidence

Audited working tree on `history-semantics`, HEAD
`bc5712a2d3113624afe878c8f14cf1fbe7f43d68`. A read-only remote ref lookup
confirmed that commit at `origin/history-semantics`. The last commit is the
graph-head checkpoint. The working tree additionally changes the library
imports, packet model/evaluator/decisions, process graph, graph safety and
process-graph regression. Graph moves, normalization, restriction and tail,
NetKAT axioms, the KATch bridge and their new regression files are untracked.
Thus statements below about those declarations describe local work. Compare
`git status --short` and the umbrella imports in
[DyNetKAT.lean](../lean/DyNetKAT.lean) before using any of those results as
release evidence.

**Evidence terms.** Implemented means a declaration exists. Proved means a
Lean theorem exists and its statement was checked at its stated domain.
Tested means the corresponding check was run on this working tree. Integrated
means imported by the umbrella library or callable through a named library
entry point. The executable is a separate entry point. Committed and pushed
refer to the pinned Git snapshots above.

`lake build DyNetKAT dynetkat` succeeded. All 18 `test_*.lean` files
checked individually and 16 Python auxiliary tests passed. The KATch
common-fragment corpus passed 18 differential comparisons. The test files
exercise history semantics and evaluation, NetKAT decisions and derivations,
AST head/tail/safety, graph correspondence and head/tail, normalization
admissibility, the firewall and an infinite derivative family. The executable
[Main.lean](../lean/DyNetKAT/Main.lean) prints the project name. The current
verification script builds the library and runs Python tests. Individual Lean
regressions and backend comparisons are extra invocations. See the [tool
audit](DYNETIKAT_REFERENCE_AUDIT.md#v11-feature-parity) for original artifact
evidence.

## NetKAT foundations

| Source | Mathematical item | Working-tree coverage | Remaining |
|---|---|---|---|
| Def. 1, §§II-A/C | A packet is a total valuation over finitely many fields, with natural-number values. The calculus uses a finite domain per field. Packet lists have ordered empty/cons constructors. NetKAT observes the head of a history. | `FieldName`, `FieldValueEnum`, `CtxPkt`, `Packet.update` in `Packet`; `History` is nonempty with a head and tail. `Config` uses possibly empty lists independently of NetKAT history inputs. | Arbitrary finite schemas with per-field domains. Clarify the NetKAT domain on which a head is required and DyNetKAT's singleton invocation. |
| Fig. 3 predicate grammar | False, true, field equality, disjunction, conjunction, negation. | `Predicate` and its evaluator. | General schema and typed elaboration. |
| Fig. 3 policy grammar and denotation | Tests return the original history or no result. Negation is complement inside the input singleton. Assignment updates only the head field. Choice is set union. Sequencing is Kleisli composition on the same packet history. Star is the union of all finite powers, including identity. Full NetKAT `dup` copies the head into the history. | `NetKAT`, `Semantics`, `HistorySemantics`, `execute`, `executeHistory`; dup-free `eval_correct`, `executeHistory_correct` and `historySemantics_singleton_iff_packetSemantics`. `execute_star_correct` proves unrestricted star closure on any finite schema. | Full supporting history calculus with dup and conservative inclusion of the dup-free fragment. DyNetKAT still uses the dup-free type. |
| Def. 4 | Complete test α is the product of all field equalities; complete assignment π is the product of all field updates. α and π encode packets; replace all tests by updates or vice versa for conversions. α·π denotes the singleton input/output pair. | `CompleteTest`, `CompleteAssignmentValuation`, `completeTestExpr`, `completeAssignExpr`, `holdsComplete_iff_eq`, `completeTestExpr_correct`, `completeAssignExpr_sem`, `ofSummand_sem` in `NormalForm.lean`, and packet valuation semantics. | General schema, canonical enumeration and the corresponding derivation lemmas. |
| Fig. 4 E_NK | KA, BA and PA, listed below. | `NetKAT/Axioms.lean` defines an actual `Derives` relation with congruence, refl/sym/trans and elaboration rules. `Derives.sound` and `Derives.historySound` are dup-free theorems over finite schemas. | Dup-free completeness follows from `normalize_derives` and pair-sum extensionality. The full history calculus and the relationship between full and restricted derivability remain open. |
| Lemma 5, Eqs. (7)–(8) | Dup-free policies admit a finite sum of complete test/assignment pairs, with derivable equality in E_NK. | Proved over finite schemas by `exists_derives_pairSum`, which packages executable `normalize`, pair-sum shape, and `normalize_derives` in the existing `Derives` relation. `normalize_history_correct` gives semantic equality. The existing symbolic compiler supplies the exact star fixed point. Accepting-path decoding emits the required branches, and the proof uses field-local packet algebra. The full history language-model development remains open. |
| §V decision queries | Empty packet relation for zero, equality of relations for dup-free equivalence. | `netkatNativeEquiv_correct` proves symbolic equivalence for the dup-free AST. The public zero and equality checks use the symbolic solver. `netkatNativeEquiv_iff_derives` uses per-field partition and symbolic star closure. | Extend the proof to future schema-generalized ASTs. |

The [KATLean foundation table](KATLEAN.md#ka-conformance-and-inequalities)
adds an algebraic account of all Figure 4 KA laws, the six BA laws and
the seven dup-free PA laws. `Derives.katSound` interprets the existing
fixed-domain derivations by direct rule induction in this algebra.
`Derives.sound` then transfers the equality through `katInterp_correct`.
The [rule audit](KATLEAN.md#derives-rule-audit) records all 40 constructors
and their proof sources. PA-DUP-FILTER-COMM remains
open in an optional full NetKAT history model.

### Figure 4 axiom inventory

Write `p ≤ q` for `p + q ≡ q`. Each row groups the printed equations by
family. Lowercase a, b, c denote tests.

| Rules | Equations or implications | Fixed-domain Lean constructors |
|---|---|---|
| KA-PLUS-ASSOC, COMM, ZERO, IDEM | Associativity, commutativity, identity 0 and idempotence of + | `plusAssoc`, `plusComm`, `plusZero`, `plusIdem` |
| KA-SEQ-ASSOC, KA-ONE-SEQ, KA-SEQ-ONE, both zero laws | Associativity of ·, two units 1 and two annihilators 0 | `seqAssoc`, `oneSeq`, `seqOne`, `zeroSeq`, `seqZero` |
| KA-SEQ-DIST-L/R | Distribute · over + on both sides | `seqDistL`, `seqDistR` |
| KA-UNROLL-L/R | `1+p·p* ≡ p*` and `1+p*·p ≡ p*` | `unrollL`, `unrollR` |
| KA-LFP-L/R | `q+p·r ≤ r ⇒ p*·q ≤ r`; `p+q·r ≤ q ⇒ p·r* ≤ q` | `lfpL`, `lfpR`; semantic `starLfpLeft`, `starLfpRight` |
| BA-PLUS-DIST, PLUS-ONE, EXCL-MID | `a+(b·c) ≡ (a+b)·(a+c)`, `a+1 ≡ 1`, `a+¬a ≡ 1` | `baPlusDist`, `baPlusOne`, `baExclMid` |
| BA-SEQ-COMM, CONTRA, SEQ-IDEM | Test product commutes, `a·¬a ≡ 0`, `a·a ≡ a` | `baSeqComm`, `baContra`, `baSeqIdem` |
| PA-MOD-MOD-COMM, PA-MOD-FILTER-COMM | Assignment commutes with assignment or test on another field | `paModModComm`, `paModFilterComm` |
| PA-MOD-FILTER, PA-FILTER-MOD, PA-MOD-MOD | Matching post-test after write is redundant. Matching write after test is redundant. Two writes to one field retain the last. | `paModFilter`, `paFilterMod`, `paModMod` |
| PA-CONTRA, PA-MATCH-ALL | Distinct tests on one field multiply to 0. Sum of its tests for all domain values equals 1. | `paContra`, `paMatchAll`; semantic `paContra_sem`, `paMatchAll_sem`. Domain here is {0, 1, 8, 9} at each field. |
| PA-DUP-FILTER-COMM | `dup·(f=v) ≡ (f=v)·dup` | Open in the full supporting NetKAT layer. This law has no instance in the dup-free grammar. |

The underlying [POPL 2014 NetKAT paper](https://doi.org/10.1145/2535838.2535862)
establishes full history-model completeness. Lemma 5 cites its language
model and completeness for dup-free endpoints. The fixed-domain Lean proof
derives normalization using the existing dup-free rules, with no appeal to
a conservativity theorem or an external decision procedure.
[Fixed-domain derivability regressions](../lean/test_netkat_normalization.lean).

## DyNetKAT syntax and SOS

Eq. (1) covers deadlock, NetKAT prefix, receive, send, parallel, choice and
named variables. Eq. (6) adds reconfiguration prefix, restriction, projection,
left merge and communication merge. `AST.lean` implements every listed form,
including finite choice via `choiceOf` and implicit trailing deadlock via
`policy`. `RecEnv.lookup` gives at most one body per name. Uniqueness and
closedness of accepted declaration lists are frontend obligations.

In the table, `H` is the pending packet list and `K` is the handled list.
`Action` implements packet pairs, send, receive and reconfiguration. The
relations are in `Semantics.lean` and `ProcessGraph.lean`. Packet cases
use fixed-domain NetKAT history semantics.

| Paper SOS rule | Premise, label and configuration effect | Lean constructor |
|---|---|---|
| Fig. 8 deadlock | No transition | No constructor; `deadlock_no_step` |
| Fig. 8 packet prefix | N maps singleton σ to singleton τ, input σ::H. Emit (σ,τ), continue with D, H, τ::K. Failure or empty pending list enables no packet step. | `cpol_seq_ok` |
| Fig. 8 variable | X has a unique body and that body can step. Copy the action, successor and both lists. Unfolding itself consumes no action. | `cpol_var` |
| Fig. 8 choice L/R | Either side can step. Take its label, successor and lists. | `cpol_choice_l/r` |
| Fig. 8 parallel L/R | Either side can step. Retain the other side in parallel and copy label and lists. | `cpol_par_l/r` |
| Fig. 8 receive/send | No premise. Emit x?N or x!N, continue with D and the same lists. | `cpol_recv/send` |
| Fig. 8 synchronization, both orders | Complementary steps with identical channel and payload, both preserving the same lists. Emit rcfg(x,N), continue with both residuals in parallel. | `cpol_sync_recv_send/send_recv` |
| Eq. (2) restriction | Copy allowed step and wrap successor in the same δ. Only declared send/receive labels can be blocked. Packet and rcfg labels pass. | `cpol_restrict` |
| Eq. (3) projection | At depth n+1, copy a step and continue under depth n. Depth 0 has no step. | `cpol_project`, `project_zero_no_step` |
| Eq. (4) rcfg | No premise. Emit rcfg(x,N) and continue with unchanged lists. | `cpol_rcfg` |
| Eq. (5) left merge | First step of the left operand with its lists and label. Continue with its residual in parallel with the right operand. | `cpol_left_merge` |
| Eq. (5) communication merge, both orders | Only a matched handshake as in parallel. Both residuals run in parallel. The payload r in the premises determines rcfg(x,r), as in Fig. 8 and A12. | `cpol_comm_merge_recv_send/send_recv` |

The last rule reads the printed `rcfg(x,p)` in Eq. (5) as a metavariable
error. The same payload appears in both premises and A12. The uniform Lean AST reads the extended
grammar's `N;D` with an extended continuation, as used by its equations.
`PaperSyntax true` separately checks the printed continuation sort.
Per-packet consistency is the design property that a single
step invokes one NetKAT policy to completion. There is no numbered
per-packet-consistency theorem. `NetKATBridge` connects the packet rule
to the evaluator, and `packetTransitions_sound/complete` cover the
standalone packet-prefix executable.

## Recursion, semantic results and algebra

| Source | Statement and assumptions | Working-tree coverage and gap |
|---|---|---|
| §II-C, Fig. 8 | Named recursive equations, one definition per referenced name. Variables inherit a body's steps. | `RecEnv` enforces at most one body. `ClosedDefined.existsUnique_lookup` proves exactly one body for each reachable name. `cpol_var` inherits the looked-up body's transition. |
| Def. 7 | Every variable occurrence must be guarded. Clause (i) places the occurrence in the continuation of a sequence with a variable-free or itself guarded prefix. Clause (ii) mentions `y?X;t`, `y!X;t` and `rcfg_{X,t}`. | `typedPaperGuarded_iff_guardedOccurrences` proves the typed occurrence-path interpretation. `wellFormed_iff_closedDefined_and_typedPaperGuarded` checks reachable **bodies**. See the typing audit below for the literal clause. |
| Lemma 8 | Finite branching of guarded policies, including reachable derivatives. | `WellFormed.finite_targets_from` bounds immediate source targets uniformly over actions and packet lists at every reachable `CtxPkt` state, with arbitrary restriction sets and no finite-support hypothesis. The executable `finite_branching_supported` route remains available. |
| Def. 2 | Symmetric relation on policies. Match every step from every initial list pair with the same action and final lists, and relate the derivatives. Bisimilarity is the largest such relation. | `IsBisimulation`, `Bisimilar`, refl/sym/trans under a shared environment. Graph `GBisimilar` uses a shared graph. `GraphBisimilarBetween` compares two closed graphs. `gbisimilar_iff_bisimilar` and `compileGraph_bisimilar_iff` give a shared-source-environment bridge under correspondence/support. Cross-environment closure and name independence remain open. |
| Prop. 1 | Equal NetKAT denotations iff `p;d ∼ q;d` for each continuation d. | Machine checked by `Equations.historySemantics_iff_nSeq_bisimilar` for dup-free `CtxPkt` policies in any fixed `RecEnv`. `Program.historySemantics_iff_packetPrefix_bisimilar` gives the admitted version with the base continuation sort. |
| Lemma 3 | Bisimilarity is a congruence for process operators. | Fixed-environment congruence is proved per constructor in `Bisimulation` for process operands of four prefixes, parallel, choice, both merges, δ and π. Recursive binding congruence remains open. Payload labels require special care when importing E_NK. |
| Def. 6 | A finite choice of complete packet prefixes α·π or send, receive and rcfg prefixes, with arbitrary continuations and optional deadlock. | `HeadNormalForm` and `IsDNKNormalForm` represent this algebraic form. `HeadNormalForm.step_iff` recovers an exact head and continuation from a rendered SOS transition. |
| Lemma 9 | E_DNK derives equality from a guarded policy to a Def. 6 normal form. | Proved for the typed `CtxPkt` domain by `guarded_normalizes` in `DerivesNoAIP`. `WellFormed.normalizes` extends the result to closed entry terms with exposed references, by the fixed-environment unfolding rule. Both retain arbitrary continuations. The packet-prefix case emits the exact atomic heads from accepting symbolic paths using Lemma 5. The syntactic hypothesis is equivalent to `TypedPaperGuarded`. |
| Lemma 10, Appendix A | Every derivation in E_DNK without AIP implies bisimilarity. Includes A0–A15 and δ/π equations. | `DerivesNoAIP.sound` proves soundness of the typed rules below in a fixed environment. |
| Eq. (3), Fig. 11 Π rules and Lemma 9 | A positive projection takes one source step and projects the derivative one depth lower. The equations reduce zero and projected deadlock to deadlock, distribute over choice, and move successor projection under an atomic prefix. | `WellFormed.project_exists_ground` iterates the Lemma 9 head form and the Π rules to derive a ground term at each finite depth. `renderProjection_derives` identifies that ground term with the actual certified rendering by `ground_complete`. The executable renderer is a Lean integration of these paper results. |
| Lemma 11, Eqs. (20)–(24) | Bisimilarity at every finite projection implies bisimilarity through descending sets of matching successors. | `Derives.aip` uses full derivation premises at every depth and reachable image finiteness at both endpoints. `Derives.sound` supplies premise soundness recursively and invokes `approximation_induction`. `Derives.aip_guarded` supplies image finiteness from `WellFormed`. |
| Theorem 1, Eq. (25) | Soundness and ground completeness for strong bisimilarity. Proof 7 derives both choice absorptions by matching summands and comparing continuations. | `ground_derives_iff_bisimilar` proves the characterization for variable-free `CtxPkt` processes in any fixed environment. `ground_complete` derives the reverse direction without AIP. Soundness includes nested AIP and has no ground hypothesis. |

The projection derivation uses the printed equations at the algebraic
level. The admitted wrappers take a `Program` or reachable `Residual`
as the source. The result concerns the generated finite rendering in
`DerivesNoAIP`, whose internal syntax can place a projected continuation
under an atomic prefix as in Figure 11.

Proposition 1 compares `NetKAT.HistorySemantics` on all input and output
histories. The forward implication matches `Step.cpol_seq_ok` transitions
using singleton histories. The reverse implication inverts matching steps
and uses the history-to-packet bridge, which preserves history tails, to
recover equivalence on every history. The continuation is shared and may
be recursive. The admitted version requires its reachable declarations to
satisfy the existing sorting and guardedness checks. Communication payloads
retain syntactic equality.

### Definition 7 typed guardedness

The §II-C base grammar in Eq. (1) has process forms
`⊥ | N;D | x?N;D | x!N;D | D∥D | D⊕D | X`. Here `N` is dup-free
NetKAT, `x` is a channel name, and `X` is a recursive process variable.
Equation (6) adds `rcfg_{x,N};Dₑ`, `δ_L(Dₑ)`, `π_n(Dₑ)`, and both
merges. It prints the packet-prefix continuation as `D`; Lean's
`nSeq` takes the same extended process type as the other continuations.
The payload sort remains dup-free NetKAT. Lean represents `X` by `DyNetKAT.var : Var → DyNetKAT`. Each of
`recv`, `send` and `rcfgPrefix` has type
`Channel → NetKAT → DyNetKAT → DyNetKAT`. The NetKAT AST has no
process-variable constructor. `Channel` and `Var` both use strings for
names, so a shared spelling in a channel is a channel name and does not
denote a recursive occurrence.

Clause (i) talks about the continuation of a sequence with a variable-free
or already guarded prefix. The packet-policy operand in the typed grammar
has no process variables. Clause (ii)'s printed `y?X;t` and `y!X;t`
place a process variable in a NetKAT payload position, and `rcfg_{X,t}`
places it in a channel position. A reconfiguration payload also has the
NetKAT sort. These positions cannot contain `DyNetKAT.var`. Figure 5
shows the well-typed communication pattern with a NetKAT payload and
recursive calls in the process continuation. The typed interpretation
counts all four prefix continuation edges and adds no variable form to the
payload or channel grammar.

`TypedPaperGuarded` excludes any `ProcessVarOccurrence` path whose
prefix-crossing flag is false. Deadlock has no paths. A variable has an
unprefixed path. Packet, send, receive and reconfiguration set the flag
to true. Both operands of choice, parallel and both merges retain their
flags, as do the operands of restriction and projection. The equivalence
with `GuardedOccurrences` is proved by constructor induction. This is a
theorem about the typed reading. The printed ill-sorted clause has no
literal AST interpretation.

`Defined` tests direct names from `recursiveVars`. `ReachableVar`
starts with those names and follows occurrences in each looked-up body.
`RecEnv = Var → Option DyNetKAT` gives at most one body per name.
`ClosedDefined` supplies existence throughout the reachable closure.
`WellFormed` adds typed guardedness of each reachable body. Names outside
the closure may be undefined. The source rule `cpol_var` uses the body
from lookup and inherits its step with the same action and packet lists.
The Figure 5 fixture checks guarded bodies for Host and Switch and
well-formedness of the entry `Host ∥ Switch`, which has unprefixed
occurrence paths. This is environment-level packaging of guarded equations.

### Source grammar and SOS residual closure

`PaperSyntax false` recognizes Eq. (1). `PaperSyntax true` recognizes the
printed Eq. (6), including the Eq. (1) continuation immediately below a
packet prefix. The FoSSaCS Eq. (2) repeats that sort. The repository also
supports the uniform extended grammar in which a packet prefix can have an
extended continuation. For example, A10 permits a packet prefix with a parallel
continuation and Definition 6 gives packet heads policy continuations.
`WellFormed` operates over that uniform AST. The literal-sort theorems and
the uniform-AST theorem both use the same SOS.

`paperAdmissible_iff` checks the entry's grammar and a unique,
syntactically admitted, typed-guarded body for every reachable name.
The firewall's `Init` names a composite entry, with its component names
resolved by their guarded equations. This entry convention follows Fig. 5.
The Eq. (1) and Eq. (6) residuals stay in their respective grammars
(`Step.preserves_paperAdmissible`). The defining equations keep their
guardedness while a residual can expose reference occurrences. The
algebraic head normal form of Definition 6 describes a representation of
available actions, with arbitrary policy continuations. The SOS uses
ordinary process terms as residuals.

`Steps.preserves_paperAdmissible` covers finite traces with consistent
packet lists. `PaperAdmissible.reachable` covers the stateless
`ProcessStep` reachability used for bisimulation and AIP, where each
edge can choose packet lists independently. `GSteps.preserves_paperAdmissible`
transfers to a source representative under the existing `Corr`.
The source theorems need no finite-support hypothesis.

A source grammar is a formation judgment. An admissible program also
satisfies the recursive declaration conditions. A reachable residual has
a finite SOS path from a particular admitted entry. The reachability lift
admits the empty path and preserves the fragment and environment. A raw
Lean AST with the right constructor shape can still fail the recursive
declaration or reachability condition.

| Raw Lean AST constructor | Paper source formation | SOS residual and public construction |
|---|---|---|
| `deadlock` | Eq. (1), Eq. (6) | Can be an entry, exposed continuation or retained operand. No outgoing step. |
| `nSeq` | Both, with a dup-free packet policy and Eq. (1) continuation | The step exposes the continuation. A residual can contain a packet prefix inherited from its source or a defining body. An immediate extended-only continuation under `nSeq` is rejected even in printed Eq. (6). |
| `recv`, `send` | Both, with channel and dup-free payload. Continuation in the chosen fragment | A step exposes the continuation. A synchronized step retains both continuations in parallel. |
| `parallel` | Both, with two terms in the chosen fragment | Interleaving, synchronization and merge rules produce parallel terms. An exposed reference operand is allowed at an entry or in a residual. An exposed occurrence in a defining body still needs an enclosing prefix. |
| `choice` | Both, with two terms in the chosen fragment | A choice step takes the selected branch's residual. Choice may survive in a continuation or retained operand. |
| `var` | Both, with a unique guarded reachable definition | The variable inherits a step of its body. A prefix can expose a variable and does not unfold it as a separate action. |
| `rcfgPrefix` | Eq. (6), with channel, dup-free payload and extended continuation | A step exposes the continuation. Synchronization can emit the same label from Eq. (1) without creating a reconfiguration prefix. |
| `restrict` | Eq. (6), with a set of communication labels and an extended operand | A step retains the wrapper around the residual. |
| `project` | Eq. (6), with a natural depth and an extended operand | A step retains the wrapper with one less unit of depth. Depth zero has no outgoing step. |
| `leftMerge`, `commMerge` | Eq. (6), with two extended operands | A merge step creates a parallel residual. A merge can occur in an inherited term. |
| `GProc.ref`, auxiliary node IDs, checked rows and generated model tables | Internal helper syntax | No direct paper source constructor. Compiled states require source correspondence and an SOS reachability witness. |

All source constructors in the table can be constructed through `Program`
with proof of admissibility. The selected grammar has no constructor
reserved solely for residuals. The authoritative API exposes reachable
states as `Program.Residual` and `Program.Compiled.State`. Packet-list
traces enter via `Program.afterTrace`. Symbolic enumeration returns an exact
row, and a realization of an edge yields a state with both reachability
proofs through `State.successor`.

| Fixture | Grammar and residual classification |
|---|---|
| Author example `X ≜ (a!1;⊥) ∥ X` | Eq. (1) raw syntax. Rejected as a program in either grammar by `rejects_unguarded_parallel`. The path to the right-hand `X` never passes through a prefix. |
| Original spawning `X ≜ rcfg(a,1);(X ∥ rcfg(b,1);⊥)` | Admitted by printed Eq. (6). The reconfiguration prefix puts it outside Eq. (1). Each `spawnState n` corresponds to a legitimate residual of this source. Existing regressions give infinitely many derivatives, no finite strong quotient and a checked forward abstraction for a specific property. |
| Deadlock-spawning in `test_finite_abstraction.lean` | Admitted by Eq. (6), using `rcfg(tick,1);(X ∥ ⊥)`. The `grow n` graph states are reachable from its compiled source. They are syntactically distinct and admit a one-state strong quotient. |
| Send-only deadlock-spawning in `test_paper_domain.lean` | Admitted by Eq. (1), using `a!1;(X ∥ ⊥)`. `base_admissible_infinite_derivatives` proves there are infinitely many admissible SOS residuals even with empty packet lists and one defining equation. |
| Mutual recursion | The packet-prefix pair in `test_graph_head.lean` and the send/receive pair in `test_paper_domain.lean` use Eq. (1). The reconfiguration-prefix mutual strategy in `test_finite_certificates.lean` uses Eq. (6) and has a checked finite concrete closure. |
| Firewall | The Fig. 5 source fixture `rawInit` is Eq. (1), with `Host`, `Switch` and `SwitchOpen` declarations. Its externally restricted and projected versions use Eq. (6). The two-mode normalized safety fixture uses Eq. (6) reconfiguration prefixes. |
| Infinite name chain `infEnv` | Admitted by the Eq. (1) grammar and local guarded-equation discipline. It models infinitely many declarations and has no finite support for graph compilation. A finite declaration file is a separate executable input condition. |
| Administrative aliases and synthetic graph certificates | An entry alias such as the firewall's expanded `Init` is permitted. A reachable unprefixed alias stored as a recursive equation fails Definition 7. Analysis of such raw environments, or abstract graph tables without a source correspondence, is a generalization. |

The author feedback excludes the exposed recursive operand in
`(a!1;⊥) ∥ X`. Equation (1) explicitly allows a parallel continuation and
Definition 7 guards occurrences beneath a prefix. Hence `a!1;(X ∥ ⊥)`
passes both checks. The corresponding Eq. (6) reconfiguration prefix
also guards its continuation. Neither printed rule imposes a fixed
parallel width or a flat tail-call grammar. Infinite reachability on
these fixtures follows from the constructor and step proofs.

The abstraction fixture audit also covers the following cases.

- The original spawning forward simulation represents reachable
  mixtures of live blockers and spent deadlocks. A sequence of spawn
  steps creates the desired number of positions, and blocker actions
  consume any chosen positions. Its abstract looping table permits
  extra traces for overapproximation.
- The one-state deadlock-spawning quotient represents precisely the
  reachable `grow n` family. The missing-edge, wrong-target and invented-edge
  tests are negative certificate tests for that admitted source.
- The identity loop, opaque restricted graph and deliberately incorrect
  payload or packet tables are internal certificate-and-label tests.
  The restricted deadlock's shape is permitted as an Eq. (6) source,
  while its synthetic graph fixture supplies no paper program provenance.
- A candidate supplied to the public strategy is intersected with
  graph states reachable from the analyzed entry or residual. An
  auxiliary abstract state or an unrealizable symbolic row target
  does not become a concrete residual.

Lemma 8 gives local finite branching. The two growth fixtures establish a
separate fact about the size of the transitive closure. Exact finite-depth
projection remains a paper-core route. Finite concrete closures, simulation
and strong quotients are certified tool extensions for all-depth analysis
of admitted programs when the corresponding certificates exist. They also
apply beyond the paper domain under their own hypotheses.

| Result | Lean hypotheses |
|---|---|
| Lemma 8, `WellFormed.finite_targets_from` / `WellFormed.imageFiniteFrom` | `WellFormed` at the initial root. No finite support or executable restriction classifier. |
| Lemma 9, `guarded_normalizes` | `GuardedOccurrences` of the term, equivalently `TypedPaperGuarded`. |
| Environment-aware normalization, `WellFormed.normalizes` | `WellFormed` at the root, including exposed references. |
| Executable guarded moves, `guardedMoves_toGraph_source_exact` | `WellFormed`, `FiniteSupport`, correct classifiers at active restriction sites. |
| Finite-depth projection, `renderProjection_source` | `WellFormed`, `FiniteSupport`, correct restriction classifiers for the root and reachable bodies. |
| Semantic AIP, `approximation_induction` | `ImageFiniteFrom` at both endpoints. `WellFormed.imageFiniteFrom` supplies it. |
| Full AIP soundness, `Derives.sound` | A full derivation, whose AIP nodes carry image finiteness. `Derives.aip_guarded` supplies that evidence from `WellFormed` endpoints. |
| Theorem 1 ground completeness, `ground_complete` | `Ground` on both terms, meaning `recursiveVars = ∅`, and bisimilarity. The soundness direction has no groundness or recursive-environment guardedness premise. |

### Figure 11 and A16

Here `a` may be any dup-free policy prefix or a communication/reconfiguration
prefix. `at` is a complete α·π or a communication/reconfiguration prefix.
These are distinct quantifications in the figure. The symbols `⊕`, `∥`,
`⊳` and `|` stand for choice, parallel, left merge and communication merge.

| Axiom | Equation or rule | Lean evidence or obligation |
|---|---|---|
| A0 | `0;p ≡ ⊥` | `DerivesNoAIP.a0`. `a0_sound` by empty NetKAT history semantics. |
| A1 | `(z+y);p ≡ z;p ⊕ y;p` | `DerivesNoAIP.a1`. `a1_sound` by union of history relations and exact packet-step reconstruction. |
| A2 | `p⊕q ≡ q⊕p` | `DerivesNoAIP.a2`. `a2_sound` by choice inversion. |
| A3 | `(p⊕q)⊕r ≡ p⊕(q⊕r)` | `DerivesNoAIP.a3`. `a3_sound` by choice inversion. |
| A4 | `p⊕p ≡ p` | `DerivesNoAIP.a4`. `a4_sound` by choice inversion. |
| A5 | `p⊕⊥ ≡ p` | `DerivesNoAIP.a5`. `a5_sound` by choice inversion and deadlock. |
| A6 | `p∥q ≡ q∥p` | `DerivesNoAIP.a6`. `a6_sound` by coinduction, swapping operands and synchronization orientations. |
| A7 | `p∥⊥ ≡ p` | `DerivesNoAIP.a7`. `a7_sound` by coinduction on the surviving component. |
| A8 | `p∥q ≡ p⊳q ⊕ q⊳p ⊕ p\|q` | `DerivesNoAIP.a8`. `a8_sound` matches the SOS cases, using A6 for the right interleaving target. |
| A9 | `⊥⊳p ≡ ⊥` | `DerivesNoAIP.a9`. `a9_sound` by inversion of the left premise. |
| A10 | `(a;p)⊳q ≡ a;(p∥q)` | `DerivesNoAIP.a10`. `a10_sound` uses prefix inversion for all four `MoveLabel` cases. |
| A11 | `(p⊕q)⊳r ≡ (p⊳r)⊕(q⊳r)` | `DerivesNoAIP.a11`. `a11_sound` by choice and left-merge inversion. |
| A12 | `(x?z;p)\|(x!z;q) ≡ rcfg(x,z);(p∥q)` | `DerivesNoAIP.a12`. `a12_sound` uses the same syntactic channel and payload. `a12_reverse` derives the reverse orientation via A14 and A6. |
| A13 | `(p⊕q)\|r ≡ (p\|r)⊕(q\|r)` | `DerivesNoAIP.a13`. `a13_sound` distributes the left choice through both synchronization rules. |
| A14 | `p\|q ≡ q\|p` | `DerivesNoAIP.a14`. `a14_sound` swaps both synchronization orientations and uses A6 for targets. |
| A15 | `p\|q ≡ ⊥` [otherwise] | `DerivesNoAIP.a15`. `a15_sound` proves deadlock from `CommMismatch`: Appendix A (96)–(100) and the deadlock operand case. The complementary mismatch requires unequal channels or unequal syntactic payloads. Swap operands with A14. |
| δ⊥, δ;, δ;⊥, δ⊕ | δ preserves deadlock; passes an allowed prefix with restricted continuation; maps a forbidden prefix to deadlock; distributes over choice. | `restrictDeadlock`, `restrictAllowed`, `restrictBlocked`, `restrictChoice`. The prefix rules require `AtomicPrefix` and the corresponding `PrefixBlocked` test. Soundness reuses the restriction SOS theorems. |
| Π0, Π⊥, Π;, Π⊕ | π₀ is deadlock; every π of deadlock is deadlock; a prefix consumes one from positive depth; projection distributes over choice. | `projectZero`, `projectDeadlock`, `projectPrefix`, `projectChoice`. The prefix rule requires `AtomicPrefix` at successor depth. Soundness reuses the projection SOS theorems. |
| AIP | If `π_n(p) ≡ π_n(q)` for all n, derive `p ≡ q`. | `Derives.aip`, with `ImageFiniteFrom` at each endpoint and full `Derives` premises for every n. `WellFormed.imageFiniteFrom` supplies the side condition on the guarded source domain. |
| A16, Eq. (26) | `a;(q⊕r) ≡ a;q ⊕ a;r` in the trace extension. Here a is a well-typed prefix. | `TraceDerives.a16` in `TraceEquations.lean`. `trace_a16` and `TraceDerives.sound` prove trace soundness with the original action labels. `TraceDerives.complete` uses A16 to distribute each finite projection into a sum of words, then applies AIP. |

The Fig. 11 reference to E_NK is represented by `DerivesNoAIP.netkat`, which imports a `NetKAT.Derives` proof only at a packet prefix. `DerivesNoAIP.unfold` gives equational use of the named definitions surrounding Figure 11. It requires a successful lookup in the fixed recursive environment, following the variable SOS, and is separate from the printed Figure 11 axiom list. For instance,
`z ≡ z+0` at the NetKAT level can replace a packet prefix by Prop. 1.
Substituting it into a send prefix would change the action label under the
current and printed syntactic payload matching. See the [proof
ledger](PROOF_OBLIGATIONS.md#algebra-and-completeness).

## Safety-property theory

| Source | Mathematical item | Current coverage |
|---|---|---|
| Def. 12 | Alphabet 𝒜 consists of complete packet-transform letters α·π and rcfg(x,p). Expressions are letters, union and concatenation. The formula `[r]false` forbids a trace starting with a word of r. | **Formalized.** `TraceSafety.Letter`, `Alphabet`, `Formula`, `Regexp.Matches` and `Safe` in `TraceSafety.lean`. Consumed by Defs. 13–14 and 16. |
| Def. 13 | A word is a nonempty sequence over 𝒜. Prefix includes equality. `hnf` gives a finite sum of words using two-sided distributivity. | **Formalized.** `Regexp.hnf`, `Regexp.mem_hnf`, `Regexp.hnf_nonempty_word` and `Regexp.hnf_inAlphabet` in `TraceSafety.lean`. Consumed by Def. 14(c2). The printed left-distributivity line repeats the first branch. The implementation distributes to both branches, as required by word-language union. |
| Def. 14 | Let W = hnf(r) and M be its longest word length. Sum `w;⊥` for permitted shorter words and `w;⊥ ⊕ w;Θ` for permitted length-M words. Θ is guarded and sums both stopping and continuing for each letter. | **Formalized.** `branches` and `translate` in `TraceSafety.lean` build the sums as an admitted extended program. Guarded names stand for suffixes to satisfy the packet continuation sort of Eq. (6). `translate_trace_iff` proves exact avoidance of forbidden prefixes over the supplied finite alphabet. The empty sum forbids no word and uses M = 0. Consumed by Def. 16. |
| Def. 15, Eq. (26) | E_DNK^tr extends Fig. 11 with A16, distribution of a prefix over a choice of continuations. | **Formalized.** `TraceDerives`, `trace_a16` and `TraceDerives.iff_traces` in `TraceEquations.lean`. Trace congruence includes parallel, both merges, restriction and projection. Completeness uses the existing typed Fig. 11 rules and AIP over all depths for closed guarded terms. Consumed by Eq. (27). |
| Def. 16, Eq. (27) | A network i is safe if E_DNK^tr derives `⟦s⟧⊕i ≡ ⟦s⟧`. This corresponds to trace inclusion in the translation. | **Formalized.** `EquationalSafety`, `safe_iff_trace_inclusion` and `Formula.equational_iff` in `TraceSafety.lean`. Both endpoints are admitted and share a declaration system via trace-preserving recursive renaming. `UsesAlphabet` requires the network's observed traces to lie in 𝒜, including all packet pairs and syntactic reconfiguration labels actually observed. No global finite derivative closure is required. |
| Def. 17 | Extended actions are packet or reconfiguration literals or negated extended actions. Extended expressions add `true`, union, concatenation and positive repetition. | `PrintedAction` and `PrintedRegexp` represent the printed grammar. `elaborate` accepts the fragment with explicit desugaring clauses. `ExtendedRegexp.desugar_correct`, `Regexp.matches_repeatPositive` and `ExtendedRegexp.equational_iff_core` give its language and Eq. (27) bridges. Nested negation is represented in the surface grammar and has no elaboration. |
| Eq. (28) | For every natural n, absorb the network into the specification forbidding the designated packet action immediately after n alphabet events. | **Formalized.** `padded`, `mem_padded`, `padded_exists_coreFormula` and `padded_equational_iff` verify each formula. `eq28_iff_no_occurrence` proves the full family equivalent to absence of the action on every feasible source trace over the alphabet. At n = 0, `padded_zero` gives the unpadded literal. The two distributed-controller instances are recorded below. |
| §V positive absorption | For `s = ⟨r⟩true`, derive `i ⊕ ⟦s⟧ ≡ i` in the trace theory. | `TraceSafety.positiveSpecification` renders the finite word witnesses. `positiveAbsorption_iff_traces` proves inclusion of **each** word in source traces. For a singleton word this says that word is feasible. `checkPositive_correct` uses exact symbolic moves with supported compilation and restriction classifiers. |
| §V static endpoint query | Test `in · (p · t)* · out` for nonzero. | `staticReachability_iff` gives an existential endpoint flow through zero or more switch/topology rounds. The ingress and egress predicates test the endpoints. |
| §V dynamic endpoint queries (34)–(35) | Initial isolation uses zero of the head policy. Post-event forwarding uses nonzero of the head of the selected tail. | `graphHead_source_iff` identifies feasible source-visible packet observations after preprocessing, including nested tails. `compiledSafety_source_correct` connects both verdicts to the source. `projectedReachability_correct` is bounded by the total source-word length, and `normalizedReachability_correct` is all-depth with exact finite derivative rows. Waypoint correspondence remains open. |

`SourceTrace` and `Program.Trace` in `SourceTrace.lean` use the existing
`Steps` relation with consecutive packet lists. One-sided sends and receives
remain visible in the source. A network over the paper safety alphabet
must eliminate those observations, for example by restriction after
synchronization. `Program.Compiled.trace_iff` transfers whole traces with
those same packet lists. `TraceSafety.check_correct` in
`TraceSafetyCheck.lean` checks supplied forbidden words via exact symbolic
moves and supplied-packet execution. It proves the full finite-formula
property. Its completeness bound is the longest forbidden word, as proved
by `safe_iff_project_maxLength`, and the checker assumes correct restriction
classifiers and finite compilation support. `check_iff_equationalSafety`
adds the alphabet condition for Eq. (27).

Section V gives the positive absorption equation without a separate
translation algorithm for its diamond formula. The Lean witness is the
finite sum of the matching action words ending in deadlock. Its trace
language contains the prefixes of those words. Absorption therefore asks
for inclusion of every matching word, including both branches of a union.
The endpoint query in Eq. (35) quantifies existentially over the packet
pair and the earlier feasible actions.

The Eq. (27) endpoints are admitted programs. As in Lemma 9, the internal
normal forms are algebraic proof witnesses. The word-sum proof does not
expose those witnesses as admitted programs or SOS residuals.

### Definition 17 desugaring boundary

The printed grammar has extended actions `α·π | rcfg(x,p) | ¬actₑ`,
extended expressions `true | actₑ | r+s | r·s | rⁿ` with n ≥ 1, and
formulas `[r]false`. Its desugaring sums all alphabet letters for
`true`, other packet letters for a negated packet literal, and other
reconfiguration letters for a negated reconfiguration literal. It
expands positive repetition into n concatenated copies, descends
through products and sums when they are outside the core grammar, and
leaves core expressions unchanged. The extended translation applies
Definition 14 to the desugared result.

The literal-negation clauses exclude letters of the other kind.
Consequently they differ from the surrounding whole-alphabet reading
on a mixed alphabet. Lean follows the displayed sums. The fallback
identity on core expressions cannot eliminate nested negation, which
is outside the core grammar. Empty desugared sums use the existing
word-sum form of Eq. (27). Every nonempty well-formed sum has an ordinary
`Formula` with the same language.

Eq. (28) treats the empty prefix at n = 0 as the concatenation
identity, without adding zero repetition to Definition 17. A fixed
member forbids words of length n + 1, and
`safe_padded_iff_project` proves that depth n + 1 completely checks
that member. Different indices check different positions. The theorem
over every n expresses absence at every position.

## Head and tail

| Input D | head(D) | tail(D,R) |
|---|---|---|
| ⊥ | 0 | ⊥ |
| N;Q | N + head(Q) | tail(Q,R) |
| Q⊕S | head(Q) + head(S) | tail(Q,R)⊕tail(S,R) |
| rcfg(x,N);Q with (x,N) ∈ R | 0 | Q ⊕ tail(Q,R) |
| rcfg(x,N);Q with (x,N) ∉ R | 0 | ⊥ |

Eqs. (29)–(33) apply after normalization and removal of unilateral
communication. Parallel, merges, variables, δ and π have no raw head/tail
equations. The tool unfolds only as needed by finite π and then extracts.
The matching branch of (32) uses N for event membership, consistent with
(33) and the v1.1 rewrite. Head can traverse several packet prefixes before
an event. Tail can cross packet prefixes and selected events, keeps each
matching continuation, and stops at the first event outside R along a
branch. Each nested tail starts from a continuation selected by the
previous tail. `graphTails_feasible_iff` concatenates those segments before
a nonempty observation suffix. A selected event at the last step can
leave a deadlocked continuation. The final input/output pair belongs to
one packet action. Earlier packet actions consume their own inputs as in
the SOS, and synchronization matches communication payloads syntactically.

| Lean layer | Actual theorem boundary | Additional assumptions and remaining bridge |
|---|---|---|
| AST `SafetyHead`, `TailExtraction` | `head_spec`, `tail_spec_iff`, `tail_domain_iff`, `tail_head_spec`; `tail_step_suffix` and `suffix_step_tail` for the supported AST setting. | Constructor fragment; the full tail support predicate requires communication-free and variable-free terms. Domain can be query-dependent. |
| `ProcessGraph` | `compileGraph_eq_some_iff` requires `FiniteSupport`; `compileGraph_corr` and `graph_step_iff` preserve raw transitions, including parallel, synchronization, merges, δ and π. | Supplied finite transitively closed support with defined variables. A finite graph of definitions can describe infinitely many residual terms. |
| `GraphRestriction` | `preprocessGraph_bisimulation` on successful preprocessing, comparing with the original graph under an outer block on send/receive. | Sequential preprocessing blocks unilateral communication and replaces zero packet prefixes by deadlock. `preprocessGraph_traceReady` verifies the enabled fragment. Parallel handshakes must be resolved by projection or normalization before this pass. |
| `GraphHead` | `graphHead_supported_some`, `graphHead_sound`, `graphHead_complete`, `graphHead_spec_iff` characterize the inductive head relation. | `GraphHeadSpec.iff_feasible` gives exact packet-only prefix execution followed by the observed packet on enabled sequential graphs. References are administrative. |
| `GraphTail` | `graphTail_domain_iff`, `graphTail_bridge`, `graphTail_spec_iff_of_domain`, `graphTailSpec_toGProc_iff` for variable-free source comparison. Tail adds fresh labels for transformed references and retains the original labels needed by selected continuations. | Exact query domain `GraphTailDomain G R`; `GraphTailSupported` is a sufficient all-sets domain. `graphTail_path_iff` preserves the continuation endpoint. `graphTail_feasible_iff` and `graphTails_feasible_iff` recover exact selected-event segments before a nonempty suffix on enabled graphs. |
| `GraphNormalization` | `exists_exactNormalization_iff` for finite restricted derivatives uses syntactic policy labels and symbolic zero checks. `exists_checkedNormalization_iff` adds admissibility, and `normalizeGraph_correct` establishes graph bisimilarity and extractor support. | Caller supplies a derivative table. Boolean validation also requires restriction-free derivative syntax and one checked reference order with supported one-step rows. The certificate path is separate from finite-depth rendering. |
| `FiniteProjection` | `renderProjection_source` proves exact executable finite projection on guarded, finitely supported inputs over any finite schema with correct executable membership at restriction sites. `renderProjection_restricted` compares with an outer restriction of the projection. | `projectedReachability_correct` verifies the bounded consumer on guarded source programs with finite definition support. `renderProjection_derives` and `renderProjection_restricted_derives` prove algebraic equality without AIP. The `Program.Compiled` and `State` wrappers use admitted entries and reachable residuals as sources. |
| `SafetyCheck` and compiled graph entry points | `safetyCheckGraph_correct` yields the two verdicts against `GraphHeadSpec` and `GraphTailSpec` on their domains. `compileNormalizeAndSafetyCheckGraph_correct` adds source/graph correspondence and restricted graph bisimilarity on successful compilation and normalization. | `compiledSafety_source_correct` connects the sequential API to source traces. `normalizedReachability_correct` bridges exact finite derivative certificates without a depth bound. Parser and waypoint correspondence remain open. |

The local Fig. 5 firewall regression uses a hand-supplied certificate and
the two Eq. (34)–(35) queries. Its source witnesses remain in the existing
firewall and reachability regressions. The full v1.1 JSON fixtures and
FatTree results are tracked in the [feature
matrix](DYNETIKAT_REFERENCE_AUDIT.md#v11-feature-parity).

## Distributed controllers in arXiv v4

The admitted examples and theorems live under `DistributedControllers` in
[DistributedControllers.lean](../lean/DyNetKAT/Examples/DistributedControllers.lean).
The executable checks live in
[test_distributed_controllers.lean](../lean/test_distributed_controllers.lean).

| Paper item | Lean representation and status |
|---|---|
| §I-A, Example 2 and Fig. 2 | `links` retains all seven wires and `originalRoute` retains the six initial switch policies, including the two drops. `portTest` and `setPort` encode paper port n as the base-four digits of n−1 in `swId` and `port`. Both transport fields are preserved. `hop_sem` verifies that joining switch and topology edges denotes exactly one NetKAT forwarding round. |
| Fig. 6, independent controllers | `independent_admitted` verifies Eq. (1) for the parallel controllers in `independent`. `body` has the starred packet policy and all five receive alternatives at each of the six switches. `env` expands the flow-table tuple into a single recursive name. All defining bodies satisfy typed Definition 7. |
| Fig. 10, initial and intermediate behavior | `initial_outputs_at`, `after_s6_outputs_at` and `after_s4_s6_outputs_at` prove the exact output sets for the paper's input port 2 with arbitrary transport headers. The initial set is {2, 6, 8, 12, 16}. After the S6 update the reachable stopping ports are {2, 6, 8, 11}, and after S4 they are {2, 6, 8, 11, 15}. `independent_initial_forwarding` gives a source step to H2, and `independent_initial_isolation` excludes the specific initial breach observation. |
| Fig. 10, breach | `independent_s6` and `independent_s4` prove the literal synchronizations, their continuation processes, and unchanged packet lists. `independent_breach_steps` then forwards from 2 to 15 in one packet-processing step. `afterBreach` packages the final SOS residual. `independent_reachable` proves the source endpoint query and `independent_headTail_verdict` proves the depth-three head/tail verdict for that witness. |
| Fig. 7 and Eq. (2), synchronizing controllers | `synchronized_admitted` verifies the restricted Eq. (6) program. Each controller disables its old ingress or egress switch, uses the literal `syn` identity payload, and then installs its two new policies in the printed order. `controllerRestriction` blocks standalone update-channel operations and the two `syn` operations. `synchronized_barrier` proves the synchronization with unchanged lists; `synchronized_order` classifies every trace by `PhaseTrace`, whose control edges permit the barrier only with both switches disabled and permit installations only afterward. `synchronized_no_early_barrier` proves an initial negative instance. |
| Example 2, isolation and new route | `synchronized_isolation` excludes both H1-to-H4 and H3-to-H2 leakage at every source trace length and for arbitrary transport headers. It checks closure of port sets at each of 13 reachable control phases using exact symbolic move rows. `synchronized_initial_forwarding` gives H1-to-H2 before updates; `synchronized_forwarding_steps` and `synchronized_reachable` give H3-to-H4 after the two deactivations, barrier, and four installations. `afterInstallation` packages the final residual. `synchronized_headTail_verdict` proves the accepted depth-eight query for this witness; `synchronized_unreachable` excludes the breach for any stages and budget. |
| §IV-A, Eqs. (27)–(28) | The prose that names S2 is read using the printed formula's endpoints port 2 and port 15, consistent with Fig. 2 and the Fig. 10 breach. `independent_eq28_fails` refutes the n = 2 conjunct for the communication-restricted observation of Fig. 6, which retains both synchronizations and the packet step. `synchronized_safe_padded` proves every member of the family at source level. `synchronized_eq28` transfers this to the equational family via the existing Eq. (27) bridge. Equational statements take the existing `UsesAlphabet` coverage premise. The source isolation result requires no materialized packet alphabet or depth bound. |
| Executable evidence | Regressions evaluate the Fig. 10 output sets and update rows, the Fig. 7 phase-event lists, and the final H3 and H1 output sets. Finite-word checker verdicts are Lean theorems via `check_correct`. Head/tail verdicts are Lean theorems via `projectedReachability_correct`. The executable regressions compute the relevant rows and packet policies on demand. |

Fig. 7's proof uses the SOS and symbolic rows at every step of an arbitrary
finite trace. The finite table of defining names and the 13 control phases
are specific to this example. The proof does not assume a global
derivative-closure or quotient certificate. The head/tail corollaries use
finite witness depths, and `synchronized_projection_derives` reuses the
general algebraic rendering theorem. The all-depth AIP rule remains
separate from those finite renderings.

The controller case studies cover the paper's source semantics and
queries. The pinned DyNetiKAT v1.1 JSON benchmark files and benchmark
timings are separate parity work.

## Finite packet-schema foundation

The first schema stage is machine checked. `PacketSchema` extends the
existing KATLean lookup and update model with finite dependent value
domains and total packet valuations. `ctxSchema` specializes this
boundary to the existing `CtxPkt`. The same NetKATLean policy grammar,
history semantics, and supplied-packet evaluator serve both the
concrete schema and new schemas.

| Paper item | Generic Lean scope |
|---|---|
| Definition 1 and Fig. 3 | `PacketSchema.Packet`, `History`, `Semantics`, `katInterp`, `HistorySemantics` and `historySemantics_iff_packetSemantics`. The existing history relation preserves the entire tail under dup-free policies, including nested stars. |
| Eqs. (1) and (6), Fig. 8, Eqs. (2)–(5) | `DyNetKAT`, `Action`, `Config` and `Step` share a schema parameter. All original SOS constructors apply, including both synchronization and communication-merge orientations. `execute_packet_step` connects a computed output for one supplied packet to the packet-prefix rule. |
| Definition 7 and source residuals | `RecEnv`, `TypedPaperGuarded`, `paperAdmissible_iff`, `Program` and `Residual` retain the grammar and guardedness conditions. `Step.preserves_paperAdmissible` is generic. |
| Finite source traces and endpoints | `Steps`, `Program.Trace`, `Program.trace_iff_reaches_residual` and `EndpointReachable` apply to a schema and preserve pending and handled packet lists. The certified graph checkers use the same schema. |
| Proposition 1 | `Program.historySemantics_iff_packetPrefix_bisimilar` is generic. Observable communication and reconfiguration payloads retain syntactic identity. |

The large-schema regression gives the switch field type `Fin 1344`
and gives the port and SSH fields independent domains. It proves
injective switch representation, lookup and update behavior, policy
semantics, recursive admission, and a two-step source trace. It also
executes a starred policy from one supplied packet. The symbolic compiler
now handles field-dependent domains. `compileSymbolic_correct` covers
every dup-free constructor. `netkatNativeEquivFinite_correct` gives an
executable equivalence decision from the packet schema alone.

| Analysis path | Schema support |
|---|---|
| Symbolic compilation and equivalence | The original `symbolicSchema` supplies the `CtxPkt` compatibility layout. `DiagramLayout` and `PacketSchema.diagramLayouts` supply bit orderings for arbitrary schemas. |
| Semantic normalization | `symbolicNormalFormFor_correct`, `symbolicPairsFor_sum_correct`, and `symbolicPairsFor_history_correct` are generic. The exact finite sum is obtained from accepting paths only and is expanded on request. |
| Algebraic Lemma 5 | `Derives.katSound`, `normalize_derives`, `exists_derives_pairSum`, and `netkatNativeEquivFinite_iff_derives` are generic. Complete test expansion and PA-MATCH-ALL use proofs of coverage for field-local lists. A field with no values yields the paper equation that the empty sum is identity, so policies over an empty packet domain are covered. |
| Lemma 9, Theorem 1 and algebraic projection | `WellFormed.normalizes` and `guarded_normalizes` derive the full head form over a schema. `ground_derives_iff_bisimilar` preserves the variable-free scope and shared environment. `renderProjection_derives` and its total, restricted and memoized wrappers use `DerivesNoAIP`. |
| Trace safety, A16, Eqs. (27) and (28) | `TraceDerives.iff_traces`, `TraceSafety.equationalSafety_iff_safe`, `TraceSafety.eq28_iff_no_occurrence` and the compiled word checker are generic. The source proofs retain their alphabet and visibility premises. The printed nested-negation ambiguity is unchanged. |
| Positive reachability and head/tail extraction | `TraceSafety.positiveAbsorption_iff_traces`, `graphHead_source_iff`, `graphTails_source_iff`, `normalizedReachability_correct` and `projectedReachability_correct` preserve observable labels and the distinction between all-depth and bounded queries. |
| Finite projection and certified graph analysis | `GProc`, `Corr`, exact checked rows and `ProjectionSupport` share the source schema. Concrete closure and finite certificates keep their explicit termination assumptions. |
| Example, compatibility, and auxiliary code | `DistributedControllers.lean` and the fixed field fixtures are concrete instances. The concrete cardinality lemma, optional Legacy and KATch code, and experimental certificates are outside the generic compiler and normalization proof. |

The synthetic schema checks semantic and algebraic normalization for a
forwarding policy, proves a trace-safety violation, and exhibits source
reachability. Its executable 1,344-switch solver check compiles drop.
Executable compound-policy cases exercise test, assignment, composition,
union, and star on a smaller dependent schema. The 1,344-switch schema also has theorem-backed head normalization,
algebraic projection, positive absorption and certified safety and reachability
verdicts. The FatTree case study remains open. The FatTree waypoint
claim concerns endpoint relation inclusion. All-trace traversal would
require a distinct property and proof.

## FatTree migration in arXiv v4

The benchmark in §V and Figs. 12–13 remains open. Figure 12 shows
core, aggregation, and top-of-rack (ToR) switches, with the ToRs
grouped into pods. The workload uses shortest-path
forwarding between all ToRs in six generated topologies. Section V
reports the 931- and 1,344-switch instances. The selected ToRs
`Ta` and `Tb` are in different pods, and their initial traffic passes
through aggregation firewall `Ax`, which filters SSH traffic. The
controller moves the firewall to aggregation switch `Ax'` by four
updates to aggregation and core flow tables.

The paper describes the scenario and the three checks. It does not
give the full benchmark topology tables, a concrete selection of the
firewall switches, the packet field layout or numeric SSH predicate,
the four ordered payloads and event labels, or a recursive declaration
environment. The [pinned DyNetiKAT v1.1 source audit](DYNETIKAT_REFERENCE_AUDIT.md#v11-feature-parity)
records generator-specific data separately. Its 16-pod instance has
1,024 ToR endpoints, 256 aggregation nodes, and 64 core nodes. It
records four ordered updates and query depths 2, 3, 4, and 5 for the
corresponding nonempty update prefixes. Those depths describe the
reference runs. Source isolation quantifies over all feasible traces.

| v4 item | Intended Lean model or proof | Status |
|---|---|---|
| §V and Fig. 12, generated topology and shortest-path forwarding | Retain the graph's actual switch and link-endpoint identities in the packet location. Use symbolic NetKAT location tests, link assignments, and per-phase forwarding policies. Preserve the SSH distinction independently of location. | Open. The full benchmark requires its own schema to represent all locations. |
| §V, initial firewall and four updates | Define the initial, three intermediate, and final configurations in one admitted `Program` using `RecEnv`. Establish reachable `Residual` values and the actual update labels, order, and packet effects from source SOS. Use a synchronization theorem if the concrete controller encoding uses handshakes. | Open. The paper's four updates alone do not specify the source controller syntax or literal SOS events. |
| §V (i), Reachability-I | Use `staticReachability_iff` for forwarding in each phase and `EndpointReachable` with the head/tail source bridge after selected migration events. Prove feasible non-SSH forwarding from `Ta` to `Tb` at each phase, including the initial and final configurations. | Open. The general endpoint bridges are machine checked. |
| §V (ii), Reachability-II | Exclude a feasible SSH observation from `Ta` to `Tb` across every reachable phase, including traces with arbitrary preceding packet observations. Apply the existing Eq. (27) or Eq. (28) bridge if the property is rendered as a forbidden trace family. | Open. The generic safety and equational bridges are machine checked. |
| §V (iii), Waypointing | For the final phase, instantiate the printed NetKAT test `R + W ≡ W`. Here `R` is the ingress-to-egress relation and `W` is the relation factored through `Ax'` with the printed endpoint guards. The equality checks inclusion of endpoint pairs in `W`. A statement that excludes every individual bypass with the same endpoints needs a path-level argument. | Open. There is no FatTree waypoint theorem or regression. |
| Fig. 13, experimental timings | Reproduce the benchmark instances, query groups, and measurement setup separately from proving the source properties. The figure reports measured checking and preprocessing times. | Open empirical work. |

Eqs. (34)–(35) are the preceding stateful firewall example. Eq. (28)
is introduced for the distributed controllers. Neither gives a
FatTree-specific formula or names the four migration events. If a
FatTree checker later uses projection, the existing
`projectedReachability_correct` and `ProjectionDerivation` apply under
their stated premises. The source claims do not call for an AIP
argument.

### Fixed-schema obstruction

This historical obstruction applies to the `CtxPkt` specialization.
The generic equational and certified analysis pipeline now accepts a
FatTree schema with distinct locations. The case study still requires
its own schema, verified encoding, and property proofs.

`CtxPkt` has the four fields `tpSrc`, `tpDst`, `swId`, and `port`.
Each field has four values, so the existing `ctxPkt_card` theorem
gives 256 distinct complete packets. The packet step observes one
input packet and one output packet. In the printed forwarding form
`(p · t)*`, the intermediate location is consumed by NetKAT tests
inside that same packet-processing step.

A faithful location encoding for the full all-pairs workload must
distinguish switch locations in these packet values. Even allowing
all four fields to encode location gives only 256 states before
accounting for link ports, ingress or egress identification, and
traffic class. For example, assign a representative packet to
each switch. Preserving location tests forces representatives of
distinct switches to be distinct. The following Lean proof rules out
even this injection.

```lean
import DyNetKAT.NetKAT.Packet

open DyNetKAT.NetKAT

theorem fatTree1344_exceeds_ctxPkt :
    ¬ ∃ encode : Fin 1344 → CtxPkt, Function.Injective encode := by
  rintro ⟨encode, injective⟩
  have h := Fintype.card_le_of_injective encode injective
  rw [Fintype.card_fin, ctxPkt_card] at h
  omega

#print axioms fatTree1344_exceeds_ctxPkt
```

The same check succeeds with 931 in place of 1344. This argument
uses the existing cardinality theorem and does not select a packet
representative by searching. Packing coordinates as in the small
controller example, moving location information into the control
term, or quotienting to a single selected route would not supply
the distinguishable intermediate packet locations demanded by the
full workload. A smaller topology may fit, but it would leave the
reported larger instances open. No FatTree program, source
transition theorem, or executable migration regression has been added.
