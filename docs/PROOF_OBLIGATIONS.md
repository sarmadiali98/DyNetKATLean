# Proof obligations for paper and tool coverage

## Symbolic native KAT

`KATLean.Native` decides the pure KAT equational theory using reduced ordered
Boolean decision trees and symbolic partial derivatives.
`decideEquiv_iff_equational` characterizes derivability from the KAT rules and
`decideEquiv_iff_algebraicallyEquivalent` characterizes equality in every
abstract KATLean model. `nativeSolver_derives` yields a NetKAT derivation
under any substitution of primitive actions and tests.

`netkatNativeEquiv` adds executable symbolic equivalence for the current
dup-free NetKAT AST. KATLean → native KAT → symbolic packet frontend →
NetKAT equivalence → E_NK → E_DNK is the resulting proof path.
`netkatNativeEquiv_correct` is independent of KATch, concrete packet
enumeration and Boolean valuation enumeration. The E_NK completeness proof
uses symbolic closure and the field-level partition axiom. The public
`netkatEquiv` and `netkatIsZero` APIs serve graph normalization and safety
through the symbolic checker. `legacyNetkatEquiv` is the regression oracle.

See the [symbolic frontend and dependency audit](NETKAT_AUDIT.md).

See [NATIVE_KAT.md](NATIVE_KAT.md) for the theorem chain and proof construction.

## Native symbolic equivalence obligations

| Obligation | Status |
|---|---|
| Generic syntax and guarded-string semantics | Proved in `KATLean.Native` |
| Nullable and partial-derivative correctness | `nullable_correct`, `derivative_correct` |
| Finite reachable state space and sufficient search bound | `continuations_closed`, `state_space_finite`, `saturate_closed` |
| Executable generic language soundness/completeness | `decideLanguageEquiv_correct` |
| Exact KATLean relational-model correspondence | `interp_iff_accept`, `guarded_model_correct`, `relational_iff_language` |
| Complete decision for all relational KAT models | `decideEquiv_correct` |
| Equality in all arbitrary abstract KATs / axiomatic completeness | Proved by `algebraicallyEquivalent_iff_equational` and `decideEquiv_iff_algebraicallyEquivalent` |
| Symbolic packet constraints, updates, AST and Derives bridge | Proved by `compileSymbolic_correct`, `netkatNativeEquiv_correct` and `netkatNativeEquiv_iff_derives`. The last uses field-level partitions and symbolic closure. |
| Remove core full-packet enumeration in the fixed model | Equality uses native symbolic equivalence. Lemma 5 and Lemma 9 emit accepted pairs from the diagram. Graph normalization retains whole policy labels and safety uses symbolic zero checks. Supplied-packet star uses the generic growth bound in `reachableWithin_finite_stabilizes`. See [audit](NETKAT_AUDIT.md). |
| Inequivalence witness | `distinguishingGuard_sat` decides satisfiability of the symbolic counterexample constraints. Concrete witness existence is proved and extraction is open. |

The native proof and the symbolic normalization proofs are independent
of complete packet enumeration and KATch. The exhaustive checker and
normalizer remain available for differential regression through an explicit `DyNetKAT.NetKAT.Legacy` import.

Paper identifiers use [arXiv:2102.10035v4](https://arxiv.org/pdf/2102.10035v4).
The [conformance inventory](PAPER_CONFORMANCE.md) gives the complete
definition, rule and axiom crosswalk and the existing Lean results.
Statements labeled as targets below are open. The dependencies refer to the
[roadmap](../PLAN.md). The [S6C audit](S6C_TAIL_EXTRACTION_AUDIT.md) preserves
the detailed recursive tail analysis and the original design alternatives.

## Core formalization path

The source grammar and `Program` / reachable `Residual` boundary determine
the SOS domain. KATLean over Mathlib KA supplies the algebra for dup-free
NetKAT E_NK; E_DNK and certified analysis build on the existing connected
NetKAT proofs. KATch has no core proof obligation or completion gate.
Backend experiments are tracked under optional tooling below.

## NetKAT foundations

| Obligation | Required statement and dependencies |
|---|---|
| N1 Packet model, Defs. 1 and 4 | Over a finite type of fields and a nonempty finite domain for each field, packet valuations are total, tests are decidable and updates affect precisely the specified field. Complete tests recognize one packet, complete assignments overwrite all fields, the conversions are inverses, and the paired term α·π relates precisely (σ_α,σ_π). Covers heterogeneous and singleton field domains. Explain the empty field product. |
| N2 Fig. 3 denotation | Give the dup-free relational clauses and their history correspondence. Prove that dup-free history outputs have the original tail, and that their possible heads are exactly the relational outputs. Consequently singleton observations suffice for all histories in this fragment. Full history semantics with dup is an optional supporting extension. |
| N3 Evaluation | Preserve the concrete evaluator as reference/model tooling. Core decisions must use the verified native symbolic packet layer, independently of exhaustive packet enumeration. Prove exact evaluation for every constructor on a general schema. For star, executable closure iff an arbitrary finite execution exists. Prove stabilization/termination from the finite domain, including nested stars. Lift zero and equivalence in both directions to the history denotation where applicable. `eval_correct`, `execute_star_correct` and the decision theorems currently cover the fixed model. |
| N4 Fig. 4 E_NK soundness | Inductive derivations for the dup-free printed laws and well-sorted equational reasoning, with a proof for each constructor. Prove both least-fixpoint rules and PA-MATCH-ALL over the declared domain. PA-DUP-FILTER-COMM belongs to the optional full NetKAT extension. Lift fixed-domain `Derives.sound/historySound` for the restricted system. |
| N5 Fig. 4 completeness and Lemma 5 | Lemma 5 is proved for dup-free policies over arbitrary finite schemas by `exists_derives_pairSum`. `normalize_derives` uses the proved symbolic star fixed point to obtain a star-free representative, and field-local packet laws to derive equality with the sum from accepting paths. `symbolic_normalize_pairSum` recovers the original paper syntax. Lemma 9 uses the same list through `packetHeads_correct`. The separate language-model development remains open. Full history ground completeness belongs to the optional full NetKAT extension. |
| N6 Query correctness | Prove interpretation-preserving elaboration for declared field names, values, input guard, and every term constructor in the dup-free fragment. Establish zero/equivalence against the mathematical query semantics with a proved Lean evaluator, including completeness and termination. See the [query and experimental-tooling audit](NETKAT_AUDIT.md). |

### KATLean foundation

The [KATLean conformance table](KATLEAN.md) maps each Figure 4 law.
Mathlib supplies `IdemSemiring`, `KleeneAlgebra`, the addition-induced
order and star induction. KATLean derives the paper unfold equations
and both equation/inequality induction formulations. Its Boolean
embedding proves all six BA laws. Its dependent-field packet interface
proves all seven dup-free PA laws, including finite-value exhaustiveness.

`katInterp_correct`, `execute_katInterp` and `Derives.katSound`
connect the current AST, evaluator and derivations to that model.
`normalize_katInterp` is the existing Lemma 5 derivation interpreted
in KATLean. `Derives.katSound` now justifies each algebraic constructor
directly from KATLean and its Mathlib instances. `Derives.sound` follows
from that algebraic induction and the independently proved interpretation
bridge. The [40-rule audit](KATLEAN.md#derives-rule-audit) records each
constructor and the [duplication audit](KATLEAN.md#duplication-and-dependency-audit)
records retained syntax and compatibility lemmas.
The dup-free finite-schema requirements in N1–N5 are covered. A history/dup model for
PA-DUP-FILTER-COMM is optional supporting work outside current DyNetKAT
completion.

## SOS, recursion and bisimulation

| Obligation | Required statement and dependencies |
|---|---|
| D1 Grammar and SOS | Generalize every constructor in Eqs. (1), (6), every rule in Fig. 8 and Eqs. (2)–(5), and their inversion lemmas. Prove packet effects, unchanged lists for communications, matching payload identity and absence of steps for deadlock and π₀. Establish atomic per-packet evaluation and the exact prefix enumerator bridge. |
| D2 Definition 7 and recursive declarations | Typed conformance is proved in `TypedGuardedness.lean`. `ProcessVarOccurrence` records prefix crossings, and `typedPaperGuarded_iff_guardedOccurrences` proves the occurrence interpretation equivalent to the structural predicate. `ClosedDefined.existsUnique_lookup` and `wellFormed_iff_closedDefined_and_typedPaperGuarded` characterize the reachable named equations. `Step.preserves_wellFormed` supplies derivative preservation. A separate executable validator for finite declaration input remains open. |
| D3 Lemma 8 | `WellFormed.finite_targets_from` proves local finite branching at every reachable source state, uniformly over labels and packet lists. `WellFormed.imageFiniteFrom` discharges AIP without finite support or executable restriction classifiers. The theorem is schema-generic. |
| D4 Definition 2 and Prop. 1 | `Bisimilar` gives the largest stateless bisimulation. `Equations.historySemantics_iff_nSeq_bisimilar` proves both directions over any finite schema in a fixed recursion environment. Forward uses equality on singleton histories to match steps. Reverse inverts matching packet steps in both directions and lifts packet-pair equivalence to every history by tail preservation. `Program.historySemantics_iff_packetPrefix_bisimilar` gives the admitted statement for a shared base-sorted continuation, including guarded recursive continuations. The theorem is schema-generic. |
| D5 Lemma 3 | Lift process-context congruence through every constructor and well-scoped recursive bindings where substitution is claimed. Prove name invariance and graph/closed-source bisimilarity, including comparisons across independently compiled environments. The current constructor lemmas work in one fixed environment. Prove the stronger closure result with explicit relation and scope. |
| D6 Compilation | For a finite parsed declaration map compute support, reject unresolved and duplicate names, and prove `compileGraph` accepts a support for every valid finite input. Prove both directions of step and residual correspondence for the full SOS and any optimized graph representation. Existing `Corr` and step correspondence apply after support is supplied. |

### Grammar boundary and preservation

`paperAdmissible_iff` characterizes the two printed grammars and the
unique, guarded reachable definitions. `Step.preserves_paperAdmissible`
checks each SOS rule, reusing `Step.reachableVar_mono` and
`Step.preserves_wellFormed`. `Steps.preserves_paperAdmissible` and
`PaperAdmissible.reachable` cover the existing trace and stateless
reachability relations. `GSteps.preserves_paperAdmissible` transfers
closure through `Corr`. These results cover `CtxPkt` and precede the
finite-support, restriction-classifier and certificate obligations of
executable analysis. See the [fixture audit](PAPER_CONFORMANCE.md#source-grammar-and-sos-residual-closure).

### Public theorem and operation scope

| Area | Classification and paper-facing entry |
|---|---|
| Formation and recursion | `PaperSyntax` is A (syntax formation). `paperAdmissible_iff` and `Program` are C (paper-semantic API). Raw `RecEnv` construction is B (internal raw representation). |
| SOS and executable transitions | `Step`, `GStep`, `checkedMoves` and exactness lemmas are B (raw syntax theorems with their stated hypotheses). `Program.Compiled.State.moves_exact` and `State.successor` are C (reachable-residual theorems). |
| Finite branching and AIP | `WellFormed.finite_targets_from` and `approximation_induction` are B (internal theorems over their own hypotheses). `Program.Residual.finite_targets` and `Program.approximation` are C. AIP uses extended projections as observations. |
| Graph correspondence | `Corr`, `toGraph_corr` and step transfer are B. `Program.Compiled.corr` starts with a program and `source_reachable` recovers a reachable residual. |
| Projection, closure, bisimulation and strategy | The raw renderers, certificate checkers, discovery functions and `Internal.analyze…` functions are B. `Program.Compiled.analyze` and `State.analyze` supply the domain for one-root analyses. `Program.equivalence` and `State.equivalence` check both input endpoints. Rendered terms are models. |
| Normalization and ground completeness | `Derives`, `WellFormed.normalizes` and `ground_derives_iff_bisimilar` are B. `Program.normalizes` and `Program.ground_complete` are C, with an admissible source or two admissible ground operands. Normal form witnesses are algebraic models. |
| Safety and query evaluation | Raw head, tail, restricted graph preprocessing and executable safety helpers are B. `Program.Compiled.safety` and `safety_correct` are C. Successful preprocessing remains an independent hypothesis of the legacy head/tail query theorem. |
| Abstract certificates | Generic table and certificate checking is B. The public strategy takes an admitted source or reachable residual and restricts candidate relations to reachable states. Graph-only experiments and analysis of unguarded defining aliases are D (outside DyNetKAT). |

### Guardedness and representability

Definition 7's clause (i) places an occurrence in the continuation of a
sequencing subterm with a variable-free or already guarded prefix. In the
typed grammar the packet policy is dup-free NetKAT and has no DyNetKAT
process variables. The typed reading counts the continuation edge of
each packet, send, receive, or reconfiguration prefix as a guard. Clause
(ii) as printed has no well-typed instance with a recursive process
variable in a payload or channel position. The [typing audit](PAPER_CONFORMANCE.md#definition-7-typed-guardedness)
records the sorts and the firewall evidence.

`TypedPaperGuarded` excludes paths with no prefix crossing. Choice,
parallel, merges, restriction and projection transmit the path flag
unchanged. A bare variable under π₀ or in the right operand of a left
merge still fails syntactic guardedness. `WellFormed` checks reachable
defining bodies, so it can admit a bare entry reference or `Host ∥ Switch`.
After a step, `Step.preserves_wellFormed` preserves that environment
condition even when the residual exposes a variable.

The countably infinite name space does not impose finite global support.
A finite list of mutually recursive declarations has finite support,
even if it has infinitely many process derivatives. Conversely, a
countably infinite environment such as `X_i ≜ rcfg(x_i,N);X_(i+1)`
with all channels distinct is guarded and locally finite but may need
infinitely many names for a global representation. A finite JSON file
describes a finite declaration map. For the mathematical statements on
possibly infinite environments, use lazy access to definitions and local
finiteness, or state explicitly the paper basis for a finite specification
assumption. Finite-depth exploration of a guarded environment only needs
the finitely many definitions consulted at that depth.

The current compiler preserves all raw step constructors, including
arbitrary guarded parallel and both synchronization orientations, given
`FiniteSupport`. It does not check Definition 7 and does not ensure that
one can build a finite derivative table. In
[`test_infinite_derivatives.lean`](../lean/test_infinite_derivatives.lean),
`spawn_no_finite_derivatives` proves infinite syntactic derivative
closure for `X ≜ rcfg(a,id);(X ∥ rcfg(b,id);⊥)` under the current graph SOS,
and `spawn_rejects_every_candidate` proves that all Boolean normalization
candidates are rejected. This proof does not classify the bisimulation
quotient. The finite-depth route below must accept the example under the
resolved guardedness criterion.

## Finite-depth projection

Items 1–4 record the current `CtxPkt` construction. Item 5 records
the remaining consumer and algebra obligations.

1. **Finite exact one-step rows.** For `CtxPkt`, `guardedMoves` scans
   the root structurally and computes the body row on demand at each
   active reference. The body pass disables lookup. Syntactic guardedness
   rules out a second active lookup, including inside a restriction.
   `guardedMoves_toGraph_exists` derives successful traversal from
   `FiniteSupport` and `WellFormed` with executable membership functions.
   `guardedMoves_toGraph_source_exact` gives both directions of source
   correspondence with identical actions and packet lists and corresponding
   residuals, provided those functions are correct at active restriction
   sites of the root and consulted bodies. Classifiers are supplied by
   structural path and by definition node. The abstract SOS retains
   arbitrary `Set CommunicationAction`, so finite support and guardedness
   alone do not supply executable membership. Chains of active lookups inside
   definition bodies are outside this typed guardedness condition.
2. **Per-rule exactness.** A symbolic packet move carries its NetKAT policy
   and exact continuation. It realizes a transition exactly when the
   policy maps the pending head to the emitted packet. Send, receive and
   reconfiguration moves retain their channels, payloads and continuations.
   Choice combines rows. Parallel retains the passive operand and combines
   matching sends and receives in both orientations. Left merge inspects
   only the left operand, and communication merge forms only matched
   products. `MovesExact.restrict` proves that a nested restriction filters
   the completed operand row, including any synchronizations, and wraps
   each retained residual in the same restriction. A nested π₀ yields no
   moves and π_(m+1) wraps each successor in π_m.
3. **Structural recursion on depth.** `renderProjection` returns deadlock
   at zero. At positive depth it computes a finite row, renders each
   successor at the smaller depth, and assembles the prefixed branches
   with `choiceOf`. `checkedMoves_erase` identifies the row with
   `guardedMoves` after dropping classifier data. `checkedMoves_spec`
   proves the classifier and reachable-name invariant for every row
   target, including dormant restrictions in continuations and passive
   operands. `GSteps.checkedResidual` and `Steps.checkedResidual` lift
   the invariant to finite executions. `renderProjection_exists` proves
   success at every depth and `renderProjectionTotal` extracts the
   executable result. Lookup and restriction consume zero levels.
   Synchronization and each other genuine move consume one level.
4. **Correctness against SOS.** `renderProjection_source` proves strong
   source bisimilarity with `π_n(P)`, under finite support, `WellFormed`,
   and classifier correctness throughout the root and reachable defining
   bodies. `renderProjection_restricted` gives the corresponding
   `δ_L(π_n(P))` theorem with executable membership for `L`.
   `renderProjection_closed` shows the resulting prefix-and-choice term
   has no recursive references. A symbolic packet prefix with an empty
   relation has no realizing SOS step. The finite-derivative certificate
   continues to serve the separate normalization route.
5. **Executable consumers and algebra.** `projectedReachability_correct`
   uses exact finite projection and sequential preprocessing to verify head
   and nested tail queries against source traces of length at most n. The
   projection law counts the selected events and final packet. General
   schemas are supported, and the finite rendering has an algebraic derivation without AIP.

The existing `restrict_project_commute` proves commutation up to
bisimilarity for an outer restriction. The tool can preserve the original
δ(π_n(P)) workflow. `NormalizationExact` has a classical existence
equivalence with finite restricted derivative closure and a renderer
taking a supplied proof. The Boolean checker adds admissibility
(restriction-free derivative syntax and a checked order/row computation).
Either can be reused for suitable systems, with a theorem that its
bounded queries agree with the direct projection. Neither is a
termination argument for arbitrary guarded inputs.

## Paper-faithful recursive execution acceleration

`MemoProjection.lean` proves that a fresh-cache memoized run yields exactly
the `renderProjection` result, including failure. Entries are scoped to a
fixed graph and body-classifier table. A key certifies rendering equality
at every depth, and the actual lookup pairs it with the remaining depth.
`ProjectionMemo.Valid` requires each stored subtree to be the reference
answer for every state accepted by that key. Empty, lookup, insertion and
threaded recursion proofs establish this invariant.

The default key recognizes only prefix chains ending in deadlock or a
reference. Their incoming classifier is irrelevant: prefix descent has
no restriction tests and a reference uses the fixed body classifier.
Arbitrary restriction sets and classifier functions have no general
executable equality. Unkeyed states still traverse exact checked rows.
Each child is called at the predecessor depth, with administrative
reference resolution and restriction filtering inside the unchanged row
builder. Cache hits reuse the rendered subtree. There is no separate DAG
serialization or finite quotient discovery. Hits, misses and stored
entries are measured by pure counters, with a disabled-key traversal
available as a baseline.

### Recursive definition dependencies

`DependencyGraph.build` filters the finite support to the names reachable
from the root's direct references. Its edges are occurrences in looked-up
bodies, including occurrences behind prefixes. Node and edge correctness
relate the finite graph to `ReachableVar` and `recursiveVars`. Repeated
finite-set saturation computes reachability, and mutual reachability gives
a partition into SCCs. The condensation exposes cross-component edges,
with strictly decreasing `componentRank` in dependency order.

`guarded_scc` derives typed guardedness of all reachable bodies from
`WellFormed`. `cyclic_scc_iff_cycle` detects a nonempty dependency cycle,
and `acyclic_unfolds_ground` constructs a finite derivation using only
lookup unfolding and congruence (with reflexivity and transitivity).
This is static analysis. Cyclic SCCs give no finite-derivative or quotient
claim, as witnessed by the spawning example.

## Algebra and completeness

| Obligation | Required statement and dependencies |
|---|---|
| A1 Derivability | `DerivesNoAIP env` gives typed non-AIP derivations. `Derives env` embeds them and closes over full symmetry, transitivity, process contexts, and the infinitary AIP rule. Every AIP node carries reachable image finiteness at both endpoints. |
| A2 Lemma 10 | `DerivesNoAIP.sound` proves strong stateless bisimilarity by derivation induction. `CommMismatch` encodes the Appendix A cases and excludes both handshake orientations. The [Fig. 11 table](PAPER_CONFORMANCE.md#figure-11-and-a16) records the rule mapping. |
| A3 Def. 6 and Lemma 9 | Proved for the typed `CtxPkt` domain in `HeadNormalForm.lean`. `guarded_normalizes` proves `DerivesNoAIP` from each `GuardedOccurrences` term to a finite choice of complete packet or communication/reconfiguration prefixes with arbitrary continuations. `WellFormed.normalizes` also handles exposed entry references using their guarded bodies. Packet heads use N5 and A0/A1, parallel uses A8 and A9–A15, and restriction and projection use their atomic prefix equations. Arbitrary restriction sets use classical membership in the algebraic proof. No derivative certificate or classifier is needed. |
| A4 Lemma 11 and AIP | `Derives.sound` supplies soundness of all projected premises by derivation induction and invokes `approximation_induction`. Matching at depth n+1 yields residuals at depth n, and projection truncation and a finite bound on candidate failure depths give a common residual. `Derives.aip_guarded` supplies the endpoint evidence from `WellFormed`. |
| A5 Theorem 1 | Proved for typed `CtxPkt` ground terms by `ground_derives_iff_bisimilar`. `Ground p` means `recursiveVars p = ∅`. `ground_complete` uses the strengthened Lemma 9 witness, exact head inversion, and both choice absorptions. Strong induction on the sum of process-prefix counts derives matched continuations in `DerivesNoAIP`. `derivability_sound` remains valid without the ground hypotheses. |
| A6 Finite projection rendering | `renderProjection_zero_derives` applies Π₀. `WellFormed.project_exists_ground` uses `exists_headNormalForm_closed`, the Π equations and depth induction on the continuations. `renderProjection_derives` applies Theorem 1 on the ground witness and the recursion-free renderer, using `renderProjection_closed` and `renderProjection_bisimilar`. The restricted renderer uses restriction congruence, and the total and memoized variants use `renderProjectionTotal_eq_some` and `renderProjectionMemo_eq`. Finite rendering requires local move support and correct classifiers. It requires neither an AIP premise nor a finite global derivative or quotient certificate. |

**Soundness boundaries.** The printed E_NK import cannot license unrestricted
payload substitution with syntactic action labels. For example, E_NK
derives `z ≡ z+0`, while `x!z;⊥` and `x!(z+0);⊥` have different observable
labels and may synchronize with different peers. The analogous issue
applies to receive, rcfg and restriction membership. Keep an explicit
layering rule for NetKAT packet prefixes, and justify that typed import
as the interpretation of Fig. 11. An alternative that identifies
semantically equivalent payloads changes the label and handshake
semantics and needs a separate calculus and correspondence result.
Likewise, a syntactic failure to match A12 before expanding choices or
unfolding variables does not justify A15. A15's Appendix A mismatches
are the source for the rule, including unequal channel or payload.
Proof 7 passes from matching heads to an induction hypothesis on their
continuations. For ground terms, the normalization witness certifies that
each continuation has strictly fewer process prefixes than the source, even
when normalization duplicates branches. Every atomic head has an enabled
step, so a head form bisimilar to deadlock has an empty list. For terms
with recursive variables, a continuation can refer back to its source.
Extending completeness to that domain would require a separate argument.

## Safety, extraction and end-to-end correctness

| Obligation | Required statement and dependencies |
|---|---|
| S1 Definitions 12–13 and 17 | `Formula` and `Regexp.mem_hnf` give the core word language. `PrintedRegexp.elaborate` accepts the explicitly defined Definition 17 fragment. `ExtendedRegexp.desugar_correct` and `Regexp.matches_repeatPositive` verify its language. `ExtendedRegexp.equational_iff_core` connects nonempty sums to ordinary formulas and Eq. (27). |
| S2 Definition 14 | `translate_trace_iff` proves the translated admitted program realizes precisely the words over the supplied finite alphabet with no forbidden prefix. The proof checks the guarded Θ and the two word sums. Named suffixes preserve printed continuation sorting. |
| S3 Definitions 15–16, Eqs. (26)–(27) | `SourceTrace` uses the feasible source SOS. `TraceDerives.sound` and `TraceDerives.complete` establish exact trace equivalence for closed guarded terms. `Formula.equational_iff` proves Eq. (27) for networks over the supplied alphabet. `Program.Compiled.trace_iff` and `TraceSafety.check_iff_equationalSafety` transfer the result to certified symbolic moves for supplied forbidden words. |
| S4 Eq. (28) and §V | `eq28_iff_no_occurrence` characterizes the all-length safety family. `TraceSafety.positiveAbsorption_iff_traces` verifies the positive witness equation as source-trace inclusion and `checkPositive_correct` verifies every word of the finite expression. The controller instance remains open. |
| S5 Eqs. (29)–(33) | `GraphHeadSpec.iff_feasible` gives exact packet observations on enabled sequential graphs. `graphTail_path_iff` preserves original continuation endpoints. `graphTails_feasible_iff` composes selected segments before a nonempty suffix. `preprocessGraph_traceReady` proves that preprocessing drops the infeasible packet prefixes detected by symbolic zero. |
| S6 Eqs. (34)–(35) | `compiledSafety_source_correct` lifts the existing verdicts to source isolation and post-event forwarding. `projectedReachability_correct` checks the entire source trace within the indicated projection, and `normalizedReachability_correct` uses exact rows without a depth restriction. The Figure 5 regression checks the synchronized forwarding witness. |
| S7 Original tool queries | Parse the v1.1 property expression, preserve operator precedence and event identities, and prove that reachability, non-reachability and waypoint verdicts match the mathematical NetKAT expressions. Prove waypointing for the accepted network shape and distinguish endpoint-relation inclusion from an all-path claim. For the latter, use path-observing semantics or prove a suitable hypothesis such as unique paths. |
| S8 User-facing correctness | Prove parser/elaborator soundness and acceptance for the documented valid input language. Compose D1–D6, finite projection, S5 and N3/N6 into a parser-to-verdict iff for each property kind. Show that support checks, preprocessing reuse, graph normalization optimization and parallel scheduling preserve verdicts. Errors or resource exhaustion are a separate observable result. |
| S9 Case studies | The firewall source and query regressions and both [distributed-controller variants](PAPER_CONFORMANCE.md#distributed-controllers-in-arxiv-v4) have machine-checked results. The [FatTree migration](PAPER_CONFORMANCE.md#fattree-migration-in-arxiv-v4) remains open. The semantic foundation can represent all 1,344 switch identities, and the symbolic compiler, equivalence decision, and algebraic Lemma 5 support finite schemas. The source trace-safety translation also supports finite schemas. The DyNetKATLean graph, projection, and equational trace-safety proof chains support arbitrary finite schemas. Admission, ordered updates, per-phase forwarding, all-trace SSH isolation, final waypointing, and empirical parity and performance gates remain open. |

The translation needs a finite alphabet to build Θ and the bounded
word sums in the paper's finite syntax. For a finite network
specification, derive a finite support of packet letters and literal
reconfiguration labels after encapsulation. State whether traces are
required to lie in that alphabet or projected onto it and prove the
characterization under the selected convention. Arbitrary countably
many observable labels would need a finite abstraction or a different
translation.

### Printed safety ambiguities

- Def. 13 repeats the left term in the equation distributing on the
  left of a product. Distribution needs both terms to preserve the word
  language, consistent with the definition in prose and the chapter.
- Def. 17 gives same-kind negation sums. The accompanying prose suggests
  a whole-alphabet complement, which differs on mixed alphabets. Lean
  follows the explicit sums. The printed surface grammar permits nested
  negation, but no supplied clause eliminates it. `PrintedAction.elaborate`
  returns `none` for the nested case. Union, concatenation and repetition
  can still be nested over supported actions.
- Def. 17 admits only positive repetition. Eq. (28) ranges over all
  natural numbers. At n = 0 there is one possible prefix, the empty word,
  and `padded_zero` reduces the family member to the unpadded literal.
  This introduces no epsilon formula. An empty desugared sum forbids
  no word and uses the word-sum form of Eq. (27).
- Eq. (32) prints Z in the membership check of an N-prefixed term.
  Use N, as in Eq. (33) and the v1.1 implementation. Def. 4 and its
  prose also use π and π-derived test notation inconsistently in
  extraction examples. Use the complete test of the output valuation.
- The published §5 Eqs. (4)–(5) are not literally a characterization of
  an exact-length forbidden prefix for arbitrary networks. For example,
  a short prefix exposing a bad packet can be detected by head even
  when there is no execution long enough for the padded word. State
  the correct bounded condition with the packet action counted in
  the projection depth. The v4 firewall uses positive post-event
  reachability, which does not quantify over every later configuration.
- Def. 16 states an equational safety criterion and §V proposes a
  positive variant. The paper supplies no general parser-to-verdict
  theorem and no measured runtime guarantee. Prove the executable
  reductions at their actual domains.


### Checked concrete recursive analysis

- `ConcreteRow` uses `MovesExact` from the checked residual enumerator.
  Empty packet policies are filtered with the existing certified zero test.
  Send and receive remain in the row when the supplied root allows them.
  `NormalizationCandidate` serves the separate restricted sequential
  normalization path and uses only visible labels.
- `checkClosure_sound` checks root membership and every exact symbolic
  target. `ValidClosure.allReachable` uses reflexive-transitive closure with
  no depth index. `coversSource` transfers actual source executions through
  `Corr`, and `liftProperty` lifts any predicate established on the
  represented graph processes. `ConcreteStep` existentially quantifies
  packet lists at each step, so this process-level theorem also covers
  concatenations of edges whose packet lists need not compose.
- Finite projection describes exact behavior through the requested
  depth. Finite closure covers all depths when checking succeeds.
  Discovery failures carry no claim about finiteness, safety, or
  equivalence. A transition budget counts enumerated enabled symbolic row
  entries, including duplicates. A row is computed before its size is
  charged, so the budget does not bound the cost of computing a row.
- `ConcreteIdentity.structural` reuses `sameProcess_sound`. Callers can
  supply another partial test with a proof that a positive match implies
  actual graph syntax equality. Classifiers justify moves via
  `ProjectionSupport` and `CheckedResidual.Valid`. The structural test
  cannot identify residuals containing opaque restriction sets.
- `checkBisimulation_sound` checks symmetry and every outgoing move.
  Discovery starts from the product of the two concrete closures and prunes
  pairs using existential matching over all same-label alternatives.
  Identical symbolic labels preserve the same action and both packet lists
  by `MoveLabel.Realizes`. Packet policies with different syntax may be
  semantically equivalent, so symbolic matching can return `unknown`.
  `ValidBisimCertificate.bisimilar` transfers through `Corr`.
  The separate reconfiguration mismatch checker proves absence of a matching
  concrete action. Failure of relation discovery supplies no negative evidence.
- Regressions count one state and one edge for the recursive self-loop,
  three states and four edges for the mutually recursive nondeterministic
  fixture, four states and ten edges for `Host || Switch`, and two states
  and eleven edges for the unrestricted firewall. The firewall with an
  explicit outer restriction returns `cannotIdentifyState` with structural
  comparison. Its existing restricted normalization and projection proofs
  still apply. Spawning hits the four-state limit, is independently proved
  to admit no valid finite closure, and retains exact finite projection at
  every requested depth.

### Finite simulation abstractions and strong quotients

- `AbstractTable` uses `Fin n` nodes and executable lists of labeled
  successors. Its edges use `MoveLabel.Realizes` with the original action,
  input and output packets, and both pending and handled lists.
  Communication payload syntax remains literal.
- A user or heuristic supplies the table and a relation over graph
  residuals. `SimulationAbstraction` requires root representation and
  forward matching. `allReachable` and `liftProperty` apply at any depth.
  `coversSource` transfers source executions through `Corr`.
- `BisimulationQuotient` additionally requires backward matching for each
  represented residual. `sourceModel` uses `IsBisimulation2` with an
  executable finite model environment. When the original environment
  implements the table as well, `bisimilar` gives the existing
  same-environment `Bisimilar` theorem directly.
- Spawning residuals contain unspent reconfiguration prefixes and spent
  deadlocks. Action `a` adds an unspent blocker and `b` consumes one.
  Synchronization is impossible in that family. Matching successive
  `b` steps forces bisimilar residuals to have equal blocker counts.
  All counts are reachable, so a finite strong quotient is impossible.
  The forward abstraction allows both labels at one reachable abstract
  node and proves absence of packet, send and receive steps at every depth.
- The deadlock-spawning variant has distinct reachable syntax after each
  tick. Its one-node quotient proves source `Bisimilar` to a finite tick
  loop. A separate restriction example certifies a deadlock with an
  arbitrary blocked set without comparing sets.
- Existing finite concrete closure remains the preferred certificate for
  finite concrete derivatives. Exact projection supplies bounded analysis
  under its existing hypotheses. No automatic quotient inference is
  required by the proof-carrying API.

Simulation and strong quotient checking are certified tool extensions
that apply to some admitted Eq. (6) programs. The proofs above distinguish
infinite syntax from the existence of a finite exact behavioral model.
Paper-core finite projection and local branching still apply to the
admitted examples with infinite growth.

### Certified recursive strategy selection

- `AnalysisRequest` distinguishes explicit bounded inspection, all-depth
  state properties, and exact finite models. `analyzeCompiledSource` uses
  exact projection directly for explicit bounded requests. For the other
  requests it selects ground unfolding on acyclic dependencies before
  attempting concrete closure on cyclic dependencies.
- `AnalysisResult` retains the underlying ground derivation, closure,
  forward simulation, strong quotient, or exact depth-indexed projection
  proof. Concrete closure takes priority over supplied models. A strong
  quotient serves either unbounded request and a forward simulation serves
  an all-depth property request. If neither applies, the requested depth
  permits projection. Results retain the concrete discovery failure when
  taking a fallback route.
- `proveStateProperty` requires evidence on represented states before
  returning an all-depth property proof. A bounded model yields an unknown
  all-depth property verdict even if a property callback is supplied.
  Selection of the ground route exposes the derivation for separate
  ground analysis.
- `analyzeEquivalence` can use a checked reconfiguration mismatch,
  finite concrete bisimulation, or supplied exact pair evidence. Its
  positive evidence implies the existing `Bisimilar`, and an executable
  negative result carries a literal action witness and a proof of
  non-bisimilarity. Discovery failure is semantically neutral.
- `AnalysisGuarantee` exposes depth and table or certificate sizes for
  reporting. The abstract size counts declared nodes, including unreachable
  nodes. Model availability and a verdict about a particular query are
  distinct. Projection guarantees exact bounded behavior, concrete
  closure gives all-depth concrete coverage, forward simulation gives
  all-depth overapproximation, and strong quotients give exact finite
  behavioral models.

## Post-development package verification

After paper and parity development, the
[modularization plan](MODULARIZATION_PLAN.md) requires lower-layer builds
in isolation, theorem-backed external consumer examples, transitive
dependency checks, and regression and axiom evidence for the public
interfaces. Record that evidence against the verified development
baseline when moving definitions or retiring comparison oracles. These
release checks are separate from the paper proof obligations above.

## Optional / experimental tooling

These modules support external comparisons and possible future acceleration.
Their validation obligations apply only to those experiments. Core E_NK,
E_DNK, completeness, normalization and certified analysis use KATLean and
the existing Lean evaluator without a backend premise. Core imports exclude
the optional modules. Use `DyNetKAT.Experimental` for their exports.

### Fixed-domain backend validation

- `checkBackendRelation_sound` checks complete output sets against
  `execute_correct`. Its accepted rows agree with both
  `netkatNormalForm` and `normalize`. Star uses the evaluator's finite growth proof over reached packets.
- `checkBackendEquivalent_sound` validates a common relation for both
  policies. `checkBackendCounterexample_sound` validates a single
  distinguishing input by comparing its complete output sets.
- `decideWithBackend_correct` reduces every accepted or fallback
  decision to existing packet equivalence. The history and derivation
  bridges serve packet-prefix consumers. Communication payloads still
  use literal syntax.
- Integer-packet semantic correspondence is in `KATch.lean`.
  NKPL formatting, backend computation, and conversion to candidate
  JSON carry no proof authority. The [backend audit](NETKAT_AUDIT.md)
  records the verified live replay and its timings.

`checkEquationalCertificate_sound` validates a proposed common reduced
term through `E_NK` identity and zero laws and congruence, including
star congruence. `decideWithEquationalCertificate_correct` covers both
accepted candidates and fallback, without changing payload equality.
The optional KATch driver uses guarded assertions as candidate hints.
Its backend status has no semantic authority. Both live paths passed
against the pinned executable using Lean to certify the result. The
[source protocol audit](NETKAT_AUDIT.md#optional-katch-driver-and-equational-checking)
documents the launcher, protocol and replay outcomes.
Replaying a future symbolic certificate would require checking both
the connection from the original terms to the exported automata and
the symbolic bisimulation obligations.
