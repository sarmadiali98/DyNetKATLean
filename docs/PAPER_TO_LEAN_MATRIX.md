# Paper-to-Lean Correspondence Matrix

Read-only audit of the current workspace, including modified and untracked Lean sources. Paper locations refer to `DyNetKAT.pdf` (38 PDF pages; printed page references are supplied where recoverable). Selected pages were extracted with `pdftotext -layout`; figures and numbered statements are the anchors because printed and PDF pagination differ. Lean line numbers are workspace line numbers at audit time.

## Build result

Ran `lake build DyNetKAT` from `lean/`. Result: **success**. The command completed with exit status 0 and reported `Build completed successfully`; existing linter warnings remain, but there were no compilation errors. This only establishes compilation of the configured library target, not correspondence with all paper results.

## Correspondence

| Paper statement / rule | Lean correspondence | Exact Lean source | Status and scope |
|---|---|---|---|
| Figure 8 configuration `(d,H,H')` | `Config` fields `proc`, `pending`, `handled` | [`Config.lean`](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/Config.lean:11) | **Formalized only** as a structure; no theorem proving a global configuration correspondence. |
| Figure 8 labels `(σ,σ')`, `x?N`, `x!N`, `rcfg(x,N)` | `Action.packet`, `.recv`, `.send`, `.rcfg` | [`Action.lean`](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/Action.lean:9) | **Formalized only** as inductive constructors. |
| Figure 8 `(cpolX;)` NetKAT-to-process step | `Step.cpol_seq_ok`, premise `NetKAT.Semantics p sigma sigma'`; consumes pending head and pushes output to handled history | [`Semantics.lean`](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/Semantics.lean:13) | **Formalized** SOS rule; bridge is proved for executable outputs in `execute_packet_step`, but the entire SOS is not proved equivalent to the paper system. |
| Figure 8 `(cpolX)` recursive-variable rule | `Step.cpol_var`; successful `env.lookup name = some body`, then same labeled step from body | [`Semantics.lean`](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/Semantics.lean:156) | **Formalized only**. Explicit environment premise; no theorem that all recursive specifications are defined/guarded/productive. |
| Figure 8 two `(cpol⊕)` rules | `Step.cpol_choice_l`, `Step.cpol_choice_r` | [`Semantics.lean`](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/Semantics.lean:26) | **Formalized only** SOS constructors. |
| Figure 8 parallel interleaving | `Step.cpol_par_l`, `Step.cpol_par_r` | [`Semantics.lean`](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/Semantics.lean:50) | **Formalized** as SOS constructors; congruence for parallel is separately proved from a `Bisimilar` hypothesis (see below). |
| Figure 8 `(cpol!?)`, `(cpol?!)` parallel synchronization | `Step.cpol_sync_recv_send`, `Step.cpol_sync_send_recv` | [`Semantics.lean`](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/Semantics.lean:169) | **Formalized** constructors; distinct from communication-merge rules. |
| Later extended prefixes and `rcfg` prefix | `Step.cpol_recv`, `.cpol_send`, `.cpol_rcfg` | [`Semantics.lean`](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/Semantics.lean:123) | **Formalized only** constructors. `cpol_rcfg` belongs to the later extended language, while recv/send are also in Figure 8. |
| Later extended left merge and communication merge | `Step.cpol_left_merge`, `.cpol_comm_merge_recv_send`, `.cpol_comm_merge_send_recv` | [`Semantics.lean`](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/Semantics.lean:74) | **Formalized only**. These are later extended semantics, not Figure 8. |
| Later extended restriction and projection | `Step.cpol_restrict`, `Step.cpol_project` | [`Semantics.lean`](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/Semantics.lean:205) | **Formalized only** constructors. Restriction is limited to communication actions by the AST type. |
| Definition 2: bisimulation | `IsBisimulation env R` is symmetric and has one-way matching; symmetry supplies converse matching | [`Bisimulation.lean`](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/Bisimulation.lean:9) | **Formalized only** definition. It is parameterized by one fixed `RecEnv`; it does not encode “largest” as an operator. |
| Definition 2: bisimilarity as largest bisimulation | `Bisimilar env p q := ∃ R, IsBisimulation env R ∧ R p q` | [`Bisimulation.lean`](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/Bisimulation.lean:25) | **Formalized** as existence in a bisimulation. Reflexivity, symmetry, transitivity have proofs at lines 29, 38, 43. Largest-relation characterization/equivalence to the union of all bisimulations is not separately stated. |
| Proposition 1: `⟦p⟧=⟦q⟧ iff (p;d)~(q;d)` for all `d` | `execute_supported_iff_semantics` relates supported finite executable membership to the NetKAT relational semantics; `Step.cpol_seq_ok` exposes a packet step | [`NetKATBridge.lean`](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/NetKATBridge.lean:10), [`Semantics.lean`](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/Semantics.lean:14) | Paper Proposition 1 is **missing as a theorem**. The underlying packet-transition bridge is partially present, but no iff connecting denotational equality and process bisimilarity is proved. |
| Lemma 3: bisimilarity is a congruence | `Bisimilar.choice_left/right`, `parallel_left/right`, `leftMerge_left/right`, `commMerge_left/right`, `nSeq_left`, `recv_left`, `send_left`, `rcfgPrefix_left`, `restrict`, `project` | [`Bisimulation.lean`](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/Bisimulation.lean:68) | **Partially proved**: explicit contextual preservation theorems exist for the constructors represented in Lean. This is not a single full congruence theorem; recursion-variable context/substitution and any paper operators absent from Lean are not covered. |
| Figure 11 axiom system `EDNK` (A0–A15, AIP, plus `ENK`) | No Lean axiom relation, derivability judgment, or complete Figure 11 axiom set found | Search of all `lean/**/*.lean` sources; related NetKAT semantic laws in [`NetKAT/Semantics.lean`](/Users/ali/Desktop/DyNetKAT-Lean/packages/NetKATLean/NetKATLean/Core/Semantics.lean:352) | **Missing** as a DyNetKAT proof system. NetKAT semantic identities are not Figure 11 equational derivations. |
| Lemma 5: dup-free NetKAT normal forms | `NormalForm`, interpretation and semantic lemmas | [`NormalForm.lean`](/Users/ali/Desktop/DyNetKAT-Lean/packages/NetKATLean/NetKATLean/Core/NormalForm.lean:60) | **Partially formalized**: representation and semantic correspondences proved; no general `G` normalizer or `E_NK ⊢ p ≡ q`, so Lemma 5 is **not proved**. |
| Definition 7: guardedness | `GuardedOccurrences` and alias `IsGuarded` | [`Definedness.lean`](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/Definedness.lean:90) | **Formalized only; not shown equivalent**. It treats each prefix as guarding its entire continuation; paper Definition 7 uses a conditional recursive test on variables in the prefix subterm and continuation. |
| Recursive equations / guarded and defined specifications | `RecEnv`, `Defined`, `ReachableVar`, `ClosedDefined`, `WellFormed` | [`RecEnv.lean`](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/RecEnv.lean:9), [`Definedness.lean`](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/Definedness.lean:22) | **Partially proved**: helper implications about reachable definitions and well-formed bodies are proved. Not a proof of branching finiteness or AIP. |
| Lemma 8: guarded processes finitely branching | No branching-finiteness predicate/theorem over `Step` found | Search of all Lean sources | **Missing**. Finite packet domain alone does not prove the paper’s finite branching claim for all process transitions. |
| Lemma 9: every guarded process normalizes under `EDNK` | No DyNetKAT normalizer or equational derivability relation | [`Definedness.lean`](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/Definedness.lean:140) defines well-formedness only | **Missing**. |
| Lemma 10: soundness of `EDNK \ AIP` | No `EDNK` derivability or axiom soundness development | Search of all Lean sources | **Missing**. |
| Lemma 11: AIP soundness | No AIP axiom/theorem; `project` has SOS and congruence only | [`Semantics.lean`](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/Semantics.lean:205), [`Bisimulation.lean`](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/Bisimulation.lean:617) | **Missing**. Projection is not AIP; no guarded branching-finiteness proof exists. |
| Theorem 1: `EDNK` sound and ground-complete for DyNetKAT bisimilarity | No equational proof system nor theorem of this statement | Search of all Lean sources | **Missing**. Do not conflate with executable NetKAT correctness or packetTransitions soundness/completeness. |
| Additional executable NetKAT correctness | `execute_correct`: every NetKAT term evaluates to a supported finite set exactly matching relational semantics | [`NetKAT/Evaluator.lean`](/Users/ali/Desktop/DyNetKAT-Lean/packages/NetKATLean/NetKATLean/Core/Evaluator.lean:1078) | **Fully proved**, for the defined finite packet domain and all constructors in the `NetKAT` inductive, including bounded-star argument. This is not paper Theorem 1. |
| Additional executable DyNetKAT packet-step soundness/completeness | `packetTransitions_sound` and `.complete`; `execute_packet_step` | [`Executable.lean`](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/Executable.lean:57), [`NetKATBridge.lean`](/Users/ali/Desktop/DyNetKAT-Lean/lean/DyNetKAT/DyNetKAT/NetKATBridge.lean:24) | **Fully proved, restricted** to packet-processing transitions of an `nSeq` process. It is an enumeration/SOS correspondence, not bisimulation or algebraic soundness/completeness. |

## Scope warning

`execute_correct` concerns the NetKAT expression evaluator. `packetTransitions_sound` and `packetTransitions_complete` concern exact enumeration of the `nSeq` packet-step fragment. The paper’s Theorem 1 concerns derivability in the DyNetKAT axiom system and bisimilarity, including guarded recursion and AIP. Those are different propositions, with different domains and conclusions.

## Verbatim declaration index

Complete verbatim Lean declarations are included in [SOS_AND_BISIMULATION_AUDIT.md](/Users/ali/Desktop/DyNetKAT-Lean/docs/SOS_AND_BISIMULATION_AUDIT.md) and [LEAN_PROOF_STATUS_AND_SNIPPETS.md](/Users/ali/Desktop/DyNetKAT-Lean/docs/LEAN_PROOF_STATUS_AND_SNIPPETS.md), with exact source locations for `Step` and every SOS constructor, `IsBisimulation`, `Bisimilar`, `RecEnv`, `execute_correct`, `execute_packet_step`, `packetTransitions_sound`, and `packetTransitions_complete`. Complete congruence proof bodies are kept in their source module and linked with line anchors, rather than reconstructed in this matrix.

Status vocabulary: **fully proved** means a theorem proof is present and the requested library target compiles; **partially proved** means supporting lemmas or a restricted statement exist; **formalized only** means a definition/relation exists without the claimed result; **missing** means no corresponding development was found. These labels do not equate executable correctness with the paper’s algebraic theorem.

## Presentation proposal: approximately 18 slides / 30 minutes

| # | Slide | Time | Center of gravity |
|---:|---|---:|---|
| 1 | Research question and claim boundary | 1:00 | Dynamic network updates; what is and is not formalized here |
| 2 | Paper setting: NetKAT plus control plane | 1:30 | Dup-free policy fragment, channels, histories |
| 3 | Process syntax and Lean AST | 1:30 | `DyNetKAT` constructors; highlight extensions |
| 4 | Figure 8 configuration model | 1:30 | Pending/handled histories and labels |
| 5 | NetKAT relational semantics | 2:00 | `Semantics`, union, sequencing, star |
| 6 | Figure 8 base rule: packet evaluation | 2:00 | `cpol_seq_ok`, packet histories |
| 7 | Choice and parallel SOS | 1:30 | Choice, interleaving, synchronization |
| 8 | Restriction, projection, merge operators | 1:30 | Which paper rules are in `Step`, which are added |
| 9 | Definition 2: bisimulation | 2:00 | Relation, matching labels/config histories |
| 10 | Bisimulation properties proved | 1:30 | Equivalence properties and contextual theorems |
| 11 | Lemma 3 congruence comparison | 1:30 | Constructor-by-constructor result versus paper claim |
| 12 | Recursion environment design | 2:00 | `RecEnv := Var → Option DyNetKAT`; lookup semantics |
| 13 | `cpol_var` and recursive unfolding | 1:30 | Exact environment-relative rule; distinction from implicit paper notation |
| 14 | Definition 7 and well-formedness gap | 2:00 | Guardedness encoding, limitations, missing branching finiteness |
| 15 | Figure 11 / Lemmas 5, 8–11 / Theorem 1 status | 2:00 | Axiom system and major open proof obligations |
| 16 | Verified NetKAT evaluator | 2:00 | Finite packet enumeration and `execute_correct` |
| 17 | Verified packet transition bridge | 2:00 | `execute_packet_step`, `packetTransitions_sound/complete` |
| 18 | Results, limitations, research roadmap | 1:00 | Honest claims and next formalization milestones |

Total: 30:00. Center the narrative on the layered semantics and actual Lean proofs, with the final theorem-status slide explicitly distinguishing executable transition correctness from paper Theorem 1.
