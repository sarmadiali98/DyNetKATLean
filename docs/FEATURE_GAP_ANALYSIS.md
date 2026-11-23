# FEATURE_GAP_ANALYSIS.md — DyNetiKAT vs. DyNetKAT-Lean

**Task type:** Documentation-only gap analysis (planning task P2).
**Date:** 2026-10-17
**Repository analyzed:** `/Users/ali/Desktop/DyNetKAT-Lean`
**Reference material sources:**
- `docs/DYNETIKAT_REFERENCE_AUDIT.md` — reference tool audit (P1)
- `docs/PAPER_CONFORMANCE.md` — paper conformance map (31 items)
- `docs/PROOF_OBLIGATIONS.md` — proof obligations (31 theorems, 9 tiers)
- `docs/ARCHITECTURE.md` — proposed architecture
- `docs/NETKAT_AUDIT.md` — NetKAT phase 1.5 audit
- `docs/DESIGN_ALARMS.md` — design alarms log
- Lean source: `lean/DyNetKAT/NetKAT/{Packet,AST,Semantics,NormalForm}.lean`
- Python source: `python/tests/test_netkat.py`
- `HANDOFF.md` — progress checkpoints

---

## 0. Analysis methodology

For each documented DyNetiKAT capability, this analysis records:
- **Capability name**
- **Reference implementation evidence** (from P1 audit of DyNetiKAT)
- **Corresponding implementation** in `DyNetKAT-Lean`, if any
- **Current status:** Implemented / Partially implemented / Missing / Not verified
- **Executable?** — whether the current implementation is executable (can produce a result on input)
- **Machine-checked?** — whether correctness is verified by a Lean proof
- **Missing components** needed for parity
- **Required verification or regression tests**

Two axes are distinguished throughout:
1. **Executable analysis algorithm** — can the tool take a DyNetKAT program and produce a yes/no answer for a property?
2. **Machine-checked mathematical semantics** — are the semantics and proofs formalized in Lean?

These are separable: a feature may be implemented (Lean definition exists) but not proven correct (no theorem), or proven but not executable (relations live in `Prop` with no decision procedure).

---

## 1. Reference CLI and invocation

### 1.1 CLI entry point

| Field | Value |
|---|---|
| **Capability** | CLI entry point accepting Maude path, NetKAT tool path, JSON input, and options |
| **Reference evidence** | `dnk.py:20-32` — `python3 dnk.py <path_to_maude> <path_to_netkat_tool> <input_file> [options]` |
| **Our implementation** | `lean/DyNetKAT/Main.lean` — prints a project name string only. No CLI argument parsing, no JSON input, no analysis invocation. |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | A CLI that parses JSON input, parses DyNetKAT programs, executes the analysis pipeline (projection -> restriction -> head/tail -> equivalence), and reports results |
| **Required tests** | CLI invocation test against the reference benchmarks (stateful firewall, distributed controller) |

### 1.2 CLI options

| Field | Value |
|---|---|
| **Capability** | `-t/--threads` (parallel workers), `-p/--preprocessed`, `-v/--netkat-version`, `-s/--time-stats` |
| **Reference evidence** | `dnk.py:24-31` |
| **Our implementation** | None — `Main.lean` accepts no options |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | Option parsing, parallel execution, timing output, version selection |
| **Note** | Threading is an implementation concern of the CLI, not a mathematical feature |

### 1.3 Dependency installation

| Field | Value |
|---|---|
| **Capability** | `install.sh` — installs Python deps, Maude, and NetKAT tool |
| **Reference evidence** | `install.sh:1-22` |
| **Our implementation** | `lean/lakefile.toml` — declares Mathlib4 dependency. `python/pyproject.toml` — no external deps required beyond pytest. |
| **Status** | Not applicable (our approach is self-contained Lean, no external solvers) |
| **Executable** | N/A |
| **Machine-checked** | N/A |
| **Missing components** | None — by design, we do not depend on external solvers |
| **Note** | This is a deliberate architectural difference: DyNetiKAT is a tool that drives external solvers; ours is a self-contained formalization |

---

## 2. Input format (JSON schema)

| Field | Value |
|---|---|
| **Capability** | JSON input schema with keys `module_name`, `recursive_variables`, `program`, `channels`, `in_packets`, `out_packets`, `properties` |
| **Reference evidence** | `docs/DYNETIKAT_REFERENCE_AUDIT.md` Section 3; `README.md:85-131`; `dnk.py:52-54` |
| **Our implementation** | No JSON parser or schema. The `DyNetKAT` AST has no input format; terms are constructed directly in Lean. |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | JSON schema definition; JSON-to-DyNetKAT parser; JSON-to-normal-form converter |
| **Required tests** | Round-trip parsing of the reference benchmarks (stateful firewall, distributed controller, FatTree) |

---

## 3. NetKAT syntax

### 3.1 NetKAT^-dup syntax

| Field | Value |
|---|---|
| **Capability** | `N ::= 0 \| 1 \| f=v \| f<-v \| alpha \| pi \| N+N \| N;N \| N*` (dup-free fragment) |
| **Reference evidence** | PAPER_CONFORMANCE.md item 2; paper p. 6, Section I-B (Eq. 1) |
| **Our implementation** | `packages/NetKATLean/NetKATLean/Core/AST.lean:89-97` — `NetKAT` inductive with 8 constructors: `drop`, `id`, `test`, `completeTest`, `assign1`, `union`, `seq`, `star` |
| **Status** | Implemented |
| **Executable** | Partial — terms are inductive; `Predicate.eval` is computable, but full NetKAT semantics evaluation is not (see Section 3.3) |
| **Machine-checked** | N/A (syntax definition, not a theorem) |
| **Missing components** | A concrete parser from string encoding to `NetKAT` terms (for CLI use). The AST itself is complete and faithful. |
| **Required tests** | Parser round-trip tests for each constructor; conformance to Figure 3 syntax |

### 3.2 Predicate syntax

| Field | Value |
|---|---|
| **Capability** | `Pr ::= 0 \| 1 \| f=v \| Pr+Pr \| Pr.Pr \| ~Pr` (boolean predicates) |
| **Reference evidence** | PAPER_CONFORMANCE.md item 3; paper Figure 3, p. 5 |
| **Our implementation** | `packages/NetKATLean/NetKATLean/Core/AST.lean:37-44` — `Predicate` inductive with 6 constructors: `pFalse`, `pTrue`, `pFieldEq`, `pAnd`, `pOr`, `pNot` |
| **Status** | Implemented |
| **Executable** | `Predicate.eval` is computable (`Bool`-valued) |
| **Machine-checked** | Boolean algebra lemmas (`not_not`, `excluded_middle`, `contra`, `deMorgan_or`, `deMorgan_and`) proven in `AST.lean:205-229` |
| **Missing components** | None for syntax. The predicate type fully covers Figure 3. |
| **Required tests** | Golden tests for predicate evaluation on concrete packets |

### 3.3 NetKAT denotational semantics

| Field | Value |
|---|---|
| **Capability** | `[|N|] subset of Packet x Packet`, compositional: `[|0|]=empty`, `[|1|]={(s,s)}`, `[|N1+N2|]=[|N1|] union [|N2|]`, `[|N1;N2|]=[|N1|] circle [N2]`, `[|N*|]=Union_k [|N|]^k` |
| **Reference evidence** | PAPER_CONFORMANCE.md item 3; paper p. 6, Section I-B "Semantics"; `NETKAT_AUDIT.md` Section 3.5 |
| **Our implementation** | `Semantics.lean:61-71` — `Semantics (N : NetKAT) : CtxPkt -> CtxPkt -> Prop`, compositionally defined with `StarClosure` for Kleene star |
| **Status** | Implemented + verified |
| **Executable** | Partial — the relation is `Prop`-valued, not directly executable. `StarClosure` is an inductive type. |
| **Machine-checked** | Yes — `drop_empty`, `id_diag`, `union_sem`, `seq_sem`, `completeTest_sem`, `assign1_sem`, `assign1_seq_sem`, `assign_list_sem`, `fieldEnum_updates_complete`, `completeAssignExpr_sem`, Boolean/Kleene/packet algebra theorems all proven with no `sorry`/`admit`/`axiom` (verified Task 2U, 2V, 2M) |
| **Missing components** | A decision procedure for NetKAT equivalence (the external `katbv`/`netkat-automata` tool in DyNetiKAT). Requires implementing normalization algorithm and equivalence checking on normal forms. |
| **Required tests** | Regression tests for each semantic clause; equivalence decision procedure test suite |

### 3.4 NetKAT axioms (E_NK)

| Field | Value |
|---|---|
| **Capability** | NetKAT equational theory: `0+p=p`, `1*p=p*1=p`, associativity, Kleene algebra laws, Boolean algebra axioms (BA-EXCL-MID, BA-CONTRA), packet algebra axioms |
| **Reference evidence** | PAPER_CONFORMANCE.md item 14; paper Figure 4, p. 11; `docs/DYNETIKAT_REFERENCE_AUDIT.md` Section 11 |
| **Our implementation** | Semantic proofs of specific instances: `union_assoc`, `union_comm`, `union_idem`, `seq_distrib_left`, `seq_distrib_right`, `seq_id_left`, `seq_id_right`, `seq_drop_left`, `seq_drop_right`, `assign_overwrite`, `assign_comm_diff`, `assign_test_same_field`, `test_assign_same_field`, `pred_excluded_middle`, `pred_contra`, `pred_double_neg`, `pred_deMorgan_or`, `pred_deMorgan_and` (`Semantics.lean` and `AST.lean`) |
| **Status** | Partially implemented |
| **Executable** | No (these are mathematical theorems, not executable) |
| **Machine-checked** | Yes — all listed theorems are machine-checked in Lean with no proof holes |
| **Missing components** | The full E_NK axiomatization as a formal derivability relation (`E_NK |- p = q`). Currently we have semantic *theorems* (proofs about denotational semantics), not a syntactic *derivation system* (inductive relation over axiom applications). |
| **Required tests** | N/A (theorems are verified by compilation) |

### 3.5 NetKAT normal forms (Lemma 5)

| Field | Value |
|---|---|
| **Capability** | Every NetKAT term `p` has a normal form `q = Sum_{alpha*pi in G} alpha*pi` such that `E_NK |- p = q` |
| **Reference evidence** | PAPER_CONFORMANCE.md item 15; paper Lemma 5, p. 13; `PROOF_OBLIGATIONS.md` Tier 1.4; `docs/NETKAT_AUDIT.md` Section 0.4 |
| **Our implementation** | `packages/NetKATLean/NetKATLean/Core/NormalForm.lean` — `NormalForm` type (`Finset (CompleteTest x CompleteAssignmentValuation)`), `interpret`, `ofSummand_sem`, `interpret_sem`, `emptyNF_sem`, `idNF` + `idNF_sem`, `testNF` + `testNF_sem`, `assign1NF` + `assign1NF_sem`, `seqNF` + `mem_seqNF_iff` + `seqNF_sem`, `unionNF` + `unionNF_sem`, `fold_sem` |
| **Status** | Partially implemented |
| **Executable** | Partial — `interpret` is `noncomputable` (uses `Finset.toList`/`Finset.map`). The semantic correspondence theorems are proven but the *normalization algorithm* (function producing the normal form from a term) is not implemented. |
| **Machine-checked** | Yes — all semantic theorems proven with no proof holes |
| **Missing components** | 1. The normalization *algorithm* `G : NetKAT -> NormalForm` (Task 3D, 3E per PLAN.md). 2. The proof that `E_NK |- p = interpret(G(p))` (Lemma 5 itself). 3. `Fintype CtxPkt` instance was added (Task 2S, `Packet.lean:158-161`). |
| **Required tests** | Normalization algorithm tests; equivalence preservation tests |

### 3.6 Kleene star termination (finite iteration)

| Field | Value |
|---|---|
| **Capability** | `[|N*|] = Union_k [|N|]^k` terminates on finite packet domains |
| **Reference evidence** | PAPER_CONFORMANCE.md item 2; paper p. 6, Section I-B; `PROOF_OBLIGATIONS.md` Tier 1.2 |
| **Our implementation** | `Semantics.lean:51-53` — `StarClosure` inductive (reflexive-transitive closure). `star_refl`, `star_step` proven. `Fintype CtxPkt` added (Task 2S). |
| **Status** | Partially implemented |
| **Executable** | `StarClosure` is defined but no proof that iteration terminates on finite domains |
| **Machine-checked** | Partial — definition and basic properties proven, but finite-domain termination theorem not proven |
| **Missing components** | Proof that `StarClosure` on `Fintype CtxPkt` stabilizes after at most `|CtxPkt|^2` steps |
| **Required tests** | N/A (requires a finiteness proof) |

---

## 4. DyNetKAT syntax

| Field | Value |
|---|---|
| **Capability** | Extended DyNetKAT syntax (Eq. 6, p. 14): `bottom`, `N;D`, `x?N;D`, `x!N;D`, `rcfg(x,N);D`, `D||D`, `D oplus D`, `delta_L(D)`, `pi_n(D)`, `D << D`, `D | D`, `X` (recursion) |
| **Reference evidence** | PAPER_CONFORMANCE.md item 4; paper Figure 5 (p. 8), Figure 6 (p. 14), Eq. 6 (p. 14) |
| **Our implementation** | **None.** No `DyNetKAT.DyNetKAT.AST` module exists. The `lean/DyNetKAT/` directory contains only `Basic.lean`, `Main.lean`, and `NetKAT/` subdirectory. |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | - DyNetKAT process type (`bottom`, `;`, `x?N`, `x!N`, `rcfg`, `||`, `oplus`, `X`) <br> - Extended operators (`delta`, `pi_n`, `<<`, `| |`) <br> - Recursive variable handling <br> - Channel type (`Channel`) <br> - Configuration type `(d, H, H')` <br> - Action/label type `gamma` |
| **Required tests** | Syntax well-formedness; parser conformance to Figure 5 |

### 4.1 Specific DyNetKAT constructs

#### 4.1.1 Deadlock (bottom)

| Field | Value |
|---|---|
| **Capability** | The `bottom` (deadlock/bottom) process term — neutral element of `oplus` |
| **Reference evidence** | REF_AUDIT Section 4.2; paper Eq. 6, p. 14; A4 (p. 576) |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | `deadlock` constructor in DyNetKAT inductive type |

#### 4.1.2 Policy sequencing (N;d)

| Field | Value |
|---|---|
| **Capability** | Sequencing of a NetKAT policy N followed by a DyNetKAT process d |
| **Reference evidence** | REF_AUDIT Section 4.2; paper Eq. 6, p. 14 |
| **Our implementation** | None (only `NetKAT.seq` for NetKAT-internal sequencing exists) |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | `nSeq` constructor in DyNetKAT inductive type |

#### 4.1.3 Send and receive (x!N, x?N)

| Field | Value |
|---|---|
| **Capability** | Send (`x!N`) and receive (`x?N`) communication actions |
| **Reference evidence** | REF_AUDIT Section 4.2; paper Eq. 6, p. 14; Figure 8 (labels) |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | `send` and `recv` constructors with `Channel` and `NetKAT` parameters |

#### 4.1.4 Parallel composition (D || D)

| Field | Value |
|---|---|
| **Capability** | Parallel composition of two DyNetKAT processes |
| **Reference evidence** | REF_AUDIT Section 4.2; paper Eq. 6, p. 14; A5-A8 |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | `parallel` constructor; parallel transition rules |

#### 4.1.5 Nondeterministic choice (D oplus D)

| Field | Value |
|---|---|
| **Capability** | Nondeterministic choice between two DyNetKAT processes |
| **Reference evidence** | REF_AUDIT Section 4.2; paper Eq. 6, p. 14; A2-A5 |
| **Our implementation** | None (only `NetKAT.union` for NetKAT-internal choice) |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | `choice` (`oplus`) constructor in DyNetKAT type |

#### 4.1.6 rcfg constant

| Field | Value |
|---|---|
| **Capability** | Reconfiguration constant `rcfg(x,N)` — a synchronization step |
| **Reference evidence** | REF_AUDIT Section 4.2; paper Eq. 4, p. 13; Figure 8 |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | `rcfg` constructor in DyNetKAT syntax; rcfg transition rule |

#### 4.1.7 Recursive variables (X)

| Field | Value |
|---|---|
| **Capability** | Recursive variables with unique definitions; guarded recursion |
| **Reference evidence** | REF_AUDIT Section 4.2, 7.1; paper Eq. 6, p. 14; Definition 7 (guardedness), p. 13 |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | `var` constructor; variable environment; guardedness checker (Definition 7) |

---

## 5. Configurations and operational semantics

### 5.1 Multi-packet configurations (d, H, H')

| Field | Value |
|---|---|
| **Capability** | Configuration `(d, H, H')` where d is the process term, H is the pending packet list, H' is the handled packet list |
| **Reference evidence** | PAPER_CONFORMANCE.md item 5; paper p. 9, Section II-B; `PROOF_OBLIGATIONS.md` T2.1 |
| **Our implementation** | None — no `Config` structure exists in the codebase |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | `structure Config` with `proc : DyNetKAT`, `pending : List Packet`, `handled : List Packet` |
| **Required tests** | Configuration well-formedness; list operations (push/pop) |

### 5.2 Small-step labeled transition system (Fig. 8)

| Field | Value |
|---|---|
| **Capability** | Labeled transition relation `(d, H, H') ->_gamma (d', H'', H''')` with actions `gamma ::= (sigma,sigma') | x?r | x!r | rcfg(x,r)` |
| **Reference evidence** | PAPER_CONFORMANCE.md item 7; paper p. 9-10, Figure 8; `PROOF_OBLIGATIONS.md` T2.2 |
| **Our implementation** | None — no `Step` inductive relation exists |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | `inductive Step : Config -> Action -> Config -> Prop` with all rules: `cpol_seq_ok`, `cpol_seq_bad` (drop), `cpol_choice`, `cpol_parallel`, `cpol_recv`, `cpol_send`, `cpol_sync`; `Action` type |
| **Required tests** | Each transition rule: valid derivations and counter-examples for invalid transitions |

### 5.3 Per-packet consistency

| Field | Value |
|---|---|
| **Capability** | Each packet is processed by exactly one flow table (process term) throughout its flight |
| **Reference evidence** | PAPER_CONFORMANCE.md item 29; paper p. 8-9, Section II-B |
| **Our implementation** | None (no DyNetKAT syntax exists to enforce this) |
| **Status** | Missing |
| **Executable** | N/A |
| **Machine-checked** | N/A |
| **Missing components** | Theorem stating the invariant; depends on operational semantics (T2.2) |
| **Required tests** | N/A (design invariant) |

---

## 6. Extended DyNetKAT operators

### 6.1 Restriction operator (delta_L)

| Field | Value |
|---|---|
| **Capability** | `delta_L(p)` filters transitions whose labels are in L (encapsulation set) |
| **Reference evidence** | PAPER_CONFORMANCE.md item 8; paper p. 12, Section III; Eq. 2; REF_AUDIT Section 6.1; `PROOF_OBLIGATIONS.md` T3.1 |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | `delta` operator definition; restriction axioms (delta; bot, delta; receive, delta; send, delta; rcfg, delta; plus) |
| **Required tests** | Restriction preserves bisimulation equivalence |

### 6.2 Projection operator (pi_n)

| Field | Value |
|---|---|
| **Capability** | `pi_n(p)` captures first n steps of a DyNetKAT policy (bounded unfolding) |
| **Reference evidence** | PAPER_CONFORMANCE.md item 9; paper p. 12, Section III; Eq. 3; REF_AUDIT Section 6.2; `PROOF_OBLIGATIONS.md` T3.2 |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | `pi` operator definition; projection axioms (Pi-0, Pi-1, Pi-netkat, Pi-receive, Pi-send, Pi-rcfg, Pi-plus) |
| **Required tests** | `pi_0(p) = bottom`; `pi_n(bottom) = bottom`; `pi_{n+1}(at; p) = at; pi_n(p)` |

### 6.3 rcfg constant

| Field | Value |
|---|---|
| **Capability** | `rcfg(x,r);p ->_{rcfg(x,r)} p` — instantaneous synchronization step |
| **Reference evidence** | PAPER_CONFORMANCE.md item 10; paper p. 13, Section III-A; Eq. 4; REF_AUDIT Section 4.2 |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | `rcfg` constructor in DyNetKAT syntax; rcfg transition rule |
| **Required tests** | rcfg steps immediately to continuation |

### 6.4 Left-merge (<<) and communication-merge (| |)

| Field | Value |
|---|---|
| **Capability** | Left-merge `p << q` and communication-merge `p | q` — internal operators for axiomatization |
| **Reference evidence** | PAPER_CONFORMANCE.md item 11; paper p. 13, Section III-A; Eq. 5; REF_AUDIT Section 4.2 |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | `leftMerge` and `commMerge` constructors; their transition rules (A10-A15) |
| **Required tests** | Left-merge rule correctness; communication-merge synchronization |

---

## 7. DyNetKAT axiomatization (A0-A15, AIP, A16)

### 7.1 Axioms A0-A15 (Fig. 11)

| Field | Value |
|---|---|
| **Capability** | Full DyNetKAT equational theory: A0 (deadlock sequencing), A1 (NetKAT sum to DyNetKAT choice), A2-A5 (choice laws), A6-A7 (parallel laws), A8 (parallel expansion), A9-A10 (left-merge), A11 (left-merge distributes over choice), A12 (communication synchronization), A13-A15 (communication-merge laws) |
| **Reference evidence** | REF_AUDIT Section 11.2; paper p. 11, Figure 11; PAPER_CONFORMANCE.md item 13 |
| **Our implementation** | None — no `AxEq` inductive relation or `EDNK` derivability exists |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | `inductive AxEq : DyNetKAT -> DyNetKAT -> Prop` with A0-A15 cases; `EDNK` derivation relation (reflexive, symmetric, transitive closure + substitution closure) |
| **Required tests** | Each axiom: soundness w.r.t. bisimilarity (Lemma 10) |

### 7.2 Approximation Induction Principle (AIP)

| Field | Value |
|---|---|
| **Capability** | `p = q` if for all `n`: `pi_n(p) = pi_n(q)` |
| **Reference evidence** | REF_AUDIT Section 11.2; paper p. 11, AIP; PAPER_CONFORMANCE.md item 12; `PROOF_OBLIGATIONS.md` T5.2 |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | AIP theorem statement; proof using sequence construction S_n, finite branching, diagonalization |
| **Required tests** | N/A (meta-principle) |

### 7.3 Trace-equivalence axiomatization (A16)

| Field | Value |
|---|---|
| **Capability** | `E_DNK^tr = E_DNK + {A16}` where A16: `p;(q oplus r) = p;q oplus p;r` |
| **Reference evidence** | PAPER_CONFORMANCE.md item 16; paper Definition 15, p. 19; REF_AUDIT Section 13.5 |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | A16 axiom in the derivation relation |
| **Required tests** | N/A (just adding an axiom) |

---

## 8. Bisimulation

### 8.1 Bisimulation definition (Definition 2)

| Field | Value |
|---|---|
| **Capability** | Bisimulation relation R: for (p,q) in R, if `p ->_gamma p'` then exists `q'` with `q ->_gamma q'` and `(p',q') in R` |
| **Reference evidence** | PAPER_CONFORMANCE.md item 17; paper p. 11, Definition 2; `PROOF_OBLIGATIONS.md` T4.1 |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | Coinductive bisimulation definition or greatest fixed point |
| **Required tests** | N/A (definition) |

### 8.2 Bisimilarity congruence (Lemma 3)

| Field | Value |
|---|---|
| **Capability** | Bisimilarity (~) is preserved by all DyNetKAT operators |
| **Reference evidence** | PAPER_CONFORMANCE.md item 18; paper p. 14, Lemma 3 |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | Congruence proof for all operators; requires coinduction |
| **Required tests** | N/A (theorem) |

### 8.3 Semantic layering (Proposition 1)

| Field | Value |
|---|---|
| **Capability** | For p,q in NetKAT^-dup and any d: `[|p|] = [|q|]` iff `(p;d) ~ (q;d)` |
| **Reference evidence** | PAPER_CONFORMANCE.md item 19; paper p. 11, Proposition 1 |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | Proposition 1 theorem; requires bisimilarity and operational semantics |
| **Required tests** | N/A (theorem) |

---

## 9. Soundness and completeness

### 9.1 Soundness (Theorem 1, part 1)

| Field | Value |
|---|---|
| **Capability** | `E_DNK |- p = q` implies `p ~ q` |
| **Reference evidence** | PAPER_CONFORMANCE.md item 20; paper p. 11, Theorem 1; `PROOF_OBLIGATIONS.md` T7.1 |
| **Our implementation** | NetKAT semantic identities are proven (Section 3.4), but no full E_DNK soundness theorem |
| **Status** | Partially implemented |
| **Executable** | No |
| **Machine-checked** | Partial — individual NetKAT axioms are proven as semantic theorems, but A0-A15 + AIP soundness not established |
| **Missing components** | Soundness proofs for all 15 axioms + AIP (Lemmas 10, 11) |
| **Required tests** | N/A (theorems) |

### 9.2 Ground-completeness (Theorem 1, part 2)

| Field | Value |
|---|---|
| **Capability** | `p ~ q` implies `E_DNK |- p = q` (for ground terms) |
| **Reference evidence** | PAPER_CONFORMANCE.md item 21; paper p. 15, Theorem 1; `PROOF_OBLIGATIONS.md` T7.2 |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | Normalization (Lemma 9); summand matching; relies on Lemma 5 (NetKAT completeness) |
| **Required tests** | N/A (theorem) |

### 9.3 Branching finiteness (Lemma 8)

| Field | Value |
|---|---|
| **Capability** | All guarded DyNetKAT policies are finitely branching |
| **Reference evidence** | PAPER_CONFORMANCE.md item 6; paper p. 13, Lemma 8; `PROOF_OBLIGATIONS.md` T5.3 |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | Guardedness definition (Definition 7); branching finiteness proof |
| **Required tests** | N/A (theorem) |

---

## 10. Safety framework

### 10.1 Safety property syntax (Definition 12)

| Field | Value |
|---|---|
| **Capability** | Safety properties as regexps over alphabet `{alpha*pi, rcfg(x,p)}` with `[regexp]false` notation |
| **Reference evidence** | PAPER_CONFORMANCE.md item 22; paper p. 17, Definition 12; `PROOF_OBLIGATIONS.md` T8.1 |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | `Regexp` inductive type; `Prop` inductive type with `unsafe` constructor |
| **Required tests** | Regexp parsing conformance |

### 10.2 Head normal forms (Definition 13)

| Field | Value |
|---|---|
| **Capability** | `hnf(r)` distributes sequence over union in regexps |
| **Reference evidence** | PAPER_CONFORMANCE.md item 23; paper p. 17-18, Definition 13; `PROOF_OBLIGATIONS.md` T8.2 |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | `hnf` function definition + correctness theorem |
| **Required tests** | N/A (definition) |

### 10.3 Safety property semantics (Definition 14)

| Field | Value |
|---|---|
| **Capability** | Semantic map `[|prop|] : Prop -> DyNetKAT` using `Theta` (all behaviors), head/tail extraction |
| **Reference evidence** | PAPER_CONFORMANCE.md item 24; paper p. 18-19, Definition 14; `PROOF_OBLIGATIONS.md` T8.1 |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | `Theta` recursive definition; `[|prop|]` semantic map; correctness proof |
| **Required tests** | N/A (definition) |

### 10.4 Safe network system checking (Definition 16)

| Field | Value |
|---|---|
| **Capability** | Network `i` is safe w.r.t. spec `s` iff `E_DNK^tr |- [|s|] oplus i = [|s|]` |
| **Reference evidence** | PAPER_CONFORMANCE.md item 25; paper p. 19, Definition 16; REF_AUDIT Section 10.4; `PROOF_OBLIGATIONS.md` T8.4 |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | `IsSafe` predicate; full safety checking pipeline; equivalence decision procedure |
| **Required tests** | Safety verification tests against reference benchmarks |

### 10.5 Extended safety sugars (Definition 17)

| Field | Value |
|---|---|
| **Capability** | Extended actions (`act_e ::= alpha*pi | rcfg(x,p) | ~act_e`), extended regexps, desugaring `ds` |
| **Reference evidence** | PAPER_CONFORMANCE.md item 25; paper p. 20, Definition 17; `PROOF_OBLIGATIONS.md` T8.5 |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | Extended regexp types; `ds` desugaring function; semantics preservation proof |
| **Required tests** | Desugaring correctness tests |

---

## 11. Verification properties

### 11.1 Reachability property checking

| Field | Value |
|---|---|
| **Capability** | Check if egress is reachable from ingress: `in . (p . t)* . out != 0` (reachable) or `== 0` (unreachable) |
| **Reference evidence** | REF_AUDIT Section 5.2, 10.1; paper p. 912-913; README.md:65-68 |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | Reachability property encoding; NetKAT equivalence decision procedure; `head` operator extraction |
| **Required tests** | Reachability tests on stateful firewall, distributed controller, FatTree benchmarks |

### 11.2 Waypointing property checking

| Field | Value |
|---|---|
| **Capability** | Check if a waypoint `w` is on all paths from `in` to `out` |
| **Reference evidence** | REF_AUDIT Section 5.3, 10.2; paper p. 923-926; README.md:69 |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | Waypointing property encoding; equivalence decision procedure; `tail` operator extraction |
| **Required tests** | Waypointing tests on FatTree benchmarks |

### 11.3 Parallel property checking

| Field | Value |
|---|---|
| **Capability** | `-t/--threads` option for parallel property checking across packet/property pairs |
| **Reference evidence** | REF_AUDIT Section 1.2, 5; `dnk.py:24-25` |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | Parallel execution framework; result aggregation |
| **Note** | This is a performance/implementation concern, not a mathematical feature |

### 11.4 head() operator — current configuration extraction

| Field | Value |
|---|---|
| **Capability** | `head(D)` extracts the NetKAT policy representing the current configuration of DyNetKAT term D |
| **Reference evidence** | REF_AUDIT Section 6.3; paper p. 969-985; `dnk.maude:130-131, 141-143` |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | `head` function: `DyNetKAT -> NetKAT`; transition rules (head(bot)=0, head(Z;D)=Z+head(D), etc.) |
| **Required tests** | head extraction on example programs |

### 11.5 tail() operator — post-synchronization policy extraction

| Field | Value |
|---|---|
| **Capability** | `tail(D, RSet)` extracts the DyNetKAT policy after synchronization events in RSet |
| **Reference evidence** | REF_AUDIT Section 6.4; paper p. 969-985; `dnk.maude:132, 145-149` |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | `tail` function: `DyNetKAT x RSet -> DyNetKAT`; transition rules |
| **Required tests** | tail extraction on example programs |

---

## 12. Preprocessing

| Field | Value |
|---|---|
| **Capability** | Preprocessing pipeline: parse recursive variables with Maude, extract NetKAT sub-terms, zero-eliminate equivalent-to-zero terms, generate final Maude module |
| **Reference evidence** | REF_AUDIT Section 5.1, 7.3; `preprocess.py:78-129`, `preprocess.maude`; README.md |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | 1. NetKAT sub-term extraction from DyNetKAT terms. 2. Zero-elimination (check if a NetKAT term equals 0). 3. Recursive variable unfolding. |
| **Note** | In a Lean formalization, this would be replaced by the normalization algorithm + equivalence decision procedure |
| **Required tests** | Preprocessing round-trip on reference benchmarks |

---

## 13. Diagnostics and output

### 13.1 Console output

| Field | Value |
|---|---|
| **Capability** | Per (packet, property) pair: prints satisfied/violated/error. Optional timing breakdown. |
| **Reference evidence** | REF_AUDIT Section 8.1; `dnk.py:86-100` |
| **Our implementation** | `Main.lean` prints a project name string only |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | Result formatting; status classification; timing output |
| **Required tests** | Output format conformance |

### 13.2 Output files

| Field | Value |
|---|---|
| **Capability** | Writes preprocessed JSON output; temporary Maude output files |
| **Reference evidence** | REF_AUDIT Section 8.2; `dnk.py:63-67` |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | JSON output writer; temp file management |
| **Note** | Output format is a tool/CLI concern, not a mathematical feature |
| **Required tests** | Output file format conformance |

---

## 14. Benchmarks

### 14.1 Stateful firewall

| Field | Value |
|---|---|
| **Capability** | Models the firewall from Figure 3: Host || Switch with recursive variables, channels secConReq/secConEnd, reachability properties |
| **Reference evidence** | REF_AUDIT Section 9.1; paper Figure 1 (p. 3), Figure 5 (p. 8) |
| **Our implementation** | Python `examplePolicy := .seq tpSrc8Test .drop` (test only) in `AST.lean:190`; Python `test_tpSrc8_drop` in `test_netkat.py:237-247` |
| **Status** | Partially implemented (test only) |
| **Executable** | Python test is executable; Lean terms are not (no parser/CLI) |
| **Machine-checked** | No — the Lean `examplePolicy` is a definition, not a verified property |
| **Missing components** | Full DyNetKAT encoding of the firewall; safety property verification; proof that packets at port=ext cannot reach port=int before reconfiguration |
| **Required tests** | T9.1 (PAPER_CONFORMANCE.md); full firewall safety property proof |

### 14.2 Distributed controller

| Field | Value |
|---|---|
| **Capability** | Two controllers (C1, C2) independently or synchronously updating switches; cross-destination breach prevention |
| **Reference evidence** | REF_AUDIT Section 9.2; paper Figure 2 (p. 4), Figure 6 (p. 14) |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | DyNetKAT encoding of controllers; synchronization; safety property verification |
| **Required tests** | T9.2 (PAPER_CONFORMANCE.md); proof that synchronization prevents breach |

### 14.3 FatTree topologies

| Field | Value |
|---|---|
| **Capability** | FatTree topology generation (pods 6-16), reachability and waypointing properties |
| **Reference evidence** | REF_AUDIT Section 9.3; paper p. 1016-1028; `fattree.py`, `run_fattree.sh` |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | Topology generator (Python adapter); DyNetKAT encoding of FatTree policies; property checking |
| **Note** | FatTree generation is a Python adapter task; the verification must be formalized in Lean |
| **Required tests** | T9.2 (PAPER_CONFORMANCE.md); waypointing property on FatTree |

### 14.4 Benchmark performance reporting

| Field | Value |
|---|---|
| **Capability** | Timing breakdown (total, preprocessing, NetKAT decision time); parallel overhead measurement |
| **Reference evidence** | REF_AUDIT Section 12; `dnk.py:96-100`, paper Figure 8 |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | Timing instrumentation; benchmark harness |
| **Note** | This is a tool/implementation concern, not a mathematical feature |

---

## 15. Internal reference algorithms (DyNetiKAT backend)

The following are internal algorithms used by the DyNetiKAT reference tool that
are distinct from user-facing features. They represent the core analysis machinery
that must be reproduced with machine-checked correctness.

### 15.1 Maude equational rewriting pipeline

| Field | Value |
|---|---|
| **Capability** | Applies E_DNK axioms via Maude rewriting to normalize DyNetKAT terms |
| **Reference evidence** | REF_AUDIT Section 0 (architecture); `dnk.maude:46-90`; `preprocess.py`, `maude_parser.py` |
| **Our implementation** | None — we use a self-contained Lean formalization without external Maude |
| **Status** | Missing (replaced by approach) |
| **Executable** | N/A |
| **Machine-checked** | N/A |
| **Missing components** | N/A — replaced by the Lean normalization algorithm (Section 3.5) and A0-A15 derivability (Section 7.1) |
| **Note** | Maude is prohibited; our replacement is a Lean-based derivation/normalization system |

### 15.2 NetKAT decision procedure

| Field | Value |
|---|---|
| **Capability** | Checks NetKAT term equivalence via `katbv` or `netkat-automata` external tools |
| **Reference evidence** | REF_AUDIT Section 0; `netkat_parser.py:42-56`; README.md |
| **Our implementation** | None — no equivalence decision procedure exists |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | A Lean-based NetKAT equivalence decision procedure operating on normal forms |
| **Note** | External NetKAT solvers are prohibited; must be reproduced in Lean |

### 15.3 Recursive variable unfolding (pi_n)

| Field | Value |
|---|---|
| **Capability** | Lazy/on-demand unfolding of recursive variables driven by projection operator |
| **Reference evidence** | REF_AUDIT Section 7; `dnk.maude:109-122`; paper p. 958 |
| **Our implementation** | None |
| **Status** | Missing |
| **Executable** | No |
| **Machine-checked** | N/A |
| **Missing components** | `pi_n` operator (Section 6.2); on-demand unfolding strategy |

---

## 16. Summary tables

### 16.1 Feature inventory — implemented vs. missing

| # | Capability | Reference evidence | Our status | Executable | Machine-checked |
|---|---|---|---|---|---|
| 1 | CLI entry point | `dnk.py:20-32` | Missing | No | N/A |
| 2 | JSON input schema | `dnk.py:52-54` | Missing | No | N/A |
| 3 | NetKAT syntax (8 constructors) | PAPER_CONFORMANCE:2 | Implemented | Partial | N/A |
| 4 | Predicate syntax | PAPER_CONFORMANCE:3 | Implemented | Yes | Yes |
| 5 | NetKAT denotational semantics | PAPER_CONFORMANCE:3 | Implemented | Partial | Yes |
| 6 | NetKAT axioms (E_NK) | PAPER_CONFORMANCE:14 | Partially implemented | No | Partial |
| 7 | NetKAT normal forms (Lemma 5) | PAPER_CONFORMANCE:15 | Partially implemented | Partial | Yes (semantics) |
| 8 | Kleene star termination | PAPER_CONFORMANCE:2 | Partially implemented | No | Partial |
| 9 | DyNetKAT syntax | PAPER_CONFORMANCE:4 | Missing | No | N/A |
| 10 | Configurations (d,H,H') | PAPER_CONFORMANCE:5 | Missing | No | N/A |
| 11 | Labeled SOS (Fig. 8) | PAPER_CONFORMANCE:7 | Missing | No | N/A |
| 12 | Per-packet consistency | PAPER_CONFORMANCE:29 | Missing | N/A | N/A |
| 13 | Restriction (delta) | PAPER_CONFORMANCE:8 | Missing | No | N/A |
| 14 | Projection (pi_n) | PAPER_CONFORMANCE:9 | Missing | No | N/A |
| 15 | rcfg constant | PAPER_CONFORMANCE:10 | Missing | No | N/A |
| 16 | Left-merge / comm-merge | PAPER_CONFORMANCE:11 | Missing | No | N/A |
| 17 | A0-A15 axioms | PAPER_CONFORMANCE:13 | Missing | No | N/A |
| 18 | AIP | PAPER_CONFORMANCE:12 | Missing | No | N/A |
| 19 | A16 (trace eq) | PAPER_CONFORMANCE:16 | Missing | No | N/A |
| 20 | Bisimulation (Def 2) | PAPER_CONFORMANCE:17 | Missing | No | N/A |
| 21 | Bisimilarity congruence | PAPER_CONFORMANCE:18 | Missing | No | N/A |
| 22 | Semantic layering | PAPER_CONFORMANCE:19 | Missing | No | N/A |
| 23 | Soundness (Thm 1) | PAPER_CONFORMANCE:20 | Missing | No | N/A |
| 24 | Ground-completeness | PAPER_CONFORMANCE:21 | Missing | No | N/A |
| 25 | Branching finiteness | PAPER_CONFORMANCE:6 | Missing | No | N/A |
| 26 | Safety syntax (Def 12) | PAPER_CONFORMANCE:22 | Missing | No | N/A |
| 27 | Head normal forms | PAPER_CONFORMANCE:23 | Missing | No | N/A |
| 28 | Safety semantics (Def 14) | PAPER_CONFORMANCE:24 | Missing | No | N/A |
| 29 | Safe systems (Def 16) | PAPER_CONFORMANCE:25 | Missing | No | N/A |
| 30 | Extended sugars (Def 17) | PAPER_CONFORMANCE:25 | Missing | No | N/A |
| 31 | Reachability checking | REF_AUDIT:5.2 | Missing | No | N/A |
| 32 | Waypointing checking | REF_AUDIT:5.3 | Missing | No | N/A |
| 33 | head() operator | REF_AUDIT:6.3 | Missing | No | N/A |
| 34 | tail() operator | REF_AUDIT:6.4 | Missing | No | N/A |
| 35 | Preprocessing pipeline | REF_AUDIT:5.1 | Missing | No | N/A |
| 36 | Stateful firewall | REF_AUDIT:9.1 | Partial (test only) | Partial | No |
| 37 | Distributed controller | REF_AUDIT:9.2 | Missing | No | N/A |
| 38 | FatTree benchmarks | REF_AUDIT:9.3 | Missing | No | N/A |
| 39 | Parallel execution | REF_AUDIT:5 | Missing | No | N/A |
| 40 | Diagnostics/output | REF_AUDIT:8 | Missing | No | N/A |

### 16.2 Implemented capabilities (with machine-checked proofs)

| Capability | Lean location | Machine-checked proofs |
|---|---|---|
| Finite packet model (Fintype instances) | `Packet.lean:117-161` | `Fintype FieldName`, `Fintype FieldValueEnum`, `Fintype CtxPkt`, `Fintype CompleteTest`, `Fintype CompleteAssignmentValuation` (Task 2S) |
| Parameterized Packet type | `Packet.lean:36-110` | `Packet.ext`, `Packet.get_update_same`, `Packet.get_update_diff`, `Packet.update_id`, `Packet.update_update_same`, `Packet.update_update_diff` |
| Predicate syntax + eval | `AST.lean:37-77` | `Predicate.not_not`, `Predicate.excluded_middle`, `Predicate.contra`, `Predicate.deMorgan_or`, `Predicate.deMorgan_and` |
| NetKAT syntax (8 constructors) | `AST.lean:89-97` | (definition, not a theorem) |
| CompleteTest as total valuation | `Packet.lean:193` | `holdsComplete_iff_eq` (Task 3D-1) |
| CompleteAssignmentValuation | `Packet.lean:253-281` | `applyValuation_field` |
| assign1 primitive constructor | `AST.lean:94` | (definition) |
| completeAssignExpr | `AST.lean:137` | `completeAssignExpr_sem` |
| fieldEnum completeness | `AST.lean:150-156` | `fieldEnum_complete`, `fieldEnum_nodup` |
| NetKAT semantics (8 clauses) | `Semantics.lean:61-71` | `drop_empty`, `id_diag`, `union_sem`, `seq_sem`, `completeTest_sem`, `assign1_sem`, `assign1_seq_sem`, `assign_list_sem` |
| Kleene star semantics | `Semantics.lean:51-53` | `star_refl`, `star_step` |
| Seq deterministic semantics | `Semantics.lean:114-137` | `seq_deterministic_sem` |
| Boolean algebra laws | `Semantics.lean:498-550` | `pred_excluded_middle`, `pred_contra`, `pred_double_neg`, `pred_deMorgan_or`, `pred_deMorgan_and` |
| Packet algebra laws | `Semantics.lean:558-588` | `assign_overwrite`, `assign_comm_diff`, `assign_test_same_field`, `test_assign_same_field` |
| NormalForm type + interpretation | `NormalForm.lean:60-120` | `ofSummand_sem`, `interpret_sem`, `fold_sem`, `emptyNF_sem`, `idNF_sem`, `testNF_sem`, `assign1NF_sem`, `seqNF_sem`, `unionNF_sem` |
| fieldEnum_updates_complete | `Semantics.lean:595-616` | `fieldEnum_updates_complete` |
| completeAssignExpr_sem | `Semantics.lean:635-655` | `completeAssignExpr_sem` |
| fieldEnum_nodup | `AST.lean:156` | `fieldEnum_nodup` |
| seqNF membership | `NormalForm.lean:802-845` | `mem_seqNF_iff` |

---


---

## 17. Mathematical objectives mapping

This section maps existing mathematical objectives from `docs/PROOF_OBLIGATIONS.md`
(31 theorems across 9 tiers) to the current implementation status.

### Tier 1 — NetKAT semantic core (foundational)

| Item | Paper reference | Description | Status |
|---|---|---|---|
| T1.1 | Lemma 5 (p. 13) | Fintype instances for A (complete tests) and Π (complete assignments) | **Proved** — `Fintype CtxPkt`, `Fintype CompleteTest`, `Fintype CompleteAssignmentValuation` added in `Packet.lean:158-247` (Task 2S) |
| T1.2 | §I-B (p. 6) | NetKAT denotational semantics well-defined; star terminates on finite domains | **Partially proved** — semantics defined (`Semantics.lean:61-71`); `StarClosure` defined; basic star theorems (`star_refl`, `star_step`) proven; **finite-domain termination of star NOT proved** |
| T1.3 | §I-B, Fig. 4 | Basic semantic identities (0, 1, union, seq, star) | **Proved** — `drop_empty`, `id_diag`, `union_sem`, `seq_sem`, `star_refl`, `star_step` |
| T1.4 | Lemma 5 (p. 13) | NetKAT normal forms: `q = Sum_{alpha*pi in G} alpha*pi` | **Partially proved** — NormalForm type and `interpret` defined; semantic correspondence theorems proven (`ofSummand_sem`, `interpret_sem`, etc.); **normalization algorithm `G` and Lemma 5 proof NOT implemented** |

### Tier 2 — DyNetKAT syntax & operational semantics

| Item | Paper reference | Description | Status |
|---|---|---|---|
| T2.1 | Fig. 5 (p. 8) | DyNetKAT syntax well-defined (extended syntax with recursion) | **Missing** — no DyNetKAT syntax module exists |
| T2.2 | Fig. 8 (p. 9-10) | Operational semantics is well-defined (labeled transition system) | **Missing** — no `Step` relation |
| T2.3 | p. 8-9 (§II-B) | Per-packet consistency | **Missing** — depends on T2.2 |

### Tier 3 — Extended operators

| Item | Paper reference | Description | Status |
|---|---|---|---|
| T3.1 | Eq. 2 (p. 12) | Restriction semantics (delta_L) | **Missing** |
| T3.2 | Eq. 3 (p. 12) | Projection semantics (pi_n) | **Missing** |
| T3.3 | Eq. 4 (p. 13) | rcfg constant semantics | **Missing** |
| T3.4 | Eq. 5 (p. 13) | Left-merge and communication-merge rules | **Missing** |
| T3.5 | Definition 7 (p. 13) | Guardedness | **Missing** |

### Tier 4 — Bisimulation

| Item | Paper reference | Description | Status |
|---|---|---|---|
| T4.1 | Definition 2 (p. 11) | Bisimulation well-defined (coinductive) | **Missing** |
| T4.2 | Lemma 3 (p. 14) | Bisimilarity is a congruence | **Missing** — depends on T4.1, T2.2, T3.4 |
| T4.3 | Proposition 1 (p. 11) | Semantic layering: `[|p|] = [|q|]` iff `(p;d) ~ (q;d)` | **Missing** — depends on T1.2, T1.3, T4.1 |

### Tier 5 — Axiom soundness

| Item | Paper reference | Description | Status |
|---|---|---|---|
| T5.1 | Lemma 10 (p. 14) | Soundness of A0-A15 without AIP | **Missing** (A15 has `[owise]` side condition) — depends on T4.1, T4.2, T2.2, T3.4 |
| T5.2 | Lemma 11 (p. 15) | Soundness of AIP | **Missing** — depends on T5.1, branching finiteness (T5.3) |
| T5.3 | Lemma 8 (p. 13) | Branching finiteness (guarded policies are finitely branching) | **Missing** — depends on T3.5, T2.2 |
| T5.4 | — | Soundness of restriction & projection axioms | **Missing** |

### Tier 6 — Normal forms & AIP

| Item | Paper reference | Description | Status |
|---|---|---|---|
| T6.1 | Definition 6 (p. 14) | DyNetKAT normal forms | **Missing** |
| T6.2 | Definition 7 (p. 13) | Guardedness | **Missing** — (same as T3.5) |
| T6.3 | Lemma 9 (p. 14) | DyNetKAT normalization (E_DNK is normalizing) | **Missing** — depends on T1.4, T6.1, T6.2, A1 soundness |

### Tier 7 — Soundness & completeness

| Item | Paper reference | Description | Status |
|---|---|---|---|
| T7.1 | Theorem 1 (p. 11) | Soundness of E_DNK: `E_DNK |- p = q => p ~ q` | **Missing** (partial: NetKAT axioms proven semantically in T1.3) — depends on T5.1, T5.2 |
| T7.2 | Theorem 1 (p. 15) | Ground-completeness of E_DNK: `p ~ q => E_DNK |- p = q` | **Missing** — depends on T6.3, T7.1, T1.4 |

### Tier 8 — Safety framework

| Item | Paper reference | Description | Status |
|---|---|---|---|
| T8.1 | Definitions 12, 14 (p. 17-19) | Safety property syntax & semantics | **Missing** |
| T8.2 | Definition 13 (p. 17-18) | Head normal forms | **Missing** |
| T8.3 | Definition 15 (p. 19) | Trace-equivalence axioms (E_DNK^tr with A16) | **Missing** |
| T8.4 | Definition 16 (p. 19) | Safe network system checking | **Missing** |
| T8.5 | Definition 17 (p. 20) | Extended safety sugars (desugaring) | **Missing** |

### Tier 9 — Examples (verification)

| Item | Paper reference | Description | Status |
|---|---|---|---|
| T9.1 | Fig. 1 (p. 3) | Stateful firewall example safety property | **Missing** |
| T9.2 | Fig. 2 (p. 4) | Distributed controller: breach prevention with/without sync | **Missing** |

---

## 18. Key distinctions

This analysis distinguishes three levels of implementation:

1. **Type/definition exists** — A Lean definition, structure, or inductive type
   representing the concept. Does not imply correctness.

2. **Semantic theorem proven** — A machine-checked Lean theorem establishing that
   the definition has the correct semantics. This is the highest level of
   verification currently achievable.

3. **Executable algorithm** — A function that can actually execute on inputs
   (e.g., parse a string, run the analysis, produce a result). Definitions marked
   `noncomputable` are not executable in Lean's kernel.

### Currently proven theorems (no `sorry`/`admit`/`axiom`)

The following mathematical theorems are fully machine-checked in the current codebase:

**NetKAT semantic core (`Semantics.lean`):**
- `drop_empty`, `id_diag`, `union_sem`, `seq_sem` — basic semantic identities
- `assign1_sem`, `assign1_seq_sem` — single-field assignment semantics
- `assign_list_sem` — fold-of-assignments semantics
- `seq_deterministic_sem` — deterministic sequential composition
- `completeTest_sem` — complete test semantics
- `completeAssignExpr_sem` — complete assignment semantics (Definition 4)
- `fieldEnum_updates_complete` — all fields updated yields valuation π
- `pred_excluded_middle`, `pred_contra`, `pred_double_neg`, `pred_deMorgan_or`, `pred_deMorgan_and` — Boolean algebra
- `assign_overwrite`, `assign_comm_diff`, `assign_test_same_field`, `test_assign_same_field` — packet algebra
- `star_refl`, `star_step` — Kleene star basic properties

**Normal forms (`NormalForm.lean`):**
- `ofSummand_sem` — single summand semantics
- `fold_sem` — list fold semantics
- `interpret_sem` — full normal form interpretation semantics
- `emptyNF_sem` — empty NF = drop
- `idNF_sem` — identity NF = NetKAT id
- `testNF_sem` — predicate test NF = NetKAT test
- `assign1NF_sem` — assignment NF = NetKAT assign1
- `seqNF_sem` — sequential composition NF correspondence
- `unionNF_sem` — union NF correspondence

**Packet model (`Packet.lean`):**
- `holdsComplete_iff_eq` — complete test matches exactly one packet
- `applyValuation_field` — valuation overwrites every field
- `Packet.ext`, `Packet.get_update_same`, `Packet.get_update_diff`, `Packet.update_id`, `Packet.update_update_same`, `Packet.update_update_diff`

**Predicate algebra (`AST.lean`):**
- `Predicate.not_not`, `Predicate.excluded_middle`, `Predicate.contra`, `Predicate.deMorgan_or`, `Predicate.deMorgan_and`
- `fieldEnum_complete`, `fieldEnum_nodup`

### Semantic equivalence vs. equational derivability

The analysis distinguishes between:

- **Semantic equivalence proofs**: Theorems of the form `⟦p⟧(σ,τ) ↔ ⟦q⟧(σ,τ)` showing
  two terms have the same denotational semantics. These are proven about the `Prop`-valued
  `Semantics` relation.

- **Equational derivability proofs**: Theorems of the form `E_DNK ⊢ p ≡ q` showing
  that two terms are derivable from the axioms A0-A15 + AIP.

The current codebase contains **semantic equivalence proofs** (Section 3.4, 7.1, etc.)
but **NO equational derivability proofs**. Establishing `E_NK ⊢ p ≡ q` or `E_DNK ⊢ p ≡ q`
requires implementing the derivability relation itself, which is a separate
construction from semantic equivalence.

Per the analysis instructions: *"Do not treat existing semantic equivalence proofs
as equational derivability proofs."*

---


## 19. Major architectural gaps

### 19.1 No DyNetKAT process syntax

The most significant gap is the complete absence of DyNetKAT process syntax
(Section 4). The codebase only contains NetKAT⁻ᵈᵘᵖ syntax and semantics. There
is no `DyNetKAT.DyNetKAT.AST` module, no process type, no configuration structure,
and no labeled transition system. This blocks all subsequent phases:

- Operational semantics (T2.2) — requires DyNetKAT syntax
- Extended operators (T3.1-T3.5) — require DyNetKAT syntax as host
- Bisimulation (T4.1-T4.3) — requires operational semantics
- Axioms A0-A15 (T5.1, T7.1) — require extended operators and bisimilarity
- Safety framework (T8.1-T8.5) — requires bisimilarity and axiomatization
- Examples (T9.1-T9.2) — require DyNetKAT syntax

### 19.2 No executable analysis pipeline

The reference tool is a working CLI that takes JSON input, parses DyNetKAT
programs, runs the analysis pipeline (projection → restriction → head/tail →
equivalence), and reports results. Our implementation has:

- No CLI with argument parsing
- No JSON parser
- No DyNetKAT parser
- No equivalence decision procedure
- No head/tail operators
- No restriction/projection operators

The only executable code is: (a) `Predicate.eval` which evaluates boolean predicates
on concrete packets, and (b) Python golden tests that mirror NetKAT semantics.

### 19.3 Semantic theorems without derivability

The current codebase proves semantic equivalences about the denotational semantics
(`⟦p⟧ = ⟦q⟧`), but does not establish:
- An equational derivation relation `E_NK ⊢ p ≡ q`
- An axiomatization of DyNetKAT (A0-A15 + AIP)
- Soundness (derivability implies bisimilarity)
- Ground-completeness (bisimilarity implies derivability)

These are distinct from semantic equivalence and require separate construction.

### 19.4 External solver replacement

DyNetiKAT drives two external solvers:
1. **Maude** — applies equational rewriting (A0-A15 axioms)
2. **NetKAT decision procedure** (`katbv`/`netkat-automata`) — checks NetKAT term equivalence

Our project must reproduce both within Lean:
- The Maude rewriting is replaced by the Lean derivability relation (still missing)
- The NetKAT decision procedure is replaced by normalization + equivalence on normal forms (partially started with `NormalForm.lean` but the actual decision algorithm is missing)

---

## 20. Discrepancies or uncertainties discovered

### 20.1 NetKAT syntax includes `f=v` as a basic term

The paper's NetKAT syntax (Eq. 1, p. 6) includes `f=v` (single field test) and `f←v`
(single field assignment) as basic terms. Our implementation models `f=v` as
`.test (.pFieldEq ⟨f,v⟩)` and `f←v` as `.assign1 f v`. This is a valid encoding
but the `fieldTest` helper (`AST.lean:106-107`) is defined but not used in the
`examplePolicy` (which uses `.test (.pFieldEq ...)` directly). No inconsistency,
just a minor redundancy.

### 20.2 `holdsFinset` legacy path retained

`Packet.lean:182` defines `holdsFinset` (the legacy `Finset FieldEq`-based test
evaluation). This is **not used** in the current semantics (only `holdsComplete`
is referenced at `Semantics.lean:67`). It is a legacy helper, not a parallel
representation of complete tests, and is isolated from the canonical semantics.

### 20.3 Stray untracked test files

There are 16 untracked scratch files (`lean/test_*.lean`) in the `lean/` directory
(not under `DyNetKAT/`). These are experimental proof sketches not part of the
library build. Per HANDOFF.md Task 2V, they do not affect `lake build DyNetKAT` and
were not deleted per instructions.

### 20.4 NormalForm.lean is untracked

The `packages/NetKATLean/NetKATLean/Core/NormalForm.lean` file is **untracked** in git but is
imported by `DyNetKAT.lean` (`import NetKATLean.Core.NormalForm`). The build succeeds
because Lake resolves it from the working tree. This should be committed before
the file can be shared with others.

### 20.5 `noncomputable` markers in NormalForm.lean

The `NormalForm` module uses `noncomputable` extensively (via `Finset.toList`,
`Finset.map`, `Finset.filter`). This is mathematically correct (these operations
involve classical choice on non-decidable finite sets) but means the normal-form
interpretation cannot be executed as a Lean program. The semantic theorems are
still valid.

### 20.6 DyNetKAT vs DyNetiKAT naming

The reference tool is named `DyNetiKAT` (with internal "i") per `DYNETIKAT_REFERENCE_AUDIT.md`
Section 14. Our project is `DyNetKAT-Lean` (matching the paper spelling `DyNetKAT`).
This is a naming difference, not a functional one, and the conformance map confirms
the paper uses `DyNetKAT` (no internal "i").

### 20.7 `DyNetKAT.lean` imports `NormalForm` but file is untracked

The root `DyNetKAT.lean` imports `DyNetKAT.NetKAT.NormalForm` (line 8), but the
file `packages/NetKATLean/NetKATLean/Core/NormalForm.lean` is untracked. This is consistent in
the working tree but would break for anyone cloning the repo fresh without
committing the new file.

---

