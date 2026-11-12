# S6C Part 1 — Graph-Native Tail Extraction: Paper-to-Lean Audit

Status: **audit only — no implementation** (per the S6C Part 1 mandate).
Branch: `history-semantics`, HEAD `bc5712a2d3113624afe878c8f14cf1fbe7f43d68`
("Checkpoint: Complete graph-head soundness and completeness (S6B Part 3)").

Provenance legend used throughout:

* **[PAPER]** — read directly from `DyNetKAT.pdf` (arXiv:2102.10035v4). Page
  numbers are PDF pages of that file.
* **[LEAN]** — already implemented and proved in the repository at the
  checkpoint above. File and theorem names are quoted verbatim.
* **[PROPOSED]** — design produced by this audit; not yet implemented, not
  yet proved.
* **[OPEN]** — mathematically unresolved; must be settled before or during
  implementation.

---

## 1. The paper's tail operation

### 1.1 Where tail is defined [PAPER]

The tail operator is defined in §V "Implementation" (PDF p. 16), together
with `head`. The paper's motivation sentence (PDF p. 16):

> "The checking of properties is achieved by analyzing the step by step
> behaviour of DyNetKAT terms in normal form via a set of operators
> `head(D)`, and `tail(D, R)`, where `D` is a DyNetKAT term and `R` is a set
> of terms of shape `rcfg_{X,N}`. Intuitively, the operator `head(D)`
> returns a NetKAT policy which represents the current configuration in the
> input `D` and the operator `tail(D, R)` returns a DyNetKAT policy which is
> the sum of DyNetKAT policies inside `D` that appear after the
> reconfiguration events in `R`."

So:

* `tail(D, R)` returns a **DyNetKAT process** (not a NetKAT policy). The
  NetKAT policy consumed by the reachability check is `head` **of** the
  tail (Eq. (35) below).
* `R` is a **set of reconfiguration events**, each of the shape
  `rcfg_{X,N}` (channel `X`, NetKAT−dup policy `N`).

### 1.2 The equations [PAPER]

PDF p. 16, displayed together with Eqs. (29)–(32) for `head`:

```
head(⊥)            = 0                    tail(⊥, R)            = ⊥                (29)
head(N ; D)        = N + head(D)          tail(N ; D, R)        = tail(D, R)       (30)
head(D ⊕ Q)        = head(D) + head(Q)    tail(D ⊕ Q, R)        = tail(D, R) ⊕ tail(Q, R)   (31)
head(rcfg_{X,N};D) = 0                    tail(rcfg_{X,N};D, R) = D ⊕ tail(D, R)   if rcfg_{X,Z} ∈ R   (32)
                                          tail(rcfg_{X,N};D, R) = ⊥                if rcfg_{X,N} ∉ R   (33)
```

**Typo in Eq. (32) [PAPER, verified].** The printed side condition of (32)
is `rcfg_{X,Z} ∈ R` with `Z ≠ N`, while (33) uses `rcfg_{X,N} ∉ R`. The
audited Maude implementation of the original DyNetiKAT tool (recorded in
`docs/DYNETIKAT_REFERENCE_AUDIT.md` and already quoted in
`lean/DyNetKAT/DyNetKAT/TailExtraction.lean`, header lines 18–32) reads both
side conditions as speaking about the *same* event `rcfg(X,Z)` that heads
the sequence:

```
tail(rcfg(X,Z) ; D, RS) = D o+ tail(D, RS)  if rcfg(X,Z) in RS
tail(rcfg(X,Z) ; D, RS) = bot               if rcfg(X,Z) not in RS
```

The existing Lean module therefore reads Eq. (32) with side condition
`(x, N) ∈ R`. This audit adopts the same reading; nothing in the paper
contradicts it, and the alternative (`Z` ranging over *other* events of
`R`) has no support in the tool transcript.

### 1.3 What the equations actually compute [PAPER, interpretation flagged]

Reading (29)–(33) as a recursive definition on normal-form terms, and
writing "R-visible path" for a path that crosses only packet prefixes
(`N;`), choice branches (`⊕`), and **matching** reconfiguration prefixes:

* (30): packet prefixes are transparent — tail looks past them.
* (31): choice distributes — multiple reachable synchronization points
  **all contribute**, by union (`⊕`).
* (32) with `(x,N) ∈ R`: the continuation `D` after the matched event is
  contributed **wholesale**, and *in addition* `tail(D, R)` contributes the
  continuations of further matching events inside `D`.
* (33) with `(x,N) ∉ R`: the result is `⊥` **without inspecting `D`** — a
  non-matching reconfiguration is a **barrier**: branches passing through
  it contribute nothing, not even deeper matching events.

The resulting exact characterization (derived from the equations, not
stated verbatim in the paper — flagged as interpretation):

> `tail(D, R)` is the `⊕`-sum of the continuations `D'` of all
> reconfiguration prefixes `rcfg_{x,N}; D'` with `(x,N) ∈ R` that are
> reachable from `D` along R-visible paths.

Consequences worth stating explicitly:

1. Extraction does **not** stop at the first matching synchronization;
   every matching event reachable on an R-visible path contributes
   ((31) distributes, (32) recurses into `D`).
2. A non-matching event **blocks** its branch entirely ((33) never
   inspects the continuation). This is what keeps the "closed" state of
   the firewall out of the post-`secConReq` configuration.
3. Because (32) embeds the verbatim continuation `D` *and* recurses into
   it, the extracted process is closed under "one more matching event":
   `tail` of a process that can re-synchronize contains the process
   itself as a summand (see §5, scenarios 3–5).

### 1.4 Synchronization prefixes and reconfiguration events [PAPER]

* Syntax (PDF p. 5–6, Eq. (1)/(6) and Def. 6): prefixes are `x?q`, `x!q`
  (communication) and `rcfg_{x,q}` (reconfiguration), `q` a NetKAT−dup
  policy. `rcfg_{x,q}` is the *synchronization product* of `x?q` and
  `x!q`: the SOS rules `(cpol!? )`/`(cpol?! )` (Fig. 8, PDF p. 8) produce an
  `rcfg(x,q)`-labelled step exactly when both operands of a `‖` (or `|`)
  agree on sending/receiving the same policy on the same channel.
* "A process synchronizes on a reconfiguration channel" therefore means:
  in the SOS, an `rcfg(x,q)` step is derivable. In the restricted normal
  form consumed by `tail`, communication prefixes are gone (see §1.5) and
  the surviving `rcfg_{x,N}; D'` summands are the synchronization points.
* The Lean mirror of this is `Step.cpol_sync_recv_send` /
  `cpol_sync_send_recv` / `cpol_comm_merge_recv_send` /
  `cpol_comm_merge_send_recv` and their graph counterparts
  `GStep.sync_recv_send` / `sync_send_recv` / `comm_merge_recv_send` /
  `comm_merge_send_recv` [LEAN, `Semantics.lean`, `ProcessGraph.lean`].
* Multiple matching synchronization points: the SOS is nondeterministic
  (`cpol⊕` left/right); every derivable `rcfg(x,N)` step with
  `(x,N) ∈ R` is a synchronization point, and (31)/(32) union them all.
  No matching point: every branch is eventually cut by (33) (or contains
  no event at all), and the result is `⊥` up to `⊕`-units.

### 1.5 The restriction precondition [PAPER]

PDF p. 16, immediately after the equations:

> "Note that we assume the input `D` to the operators `head` and `tail` do
> not contain terms of shape `x?q` and `x!q`. This can be ensured by always
> applying the restriction operator `δ` on `D`."

So the domain of `tail` is *restricted, projected normal forms* (Def. 6,
PDF p. 11). The paper does **not** define `tail` on recursive terms: the
equations are structural on finite normal-form terms, and the tool applies
them to (finite representations of) normalized processes. How recursive
definitions enter is precisely the gap S6C must close (§5).

### 1.6 Normal forms, guardedness, recursion [PAPER]

* Def. 6 (PDF p. 11): normal forms are
  `⊕_{i∈I} (α_i·π_i); d_i ⊕ ⊕_{j∈J} c_j; d_j (⊕ ⊥)` with
  `c_j ::= x?q | x!q | rcfg_{x,q}`.
* Def. 7 (PDF p. 11): guardedness of variable occurrences; Lemma 8:
  guarded policies are finitely branching; Lemma 9: `E_DNK` is normalising
  for guarded policies. The paper then "assume[s] that DyNetKAT policies
  are guarded" (PDF p. 11).
* The paper's use of recursion in examples is through defining equations
  (`X ≜ D`) interpreted by the SOS `(cpolX;)` rule (Fig. 8) — the same
  discipline the Lean `RecEnv`/`Step.cpol_var` and the S6A graph `ref`
  edges implement [LEAN].

### 1.7 The firewall example and Eqs. (34)–(35) [PAPER]

Figure 5 (PDF p. 6):

```
Host    ≜ secConReq!1; Host ⊕ secConEnd!1; Host
Switch  ≜ (port=int)·(port←ext); Switch ⊕ (port=ext)·0; Switch ⊕ secConReq?1; Switch'
Switch' ≜ (port=int)·(port←ext); Switch' ⊕ (port=ext)·(port←int); Switch' ⊕ secConEnd?1; Switch
Init    ≜ Host || Switch
```

§V (PDF p. 16): with `in ≜ port = ext`, `out ≜ port = int`,
`R = {rcfg_{secConReq,1}}`:

```
in · head(Init) · out ≡ 0                                    (34)
in · head(tail(Init, R)) · out ≢ 0                           (35)
```

> "Intuitively, the equivalence in (34) expresses that packets at port ext
> are not able to reach to port int in the initial configuration and (35)
> expresses that the configuration after the synchronization on the channel
> secConReq allows this flow."

Note what (35) needs from `tail`: the post-`secConReq` configuration must
contain `(port=ext)·(port←int)` (from `Switch'`) and must **not** be
polluted by the closed state reached through `secConEnd` — which is exactly
what the (33) barrier guarantees.

### 1.8 Direct answers to the Part-1 questions

* **What does `tail R D` return?** A DyNetKAT process: the `⊕`-sum of the
  continuations after all R-visible matching reconfiguration events
  (§1.3). [PAPER + interpretation]
* **What does "synchronize on a reconfiguration channel" mean?** An
  `rcfg(x,N)` step is derivable in the SOS (Fig. 8) — in the restricted
  normal form, a `rcfg_{x,N}; D'` summand with `(x,N) ∈ R`. [PAPER]
* **How is `R` represented?** A set of events `rcfg_{X,N}`; in Lean,
  `ReconfigSet := Finset (Channel × NetKAT)` [LEAN, TailExtraction.lean
  §0], which makes (32)/(33) decidable.
* **Multiple matching synchronization points?** All contribute, unioned by
  `⊕` ((31), (32)). [PAPER]
* **No matching points?** Every branch ends in `⊥` ((29), (33)); the
  result is the empty sum. [PAPER]
* **Branches and sequential continuations?** (30) skips packet prefixes;
  (31) distributes over branches; (32) contributes the whole continuation
  plus its recursive tail. [PAPER]
* **Synchronization inside recursive definitions?** Not addressed by the
  paper's equations (they are structural on finite terms). Under the
  least-fixpoint reading the recursion is well-defined; see §5. [OPEN →
  resolved by design in §6]
* **First match only, or all reachable matches?** All reachable matches on
  R-visible paths. [PAPER, from (31)+(32)]

---

## 2. The existing AST-level implementation (S5A) and its limitations

All of the following exists and is proved at the checkpoint [LEAN,
`lean/DyNetKAT/DyNetKAT/TailExtraction.lean`, 1311 lines].

### 2.1 The extractor

```lean
abbrev ReconfigSet := Finset (Channel × NetKAT)

def tail (R : ReconfigSet) : DyNetKAT → Option DyNetKAT
  | .deadlock => some .deadlock                                  -- (29)
  | .nSeq _ D => tail R D                                        -- (30)
  | .choice D Q => (tail R D).bind (fun D' => (tail R Q).map (.choice D'))  -- (31)
  | .rcfgPrefix x N D =>
      if (x, N) ∈ R then (tail R D).map (fun D' => .choice D D') -- (32)
      else some .deadlock                                        -- (33)
  | .recv _ _ _ => none | .send _ _ _ => none        -- excluded by δ-precondition
  | .parallel _ _ => none | .leftMerge _ _ => none | .commMerge _ _ => none
  | .restrict _ _ => none | .project _ _ => none | .var _ => none
```

* Supported constructors: `deadlock`, `nSeq`, `choice`, `rcfgPrefix`.
* Unsupported constructors fail explicitly with `none`; failure
  propagates through (30)/(31) and through the `(x,N) ∈ R` instance of
  (32). The `(x,N) ∉ R` instance of (33) succeeds **without inspecting
  `D`** — faithful to the paper.
* Recursion: structural on the AST; `.var` is rejected, so recursive
  definitions are entirely outside its domain.

### 2.2 Supportedness, two layers

* `TailSupported` (R-independent): `deadlock` always; `nSeq`/`choice`/
  `rcfgPrefix` require their continuations to be supported. Strictly
  stronger than S4A's `HeadSupported`
  (`tailSupported_strictly_stronger`), because (32) recurses into the
  reconfiguration continuation whereas head's (32) discards it.
* `TailDomain R` (R-dependent, exact success domain): refines
  `TailSupported` with `rcfgPrefix_out` (continuation uninspected).
  `tail_none_or_domain` / `tail_domain_of_some` / `tail_some_of_domain` /
  `tail_domain_iff` pin the domain exactly; `tailDomain_all_supported`
  shows the two coincide on paper-intended (restricted normal-form)
  inputs.

### 2.3 Specification and correctness theorems

* `TailSpec R D Q` — inductive, equation-shaped, deterministic
  (`tailSpec_deterministic`); `tail_spec_iff : tail R D = some Q ↔
  TailSpec R D Q`.
* `TailSuffix R D S` — process-level reading of the paper's intuition
  ("`S` is one of the policies inside `D` after the events in `R`",
  unblocked branches only). Step-level soundness and completeness:
  `tail_step_suffix` (every transition of the extracted process is a
  transition of some suffix) and `suffix_step_tail` (every transition of
  a suffix is afforded by the extracted process). Together: the
  extraction is behaviourally exact on `TailSupported` input.
* Packet-level pipeline spec: `AllRSpec R D σ τ` (positions where *all*
  preceding reconfiguration prefixes carry events of `R`) and
  `TailHeadSpec R D σ τ` (positions preceded by **at least one**
  reconfiguration prefix, all of which carry events of `R`). Main
  theorem `tail_head_spec` (proved by the simultaneous induction
  `tail_head_spec_aux`):

  ```lean
  theorem tail_head_spec (R) (D) (hsup : TailSupported D) (Q) (H)
      (hQ : tail R D = some Q) (hH : head Q = some H) (σ τ) :
      Semantics H σ τ ↔ TailHeadSpec R D σ τ
  ```

  and the decomposition identity `allR_head_spec`:

  ```lean
  theorem allR_head_spec (R) (D) (hsup : TailSupported D) (H) (hH : head D = some H) (σ τ) :
      AllRSpec R D σ τ ↔ (Semantics H σ τ ∨ TailHeadSpec R D σ τ)
  ```

### 2.4 Pipeline integration [LEAN]

* `restrictElim_tailSupported`: S4B's `restrictElim` output is
  `CommFree ∧ TailSupported` — the (32) recursion is exactly why the
  stronger fragment matters.
* `preprocess_tail_supported`, `preprocess_head_tail_some`,
  `preprocess_tail_head_spec`: the full S4B → S5A → S4A pipeline succeeds
  and is semantically characterized on the preprocessing fragment.
* S5B consumes this in `SafetyCheck.lean`: `checkCondition35` =
  `tail R q` then `head` then `netkatIsZero`; `Cond35Result` distinguishes
  `tailFailure` from `tailHeadFailure`; `safetyCheck_pipeline_semantic`
  states the end-to-end verdict equivalence.

### 2.5 Limitations

1. `.var` → `none`: recursive processes are outside the domain
   (`TailSupported.varFree`). The safety checker therefore cannot run on
   the recursive firewall specification — the very example the paper
   targets.
2. No cycle handling of any kind; no fixpoint semantics.
3. The output is an AST term; there is no finite representation of the
   fixpoint that (32) demands on cyclic inputs (§5).

---

## 3. Graph representation and constructor-by-constructor mapping

### 3.1 Recap of the S6A/S6B infrastructure [LEAN]

* `GProc` (`ProcessGraph.lean`): the DyNetKAT AST with `.var x` replaced
  by `.ref (varNode x)`; all other constructors carried verbatim
  (`deadlock, nSeq, recv, send, rcfgPrefix, parallel, choice, leftMerge,
  commMerge, restrict, project, ref`).
* `ProcessGraph`: `nodes : Finset NodeId`, `root : GProc`,
  `label : NodeId → GProc`, `root_closed`, `closed`. `NodeId = String ⊕
  Nat`; `varNode x = Sum.inl x`; `Sum.inr` is the spare namespace for
  synthetic nodes (`auxNode`).
* `GStep` mirrors Figure 8 exactly; `.ref i` steps through `G.label i`
  (rule `var`), so recursive definitions are cycles, never unfolded.
* `toGraph env root S hsup` builds the graph from a `RecEnv` under
  `FiniteSupport`; `toGraph_corr` + `graph_step_iff` certify faithfulness.
* `GraphHead.lean` (S6B): `headRefs`/`headRefsList` (head-region
  discovery), `RefReach`/`HeadPathTo` (reachability), `headRun`
  (cycle-safe worklist, lexicographic termination), `headCollect` (local
  policy collection; refs contribute `.drop` locally, never followed),
  `graphHeadUnion`/`graphHead`, `GraphHeadSpec`, and the S6B Part 3
  results `graphHead_sound`, `graphHead_complete`,
  `graphHead_spec_iff`, `graphHead_supported_some(_root)`, plus the
  example fixtures (self-loop, mutual, unguarded cycle, unreachable
  definition, reconfiguration boundary).

### 3.2 Constructor-by-constructor mapping for tail [PROPOSED]

For a graph `G`, reconfiguration set `R`, the graph-level tail equations
lift (29)–(33) with one new clause for references:

| AST case | paper eq. | graph-level equation `T(gp)` |
|---|---|---|
| `.deadlock` | (29) | `⊥` |
| `.nSeq N cont` | (30) | `T(cont)` |
| `.choice a b` | (31) | `T(a) ⊕ T(b)` |
| `.rcfgPrefix x N cont`, `(x,N) ∈ R` | (32) | `cont ⊕ T(cont)` |
| `.rcfgPrefix x N cont`, `(x,N) ∉ R` | (33) | `⊥` (continuation uninspected) |
| `.ref i` | — (new) | `T(G.label i)` |
| `.recv/.send/.parallel/.leftMerge/.commMerge/.restrict/.project` | — | **failure** (explicit `none`) at R-visible positions |

The `.ref` clause is forced by the graph semantics: a reference *is* its
label (`GStep.var`), so `T(.ref i)` must behave like `T(G.label i)`.
Everything else is the paper verbatim.

### 3.3 `.ref` nodes and cyclic references

Three properties matter:

1. **Refs are transparent in the semantics** but must **not** be unfolded
   by the extractor (constraint 2). The extracted term therefore keeps
   refs — but, crucially, in **two roles** (§5.11):
   * verbatim continuations contributed by (32) keep **original** refs,
     which must continue to resolve to the **original** labels;
   * the recursive contribution `T(ref i)` is represented by a **fresh**
     node reference whose label is the local tail of `G.label i`.
2. **Unsupported constructors behind refs**: a node whose label fails the
   local tail collection makes the whole extraction fail **iff the node
   is tail-reachable** (R-visible). Unreachable definitions neither
   contribute nor cause failure — mirroring `exUnreachable_*` in S6B.
3. **Unguarded ref cycles** (`X ≜ Y`, `Y ≜ X`): the extraction terminates
   and yields a semantically empty process — the graph analogue of
   `exUnguarded_*`. No special-casing needed (§5, scenario 7).

---

## 4–5. Recursive-cycle analysis

(This section merges the required items 4 and 5 of the deliverable: the
cycle scenarios and the algorithmic consequences.)

Throughout, `T` denotes the graph-level tail equations of §3.2 and
`tailNodes(G,R)` the set of nodes reachable from `G.root` along
R-visible paths (through `nSeq` continuations, choice branches, *matching*
rcfg continuations, and `ref` edges).

### Scenario 1 — self-recursion without events: `X ≜ N;X`

`tailNodes = {X}`. `T(label X) = T(ref X) = T(label X)` — a trivial
fixpoint with no base case; the spec relation (§6) has **no finite
derivation**, i.e. the least fixpoint is the empty relation. The extracted
process is a pure ref-cycle, which affords no transitions — semantically
empty, matching `⊥`. Extraction **succeeds** with an empty result; it must
not fail and must not diverge.

### Scenario 2 — mutual recursion without events: `X ≜ N;Y`, `Y ≜ M;X`

Same shape: the worklist visits `X` and `Y` once each; the extracted
process is a fresh ref-cycle; the spec is uninhabited (empty tail).
Correct answer: there are no reconfiguration events at all.

### Scenario 3 — synchronization inside a recursive definition:
`X ≜ rcfg_a; X ⊕ N;X`, `R = {a}`

`T(label X) = (X ⊕ T(X)) ⊕ T(X)` — the fixpoint equation `T = X ⊕ T`,
whose **least** solution is `T ≡ X` (`⊕` is idempotent). The extracted
policy `head(T)` must be `N`. Check of the proposed spec (§6): the
`AllRSpec` derivation terminates through the `nSeq_of_sem` leaf
(`Sem N`) inside the `rcfg_a` branch, so `GraphTailSpec` **is** inhabited
with exactly the `N`-contribution — the finite-derivation (least-fixpoint)
reading and the equation-level least fixpoint agree. The worklist visits
`X` once; the extracted term contains both the verbatim `ref X` (inside
the (32) continuation) and the fresh `ref f_X`.

### Scenario 4 — synchronization before a recursive reference:
`X ≜ rcfg_a; X`, `R = {a}`

`T = X ⊕ T`, least solution `T ≡ X`; `head(T) = head(X) = 0` (the rcfg is
a head boundary). The spec is uninhabited (the `AllRSpec` recursion has no
`nSeq_of_sem` leaf) — empty post-reconfiguration configuration, correct:
after `a` the process can only do another `a`.

### Scenario 5 — multiple synchronization points on a cycle:
`X ≜ rcfg_a; N; rcfg_b; X`, `R = {a,b}`

Equations: `T = (N; rcfg_b; X) ⊕ X ⊕ T`, least solution
`T ≡ (N; rcfg_b; X) ⊕ X`; `head(T) = N + 0 = N`. The extracted term is
`choice (N; rcfg_b; ref X) (choice (ref X) (ref f_X))`; the worklist
visits `X` once; `graphHead` of the constructed graph yields exactly `N`
(verified by hand-tracing the S6B machinery). Both cycle synchronization
points contribute through one visit — union semantics for free.

### Scenario 6 — unreachable recursive definitions

Nodes not in `tailNodes` are never visited; their local tails are never
computed and may fail without consequence. Mirrors `exUnreachable_*` of
S6B. Design rule: fresh tail-nodes are created **only for visited nodes**.

### Scenario 7 — unguarded reference cycles: `X ≜ Y`, `Y ≜ X`

`tailNodes = {X, Y}`; `T(label X) = ref f_Y`, `T(label Y) = ref f_X` — a
fresh pure-ref cycle. No transitions, empty spec, extraction **succeeds**
with an empty result. Termination is by the worklist measure, not by the
term structure — this scenario is exactly why a structural recursion on
`GProc` (following refs) is impossible.

### Scenario 8 — unsupported constructors inside reachable and unreachable branches

* At an R-visible position of `G.root` or of a `tailNodes` label → local
  collection fails → `graphTail` fails explicitly (`none`).
* Behind a **non-matching** rcfg → not inspected ((33)) → **no** failure.
  This is the graph analogue of `TailDomain.rcfgPrefix_out` and must be
  preserved (constraint 4/5).
* Inside a node outside `tailNodes` → no failure.
* Behind a **matching** rcfg → inspected (both verbatim embedding and
  recursion) → failure propagates (graph analogue of
  `tail_rcfgPrefix_mem_none`).

### 5.9 What the algorithm requires

* **A visited-set worklist** — yes: the traversal region is cyclic and
  R-dependent; termination must come from the node set, not the term
  structure (scenarios 1, 5, 7).
* **A fixpoint computation** — the *result* is a fixpoint
  (`T = cont ⊕ T`), but it is **represented**, not iterated: fresh
  tail-nodes turn the fixpoint into a cyclic finite graph (§7). No
  numerical/Kleene iteration is needed.
* **A different traversal algorithm than head** — yes, in three ways
  (§5.10).
* **A finite result representation** — yes: a `ProcessGraph` extending
  `G` (§7.4).
* **A termination measure** — the S6B lexicographic measure
  `((G.nodes \ visited).card, pending.length)` re-usable verbatim.
* **Least-fixpoint specification** — yes: the inductive spec of §6 has
  only finite derivations, which is exactly the least fixpoint; this is
  the same discipline as `GraphHeadSpec` ("recursive cycles are
  represented by finite derivations").

### 5.10 Where graph-tail differs from graph-head

1. **R-dependence.** The head region is R-independent; the tail region is
   defined *by* `R`: matching rcfg prefixes are transparent-and-collecting,
   non-matching ones are barriers. Discovery (`headRefsList` →
   `tailRefsR`), reachability (`HeadPathTo` → `TailPathTo`), the shape
   predicates (`HeadShapeOk` → `TailShapeOk R`), and the spec are all
   parameterized by `R`. The head algorithm cannot be reused as-is.
2. **The traversal crosses reconfiguration prefixes.** Head stops at
   *every* `rcfgPrefix`; tail descends into matching ones and collects
   their continuations. The discovery function has an `if (x,N) ∈ R`
   test that has no head counterpart.
3. **The result is a process (a graph), not a policy.** `graphHead`
   accumulates a `NetKAT` union; `graphTail` must **construct** a finite
   graph representing the fixpoint `T = cont ⊕ T`, which needs fresh
   nodes. Head has no construction step at all.
4. **Two node universes.** The extracted term mixes original refs
   (verbatim continuations) and fresh refs (recursive tail positions);
   head only ever traverses one universe.
5. **Supportedness is R-dependent and strictly weaker than a
   term-shape check.** Eq. (33) makes continuations behind non-matching
   events irrelevant, so the exact domain is `R`-dependent (graph
   analogue of `TailDomain R` vs `TailSupported`).

### 5.11 Why the fresh-node representation is forced (negative result)

A cheaper-looking alternative is to reuse the *original* nodes with
**modified labels** (`label' i = T(label i)` for tail-reachable `i`) and
let `T(ref i) = ref i`. Counterexample: `X ≜ rcfg_a; N; ref X ⊕
rcfg_c; M; ref X`, `R = {a}`. The true tail (least fixpoint of the
equations) is `N; X` — after the packet step `N` the process behaves like
the **original** `X` (it can still do `c ↦ M`; note `M` is *not* part of
the tail itself, but the continuation `N; X` legitimately contains the
original behaviour). Under label modification, `ref X` resolves to the
*tail* of `X`, whose `c`-branch has been cut by (33) — the extracted
process loses the `c ↦ M` behaviour that the verbatim continuation
`N; ref X` must retain. The two roles of `ref X` (original behaviour
inside the verbatim continuation; tail behaviour at the recursion point)
cannot be served by one label. Hence **fresh tail-nodes are
mathematically necessary**, not merely convenient.

---

## 6. Proposed graph-level semantic specification [PROPOSED]

Two mutually reinforcing inductive relations over `GProc`, parameterized
by the graph `G` (and, for the first time, by `R`), mirroring the S5A
pair `AllRSpec`/`TailHeadSpec` with one new clause each for references:

```lean
-- R-visible positions: every preceding reconfiguration prefix carries an
-- event of R; refs are transparent.
inductive GraphAllRSpec (G : ProcessGraph) (R : ReconfigSet) :
    GProc → CtxPkt → CtxPkt → Prop
  | nSeq_of_sem  (N) (cont) (σ τ) (h : Semantics N σ τ) :
      GraphAllRSpec G R (.nSeq N cont) σ τ
  | nSeq_of      (N) (cont) (σ τ) (h : GraphAllRSpec G R cont σ τ) : ...
  | choice_left / choice_right                                  -- as in AllRSpec
  | rcfgPrefix_of (x) (N) (cont) (σ τ) (hmem : (x,N) ∈ R)
      (h : GraphAllRSpec G R cont σ τ) : ...
  | ref_of (i) (σ τ) (h : GraphAllRSpec G R (G.label i) σ τ) :
      GraphAllRSpec G R (.ref i) σ τ
  -- no clauses for deadlock / recv / send / merges / restrict / project

-- Post-reconfiguration positions: at least one preceding reconfiguration
-- prefix, all of which carry events of R.
inductive GraphTailSpec (G : ProcessGraph) (R : ReconfigSet) :
    GProc → CtxPkt → CtxPkt → Prop
  | nSeq_of      (N) (cont) (σ τ) (h : GraphTailSpec G R cont σ τ) : ...
  | choice_left / choice_right                                  -- as in TailHeadSpec
  | rcfgPrefix_of (x) (N) (cont) (σ τ) (hmem : (x,N) ∈ R)
      (h : GraphAllRSpec G R cont σ τ) : ...
  | ref_of (i) (σ τ) (h : GraphTailSpec G R (G.label i) σ τ) :
      GraphTailSpec G R (.ref i) σ τ
```

Properties and readings:

* **Least fixpoint.** Both relations are inductive: membership = finite
  derivation = least fixpoint of the clause set. Scenario 3 shows the
  least fixpoint is nonempty exactly when a packet policy is reachable
  after an unblocked event — the `nSeq_of_sem` leaf is what cuts every
  cycle. Scenario 1/2/4/7 show uninhabitedness where the tail is empty.
  This is precisely the discipline of `GraphHeadSpec` [LEAN].
* **Union semantics.** Multiple synchronization points = multiple
  derivations = disjunctive union. Nothing extra to prove.
* **Relationship to the AST-level specs.** `GraphTailSpec` is
  `TailHeadSpec` + `ref_of`; `GraphAllRSpec` is `AllRSpec` + `ref_of`.
  On ref-free terms the graph relations collapse to the AST ones
  (a transfer lemma, cheap but useful for cross-checking fixtures).
* **Relationship to `GraphHeadSpec`.** `GraphHeadSpec` is R-independent
  and describes zero-preceding-rcfg positions. The decomposition
  theorem (§9.2) makes the triad precise:
  `GraphAllRSpec = GraphHeadSpec ∪ GraphTailSpec`.
* **Deadlock/unsupported shapes.** No clauses ⇒ the relations are
  uninhabited there, so the spec never silently rewards unsupported
  constructs (constraint 4/5).
* **The spec never mentions the extractor** — same independence
  discipline as `GraphHeadSpec`/`TailHeadSpec`.

The candidate signature in the task,
`GraphTailSpec G R G.root σ τ`, is thus adopted in the exact form
`GraphTailSpec G R G.root σ τ` (argument order aligned with the existing
`GraphHeadSpec G G.root σ τ`).

---

## 7. Proposed extraction algorithm [PROPOSED]

### 7.1 Signature decision

**Recommended:**

```lean
def graphTail (G : ProcessGraph) (R : ReconfigSet) : Option ProcessGraph
```

**Not** the tentative `ProcessGraph → ReconfigSet → Option NetKAT`.
Reasons:

1. The paper's `tail` returns a **process**; the NetKAT policy of
   Eq. (35) is `head` *of* the tail. Collapsing the two stages would
   discard the `tailFailure` vs `tailHeadFailure` distinction that S5B's
   `Cond35Result` deliberately preserves [LEAN, SafetyCheck.lean].
2. The extracted fixpoint can only be represented finitely as a graph
   with fresh nodes (§5.11); a `NetKAT` result would have to re-derive
   head-of-tail inside the extraction and re-prove head-style
   soundness/completeness for a combined R-dependent traversal, instead
   of **reusing `graphHead_sound`/`graphHead_complete`/`graphHead_spec_iff`
   verbatim** — those theorems are stated for *arbitrary* well-formed
   `ProcessGraph`s and apply unchanged to the constructed graph.
3. The two-stage shape keeps the audit trail aligned with the paper
   (`tail` then `head`) and with the existing AST pipeline.

Auxiliary (internal) entry points mirroring S6B's layering:

```lean
def tailRefsR   (R : ReconfigSet) : GProc → List NodeId      -- R-visible ref discovery
def tailRun     (G : ProcessGraph) (R : ReconfigSet) :
    List NodeId → Finset NodeId → List NodeId → Option (List NodeId)
def tailCollectR (G : ProcessGraph) (R : ReconfigSet)
    (fresh : NodeId → NodeId) : GProc → Option GProc          -- local tail term
def tailGraphOf (G : ProcessGraph) (R : ReconfigSet)
    (L : List NodeId) (root : GProc) : ProcessGraph           -- assembly
```

### 7.2 The components

**Discovery.** `tailRefsR R gp` lists the refs at R-visible positions of
`gp`:

```lean
| .deadlock => []
| .nSeq _ cont => tailRefsR cont
| .choice a b => tailRefsR a ++ tailRefsR b
| .rcfgPrefix x N cont => if (x,N) ∈ R then tailRefsR cont else []
| .ref i => [i]
| _ => []                    -- recv/send/merges/restrict/project stop discovery
```

Structurally recursive; every element is a `gprocRefs` member (same
safety argument as `headRefsList_subset_gprocRefs`).

**Worklist.** `tailRun` is `headRun` with `headRefsList (G.label i)`
replaced by `tailRefsR R (G.label i)`; identical visited/pending/acc
discipline, identical lexicographic termination measure, identical
invariant shape (`tailRun_spec` mirrors `headRun_spec`: pending nodes are
tail-reachable, every tail-reachable node is visited or reachable from a
pending one, visited ⊆ `G.nodes`, accumulator = visited list, no
duplicates).

**Local collection.** `tailCollectR G R fresh gp` builds the local tail
*term* of `gp`, structurally, never following refs:

```lean
| .deadlock => some .deadlock
| .nSeq _ cont => tailCollectR cont                       -- (30)
| .choice a b => choice <$> tailCollectR a <*> tailCollectR b   -- (31)
| .rcfgPrefix x N cont =>
    if (x,N) ∈ R then (.choice cont) <$> tailCollectR cont -- (32): verbatim cont + tail
    else some .deadlock                                    -- (33): uninspected
| .ref i => some (.ref (fresh i))                          -- T(ref i) = T(label i), finitely
| .recv/.send/.parallel/.leftMerge/.commMerge/.restrict/.project => none
```

Two structural facts to prove and use everywhere:

* **Image shape:** a successful `tailCollectR` never produces an
  `.nSeq` node — the image is contained in `{.deadlock} ∪ choice-nodes ∪
  {`.ref (fresh i)`}`. (Needed by the bridge, §9.2.)
* **Ref preimage:** `tailCollectR gp = .ref (fresh j)` iff `gp` is an
  `nSeq`-spine ending in `.ref j`.

**Assembly.** `graphTail G R`:

1. `tailRun G R (tailRefsR R G.root) ∅ []` — fail `none` if it fails
   (impossible for well-formed `G`, kept for robustness, as in head).
2. Compute `T₀ := tailCollectR G R fresh G.root` and `Tⱼ := tailCollectR
   G R fresh (G.label j)` for every visited `j`; fail `none` if any is
   `none`. (This is where unsupported constructors at R-visible positions
   are rejected — the graph analogue of `TailDomain R`.)
3. Return `tailGraphOf G R L T₀`: `nodes := G.nodes ∪ {fresh j | j ∈ L}`,
   `root := T₀`, `label :=` original labels on `G.nodes`, `Tⱼ` on fresh
   nodes; `root_closed`/`closed` proved from `G.root_closed`, `G.closed`,
   and the worklist invariant.

### 7.3 Fresh-node allocation

`fresh` must be injective on the visited list `L` and disjoint from
`G.nodes` (a collision would clobber an original label and corrupt every
verbatim continuation — §5.11). Constructive proposal:

```
maxAux := fold over G.nodes of (match node with .inr k => k | .inl _ => 0)
fresh i := Sum.inr (maxAux + 1 + (L.indexOf i))     -- i ∈ L, L duplicate-free
```

`L.indexOf` is decidable (`DecidableEq NodeId` from `String ⊕ Nat`);
injectivity on `L` follows from duplicate-freeness of the worklist
accumulator; disjointness from `maxAux`. Both facts are elementary but
must be proved once and reused (`fresh_inj`, `fresh_notMem_nodes`,
`fresh_inj_iff`). An association-list map built during the worklist is an
equally acceptable alternative.

### 7.4 The constructed graph

`G' = tailGraphOf G R L T₀` satisfies:

* `nodes G' = G.nodes ∪ image fresh L`, `root G' = T₀`;
* original labels unchanged — verbatim continuations inside `T₀`/`Tⱼ`
  keep their original refs and therefore their original behaviour;
* fresh labels are the local tails — the fixpoint `T = cont ⊕ T` is
  represented by the cycle `f_j ↦ Tⱼ` (scenario 3: `Tⱼ` contains both the
  verbatim continuation and `ref f_j`);
* closure (`root_closed`, `closed`): original refs come from
  `G.root_closed`/`G.closed`; fresh refs in `T₀` are exactly
  `tailRefsR R G.root` and fresh refs in `Tⱼ` are exactly
  `tailRefsR R (G.label j)` — all visited by the worklist invariant.

---

## 8. Termination argument [PROPOSED]

Three layers, all within the established discipline (no `partial`, no
`unsafe`, no fuel, no `Classical.choice`):

1. `tailRefsR` and `tailCollectR`: **structural** recursion on `GProc`.
   Refs are replaced (`fresh i`), never followed — this is what makes
   structural recursion possible on a graph with cycles.
2. `tailRun`: well-founded recursion on the lexicographic measure
   `((G.nodes \ visited).card, pending.length)` — the identical
   `termination_by`/`decreasing_by` skeleton as `headRun` [LEAN,
   GraphHead.lean:631–653]. Fresh nodes are inserted into `visited`
   before their labels are expanded, so each node is expanded at most
   once; the first measure component strictly decreases on each fresh
   visit, the second on each skip.
3. `graphTail`: a finite composition of the above (no recursion).

The subtle termination point — the *result* is a fixpoint — is resolved
representationally (§5.9): cycles live in the constructed graph, not in
the computation.

---

## 9. Soundness/completeness theorem architecture [PROPOSED]

### 9.1 Supportedness

Exact, R-dependent domain (graph analogue of `TailDomain R`):

```lean
def GraphTailDomain (G : ProcessGraph) (R : ReconfigSet) : Prop :=
  (tailCollectR G R fresh G.root ≠ none) ∧
  (∀ j, TailPathTo G R G.root j → tailCollectR G R fresh (G.label j) ≠ none)
```

Convenient R-independent sufficient condition (graph analogue of
`TailSupported`, packaging for the API):

```lean
inductive TailShapeOk (G : ProcessGraph) : GProc → Prop   -- R-independent
  | deadlock | nSeq (cont ok) | choice (both ok) | rcfgPrefix (cont ok)  -- always inspected
  | ref (i) (h : i ∈ G.nodes)

def GraphTailSupported (G : ProcessGraph) : Prop :=
  (∀ dst, FullSub G G.root dst → TailShapeOk G dst)    -- subterm closure incl. ref labels
```

`GraphTailSupported G` implies `graphTail G R` succeeds **for every `R`**
(the exact per-`R` domain is strictly weaker because (33) does not
inspect continuations behind non-matching events — scenario 8).

Two packaged facts mirroring S5A/S6B:

* `graphTail_supported_some : GraphTailSupported G → ∃ G', graphTail G R = some G'`
  (for every `R`).
* `graphTail_head_some : graphTail G R = some G' → ∃ H, graphHead G' = some H`
  — the graph analogue of `tail_head_some`. Argument: every head-visible
  position of the constructed graph sits at an R-visible position of the
  original (refs transparent, verbatim continuations), so the success of
  `tailCollectR` on the root and on all visited labels implies success of
  every `headCollect` the `G'`-worklist performs. This makes the
  two-stage pipeline total on the supported domain.

### 9.2 The bridge (the genuinely new mathematics)

The extracted graph `G'` is consumed by `graphHead`, whose spec is
`GraphHeadSpec G' G'.root`. The paper-faithful spec of the tail is
`GraphTailSpec G R G.root`. Connecting them is the heart of S6C:

**Bridge (forward / soundness direction).**

```lean
theorem graphTail_bridge_sound
    (G : ProcessGraph) (R : ReconfigSet) (G' : ProcessGraph)
    (h : graphTail G R = some G') (σ τ : CtxPkt)
    (t : GProc) (D : GraphHeadSpec G' t σ τ) (gp : GProc)
    (hpre : tailCollectR G R fresh gp = t) :
    GraphTailSpec G R gp σ τ
```
by induction on `D`. Enabling lemmas: image-shape (kills the two
`nSeq` cases of `GraphHeadSpec` — the extracted image contains no
`.nSeq`), ref-preimage inversion, the decomposition below, and the
agreement lemma below.

**Bridge (reverse / completeness direction).** Two lemmas, avoiding
mutual recursion:

```lean
-- Q₂: AllR contributions land either in the verbatim continuation's head
-- or in the tail's head.
theorem graphAllR_headSpec_split (…):
    GraphAllRSpec G R gp σ τ → refs gp ⊆ G.nodes →
    GraphHeadSpec G' gp σ τ ∨ GraphHeadSpec G' (tailCollectR G R fresh gp) σ τ
-- by induction on the GraphAllRSpec derivation; the rcfgPrefix_of case
-- recurses on the sub-derivation (structurally decreasing).

-- Q₁: the tail spec maps into the head spec of the extracted term.
theorem graphTail_bridge_complete (…):
    GraphTailSpec G R gp σ τ → refs gp ⊆ G.nodes →
    GraphHeadSpec G' (tailCollectR G R fresh gp) σ τ
-- by induction on the GraphTailSpec derivation; the rcfgPrefix_of case
-- applies Q₂ to the (sub-)derivation of the continuation.
```

**Supporting lemmas** (each a straightforward induction, but all new):

1. `allR_split` — derivation-level decomposition
   `GraphAllRSpec G R gp σ τ → GraphHeadSpec G gp σ τ ⊕ GraphTailSpec G gp σ τ`
   (split at the first `rcfgPrefix_of`; its `GraphAllRSpec` sub-derivation
   is reused verbatim inside `GraphTailSpec.rcfgPrefix_of`). Together with
   the two inclusion lemmas `head_in_allR`, `tail_in_allR` this yields the
   propositional graph analogue of `allR_head_spec`:
   `GraphAllRSpec G R gp σ τ ↔ GraphHeadSpec G gp σ τ ∨ GraphTailSpec G R gp σ τ`.
2. `graphHeadSpec_agree` — for `gp` with `refs gp ⊆ G.nodes`,
   `GraphHeadSpec G' gp σ τ ↔ GraphHeadSpec G gp σ τ` (labels agree on
   `G.nodes`; induction on the derivation).
3. `tailCollectR_image_shape`, `tailCollectR_ref_inv` (§7.2).
4. `fresh_inj`, `fresh_notMem_nodes` (§7.3).

### 9.3 Target theorems

With `graphHead_spec_iff` reused on `G'`, the packaged results are:

```lean
theorem graphTail_sound (G : ProcessGraph) (R : ReconfigSet) (G' : ProcessGraph)
    (h : graphTail G R = some G') (H : NetKAT) (hH : graphHead G' = some H)
    (σ τ : CtxPkt) (hsem : Semantics H σ τ) :
    GraphTailSpec G R G.root σ τ
-- graphHead_sound on G'  +  forward bridge at gp := G.root

theorem graphTail_complete (G : ProcessGraph) (R : ReconfigSet) (G' : ProcessGraph)
    (h : graphTail G R = some G') (H : NetKAT) (hH : graphHead G' = some H)
    (σ τ : CtxPkt) (hspec : GraphTailSpec G R G.root σ τ) :
    Semantics H σ τ
-- reverse bridge at gp := G.root  +  graphHead_complete on G'

theorem graphTail_spec_iff (G : ProcessGraph) (R : ReconfigSet)
    (hsupported : GraphTailSupported G) (σ τ : CtxPkt) :
    GraphTailSpec G R G.root σ τ ↔
      ∃ G' H, graphTail G R = some G' ∧ graphHead G' = some H ∧ Semantics H σ τ
-- existence from graphTail_supported_some + graphTail_head_some;
-- both directions from the bridges.
```

Answers to the specific design questions:

* **Does soundness require successful extraction only?** Yes — both
  bridges are stated under the success hypothesis `graphTail G R = some
  G'` (plus well-formedness of `G`, which supplies closure). This mirrors
  `graphHead_sound`/`graphHead_complete`, which need no supportedness
  beyond success.
* **Does completeness require a supportedness condition?** Only to
  *guarantee existence* of `G'`/`H` (the packaged `graphTail_spec_iff`);
  the inclusion itself needs only success. Same split as S6B Part 3B.
* **Minimal supportedness condition:** the R-dependent
  `GraphTailDomain` is exact; the R-independent `GraphTailSupported` is
  the recommended API-level condition (one check, all `R`).
* **Can graph closure discharge assumptions automatically?** Yes — the
  node-closure conjunct is derivable from `root_closed`/`closed` exactly
  as `graphHead_supported_some_root` does for head.
* **Can the AST-level `tail` correctness be reused?** The *statements*
  transfer (the graph specs are the AST specs + `ref` clauses); the
  *proofs* do not (they are structural inductions over acyclic terms).
  What is reused wholesale instead: `graphHead`'s soundness/completeness/
  equivalence, the worklist skeleton and its invariant lemmas, the
  `unionOverList` fold lemmas, and the S5B checker layer.
* **What is genuinely new:** the two specs, the R-dependent
  discovery/reachability/shape predicates, `tailCollectR` + image-shape +
  ref-preimage lemmas, fresh-node machinery, the four bridge lemmas, and
  the supportedness packaging.

---

## 10. Safety-checker integration plan (design only)

Eventual S6D shape, reusing every existing piece:

```
p, R, in, out
  → toGraph env p S hsup                    (S6A; FiniteSupport witness)
  → G
  → graphHead G = some H₁                   (S6B)          -- condition (34)
  → netkatIsZero (in · H₁ · out)                            -- verdict (34)
  → graphTail G R = some G'                 (S6C)          -- stage 1 of (35)
  → graphHead G' = some H₂                  (S6B reused)   -- stage 2 of (35)
  → netkatIsZero (in · H₂ · out)                            -- verdict (35)
```

* `checkCondition34`/`checkCondition35` remain the AST-level checkers;
  S6D adds graph-level analogues (e.g. `graphCheckCondition34/35`) with
  the same `Option Bool` discipline (`none` is never a verdict).
* `SafetyCheckResult`/`Cond34Result`/`Cond35Result` can be reused
  verbatim (the failure taxonomy already matches: preprocessing vs
  extraction vs head-of-tail), or extended with a graph-level
  preprocessing failure constructor if S6D introduces one.
* The end-to-end theorem combines `graphHead_spec_iff` (for (34)) with
  `graphTail_spec_iff` (for (35)) into the relational statements:
  verdict (34) true ⟺ no `(ρ,κ)` with `in σρ ∧ GraphHeadSpec G G.root ρκ
  ∧ out κτ`; verdict (35) true ⟺ some `(ρ,κ)` with `in σρ ∧
  GraphTailSpec G R G.root ρκ ∧ out κτ` — the recursive-process versions
  of `safetyCheck_pipeline_semantic`.
* **Open integration point [OPEN]:** the paper's δ-precondition (§1.5).
  The AST-level `preprocess` fails on recursive variables
  (`restrictElim_var = none`), so the graph pipeline cannot preprocess at
  the AST level. Options for S6D: (a) a graph-level restriction stage
  rewriting blocked `recv`/`send` prefixes to `.deadlock` in reachable
  labels (new worklist transformation + its own correspondence proof), or
  (b) a supportedness side-condition excluding `recv`/`send` from the
  reachable fragment (what `HeadShapeOk`/`TailShapeOk` already do), with
  the δ-integration deferred. S6B took route (b); the audit recommends
  the same for S6C and flags (a) as S6D scope.

---

## 11. Staged implementation roadmap for S6C

Each stage compiles and commits independently; no stage introduces
`sorry`/`axiom`/`partial`/`unsafe`.

* **S6C-1 — Graph tail specification (pure relations).** New module
  `GraphTail.lean` (or `GraphTailSpec.lean`): `GraphAllRSpec`,
  `GraphTailSpec`, clause iff-lemmas, uninhabitedness lemmas
  (deadlock/unsupported shapes), the ref transfer lemma from the AST
  specs on ref-free terms, and `allR_split` + `head_in_allR` +
  `tail_in_allR` (decomposition). No extraction yet. Validation: the
  firewall-shaped fixtures of §5 evaluated by hand against the specs.
* **S6C-2 — R-dependent traversal infrastructure.** `tailRefsR`
  (+ `mem_tailRefsR_iff`, subset-of-`gprocRefs`), `TailPathTo`/
  `RefReach`-style node reachability (R-dependent), `tailRun` with the
  `headRun` termination skeleton, and `tailRun_spec` (the invariant
  mirror of `headRun_spec`). Validation: worklist fixtures for scenarios
  1/5/6/7.
* **S6C-3 — Local tail collection.** `tailCollectR`, defining equations,
  failure propagation, image-shape and ref-preimage inversion lemmas,
  fresh-node allocation (`fresh_inj`, `fresh_notMem_nodes`).
* **S6C-4 — Assembly and well-formedness.** `tailGraphOf`, `graphTail`,
  closure proofs (`root_closed`, `closed` from the worklist invariant),
  `graphTail_supported_some`, `GraphTailDomain`/`GraphTailSupported`,
  `graphTail_head_some`.
* **S6C-5 — Bridges and main theorems.** `graphHeadSpec_agree`,
  `graphAllR_headSpec_split` (Q₂), `graphTail_bridge_sound`,
  `graphTail_bridge_complete` (Q₁), then `graphTail_sound`,
  `graphTail_complete`, `graphTail_spec_iff`.
* **S6C-6 — Fixtures.** The eight scenarios of §5 as executable `#eval`/
  theorem fixtures (self-loop, mutual, sync-inside-recursion, sync-before-
  ref, multi-sync cycle, unreachable definition, unguarded cycle,
  unsupported-behind-barrier vs unsupported-reachable), mirroring the
  S6B example section, plus a firewall-shaped recursive fixture.
* **(S6D, out of scope here)** — checker integration and the δ story.

Estimated proof-weight distribution: S6C-1 and S6C-5 carry the new
mathematics; S6C-2/3/4 are disciplined ports of existing S6B machinery.

---

## 12. What remains mathematically unresolved [OPEN]

1. **Least-fixpoint adequacy beyond the spec.** The inductive spec is the
   least fixpoint *by construction* (finite derivations). What is *not*
   yet pinned is a direct relational-semantics statement tying
   `GraphTailSpec` to the SOS (`GStep`) traces of the post-reconfiguration
   configurations — the graph analogue of S5A's step-level
   `tail_step_suffix`/`suffix_step_tail` pair. Recommended as an optional
   S6C-5 addendum: define `GraphTailSuffix G R gp S` ("`S` is the
   continuation of an unblocked R-visible matching event of `gp`") and
   prove the corresponding step-level pair. Not required for the checker,
   but it is the strongest faithfulness statement available and closes
   the gap between "spec-level" and "operational" readings.
2. **The exact strength of the (33) barrier.** The paper's equations are
   the ground truth and are implemented faithfully; the *safety
   interpretation* of the barrier (under-approximation of
   "configurations reachable after some R-sequence" in the full LTS) is
   flagged in §1.3 but needs no resolution for S6C — the checker must
   match the paper's tool, not an idealized semantics. Recorded so the
   distinction is never blurred in later stages.
3. **δ-integration for recursive graphs** (§10) — deferred to S6D by
   design; the side-condition route is recommended meanwhile.
4. **Fresh-node allocation details** — the concrete `maxAux + indexOf`
   scheme is proposed but any injective disjoint encoding is acceptable;
   only the two lemmas (`fresh_inj`, `fresh_notMem_nodes`) are load-
   bearing.

---

## 13. Validation

* Repository state at audit start: branch `history-semantics`, HEAD
  `bc5712a2d3113624afe878c8f14cf1fbe7f43d68`, working tree containing only
  the pre-existing untracked scratch files (`lean/test_*.lean`,
  `DyNetKAT.pdf`) — all preserved untouched.
* This audit added exactly one file: `docs/S6C_TAIL_EXTRACTION_AUDIT.md`.
  No Lean source, no existing report, and no configuration file was
  modified; no commit, push, branch switch, reset, stash, or clean was
  performed.
* `git diff --check`: clean (no whitespace errors; the only change is the
  new untracked report).
* `git status --porcelain` after the audit shows the same untracked files
  as before plus `docs/S6C_TAIL_EXTRACTION_AUDIT.md`.

## 14. Source index

* Paper: `DyNetKAT.pdf` — §V (PDF p. 16): Eqs. (29)–(33), (34), (35),
  restriction precondition, `R = {rcfg_{secConReq,1}}`; Fig. 5 (p. 6)
  firewall encoding; Fig. 8 (p. 8) SOS; Def. 6/7, Lemma 8/9 (p. 11)
  normal forms/guardedness/normalization; Def. 14/16 (p. 14–15) safety
  semantics.
* Lean: `DyNetKAT/DyNetKAT/TailExtraction.lean` (S5A: `tail`,
  `TailSupported`, `TailDomain`, `TailSpec`, `TailSuffix`,
  `AllRSpec`, `TailHeadSpec`, `tail_head_spec`, `allR_head_spec`,
  pipeline theorems); `SafetyHead.lean` (S4A `head`);
  `RestrictionProjection.lean` (S4B `restrictElim`/`preprocess`,
  `preprocess_bisimilar`); `SafetyCheck.lean` (S5B checkers, result
  types, `safetyCheck`, `safetyCheck_pipeline_semantic`);
  `ProcessGraph.lean` (S6A graphs, `GStep`, `toGraph`, correspondence);
  `GraphHead.lean` (S6B `headRefs(List)`, `headRun`, `headCollect`,
  `graphHead`, `GraphHeadSpec`, soundness/completeness/equivalence,
  example fixtures); `Semantics.lean` (Figure 8 `Step`); `AST.lean`
  (constructors); `NetKAT/Decision.lean` (`netkatIsZero`).
