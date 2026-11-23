# H0 - History-Based Semantics Migration Plan (DyNetKAT-Lean)

Status: design/audit only; no Lean source modified. References verified against the
working tree on 2026-11-06 (branch `master`, HEAD `e96d71a`).
Legend: **[F]** confirmed fact, **[D]** proposed design decision, **[O]** unproved
mathematical obligation.

## 1. Paper semantics versus current Lean semantics

**Paper (authoritative) [F].** `DyNetKAT.pdf` (arXiv:2102.10035v4), Figure 3 (p. 5),
defines `⟦-⟧ : N → (H → P(H))` over packet histories:

```
⟦1⟧(h) = {h}          ⟦0⟧(h) = {}
⟦f=n⟧(σ::h) = {σ::h} if σ(f)=n, {} otherwise
⟦¬a⟧(h) = {h} \ ⟦a⟧(h)
⟦f←n⟧(σ::h) = {σ[f:=n]::h}
⟦p+q⟧(h) = ⟦p⟧(h) ∪ ⟦q⟧(h)
⟦p·q⟧(h) = (⟦p⟧ • ⟦q⟧)(h)                    (relational composition)
⟦p*⟧(h) = ⋃_{i∈ℕ} Fⁱ(h), F⁰(h)={h}, Fⁱ⁺¹(h)=(⟦p⟧•Fⁱ)(h)
(f • g)(x) = ⋃ {g(y) | y ∈ f(x)}
⟦dup⟧(σ::h) = {σ::(σ::h)}
```

(Verified by raw PDF extraction; the seq clause is plain composition.)

- Definition 1 (p. 5): histories are (possibly empty) packet lists `σ::l`, `⟨⟩` empty.
  Tests, assignments, `dup` are clause-defined **only on nonempty** `σ::h`; `⟦1⟧`,
  `⟦¬a⟧` for all `h`. **[F]**
- Figure 8, rule `(cpolX;)` (p. 10): premise `σ' ∈ ⟦p⟧(σ::⟨⟩)` - **singleton-history
  evaluation** - yields `(p; q, σ::H, H') →(σ,σ') (q, H, σ'::H')`. The pending queue
  `σ::H` is *not* the evaluation input. **[F]**
- §II-C, Eq. 1 (p. 6): DyNetKAT is defined on `NetKAT⁻ᵈᵘᵖ`; analyses are reachability
  over dup-free `in · (p·t)* · out ≢ 0`. **[F]**
- NetKAT histories are distinct from the configuration lists `H` (pending) / `H'`
  (handled) of `(d, H, H')`; the latter are packet queues touching NetKAT semantics only
  via the singleton premise. **[F]**

**Current Lean [F].** `packages/NetKATLean/NetKATLean/Core/Semantics.lean:61` defines a
packet-to-packet relation `Semantics : NetKAT → CtxPkt → CtxPkt → Prop` (`drop → False`,
`id → σ=τ`, tests → `holds ∧ σ=τ`, `assign1 → τ = Packet.update σ f v`, `union → ∨`,
`seq → ∃ρ`, `star → StarClosure (Semantics n) σ τ`; generic `StarClosure` at
`Semantics.lean:51`). The header comment (`Semantics.lean:20-25`) documents the
deviation and *claims* dup-free equivalence, and `docs/DESIGN_ALARMS.md:155-163` flags
it - but **no equivalence is formalized anywhere in the repo**. Per the architectural
decision, history semantics becomes authoritative and the correspondence must be proved.

## 2. Recommended canonical History type **[D]**

```lean
structure History where
  head : CtxPkt
  tail : List CtxPkt
```

in namespace `DyNetKAT.NetKAT` (new module, e.g. `NetKAT/History.lean`).

| Option | Verdict |
|---|---|
| `structure History (head, tail)` | **Recommended.** Nonempty by construction; `⟨σ, h⟩` mirrors the paper's `σ::h` clauses; no invariant to carry. |
| `List CtxPkt` + `h ≠ []` (hypothesis or `{l // l ≠ []}`) | Invariant friction in every definition/theorem; empty-history junk clauses still need a convention. |
| Mathlib nonempty list | `List.Nonempty` is `Prop`-valued, not a data carrier; nothing suitable in the pinned Lean/Mathlib v4.19.0 (`lean/lean-toolchain`). |

- **Singleton:** `⟨σ, []⟩` = the paper's `σ::⟨⟩` of the SOS premise.
- **Comparison:** structural equality; `DecidableEq History` derives from the existing
  `DecidableEq CtxPkt` constructions (`Evaluator.lean:11`, `Decision.lean:47`,
  `Executable.lean:7`); register one instance in the new module.
- **Tests/assignments well-defined:** every history has a `head`, so `σ(f)=n` and
  `σ[f:=n]` are total on `History` - removing the paper's clause partiality on `⟨⟩`.
  No dup-free clause produces an empty history from a singleton start, so the
  empty-history behavior is never needed.
- **Cardinality:** `History` is **countably infinite** (`CtxPkt` finite via
  `Fintype CtxPkt`, `Packet.lean:158`; tails unbounded). Histories can never be
  enumerated; enumeration stays at packet level (§6).
- **Paper match:** `History` ≅ nonempty lists = exactly the domain of the paper's
  test/assignment/dup clauses; `⟨σ, h⟩` is `σ::h`.
- `Config.pending`/`handled` (`DyNetKAT/Config.lean:11-14`) stay plain `List CtxPkt`:
  they are queues, not NetKAT histories, and must not be retyped.

## 3. Proposed history-level semantic definitions **[D]**

An independent relation, not a wrapper of `Semantics`:

```lean
def HistorySemantics (N : NetKAT) : History → History → Prop
```

Clauses for the eight constructors of `NetKAT` (`NetKAT/AST.lean:89-97`; the AST is
already dup-free, so there is no `dup` clause):

| Constructor | Clause | Paper justification (Fig. 3) |
|---|---|---|
| `.drop` | `False` | `⟦0⟧(h) = {}` |
| `.id` | `h = h'` | `⟦1⟧(h) = {h}` |
| `.test Pr` | `h = h' ∧ Predicate.eval Pr (head h) = true` | `⟦f=n⟧(σ::h)`, `⟦¬a⟧(h)={h}\⟦a⟧(h)`; predicate `+`/`·` are policy-level union/composition of `{h}`/`{}`-valued tests, collapsing to `eval` (`AST.lean:49`) |
| `.completeTest α` | `h = h' ∧ holdsComplete α (head h)` | complete test = conjunction of all field tests (Def. 4, p. 8); `holdsComplete_iff_eq` (`Packet.lean:218`) |
| `.assign1 f v` | `h' = ⟨Packet.update (head h) f v, tail h⟩` | `⟦f←n⟧(σ::h) = {σ[f:=n]::h}` - **tail preserved** |
| `.union p q` | `HistorySemantics p h h' ∨ HistorySemantics q h h'` | union clause |
| `.seq p q` | `∃ k, HistorySemantics p h k ∧ HistorySemantics q k h'` | `⟦p·q⟧(h) = (⟦p⟧•⟦q⟧)(h)` |
| `.star p` | `StarClosure (HistorySemantics p) h h'` | `⟦p*⟧(h) = ⋃_i Fⁱ(h)` |

**Kleene star.** The paper's `⋃_i Fⁱ` is exactly the reflexive-transitive closure of the
one-step relation. Reuse the existing generic `StarClosure {α} (R : α → α → Prop)`
(`Semantics.lean:51`) at `α := History`; it is packet-independent. **[O]** Prove the
equivalence `StarClosure R h h' ↔ ∃ i, h' ∈ Fⁱ(h)` (induction on derivation / on `i`);
the packet-level analogue already exists (`Evaluator.lean:849-886`).

## 4. Packet/history lifting theorem and proof obligations **[O]**

Exact recommended statement:

```lean
theorem historySemantics_lift
    (p : NetKAT) (σ τ : CtxPkt) (h h' : List CtxPkt) :
    HistorySemantics p ⟨σ, h⟩ ⟨τ, h'⟩ ↔ h' = h ∧ Semantics p σ τ
```

Status: **not established anywhere in the repo**; it is the central new obligation.

Proof shape (induction on `p`, generalizing `σ τ h h'`):

- `drop/id/test/completeTest/assign1/union`: direct logical manipulation; the test
  clause's `h = h'` yields `σ = τ`, matching the packet clause's `σ = τ` conjunct;
  `assign1` forces `τ = Packet.update σ f v` and `h' = h` on both sides.
- `seq p q`: the intermediate history `k` is some `⟨ρ, g⟩`; the `p`-IH forces `g = h`,
  the `q`-IH forces `h' = g`, hence `h' = h`, and the packet existentials line up.
  Tail-invariance of every constructor is what collapses the existential.
- `star p`: auxiliary lemma
  `StarClosure (HistorySemantics p) ⟨σ,h⟩ ⟨τ,h'⟩ → h' = h ∧ StarClosure (Semantics p) σ τ`
  by induction on the closure derivation (every step preserves the tail by the `p`-IH);
  converse by induction on the packet-level closure using the `←` direction of the
  `p`-IH.

Validity analysis:

- **No constructor of the current AST invalidates the theorem**; it holds for all eight
  precisely because the AST is dup-free (`AST.lean:15`).
- **Adding `dup` would break it** (`⟦dup⟧(σ::h) = {σ::σ::h}` changes the tail); the
  theorem is valid for `NetKAT⁻ᵈᵘᵖ` only and must be documented as such.
- Special case `h = h' = []` gives the paper-faithful singleton statement
  `HistorySemantics p ⟨σ,[]⟩ ⟨τ,[]⟩ ↔ Semantics p σ τ`, exactly what the SOS premise
  needs (§7), and equivalently `⟦p⟧(σ::⟨⟩) = {σ'::⟨⟩ | Semantics p σ σ'}` for dup-free
  `p`.

## 5. Dependency impact table

| Declaration | Location | Depends on | Migration |
|---|---|---|---|
| `Semantics`, `StarClosure`, algebra laws (`union_sem`, `seq_sem`, `fieldTest_sem`, `assign_list_sem`, `completeAssignExpr_sem`, …) | `NetKAT/Semantics.lean:51,61-71,90-655` | - | **Keep.** Packet layer, justified by lifting. |
| `execute`, `boundedStar`, `execute_correct`, `post_correct`, `boundedStar_correct`, `execute_star_correct`, `ReachableWithin`, `semantics_star_iff_reachableWithin` | `NetKAT/Evaluator.lean:171,233,1078,749,1013,1058,802,882` | `Semantics` | **Keep** (backend); history wrapper added on top (§6). |
| `netkatEquiv`, `netkatEquiv_correct`, `netkatIsZero`, `netkatIsZero_correct`, `netkatIsZero_iff_empty_execute` | `NetKAT/Decision.lean:77,124,151,157,176` | `execute_correct` | **Keep**; history-level meaning via lifting. |
| `NormalForm`, `ofSummand_sem`, `interpret_sem`, `testNF_sem`, `assignNF_sem`, `unionNF_sem`, `seqNF_sem` | `NetKAT/NormalForm.lean:60,138,263,478,626,686,883` | `Semantics` | **Keep**; history restatements via lifting. |
| `Step.cpol_seq_ok` premise `Semantics p sigma sigma'` | `DyNetKAT/Semantics.lean:14-24` (premise `:18`) | `Semantics` | **Must change** to singleton-history premise (§7). |
| `execute_supported_iff_semantics`, `execute_packet_step` | `DyNetKAT/NetKATBridge.lean:10,24` | `execute_correct`, `cpol_seq_ok` | One-line premise translation each. |
| `packetTransitions`, `packetTransitions_sound`, `packetTransitions_complete` | `DyNetKAT/Executable.lean:25,57,90` | bridge, `execute_correct` | Sound unchanged; complete adds lifting `→` before `execute_supported_iff_semantics`. |
| `IsBisimulation`, `Bisimilar`, congruence lemmas (incl. `Bisimilar.nSeq_left`) | `DyNetKAT/Bisimulation.lean:9,26,441` | `Step` only | **Proof text unchanged** - `nSeq_left` forwards `evaluates` opaquely; statements unaffected. |
| `head`, `HeadSpec`, `head_spec` | `DyNetKAT/SafetyHead.lean:74,250,323` (`HeadSpec` uses `Semantics` at `:252`) | `Semantics` | **Keep packet-level**; history-level corollary via lifting later. |
| `recursiveVars`, `GuardedOccurrences`, `WellFormed` | `DyNetKAT/Definedness.lean` | syntax only | **Unaffected.** |
| Integration tests | `lean/test_evaluator_integration.lean`, `lean/test_decision.lean`, `lean/test_safety_head.lean` | `execute_correct`, `Semantics` | **Unaffected** while the packet layer is preserved. |

## 6. Evaluator and decision-procedure migration **[D]**

The packet evaluator **can remain the implementation backend**; no `Evaluator.lean`
changes.

- **History wrapper** (new code): for input history `⟨σ, tail⟩`, run `execute p σ` and
  lift each output packet `τ` to `⟨τ, tail⟩`:
  `executeHistory p h = match execute p h.head with | .unsupported => .unsupported |
  .supported outs => .supported (outs.image (fun τ => ⟨τ, h.tail⟩))`.
- **Correctness theorem [O]:** `executeHistory p h = .supported B ↔ ∀ h',
  HistorySemantics p h h' ↔ h' ∈ B`, proved from `execute_correct p h.head`
  (`Evaluator.lean:1078`) plus lifting. `execute_correct` is reused verbatim.
- **Bounded star sufficiency [O]:** for fixed tail `t`, histories reachable from
  `⟨σ, t⟩` under dup-free `p` are exactly `⟨ρ, t⟩` with `ρ` packet-reachable from `σ`
  (lifting + `semantics_star_iff_reachableWithin`). The existing bound
  `Fintype.card CtxPkt` (`Evaluator.lean:185,233`) stays sufficient: reachable-history
  cardinality ≤ `Fintype.card CtxPkt`. Assumption: dup-free policy - guaranteed by the
  AST. Packet-level stabilization (`reachableWithin_finite_stabilizes`,
  `Evaluator.lean:922`) is reused; no history enumeration is ever needed.
- **`supported` vs `unsupported`:** preserved - `unsupported` propagates unchanged; a
  supported empty packet set maps to a supported empty history set, mirroring
  `combineEvalResult` (`Evaluator.lean:40`).
- `netkatEquiv`/`netkatIsZero` stay packet-level; equivalence on all packets ⟺
  equivalence on all singleton-history evaluations, via lifting.

## 7. SOS, bridge, and bisimulation migration **[D]**

**Change.** `Step.cpol_seq_ok` (`DyNetKAT/Semantics.lean:14-24`) currently requires
`evaluates : DyNetKAT.NetKAT.Semantics p sigma sigma'`. Target premise:

```lean
evaluates : HistorySemantics p ⟨sigma, []⟩ ⟨sigma', []⟩
```

By the singleton instance of the lifting theorem this is **equivalent** to the current
premise, so the change is conservative: no transitions added or removed; the rule is
re-anchored to the authoritative semantics.

**Proof-preserving sequence:**

1. `execute_packet_step` (`NetKATBridge.lean:24`): after `apply Step.cpol_seq_ok`, close
   the goal with the `←` direction of lifting applied to the existing `Semantics` fact -
   one added rewrite.
2. `packetTransitions_sound` (`Executable.lean:57`): calls `execute_packet_step`; body
   unchanged.
3. `packetTransitions_complete` (`Executable.lean:90`): convert the new `evaluates` to
   `Semantics p sigma sigma'` via lifting `→` **before**
   `execute_supported_iff_semantics` - one added rewrite.
4. `Bisimilar.nSeq_left` and all congruence proofs (`Bisimulation.lean:441-470` et al.):
   forward `evaluates` opaquely; **no proof edits**; `IsBisimulation`/`Bisimilar` never
   mention `Semantics`.
5. `head_spec` (`SafetyHead.lean:323`): keep packet-level; the history semantics enters
   the safety pipeline later through a lifting corollary, not by editing `HeadSpec`.

The lifting theorem must exist **before** `Step` is touched, so every downstream fix is
a one-liner rather than a re-proof.

## 8. Safe dedicated-branch strategy

Findings (read-only) **[F]:** current branch `master`; only `master`/`origin/master`
exist (no migration branches); one tracked modification `M lean/DyNetKAT.lean` - purely
additive imports for the untracked new modules (`Evaluator`, `Decision`, `Definedness`,
`NetKATBridge`, `Executable`, `SafetyHead`); untracked: `DyNetKAT.pdf`, ten `docs/*.md`
audits, those Lean modules, ~22 `lean/test_*.lean` files; `git diff --check` clean; no
stashes.

Recommendation **[D]** (executed in a later task, not H0):

1. Create the branch **without switching**: `git branch history-semantics` - records the
   base without touching the worktree.
2. When implementation starts: `git switch history-semantics`. Untracked files are
   unaffected; the uncommitted `lean/DyNetKAT.lean` import change travels with the
   checkout (identical file in both branches, no conflict).
3. Never run `reset --hard`, `checkout .`, `clean`, or `stash`: the untracked audit docs
   and test files are unrecoverable work.
4. Before H1 edits `lean/DyNetKAT.lean` again (adding `History`/`HistorySemantics`
   imports), inspect the pending import diff and append to it - do not overwrite.
5. Commit granularity for H1 (when authorized): (a) pending import block as-is; (b)
   History type + HistorySemantics + lifting; (c) SOS premise change + bridge/executable
   one-liners. `lake build` green before each next step.

## 9. Proposed order of implementation **[D]**

1. **H1a - foundations (no existing-file changes):** `NetKAT/History.lean` with
   `History`, `DecidableEq`, singleton lemmas; `NetKAT/HistorySemantics.lean` with the
   eight clauses (reusing generic `StarClosure`) and the `⋃ Fⁱ` equivalence lemma.
2. **H1b - lifting:** `historySemantics_lift` by induction on `p`, including the star
   auxiliary lemmas and the singleton corollary.
3. **H1c - SOS re-anchoring:** change the `cpol_seq_ok` premise; fix
   `execute_packet_step` and `packetTransitions_complete` (one rewrite each);
   `packetTransitions_sound` and bisimulation untouched.
4. **H1d - history-level evaluator wrapper:** `executeHistory` + correctness theorem
   over the unchanged packet backend; history-level `netkatIsZero` corollary for
   reachability verdicts `in · (p·t)* · out ≢ 0` from `⟨in, []⟩`.
5. **H2 - safety pipeline:** history-level restatements of `head_spec` consumers and
   the reachability check, all derived from lifting.

Each step keeps `lake build` green and changes exactly one existing theorem statement
(the `cpol_seq_ok` premise type).

## 10. Risks and unresolved mathematical questions **[O]**

1. **Lifting theorem unproved.** Seq/star are the only nontrivial cases; the star case
   needs the tail-preservation auxiliary lemma. Risk low (all clauses are
   tail-preserving by construction) but must be machine-checked before the SOS premise
   is switched.
2. **`⋃ Fⁱ` ↔ `StarClosure` equivalence** must be proved for the history relation; the
   packet-level analogue (`Evaluator.lean:857-886`) should transfer with minimal
   adaptation.
3. **Predicate-clause collapse:** the single `test` clause relies on paper-level
   predicate composition/negation of `{h}`/`{}`-valued tests coinciding with
   `Predicate.eval` - a small lemma per predicate constructor. A maximally literal
   alternative is per-predicate-clause history semantics (same theorems, more clauses).
4. **Empty-history convention:** the paper leaves `⟦f=n⟧(⟨⟩)`, `⟦f←n⟧(⟨⟩)`,
   `⟦dup⟧(⟨⟩)` unspecified. The nonempty `History` sidesteps this, but re-adding `dup`
   or evaluating from an empty queue must revisit it; `dup` would invalidate both the
   lifting theorem and the bounded-star tail argument.
5. **Infinite history space:** no decision procedure can enumerate histories; all
   checker reasoning must go through lifting and stay packet-level. Any future
   history-level model checking needs a finiteness argument (bounded history length)
   that does not exist in the paper.
6. **`lean/DyNetKAT.lean` is already locally modified** (import block); H1 must append
   to, not overwrite, that change or the untracked-module imports could be lost.
7. **Scope boundary:** this plan does not claim `E_NK` completeness, does not prove
   Lemma 5's normalizer, and does not validate the full safety pipeline against `Step`
   traces (cf. `SafetyHead.lean:33-38`, `Decision.lean:22-26`).
