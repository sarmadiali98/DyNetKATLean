# Figure 8 Operational Semantics - Step SOS Rules Design

**Task:** Design ONLY Figure 8's packet-processing SOS rules for `Step`,
including successful processing, failure/drop, and packet-history updates.

**Paper source:** *DyNetKAT: An Algebra of Dynamic Networks*
arXiv:2102.10035v4 (22 May 2021), FoSSaCS 2022.
**Paper location:** printed p. 9–10, §II-B, **Figure 8**.
Text extraction verified from `/Users/ali/Desktop/DyNetKAT/DyNetKAT.pdf`
(`pdftotext -layout`).

**Scope:** This document covers **only** the labeled small-step SOS rules of
Figure 8. It specifies each rule's premises, conclusion, and label. It does
**not** implement any Lean code, make any commits, or push changes.

---

## 0. Scope and provenance

The operational semantics of DyNetKAT is a labeled transition system over
configurations `(d, H, H')`, defined as the **least relation** closed under
the rules of Figure 8. The transitions have the shape:

```
(d, H, H') →γ (d', H'', H''')
```

where `γ` (gamma) ranges over the **label grammar** at the foot of Figure 8:

```
γ ::= (σ, σ') | x!q | x?q | rcfg(x, q)
```

This document specifies each rule's exact premises and conclusions, the
packet-history (`H`, `H'`) manipulations, and flags ambiguities.

### Prior design artifacts (must be consistent with)

- **Packet model** (`NetKAT/Packet.lean`): `CtxPkt := Packet FieldName FieldValueEnum`,
  `[Fintype CtxPkt]` exists. `Semantics : NetKAT → CtxPkt → CtxPkt → Prop`
  is the single-packet denotational relation (equivalent to the paper's
  `⟦p⟧(σ::⟨⟩)` for the dup-free fragment; see DESIGN_ALARMS.md:A5).
- **NetKAT type** (`NetKAT/AST.lean:89`): 8 constructors (`drop`, `id`,
  `test`, `completeTest`, `assign1`, `union`, `seq`, `star`).
- **DyNetKAT AST** (`docs/PROCESS_AST_DESIGN.md` §2): `deadlock`, `nSeq N D`,
  `recv x N D`, `send x N D`, `parallel D D`, `choice D D`, `var X`.
  `Channel := String`, `Var := String`.
- **Action labels** (`docs/PROCESS_AST_DESIGN.md` §14): `Action.packet`,
  `Action.recv`, `Action.send`, `Action.rcfg`.
- **Config** (`docs/PROCESS_AST_DESIGN.md` §7): `structure Config` with
  `proc : DyNetKAT`, `pending : List CtxPkt`, `handled : List CtxPkt`.

---

## 1. Label grammar (foot of Figure 8, printed p. 10)

```
γ ::= (σ, σ') | x!q | x?q | rcfg(x, q)
```

| Label | Lean | Paper meaning |
|---|---|---|
| `(σ, σ')` | `Action.packet σ σ'` | A packet-flow action: the current packet `σ` is transformed into `σ'` by a NetKAT policy. |
| `x!q` | `Action.send x q` | An asynchronous send: transmit NetKAT policy `q` on channel `x`. |
| `x?q` | `Action.recv x q` | An asynchronous receive: receive NetKAT policy `q` on channel `x`. |
| `rcfg(x, q)` | `Action.rcfg x q` | A reconfiguration/synchronization action: the channel-`x` send/receive pair with policy `q` synchronizes. |

### Argument types (paper evidence, not invented)

| Argument | Type | Evidence |
|---|---|---|
| `σ, σ'` (in packet-flow labels) | `CtxPkt` | p. 9 §II-B: "the rule labels γ range over pairs of packets (σ, σ')" |
| `x` (channel) | `Channel := String` | Eq. (1): "x ranges over channel names" (§II-C, p. 8) |
| `q` (policy in labels) | `NetKAT` (dup-free) | §II-A p. 8: "x?N, x!N … N ∈ NetKAT⁻ᵈᵘᵖ"; Def. 6 p. 14: "q denoting terms in NetKAT⁻ᵈᵘᵖ"; A12–A15 p. 13: "z, y ∈ NetKAT⁻ᵈᵘᵖ" |

---

## 2. Configuration shape and list ordering

Per §II-B (p. 9): "We equip DyNetKAT policies with a configuration `(d, H, H')`
where `d` is the current DyNetKAT policy, `H` is the list of packets to be
processed by the network according to `d` and `H'` is the list of packets that
have been processed."

The paper uses **cons notation** `σ :: H` (line 419: `(p; q, σ :: H, H')`).
This confirms:

- **`H` (pending):** ordered list; **head = current packet** being processed.
- **`H'` (handled):** ordered list; **head = most recently produced output**.

### Design:
```lean
structure Config where
  proc    : DyNetKAT
  pending : List CtxPkt    -- H
  handled : List CtxPkt    -- H'
```

**Notation note (§2.1, resolved by paper evidence):** The text extraction
renders the empty list `⟨⟩` as `hi` (paper p. 5: "The empty list is denoted
by ⟨⟩"). In the `(cpolX;)` rule the source pending list is written `σ :: H`
and the target pending list is written `H` - i.e., **`H` in the conclusion is
the tail** of the source list (the source is `σ :: H`, the target keeps only
that `H`). The premise evaluates the NetKAT policy on the **single-packet
history** `σ :: ⟨⟩` (the current packet alone, empty rest) - the dup-free
denotation never sees the rest of the pending list. So: head consumed, tail
(`H`) becomes the new pending list. No ambiguity remains.

---

## 3. Rule (cpolX;) - packet flow through NetKAT policy (base rule)

This is the base rule that connects NetKAT denotational semantics to DyNetKAT
operational semantics. It is named `(cpolX;)` in the paper (line 417).

### Paper statement (from PDF text extraction, lines 414–419):

```
                    σ' ∈ ⟦p⟧(σ :: ⟨⟩)
    (p ; q, σ :: H, H') →_{(σ,σ')} (q, H, σ' :: H')
```

- The **source** pending list is `σ :: H`: head `σ` (the packet being
  processed), tail `H` (the remaining packets).
- The **premise** evaluates the NetKAT policy `p` on the single-packet
  history `σ :: ⟨⟩` - only the current packet, with an empty rest. (The
  extraction renders `⟨⟩` as `hi`; the paper defines `⟨⟩` as the empty list
  at p. 5.) The dup-free denotation never inspects the tail.
- The **target** pending list is `H` (the tail - head consumed) and the
  target handled list is `σ' :: H'` (output consed to head).

### Precise premises and conclusion

| Component | Detail |
|---|---|
| **Premise 1 (NetKAT denotation)** | `σ' ∈ ⟦p⟧(σ :: ⟨⟩)` - the packet `σ'` is a valid output of applying NetKAT policy `p` to the single-packet history `σ :: ⟨⟩`. For the dup-free fragment, this is equivalent to `Semantics p σ σ'`. |
| **Premise 2 (configuration shape)** | The current configuration has `proc = p ; q`, `pending = σ :: H` (head `σ`, tail `H`), `handled = H'`. |
| **Conclusion** | The resulting configuration has `proc = q`, `pending = H` (head consumed, tail kept), `handled = σ' :: H'` (output consed to head). Label: `(σ, σ')`. |

### Packet-history updates

- **Input (`H`):** `σ :: H` → `H` - the current packet `σ` is **consumed** (removed from the head of the pending list); the tail is kept.
- **Output (`H'`):** `H'` → `σ' :: H'` - the resulting packet `σ'` is **pushed** to the head of the handled list.

### Single-packet equivalence (per DESIGN_ALARMS A5)

For the dup-free fragment (NetKAT⁻ᵈᵘᵖ), the paper's `⟦p⟧(σ :: ⟨⟩)` is
equivalent to the repo's `Semantics p σ σ'` (i.e., `(σ, σ') ∈ ⟦p⟧` as a
single-packet relation). The rule therefore checks:

```
Semantics p σ σ'    (equivalently: σ' ∈ eval p σ)
```

### Lean constructor design

```lean
inductive Step : Config → Action → Config → Prop
  | cpol_seq_ok
      (p : NetKAT) (q : DyNetKAT)
      (σ σ' : CtxPkt) (H : List CtxPkt) (H' : List CtxPkt)
      (evaluates : Semantics p σ σ') :
      Step
        { proc := nSeq p q, pending := σ :: H, handled := H' }
        (Action.packet σ σ')
        { proc := q, pending := H, handled := σ' :: H' }
```

---

## 4. Drop / failure case - when `⟦p⟧(σ) = ∅`

### Paper evidence (no separate rule)

**There is no "drop rule" in Figure 8.** The paper does not define a `(cpol_;✗)`
rule with a distinct label. When a NetKAT policy `p` produces no output for `σ`
(i.e., `⟦p⟧(σ) = ∅`), the `(cpolX;)` rule's premise `σ' ∈ ⟦p⟧(σ::⟨⟩)` has **no
witness** - the rule simply does not apply. No transition fires.

This is explicitly demonstrated in the appendix proof of A0 (lines 1113–1118
of the text extraction):

> "For all σ' ∈ ⟦0⟧(σ::⟨⟩): (cpolX;) … However, observe that ⟦0⟧(σ::⟨⟩) is equal
> to empty set … Hence, the term `0; p` does not afford any transition.
> Similarly … the term ⊥ does not afford any transition. Hence … (0;p) ∼ ⊥."

### Interpretation

- **No transition, no label.** When `⟦N⟧(σ) = ∅`, there is **no** `Step`
  witness for the configuration `(N;q, σ::H, H')`. The configuration is
  *stuck*: the head packet `σ` remains in `pending` (it is NOT removed - no
  rule fires, so no state change occurs).
- **This is a rule-guard, not a rule.** The drop behavior is encoded in the
  *failure of the premise* of `(cpolX;)`, not as a separate transition rule.
  In the inductive `Step` definition there is no `cpol_seq_bad` constructor -
  the relation simply has no witness for that configuration.

### Design decision (do not invent)

Following the paper faithfully:

1. There is **no `Action.drop` constructor**.
2. There is **no `cpol_seq_bad` Step constructor**.
3. The `(cpolX;)` rule only fires when `⟦p⟧(σ)` is non-empty.
4. A configuration `(nSeq p q, σ :: H, H')` with `⟦p⟧(σ) = ∅` is **stuck**:
   `pending` keeps `σ :: H` and `handled` keeps `H'` unchanged. No step exists.

**Important correction to an earlier draft note:** a stuck configuration does
*not* "consume the packet" - consumption happens only as part of a successful
`(cpolX;)` step. Since no rule fires, the configuration is unchanged. This is
exactly what makes A0 (`0;p ≡ ⊥`) sound: both `0;p` and `⊥` afford no
transitions, so they are bisimilar.

**Ambiguity flagged (§4.1):** The journal-extension repo
(`/Users/ali/Desktop/DyNetKAT/lean/DyNetKAT/Semantics/Basic.lean:101-103`)
defines a `Label.drop` variant and a `policyDrop` rule
(`evalPolicy policy input = []` → `Step … (.drop input) continuation`).
This is a **journal-extension deviation** from the original paper. The
original DyNetKAT paper has no drop label and no drop rule. We do **not**
introduce one.

**Ambiguity flagged (§4.2):** `PAPER_CONFORMANCE.md` §7 (lines 285–294)
tentatively proposes a `(cpol_;✗)` rule with label `(σ, ⊥?)`. This is **not
supported** by the Figure 8 text extraction - no such rule appears in the
figure, and the appendix A0 proof states the term "does not afford any
transition." **Recommendation:** correct `PAPER_CONFORMANCE.md` §7 to state
that the drop case is modeled as absence of transitions (stuck configuration),
not as a labeled rule.

### Interaction with empty `H`

When `pending = []`, the `(cpolX;)` rule's pattern `pending = σ :: H` does not
match - there is no head packet to process. This is a guard on the
configuration shape, not a separate rule. No packet-flow transition fires for
an empty pending list (communication rules below do not depend on `H` and may
still fire).

---

## 5. Rule (cpol⊕) - non-deterministic choice (left and right)

### Paper statement (lines 423–430):

```
    (p, H₀, H₀₀) →γ (p', H₁, H₁₀)
    ─────────────────────────────  (cpol⊕)
    (p ⊕ q, H₀, H₀₀) →γ (p', H₁, H₁₀)         (left: mimic p)

    (q, H₀, H₀₀) →γ (q', H₁, H₁₀)
    ─────────────────────────────  (cpol⊕)
    (p ⊕ q, H₀, H₀₀) →γ (q', H₁, H₁₀)         (right: mimic q)
```

### Premises and conclusions

| Left rule | Right rule |
|---|---|
| **Premise:** `(p, H₀, H₀₀) →γ (p', H₁, H₁₀)` | **Premise:** `(q, H₀, H₀₀) →γ (q', H₁, H₁₀)` |
| **Conclusion:** `(p ⊕ q, H₀, H₀₀) →γ (p', H₁, H₁₀)` | **Conclusion:** `(p ⊕ q, H₀, H₀₀) →γ (q', H₁, H₁₀)` |

- The label `γ` is **inherited** from the child step (any of the four label shapes).
- The packet lists are **inherited unchanged**: source lists `H₀, H₀₀` in the
  premise become the parent's source lists; target lists `H₁, H₁₀` in the
  premise become the parent's target lists. The choice rule performs **no**
  history manipulation of its own.
- The target's `proc` is the child's target `p'` (or `q'`); the *other*
  operand disappears (the choice commits to one branch).

**Paper note (line 437):** "Whenever p (respectively, q) determines a
γ-labelled transition into (p', H₁, H₁₀) (respectively, (q', H₁, H₁₀)), the
policy p ⊕ q is able to mimic the same behaviour."

### Lean constructors (design sketch)

```lean
| cpol_choice_l {p q p' : DyNetKAT} {γ : Action}
    {H₀ H₀₀ H₁ H₁₀ : List CtxPkt}
    (step : Step ⟨p, H₀, H₀₀⟩ γ ⟨p', H₁, H₁₀⟩) :
    Step ⟨choice p q, H₀, H₀₀⟩ γ ⟨p', H₁, H₁₀⟩

| cpol_choice_r {p q q' : DyNetKAT} {γ : Action}
    {H₀ H₀₀ H₁ H₁₀ : List CtxPkt}
    (step : Step ⟨q, H₀, H₀₀⟩ γ ⟨q', H₁, H₁₀⟩) :
    Step ⟨choice p q, H₀, H₀₀⟩ γ ⟨q', H₁, H₁₀⟩
```

(Here `⟨d, H, H'⟩` abbreviates the `Config` anonymous-constructor notation.)

**Ambiguity flagged (§5.1):** The paper's subscript notation `H₀, H₀₀, H₁,
H₁₀` names four lists across the two configurations (pending/handled of
source and target). The extraction renders them as `H0, H00, H1, H10`; the
intended reading (confirmed by the prose at line 435–436: "Assume H0 is the
list of packets to be processed … and H00 is the list of packets handled
successfully") is: first index = source/target, second index = pending(0) /
handled(′). The rules propagate both lists unchanged.

---

## 6. Rule (cpol‖) - parallel composition (asynchronous, left and right)

### Paper statement (lines 433–439):

```
    (p, H₀, H₀₀) →γ (p', H₁, H₁₀)
    ─────────────────────────────  (cpol‖)
    (p ‖ q, H₀, H₀₀) →γ (p' ‖ q, H₁, H₁₀)       (left component steps)

    (q, H₀, H₀₀) →γ (q', H₁, H₁₀)
    ─────────────────────────────  (cpol‖)
    (p ‖ q, H₀, H₀₀) →γ (p ‖ q', H₁, H₁₀)       (right component steps)
```

### Premises and conclusions

| Left rule | Right rule |
|---|---|
| **Premise:** `(p, H₀, H₀₀) →γ (p', H₁, H₁₀)` | **Premise:** `(q, H₀, H₀₀) →γ (q', H₁, H₁₀)` |
| **Conclusion:** `(p ‖ q, H₀, H₀₀) →γ (p' ‖ q, H₁, H₁₀)` | **Conclusion:** `(p ‖ q, H₀, H₀₀) →γ (p ‖ q', H₁, H₁₀)` |

- The label `γ` is **inherited** from the child step.
- The **inactive** operand is preserved in the target process term: `q` in the
  left rule, `p` in the right rule.
- The packet lists are propagated unchanged from child to parent (no history
  manipulation at the parallel-composition level).

**Paper note (line 438):** "Rules (cpol‖) and (cpol‖) follow a similar
pattern; the only difference is that the 'inactive' operand is preserved by
the target of the semantic rule."

### Lean constructors (design sketch)

```lean
| cpol_par_l {p q p' : DyNetKAT} {γ : Action}
    {H₀ H₀₀ H₁ H₁₀ : List CtxPkt}
    (step : Step ⟨p, H₀, H₀₀⟩ γ ⟨p', H₁, H₁₀⟩) :
    Step ⟨parallel p q, H₀, H₀₀⟩ γ ⟨parallel p' q, H₁, H₁₀⟩

| cpol_par_r {p q q' : DyNetKAT} {γ : Action}
    {H₀ H₀₀ H₁ H₁₀ : List CtxPkt}
    (step : Step ⟨q, H₀, H₀₀⟩ γ ⟨q', H₁, H₁₀⟩) :
    Step ⟨parallel p q, H₀, H₀₀⟩ γ ⟨parallel p q', H₁, H₁₀⟩
```

**Design note (§6.1):** `PAPER_CONFORMANCE.md` §7 lists an extra rule
`(cpol_;_‖)` ("NetKAT policy in left of parallel") as a specialization of
`cpol‖`. The Figure 8 extraction shows **no such separate rule** - the
asynchronous parallel rules above already cover `N;d` in a parallel operand,
because `(cpolX;)` fires on the sub-configuration `(N;d, σ::H, H')` and
`(cpol‖)` lifts it. No separate constructor is needed. Flagged for
correction in `PAPER_CONFORMANCE.md`.

---

## 7. Rules (cpol?) and (cpol!) - asynchronous receive and send

### Paper statement (lines 442–445):

```
    ──────────────────  (cpol?)
    (x?p; q, H, H') →_{x?p} (q, H, H')

    ──────────────────  (cpol!)
    (x!p; q, H, H') →_{x!p} (q, H, H')
```

### Premises and conclusions

| Receive (cpol?) | Send (cpol!) |
|---|---|
| **Premise:** none (axiom-style rule) | **Premise:** none (axiom-style rule) |
| **Conclusion:** `(x?p; q, H, H') →_{x?p} (q, H, H')` | **Conclusion:** `(x!p; q, H, H') →_{x!p} (q, H, H')` |

- These are **axiom rules** (no premises): a receive/send prefix always
  affords its communication step, regardless of the packet lists.
- The label is `x?p` (resp. `x!p`) - carrying the channel `x` and the
  communicated NetKAT policy `p`.
- **Both packet lists remain unchanged:** `H → H`, `H' → H'`.

**Paper note (lines 338–340):** "Mere sending (cpol!) and receiving (cpol?)
entail transitions labelled accordingly, and continue with the DyNetKAT
policy following the ; operator. Note that the list of packets to be
processed by the network and the list of packets handled successfully by the
network remain unchanged."

### Lean constructors (design sketch)

```lean
| cpol_recv {x : Channel} {p : NetKAT} {q : DyNetKAT}
    {H H' : List CtxPkt} :
    Step ⟨recv x p q, H, H'⟩ (Action.recv x p) ⟨q, H, H'⟩

| cpol_send {x : Channel} {p : NetKAT} {q : DyNetKAT}
    {H H' : List CtxPkt} :
    Step ⟨send x p q, H, H'⟩ (Action.send x p) ⟨q, H, H'⟩
```

**Design note (§7.1):** The communicated policy in the *label* is the same
term `p` that appears in the process prefix `x?p` / `x!p`. There is no
side condition on `p` (it need not be in normal form for the rule to fire;
normal forms matter only for the axiomatization in §III).

---

## 8. Rules (cpol!?) and (cpol?!) - synchronization

### Paper statement (lines 447–457):

```
    (q, H, H') →_{x!p} (q', H, H')      (s, H, H') →_{x?p} (s', H, H')
    ─────────────────────────────────────────────────────────────  (cpol!?)
    (q ‖ s, H, H') →_{rcfg(x,p)} (q' ‖ s', H, H')

    (q, H, H') →_{x?p} (q', H, H')      (s, H, H') →_{x!p} (s', H, H')
    ─────────────────────────────────────────────────────────────  (cpol?!)
    (q ‖ s, H, H') →_{rcfg(x,p)} (q' ‖ s', H, H')
```

### Premises and conclusions

| (cpol!?) - left sends, right receives | (cpol?!) - left receives, right sends |
|---|---|
| **Premise 1:** `(q, H, H') →_{x!p} (q', H, H')` | **Premise 1:** `(q, H, H') →_{x?p} (q', H, H')` |
| **Premise 2:** `(s, H, H') →_{x?p} (s', H, H')` | **Premise 2:** `(s, H, H') →_{x!p} (s', H, H')` |
| **Conclusion:** `(q ‖ s, H, H') →_{rcfg(x,p)} (q' ‖ s', H, H')` | **Conclusion:** `(q ‖ s, H, H') →_{rcfg(x,p)} (q' ‖ s', H, H')` |

- **Both premises must use the same channel `x` and the same policy `p`** -
  this is the "agreement" condition. The paper (lines 341–344): "when both
  operands q and, respectively, s 'agree' on sending/receiving a policy p on
  channel x in the context of the same packet lists H and H', and behave like
  q', respectively, s' afterwards, then a rcfg(x, p) step can be observed.
  The system proceeds with the continuation behaviour q' ‖ s'."
- **Both premises must use the same packet lists `H, H'`** for source and
  target. Since the send/receive rules never modify the lists, this reduces
  to: source lists shared, target lists shared.
- The emitted label is `rcfg(x, p)` - the synchronization output.
- The target process is `q' ‖ s'` (both continuations run in parallel).

### How the premises are discharged

The premises `(q, H, H') →_{x!p} (q', H, H')` and `(s, H, H') →_{x?p}
(s', H, H')` are themselves derived by rules (cpol!) and (cpol?) - but note
they may also be derived by any other rule that produces an `x!p` / `x?p`
label (e.g., a nested synchronization inside a parallel operand, or a
recursion unfolding that exposes a send). The premises are generic `Step`
judgments constrained to the given label shapes; they are not hardwired to
the (cpol!)/(cpol?) axioms.

### Lean constructors (design sketch)

```lean
| cpol_sync_send_recv {x : Channel} {p : NetKAT}
    {q q' s s' : DyNetKAT} {H H' : List CtxPkt}
    (sendStep : Step ⟨q, H, H'⟩ (Action.send x p) ⟨q', H, H'⟩)
    (recvStep : Step ⟨s, H, H'⟩ (Action.recv x p) ⟨s', H, H'⟩) :
    Step ⟨parallel q s, H, H'⟩ (Action.rcfg x p) ⟨parallel q' s', H, H'⟩

| cpol_sync_recv_send {x : Channel} {p : NetKAT}
    {q q' s s' : DyNetKAT} {H H' : List CtxPkt}
    (recvStep : Step ⟨q, H, H'⟩ (Action.recv x p) ⟨q', H, H'⟩)
    (sendStep : Step ⟨s, H, H'⟩ (Action.send x p) ⟨s', H, H'⟩) :
    Step ⟨parallel q s, H, H'⟩ (Action.rcfg x p) ⟨parallel q' s', H, H'⟩
```

**Ambiguity flagged (§8.1):** The paper's premise notation writes the same
`H, H'` in both premises and the same `H, H'` in the conclusion - i.e., the
two sub-steps share the packet lists. Because (cpol?)/(cpol!) never modify
the lists, sharing is automatic when the premises are derived by those rules.
But if a premise is derived by a *different* rule (e.g., a nested parallel
step that consumes a packet), the shared-list requirement becomes a genuine
constraint: both operands must transition over the *same* packet lists. The
formalization should keep the premises as written (shared `H, H'`), which is
the faithful reading. This matters for soundness of A12.

**Ambiguity flagged (§8.2):** The synchronization emits `rcfg(x, p)` where
`p` is the agreed policy. The paper uses `p` in Figure 8 but `z` in A12
(`(x?z;p) | (x!z;q) ≡ rcfg_{x,z};(p‖q)`). The symbol variance is notational
(see PROCESS_AST_DESIGN.md §14.7 item 2); the label carries the same
dup-free `NetKAT` term.

---

## 9. Rule (cpolX) - recursion unfolding

### Paper statement (lines 414–420, right column):

```
    (p, H₀, H₁) →γ (p', H₀₀, H₁₀)
    ─────────────────────────────  (cpolX)   [X ≜ p]
    (X, H₀, H₁) →γ (p', H₀₀, H₁₀)
```

The paper prose (line 345): "As denoted by (cpolX), a recursive variable
defined as X ≜ p behaves according to p."

### Premises and conclusions

- **Premise:** `(p, H₀, H₁) →γ (p', H₀₀, H₁₀)` - the defining body `p` of the
  variable `X` affords a `γ`-step.
- **Conclusion:** `(X, H₀, H₁) →γ (p', H₀₀, H₁₀)` - the variable mimics it.
- The label and both packet lists are inherited unchanged.

### Side condition (environment, not the rule)

The defining equation `X ≜ p` is a property of the **recursion environment**
(`RecEnv : Var → DyNetKAT` with unique definitions), per
`PROCESS_AST_DESIGN.md` §4. The rule itself carries no side condition; the
environment lookup is external. In Lean this becomes either:

- an explicit `RecEnv` parameter threaded through `Step` (global environment
  design), or
- an explicit premise `env X = some p` in the constructor.

**Design decision (§9.1):** Prefer the **explicit premise** form, keeping
`Step : Config → Action → Config → Prop` environment-free and adding the
lookup as a hypothesis:

```lean
| cpol_var {X : Var} {p p' : DyNetKAT} {γ : Action}
    {H₀ H₁ H₀₀ H₁₀ : List CtxPkt}
    (definition : env X = p)
    (step : Step ⟨p, H₀, H₁⟩ γ ⟨p', H₀₀, H₁₀⟩) :
    Step ⟨var X, H₀, H₁⟩ γ ⟨p', H₀₀, H₁₀⟩
```

**Flag (§9.2, open design question):** Whether `env` is a global parameter of
the whole semantics module or an extra `Step` index is an implementation
decision deferred to the `Semantics.lean` implementation task. The paper does
not formalize the environment; it treats `X ≜ p` as meta-level notation.
Both options are faithful; the premise form is the least invasive.

---

## 10. Complete rule inventory and correspondence to the paper

| # | Paper rule name | Lean constructor | Premises | Label | H manipulation | H' manipulation |
|---|---|---|---|---|---|---|
| 1 | `(cpolX;)` | `cpol_seq_ok` | `σ' ∈ ⟦p⟧(σ::⟨⟩)` | `(σ, σ')` | `σ :: H → H` (head consumed) | `H' → σ' :: H'` (output consed) |
| 2 | `(cpol⊕)` left | `cpol_choice_l` | child step of `p` | inherited | unchanged | unchanged |
| 3 | `(cpol⊕)` right | `cpol_choice_r` | child step of `q` | inherited | unchanged | unchanged |
| 4 | `(cpol‖)` left | `cpol_par_l` | child step of `p` | inherited | unchanged | unchanged |
| 5 | `(cpol‖)` right | `cpol_par_r` | child step of `q` | inherited | unchanged | unchanged |
| 6 | `(cpol?)` | `cpol_recv` | none | `x?p` | unchanged | unchanged |
| 7 | `(cpol!)` | `cpol_send` | none | `x!p` | unchanged | unchanged |
| 8 | `(cpol!?)` | `cpol_sync_send_recv` | two child steps (`x!p`, `x?p`) | `rcfg(x,p)` | unchanged | unchanged |
| 9 | `(cpol?!)` | `cpol_sync_recv_send` | two child steps (`x?p`, `x!p`) | `rcfg(x,p)` | unchanged | unchanged |
| 10 | `(cpolX)` | `cpol_var` | child step of body `p`; `env X = p` | inherited | unchanged | unchanged |

**Total: 10 constructors** (9 rules in the figure; `(cpol⊕)` and `(cpol‖)`
each have two symmetric halves counted separately, and `(cpolX;)` is one).

**Drop case: no constructor.** When `⟦p⟧(σ) = ∅`, rule 1's premise fails and
the configuration is stuck. No `cpol_seq_bad`, no `Action.drop`.

### Full inductive sketch (consolidated)

```lean
inductive Step : Config → Action → Config → Prop
  | cpol_seq_ok   -- rule 1  (packet flow; the ONLY history-modifying rule)
  | cpol_choice_l -- rule 2
  | cpol_choice_r -- rule 3
  | cpol_par_l    -- rule 4
  | cpol_par_r    -- rule 5
  | cpol_recv     -- rule 6
  | cpol_send     -- rule 7
  | cpol_sync_send_recv -- rule 8
  | cpol_sync_recv_send -- rule 9
  | cpol_var      -- rule 10
```

---

## 11. Key structural properties (design consequences)

### 11.1 Only `(cpolX;)` touches the packet lists

Exactly one rule modifies `pending`/`handled`: the base packet-flow rule.
Every other rule propagates the lists unchanged. This is what makes the
"layered" semantics (paper line 326) work: NetKAT denotations act on packets,
DyNetKAT operators only route and synchronize.

### 11.2 Determinism of packet consumption

The head of `pending` is the only packet a `(cpolX;)` step can consume. A
configuration `(nSeq p q, σ :: H, H')` affords one `(σ, σ')` step for **each**
`σ' ∈ ⟦p⟧(σ)` - branching comes from non-determinism in `⟦p⟧` (e.g., `union`),
not from list manipulation.

### 11.3 Stuck configurations

A configuration is stuck (no `Step` witness) iff no rule applies. Notable
stuck shapes:
- `(nSeq p q, σ :: H, H')` with `⟦p⟧(σ) = ∅` - dropped packet (A0 soundness).
- `(deadlock, H, H')` - no rule has `⊥` in the source (A0: `⊥` affords nothing).
- `(nSeq p q, [], H')` - empty pending list; no head packet.
- `(var X, H, H')` where `X` is undefined in `env` - no body to unfold.

### 11.4 Label-shape exclusivity

- Only `(cpolX;)` emits `Action.packet`.
- Only `(cpol?)`/`(cpol!)`/their lifting rules emit `Action.recv`/`Action.send`.
- Only the two synchronization rules emit `Action.rcfg`.
This exclusivity is useful for inversion lemmas downstream (bisimulation
proofs, Lemma 10 soundness).

---

## 12. Ambiguities and open questions (consolidated)

| # | Ambiguity | Evidence status | Recommendation |
|---|---|---|---|
| 1 | Drop label / `(cpol_;✗)` rule | **Resolved by paper:** no drop rule exists; appendix A0 proof (lines 1113–1118) states `0;p` "does not afford any transition". | No `Action.drop`, no `cpol_seq_bad`. Stuck configuration. Correct `PAPER_CONFORMANCE.md` §7. |
| 2 | `⟨⟩` rendering in the premise | Extraction renders the empty list `⟨⟩` as `hi` (paper p. 5 defines `⟨⟩`). | **Resolved:** premise is `σ' ∈ ⟦p⟧(σ::⟨⟩)` - single-packet history. Conclusion's `H` is the tail of the source `σ :: H`. |
| 3 | `⟦p⟧(σ::⟨⟩)` vs single-packet `Semantics p σ σ'` | **Resolved:** dup-free fragment ⇒ histories are single packets (DESIGN_ALARMS A5). | Use `Semantics p σ σ'` from `NetKAT/Semantics.lean:61`. |
| 4 | Shared lists in synchronization premises | Paper writes the same `H, H'` in both premises. | Keep the shared-list constraint literally in the Lean premises (faithful; matters for A12 soundness). |
| 5 | Recursion environment threading | Paper treats `X ≜ p` meta-levelly; no environment in Fig. 8. | Explicit `env X = p` premise; global-vs-indexed `env` is an implementation decision (§9.2). |
| 6 | `(cpol_;_‖)` "specialization" rule in PAPER_CONFORMANCE §7 | Not present in Figure 8 extraction. | Remove; `(cpol‖)` lifting already covers `N;d` operands. |
| 7 | Packet type: `CtxPkt` vs parameterized `Packet F V` | Concrete fixture used by all existing modules. | Use `CtxPkt`; full parameterization is a future joint refactor of `Action`/`Config`/`Step` (PROCESS_AST_DESIGN §14.7 item 3). |
| 8 | Non-determinism in `⟦p⟧` (multiple outputs) | `⟦p⟧(σ)` is a set; each `σ'` yields a distinct step. | One constructor instance per output packet; branching is semantic, not syntactic. |
| 9 | `rcfg` label vs `rcfg_{x,z}` term constant | Label in `Action.lean`; constant in `Operators.lean` (Eq. 4/6, A12). | Out of scope here; the `(rcfg_{x,z})` rule (Eq. 4) belongs to `Operators.lean` design. |
| 10 | Empty `H` interaction with communication rules | `(cpol?)/(cpol!)` do not read `H`. | Communication steps fire regardless of `pending`; packet-flow steps require non-empty `pending`. |

---

## 13. Dependencies for the future `Semantics.lean` module

| Dependency | File:lines | Kind |
|---|---|---|
| `Config` (proc, pending, handled) | planned `DyNetKAT/Config.lean` (PROCESS_AST_DESIGN §7) | type |
| `DyNetKAT` (deadlock, nSeq, recv, send, parallel, choice, var) | planned `DyNetKAT/AST.lean` (PROCESS_AST_DESIGN §2) | type |
| `Action` (packet, recv, send, rcfg) | planned `DyNetKAT/Action.lean` (PROCESS_AST_DESIGN §14) | type |
| `Semantics` (NetKAT denotation) | `NetKAT/Semantics.lean:61` | relation (premise of rule 1) |
| `CtxPkt` | `NetKAT/Packet.lean:148` | type (list elements) |
| `Channel`, `Var` | planned `DyNetKAT/AST.lean` (§3–4) | types |
| `RecEnv` (optional) | future | environment for rule 10 |

`Semantics.lean` will import `Config.lean`, `Action.lean`, and
`NetKAT/Semantics.lean`. It defines `Step` as the inductive above and nothing
else (no theorems in the first cut; inversion lemmas and bisimulation support
are separate tasks).

---

## 14. Summary of design decisions (non-invented)

1. `Step : Config → Action → Config → Prop` is an inductive with **exactly
   10 constructors** mirroring Figure 8 (9 printed rules; ⊕ and ‖ each split
   into left/right).
2. The **only** history-modifying rule is `(cpolX;)` (`cpol_seq_ok`):
   premise `Semantics p σ σ'`; consumes head of `pending`; conses output onto
   `handled`; label `Action.packet σ σ'`.
3. **No drop rule, no drop label.** Failure = stuck configuration (premise
   failure), per the paper's A0 soundness argument.
4. Choice/parallel/recursion rules inherit label and both packet lists
   unchanged; the inactive operand is preserved (parallel) or discarded
   (choice).
5. Receive/send are premise-free axioms preserving both lists.
6. Synchronization rules require two child steps with **matching channel and
   policy** over the **same packet lists**, emitting `Action.rcfg x p`.
7. Recursion unfolding carries an explicit environment premise `env X = p`.
8. Every constructor and side condition above is cited to the paper text
   extraction; nothing is invented. Open items are flagged in §12.

---

*End of design document. This is a design artifact only; no Lean files were
created or modified. See HANDOFF.md for the Phase 2 status.*
