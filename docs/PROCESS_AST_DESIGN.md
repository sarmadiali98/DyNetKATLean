# Process AST Design — DyNetKAT (Eq. 1, paper p. 8 §II-C "DyNetKAT Syntax")

**Task:** Design ONLY `Config.lean` using Figure 8 of the DyNetKAT paper.
Specify `Config`, packet histories `H/H′`, their ordering, and dependencies.
Correct Eq. (1) section citation. Documentation only; no code, commits, or push. STOP.
**Paper source:** *DyNetKAT: An Algebra of Dynamic Networks*
arXiv:2102.10035v4 (22 May 2021), FoSSaCS 2022.
**Scope:** Eq. (1) only — the *base* DyNetKAT syntax. Documentation only; no code.
**Date:** 2026-10-18

---

## 0. Scope and provenance

The authoritative source is **Eq. (1)** of the paper (printed p. 8, §II-C "DyNetKAT
Syntax"), which defines the base DyNetKAT process syntax *on top of* the dup-free
NetKAT fragment. All constructors, channel types, recursion variables, and the `rcfg`
argument types below are justified by reference to Eq. (1), §II-C, §II-B (Fig. 8),
and — where Eq. (1) is silent — §III-A (Eq. 6) / Fig. 11.

Eq. (1) as printed (p. 8):

```
N ::= NetKAT⁻ᵈᵘᵖ

D ::= ⊥ | N;D | x?N;D | x!N;D | D‖D | D⊕D | X
X,D
```

where:
- `N` ranges over `NetKAT⁻ᵈᵘᵖ` (the existing `NetKAT` inductive in `NetKAT/AST.lean`).
- `z, y ∈ NetKAT⁻ᵈᵘᵖ` (used in axiom A1, Fig. 11).
- `x` ranges over **channel names** (§II-C: "x ranges over channel names").
- `X` ranges over **recursive variables** (§II-C: "X over a (countably infinite) set of
  recursive variables"; "each recursive variable should have a unique defining equation
  X ≜ d").
- `D, D` range over DyNetKAT processes.

**Note on Eq. (6) vs. Eq. (1):** The *extended* syntax Eq. (6) (p. 14, §III-A)
adds `rcfg_{x,N};D`, `δ_ℒ(D)`, `π_n(D)`, `D⌊⌊D`, `D|D`. The `rcfg` *constant*
appears first in Eq. (6) and in the axioms (Eq. 4, A12–A15). It is **not**
a constructor of the base syntax in Eq. (1). This design therefore places
`rcfg_{x,z}` and the extended operators in a *separate* `Operators.lean` module
(see §7), keeping `AST.lean` a faithful rendering of Eq. (1).

---

## 1. Module location and structure

Planned path (new directory, not yet created):

```
lean/DyNetKAT/DyNetKAT/
├── AST.lean         -- Eq. (1) inductive: ⊥, N;D, x?N;D, x!N;D, ‖, ⊕, X
├── Config.lean      -- configurations (d, H, H′); see §7
├── Action.lean      -- labels γ (incl. rcfg(x,r)); see §5
├── Semantics.lean   -- labeled SOS Step (Fig. 8) — NOT designed here
└── Operators.lean   -- extended syntax: δ, π_n, rcfg const, ⌊⌊, | | (Eq. 6)
```

`AST.lean` is the subject of this document. `Config.lean`, `Action.lean`, and
`Semantics.lean` are specified only where `AST.lean` *depends* on them
(channel/var types, the rcfg label decision). `Operators.lean` is named as
out of scope for *this* task (Eq. 1 only).

---

## 2. The `DyNetKAT` inductive (constructors)

Faithful to Eq. (1):

```lean
-- Channel names and recursion-variable names (see §3, §4).
inductive DyNetKAT
| deadlock : DyNetKAT                          -- ⊥        (Eq. 1)
| nSeq    : NetKAT → DyNetKAT → DyNetKAT      -- N ; D    (Eq. 1)
| recv    : Channel → NetKAT → DyNetKAT → DyNetKAT  -- x?N ; D  (Eq. 1)
| send    : Channel → NetKAT → DyNetKAT → DyNetKAT  -- x!N ; D  (Eq. 1)
| parallel: DyNetKAT → DyNetKAT → DyNetKAT    -- D ‖ D    (Eq. 1)
| choice  : DyNetKAT → DyNetKAT → DyNetKAT    -- D ⊕ D    (Eq. 1)
| var     : Var → DyNetKAT                     -- X        (Eq. 1)
```

### Constructor rationale (by case of Eq. 1)

| Lean ctor | Arity | Paper Eq. (1) production | Paper wording (§II-C) |
|---|---|---|---|
| `deadlock` | nullary | `⊥` | "By ⊥ we denote a dummy policy without behaviour" |
| `nSeq` | `NetKAT → DyNetKAT → DyNetKAT` | `N;D` | "our new sequential composition operator … N applicable to the current packet has come to a successful end … the next packet can be fetched for processing according to D" |
| `recv` | `Channel → NetKAT → DyNetKAT → DyNetKAT` | `x?N;D` | "x?N ; D … receiving NetKAT⁻ᵈᵘᵖ policies through channel x … a new packet is fetched and processed according to D" |
| `send` | `Channel → NetKAT → DyNetKAT → DyNetKAT` | `x!N;D` | "x!N ; D … sending NetKAT⁻ᵈᵘᵖ policies through channel x … a new packet is fetched" |
| `parallel` | `DyNetKAT → DyNetKAT → DyNetKAT` | `D‖D` | "The parallel composition … is denoted by D ‖ D" |
| `choice` | `DyNetKAT → DyNetKAT → DyNetKAT` | `D⊕D` | "Non-deterministic choice of DyNetKAT policies is denoted by D ⊕ D" |
| `var` | `Var → DyNetKAT` | `X` | "one can use recursive variables X … each recursive variable should have a unique defining equation X ≜ d" |

### Design notes on each constructor

**`nSeq` (`N;D`):**
- The `NetKAT` argument is the *existing* `NetKAT` type from
  `packages/NetKATLean/NetKATLean/Core/AST.lean:89` (8 constructors: `drop, id, test,
  completeTest, assign1, union, seq, star`). This is the dup-free fragment:
  Eq. (1) writes `N ::= NetKAT⁻ᵈᵘᵖ`.
- Paper §II-C: "we do not explicitly specify the trailing `; ⊥` whenever clear
  from the context." This is a *notation shorthand*: a policy written as just
  `N` at the end of a sequencing chain is implicitly `N; ⊥`. The `nSeq`
  constructor always carries an explicit continuation `D`, so the shorthand
  maps to `nSeq N deadlock`. No semantic loss; the invariant is syntactic sugar.

**`recv` / `send` (`x?N;D`, `x!N;D`):**
- §II-C: "sending and receiving NetKAT⁻ᵈᵘᵖ policies through channel x … `x?N`
  and `x!N`." The `NetKAT` argument is the same dup-free `NetKAT` type as in
  `nSeq`.
- The channel `x` is a `Channel` value (§3).
- The continuation `D` is present because Eq. (1) writes the full form
  `x?N ; D` / `x!N ; D`; a "bare" `x?N` (no continuation) is not in Eq. (1).

**`parallel` (`D‖D`):**
- Async parallel composition. §II-C: "The parallel composition of two
  DyNetKAT policies (to enable synchronization) is denoted by D ‖ D."
- Commutativity is *axiom* A6 (`p||q ≡ q||p`); the constructor itself is
  ordered (Lean needs a definite argument order).

**`choice` (`D⊕D`):**
- §II-C: "Non-deterministic choice … denoted by D ⊕ D."
- "For a non-deterministic choice over a finite domain P, we use the syntactic
  sugar `⊕_{p∈P} P₀`" — a finite-domain iteration sugar, not an extra
  constructor. `⊕` itself is binary; finite sums are built by iteration.

**`var` (`X`):**
- §II-C: "recursive variables X … a (countably infinite) set of recursive
  variables … each recursive variable should have a unique defining equation
  X ≜ d."
- The constructor takes a *name* (`Var`). The defining equation `X ≜ d` is
  **not** stored inside the constructor — that would make the type non-inductive
  (a graph, not a tree). Instead, recursive definitions live in a separate
  `RecEnv` (binding `Var → DyNetKAT`), applied when unfolding (see §4 and the
  `cpolX` rule, Fig. 8).

---

## 3. Channel type

### Paper requirement
- §II-C: "`x` ranges over channel names."
- §II-B (Fig. 8): labels include `x!q`, `x?q`, `rcfg(x, q)` — channels carry
  communication actions.
- §III ("In practice … `ℒ` be the set of forbidden actions ranging over
  elements of shape `x?N` and `x!N`") — channels index forbidden actions for
  δ restriction.
- §IV ("a DyNetKAT term encoding all possible behaviours over `𝒜`: …
  `rcfg(x,p) ∈ 𝒜`") — channels index actions in the safety alphabet.

### Cardinality
- §II-C: "`x` ranges over channel names" with no finite bound — channels are a
  **countably infinite** set. (Concrete programs use finitely many, but the
  *type* must be infinite to admit fresh channel names in compositions.)
- `UNIFIED_ARCHITECTURE_REQUIREMENTS.md` (line 306) records: "Channel type:
  countably infinite."

### Design choice
`Channel := String`

- `String` has a countably infinite supply (all finite strings over a finite
  alphabet), matching §II-C.
- No `[Fintype Channel]` instance (and must not — the paper does not bound
  channels).
- `String` already has `DecidableEq` in Lean 4 core, so channel equality is
  decidable (needed by the restriction `δℒ` and action-labelling machinery in
  later modules).

**Do not invent:** There is no evidence the paper fixes a specific finite set
of channels or a `ℕ`-indexed channel type. `String` is the most conservative
countably-infinite choice and matches the JSON `channels : list of strings`
schema (see §6 of `UNIFIED_ARCHITECTURE_REQUIREMENTS.md`).

---

## 4. Recursion variables (`Var`)

### Paper requirement
- §II-C: "one can use recursive variables X in the specification of DyNetKAT
  policies, where each recursive variable should have a **unique defining
  equation X ≜ d**."
- §III-A, Definition 7 (Guardedness): recursion restricted to *guarded*
  recursion — "a policy should be applied before changing state to a new
  recursive definition."
- Guardedness (p. 13): an occurrence of `X` is guarded iff (i) it is under a
  `;`, or (ii) it is the argument of `x?X;D` / `x!X;D` / `rcfg(X,t)`
  (extended syntax).

### Design choice
`Var := String`

- Matches the JSON input format: `recursive_variables` is a
  `dict (name → string)` (`DYNETIKAT_REFERENCE_AUDIT.md` §3.2); the keys
  *are* the variable names (e.g. "Switch", "Host", etc. in Fig. 5/6).
  Named variables are far more ergonomic than `Nat` indices and avoid an
  ad-hoc de Bruijn encoding.
- Lean `String` is countably infinite — sufficient for "a (countably infinite)
  set of recursive variables."
- `DecidableEq String` is available.

### Unique defining equation
- This is a **well-formedness invariant** of the *environment* binding `X ≜ d`,
  not a property encoded in the `var` constructor. The `var` constructor
  merely embeds the name; the binding lives in a separate `RecEnv`
  (`Var → Option DyNetKAT` or `Var → DyNetKAT` with a total function
  guaranteeing a definition for every referenced variable).
- Guardedness (Definition 7) is a separate predicate `IsGuarded` over
  environments — **not** part of the AST design. It is enforced before
  recursion is unfolded (via the `cpolX` rule, Fig. 8). **Do not invent**
  guardedness checking inside the inductive type.

### Why not `Nat` indices
- `Nat` is simpler categorically but loses the JSON parity and is less
  ergonomic. The reference tool's JSON uses symbolic names. **Flag:** if
  future work needs a de Bruijn-style encoding for mechanized substitution,
  that is a separate refactor — not assumed here.

---

## 5. The `rcfg` action-label decision (ambiguity: rcfg absent from Eq. 1)

### The conflict
Eq. (1) contains **no** `rcfg` constructor. But:

1. **Action labels (Fig. 8, p. 9–10):** The label grammar is
   `γ ::= (σ,σ′) | x!q | x?q | rcfg(x, q)`. So `rcfg` appears as an *action*.
2. **Extended syntax (Eq. 6, p. 14):** `rcfg_{x,N};D` — a *term* constructor
   of `D_e`.
3. **Axiom constant (Eq. 4 / A12–A15, p. 13–14):** `rcfg_{x,z}` is a *constant*
   used inside axioms; the semantic rule (4) is
   `(rcfg_{x,z};p, H₀, H₁) ->_{rcfg(x,z)} (p, H₀, H₁)`.

### Resolution (do not invent — resolved only by paper evidence)
- **Base AST (`AST.lean`, Eq. 1 scope):** `DyNetKAT` has **no** `rcfg`
  constructor. OK (Eq. 1 has none.)
- **`rcfg(x, q)` as an action label:** belongs in `Action.lean` (Fig. 8 label
  grammar). The `q` argument is `NetKAT⁻ᵈᵘᵖ`.
- **`rcfg_{x,z}` as a term constant (Eq. 6, A12–A15):** belongs in
  `Operators.lean` (extended syntax), not the base AST.

### Ambiguity flagged: type of `rcfg`'s NetKAT argument
The ar5iv text extraction is slightly garbled at this point (the PDF renders
`q`, `r`, `z`, `p`, `n` inconsistently for the same "NetKAT policy" argument
across `x?N`, `x!N`, and `rcfg(x,q)`).

**Paper evidence (resolved, not invented):**
- §II-C (p. 8): "`x?N` and `x!N` … `N ∈ NetKAT⁻ᵈᵘᵖ`." Explicitly dup-free.
- §II-B (Fig. 8, p. 9): the label grammar `γ ::= … | rcfg(x, q)` uses `q` —
  the same symbol family as the `x?q`, `x!q` labels, which §II-C pins to
  `NetKAT⁻ᵈᵘᵖ`.
- Axioms A12–A15 (p. 13): `z, y ∈ NetKAT⁻ᵈᵘᵖ`; `(x?z;p)|(x!z;q) ≡ rcfg_{x,z};(p||q)`.
  The `z`/`y` are stated as `NetKAT⁻ᵈᵘᵖ`.

**Design decision (confirmed by paper, not invented):** In `AST.lean`, the
`recv`/`send` constructors and (in `Action.lean`) the `rcfg` label all take a
`NetKAT` argument = the existing dup-free `NetKAT` type. No separate "full
NetKAT" type is introduced for these arguments.

**Flag for later (`Operators.lean`):** The extended `rcfg_{x,N};D` constant
   (Eq. 6) also takes `N ∈ NetKAT⁻ᵈᵘᵖ`. This must be consistent. No decision is
made here about whether the extended `rcfg_{x,N}` constant's argument should
be the same `NetKAT` type — it will be, by the same §II-C evidence — but
that decision is recorded under `Operators.lean` design, not here.


---

## 6. The `rcfg` argument types (full specification)

This section consolidates, for the `rcfg` construct that *does* appear in
Fig. 8 (as an action label), the exact argument types and the provenance of
each. There is **no** `rcfg` constructor in the base `DyNetKAT` AST
(Eq. 1); `rcfg` enters the design only as an `Action` label (this section)
and later as an extended-syntax constant in `Operators.lean` (§8).

### Action label `rcfg(x, q)` — Fig. 8 (p. 9)

The label grammar in Fig. 8 is:

```
γ ::= (σ, σ′) | x!q | x?q | rcfg(x, q)
```

where (by §II-C and the axiom text):
- `x` : channel name (`Channel := String`). Justification: §II-C, "x ranges over
  channel names" and the same `x` appears in `x!N`/`x?N` (Eq. 1).
- `q` : a `NetKAT⁻ᵈᵘᵖ` policy. **Resolved by paper evidence** (see §5):
  the `q` in `rcfg(x,q)` uses the same symbol family as the `q` in `x?q`/`x!q`
  (Fig. 8), and §II-C pins those to `N ∈ NetKAT⁻ᵈᵘᵖ`. So `q : NetKAT` (the
  existing dup-free `NetKAT` type).
- `(σ, σ′)` : packet flow. `σ, σ′ : CtxPkt` (the existing concrete packet
  type, `NetKAT/Packet.lean:148`). **Justification:** Fig. 8, "labels γ range
  over pairs of packets (σ, σ′) …". The packet type `CtxPkt` is the existing
  `Packet FieldName FieldValueEnum`. *(Flag: the general packet model
  `Packet FieldType Value` is parameterized; `CtxPkt` is the concrete 4-field
  fixture used by all current modules. See HANDOFF.md checkpoint on
  parameterization. The design uses `CtxPkt` for consistency with the
  implemented `Semantics`, and notes the parameterization opportunity as a
  future refactor.)*

So the `Action` type (in `Action.lean`, **not** `AST.lean`) is:

```lean
inductive Action
| packet  : CtxPkt → CtxPkt → Action      -- (σ, σ′)           Fig. 8
| recv    : Channel → NetKAT → Action     -- x?q               Fig. 8
| send    : Channel → NetKAT → Action     -- x!q               Fig. 8
| rcfg    : Channel → NetKAT → Action     -- rcfg(x, q)        Fig. 8
```

> **Detailed design of `Action.lean`** is given in §14 below (`Design ONLY
> `Action.lean``, per the same paper evidence). The constructor list above is
> a summary; §14 specifies exact argument types, dependencies, the
> action-label-vs-process-syntax distinction, and ambiguities.

**Argument-type table for `rcfg`:**

| Argument | Lean type | Paper source |
|---|---|---|
| `x` | `Channel` (= `String`) | §II-C ("x ranges over channel names") |
| `q` | `NetKAT` (dup-free) | §II-C ("N ∈ NetKAT⁻ᵈᵘᵖ") + Fig. 8 label grammar (same `q` in x?q/x!q) |

### `rcfg` as a *term constant* — Eq. (6), (4), A12–A15

`rcfg_{x,z}` is a *constant* (not a process constructor in Eq. 1). It appears:
- in Eq. (6) as `rcfg_{x,N};D_e`,
- in Eq. (4) as the axiom `(rcfg_{x,z};p) →_{rcfg(x,z)} p`,
- in A12 as `(x?z;p)|(x!z;q) ≡ rcfg_{x,z};(p||q)`.

This is **out of scope for `AST.lean`** (Eq. 1 only). It is deferred to
`Operators.lean`. Its argument types (by the same evidence) will be:
- `x : Channel`, `z : NetKAT` (dup-free). Recorded here for completeness;
  not designed in this task.

---

## 7. `Config.lean` — configurations `(d, H, H′)` per Figure 8

**Task scope:** Design ONLY `Config.lean` (the configuration structure). This
covers the `Config` type, the packet history lists `H` (pending) and `H′` (handled),
their cons-list ordering, and dependencies. Figure 8 operational semantics
(the `Step` relation) is **not** designed here — only the state carrier that the
rules operate over.

### 7.1 Paper source

- **Figure 8** (printed p. 9–10, §II-B): the labeled transition system
  `(d, H, H′) →γ (d′, H′′, H‴)` is the least relation closed under the SOS rules.
- The configuration triple `(d, H, H′)` is introduced in §II-B (p. 9):
  "We equip DyNetKAT policies with a configuration `(d, H, H′)` where `d` is the
  current process term, `H` is the list of packets awaiting processing, and `H′`
  is the list of packets that have been processed."
- Cons notation `σ :: H` (p. 9) confirms the lists are **ordered cons-lists**
  (not multisets or sets).

### 7.2 Configuration shape

```lean
structure Config where
  proc    : DyNetKAT        -- d    — current process term  (§II-B, p. 9)
  pending : List CtxPkt     -- H    — pending packet list   (§II-B, p. 9)
  handled : List CtxPkt     -- H′   — handled packet list   (§II-B, p. 9)
```

**Design decisions:**

1. **`proc : DyNetKAT`** — the single DyNetKAT process term governing all packets
   in both lists. Per-packet consistency (§II-B/§II-C, p. 8–9) means exactly one
   `d` drives every packet through its flight. No `flowTable` field (that is a
   journal-extension artifact, rejected in `DESIGN_ALARMS.md:A1`).

2. **`pending : List CtxPkt`** — the pending packet list `H`. The **head** of the
   list is the packet currently being processed. This matches Fig. 8's cons
   notation `σ :: H` where `σ` (the head) is the in-flight packet.

3. **`handled : List CtxPkt`** — the handled (output) packet list `H′`. The
   **head** of the list is the most recently handled packet. This matches
   Fig. 8 rules that cons outputs onto `H′` (e.g., `σ′ :: H′`).

4. **Packet type**: `CtxPkt` (defined as `Packet FieldName FieldValueEnum` in
   `NetKAT/Packet.lean:148`). This is the concrete 4-field fixture used by all
   existing modules (`Semantics`, `NormalForm`, etc.). The general parameterized
   type `Packet FieldType Value` exists in `Packet.lean` as well (definitional
   basis); `CtxPkt` is the alias used for consistency. *(Flag: parameterization
   is a future refactor; see §10 below.)*

### 7.3 Ordering of `H` and `H′` — derived from Figure 8 rules

The ordering (head = newest/current) is **not arbitrary** — it is forced by the
Figure 8 transition rules:

| Rule | H manipulation | H′ manipulation |
|---|---|---|
| `(cpol_;✓)` — packet flows through N | `σ :: H` → `H` (head consumed) | `H′` → `σ′ :: H′` (output consed to head) |
| `(cpol_;✗)` — packet dropped | `σ :: H` → `H` (head consumed) | `H′` unchanged (no output produced) |
| `(cpol_⊕)` — choice step | `H → H′′` propagated as-is | `H′ → H‴` propagated as-is |
| `(cpol_‖)` — parallel step | `H → H′′` propagated as-is | `H′ → H‴` propagated as-is |
| `(cpol_recv)` — receive | `H` unchanged | `H′` unchanged (no packet I/O) |
| `(cpol_send)` — send | `H` unchanged | `H′` unchanged (no packet I/O) |
| `(cpol_sync)` — synchronization | `H → H′′`, `H′ → H‴` propagated as-is | `H → H′′`, `H′ → H‴` propagated as-is |
| `(cpolX)` — recursion unfolding | Propagated as-is | Propagated as-is |

**Key observations:**

- **H (pending):** The head is always the *current* packet being processed by
  the `cpol_;✓` or `cpol_;✗` rule. The NetKAT policy `N` in `N;d` operates on
  `σ` (the head of `H`), transforming it to `σ′`. After processing, `σ` is
  removed (consumed) and `σ′` is pushed to `H′`. The list is a **work queue**
  in FIFO-ish order: head = next to process.

- **H′ (handled):** The head is always the *most recently produced* output packet.
  Each `cpol_;✓` step conses `σ′` onto the front of `H′`. The list is a **LIFO
  output stack**: head = most recent output.

- **No multiset semantics:** The cons-list ordering is confirmed by the
  notation `σ :: H` and `σ′ :: H′` in every rule conclusion. A multiset would
  be written `{σ, ...}` or similar; the paper consistently uses `::` (cons).

### 7.4 Dependencies on existing modules

| Dependency | File:lines | Kind |
|---|---|---|
| `CtxPkt := Packet FieldName FieldValueEnum` | `NetKAT/Packet.lean:148` | type (packet type for H and H′) |
| `Packet FieldName FieldValueEnum` | `NetKAT/Packet.lean:36-47` | generic packet model (field → value) |
| `FieldName` | `NetKAT/Packet.lean:117-122` | type (field names) |
| `FieldValueEnum` | `NetKAT/Packet.lean:132-138` | type (field values) |
| `Fintype FieldName` | `NetKAT/Packet.lean:125-130` | instance |
| `Fintype FieldValueEnum` | `NetKAT/Packet.lean:140-145` | instance |
| `Fintype CtxPkt` | `NetKAT/Packet.lean:158-161` | instance |
| `Packet.update` | `NetKAT/Packet.lean:43-47` | function (for Semantics proofs) |
| `Semantics N σ τ` | `NetKAT/Semantics.lean:61-71` | relation (consumed by `cpol_;✓`) |
| `holdsComplete` | `NetKAT/Packet.lean:204` | predicate (for complete tests) |
| `fieldEnum` | `NetKAT/AST.lean:124` | list (for finite enumeration) |

**Note on `DyNetKAT` dependency:** `Config.lean` depends on the `DyNetKAT` type
defined in `AST.lean` (the `proc` field). This is the only forward dependency
within the `DyNetKAT/` subdirectory — `Config.lean` imports `AST.lean` (for the
`DyNetKAT` type) and `NetKAT/Packet.lean` (for `CtxPkt`).

### 7.5 Module structure

```
lean/DyNetKAT/DyNetKAT/
├── AST.lean         -- Eq. (1) inductive DyNetKAT + Channel + Var types  (imported by Config)
├── Config.lean      -- THIS DESIGN: structure Config (d, H, H′)           (NEW)
├── Action.lean      -- labels γ (packet, recv, send, rcfg)                (deferred)
├── Semantics.lean   -- labeled SOS Step (Fig. 8)                          (deferred)
└── Operators.lean   -- extended syntax (δ, π, rcfg const, ⌊⌊, | |)       (deferred)
```

`Config.lean` will contain **only** the `Config` structure definition (§7.2 above),
plus any basic lemmas about the structure (e.g., projection lemmas for `proc`,
`pending`, `handled` fields). The `Step` relation (Fig. 8 rules) lives in
`Semantics.lean` and depends on this `Config` structure.

### 7.6 Ambiguities flagged (do not invent)

1. **List vs. multiset for H/H′:** Resolved — cons notation `σ :: H` in all
   Fig. 8 rules confirms ordered lists. `List CtxPkt` with head = current/newest.

2. **Empty lists:** When `H` is empty (`[]`), no packet is available for the
   `cpol_;✓`/`cpol_;✗` rules to fire. This is a well-defined empty-list state;
   the rules simply do not apply (guarded by `match` on non-empty). No special
   "empty" marker needed.

3. **`CtxPkt` vs. parameterized `Packet F V`:** `Config.lean` uses `CtxPkt`
   (the concrete 4-field fixture, `Packet FieldName FieldValueEnum`) for all
   packet lists, matching every existing module. The paper's packet is
   parameterized; parameterization is a future refactor (see §10).

### 7.7 Design decisions summary

1. `structure Config` with fields `proc : DyNetKAT`, `pending : List CtxPkt`,
   `handled : List CtxPkt` — faithful to the paper's `(d, H, H′)` triple (p. 9).
2. `pending` head = current packet to process; `handled` head = most recent output.
3. Both lists are ordered cons-lists (`List`), not multisets or sets — confirmed
   by `::` notation throughout Fig. 8.
4. No `flowTable` field — per-packet consistency uses a single `d` per config
   (§II-B/§II-C design rationale, not a mutable table).
5. `CtxPkt` is the packet type — consistent with all existing NetKAT modules.

---

## 8. `rcfg` and the extended operators (out of scope for Eq. 1)

Eq. (6) (p. 14, §III-A) extends the base syntax with:

```
D_e ::= … | rcfg_{x,N};D_e | δ_ℒ(D_e) | π_n(D_e) | D_e⌊⌊D_e | D_e|D_e
```

These are **not** in Eq. (1). Their treatment is recorded for the planned
`Operators.lean` module, so the `rcfg` placement decision above is not
misread as a missing constructor:

| Extended operator | Paper eq./fig. | Planned module | Argument types |
|---|---|---|---|
| `rcfg_{x,N};D` | Eq. (4), Eq. (6), A12 | `Operators.lean` | `x:Channel, N:NetKAT` |
| `δ_ℒ(D)` | Eq. (2), (δ⊥)(δ;)(δ;) | `Operators.lean` | `ℒ : Set {recv,send}` actions; `D:DyNetKAT` |
| `π_n(D)` | Eq. (3), (Π0)(Π⊥)(Π;)(Π⊕) | `Operators.lean` | `n:ℕ; D:DyNetKAT` |
| `D⌊⌊D` (left-merge) | Eq. (5), (T) | `Operators.lean` | `DyNetKAT → DyNetKAT → DyNetKAT` |
| `D|D` (comm-merge) | Eq. (5), (\|?! )(\|!?) | `Operators.lean` | `DyNetKAT → DyNetKAT → DyNetKAT` |

`δ_ℒ` restricts on actions of shape `x?N`, `x!N` only (§III: "ℒ … ranging
over elements of shape `x?N` and `x!N`"). `π_n` is defined on `ℕ` with the
recursive equations (Π0)–(Π⊕). These are **axioms + Step rules**, not base
syntax, so they need no `DyNetKAT` constructor — they can be defined as
functions/relations over the Eq. (1) type. **Do not invent** extra base
constructors for them in `AST.lean`.

---

## 9. Dependencies on existing NetKAT modules

`AST.lean` depends on the existing NetKAT modules (all machine-checked, build
passes per `HANDOFF.md` checkpoints):

| Dependency | File:lines | Kind |
|---|---|---|
| `NetKAT` inductive | `NetKAT/AST.lean:89-97` | type |
| `Predicate` inductive | `NetKAT/AST.lean:37-44` | type (reused via `NetKAT.test`) |
| `CompleteTest := CtxPkt` | `NetKAT/Packet.lean:193` | type alias |
| `CompleteAssignmentValuation := CtxPkt` | `NetKAT/Packet.lean:253` | type alias |
| `holdsComplete` | `NetKAT/Packet.lean:204` | pred (used in semantics proofs later) |
| `CtxPkt := Packet FieldName FieldValueEnum` | `NetKAT/Packet.lean:148` | type |
| `FieldName`, `FieldValueEnum` | `NetKAT/Packet.lean:117-145` | types (via `CtxPkt`) |
| `Fintype CtxPkt` etc. | `NetKAT/Packet.lean:158,198,258` | instances (for later finite-domain proofs) |
| `Semantics` | `NetKAT/Semantics.lean:61` | relation (for `cpol_;✓` soundness, future) |
| `fieldEnum` | `NetKAT/AST.lean:124` | computable list (for later star-bound / star termination) |
| `StarClosure` | `NetKAT/Semantics.lean:51` | inductive (for later star semantics) |

**No new NetKAT dependencies are introduced by this design.** The `NetKAT`
argument in `nSeq`/`recv`/`send` (and the `rcfg` label) reuses the existing
type verbatim. `Channel := String` and `Var := String` are standalone
(Lean 4 core `String`), with no dependency on NetKAT modules.

---

## 10. Ambiguities flagged (do not invent)

1. **rcfg in Eq. (1):** Not present. Only in extended syntax (Eq. 6) and
   as an action label (Fig. 8). Resolved by placing `rcfg` label in
   `Action.lean`, not base `DyNetKAT` AST. See §5.
2. **rcfg(x,r) label arg type:** Is `r` the same `q` (NetKAT⁻ᵈᵘᵖ) as in
   `x?N`/`x!N`?    Resolved by §II-C (explicit: N ∈ NetKAT⁻ᵈᵘᵖ) + Fig. 8 label
   grammar (same `q`). Confirmed, not invented. See §5–6.
3. **H/H′ list vs multiset:** `PAPER_CONFORMANCE.md` §5 (Config) recommends
   `List Packet` with cons notation. Resolved in `Config.lean` design (§7 above):
   `pending, handled : List CtxPkt`, head = current/newest, confirmed by `::`
   notation throughout Figure 8.
4. **Trailing `;⊥` shorthand:** Paper §II-C says trailing `;⊥` is omitted
   "whenever clear from context." Resolved: it is a notation convention; the
   `nSeq` constructor carries an explicit continuation; bare `N` = `nSeq N deadlock`.
5. **Var uniqueness (X ≜ d):** A well-formedness property of `RecEnv`, not the
   `var` constructor. Must be enforced at the environment layer. See §4.
6. **Packet parameter vs. concrete:** `CtxPkt` is the concrete 4-field fixture;
   the paper's packet is parameterized. The design uses `CtxPkt` for consistency
   with the implemented `Semantics`. Flagged as a future-parameterization
   refactor, not invented here.

---

## 11. Design decisions summary (non-invented)

1. `Channel := String` (countably infinite; matches §II-C and JSON schema).
2. `Var := String` (named; matches JSON `recursive_variables`).
3. `NetKAT` args to `recv`/`send`/`rcfg` reuse the existing dup-free `NetKAT`
   type (per §II-C; the ar5iv garbled symbol is resolved by paper evidence,
   not by guessing).
4. `rcfg` is an `Action` label variant (Fig. 8), **not** a `DyNetKAT` term
   constructor. The `rcfg_{x,z}` constant (Eq. 6) goes in `Operators.lean`.
5. Base AST covers **Eq. (1) only**; extended operators (δ, π_n, ⌊⌊, | |,
   rcfg const) are a separate `Operators.lean` module per `ARCHITECTURE.md`.
6. Unique defining equation `X ≜ d` and guardedness (Definition 7) are
   well-formedness properties of `RecEnv`, **not** encoded in the `var` ctor.
7. `⊥` trailing `;⊥` is a notation shorthand mapped to `nSeq N deadlock`.

---

## 12. Dependencies on existing NetKAT modules (consolidated)

See §8 for the full table. Key point: `AST.lean` reuses the existing `NetKAT`
type (8 constructors, `NetKAT/AST.lean:89`) as the `N` in all `N;D`, `x?N;D`,
`x!N;D` constructors. The `Predicate`, `CompleteTest`, and
`CompleteAssignmentValuation` types are already available and are referenced
**indirectly** (a `NetKAT` policy may contain `.test Pr`, `.completeTest α`,
`.assign1`-based complete assignments), but the `DyNetKAT` AST itself only
depends on the *type* `NetKAT`, not its internal constructors.

---

## 13. Next steps (deferred — implementation tasks, not this task)

1. Create `lean/DyNetKAT/DyNetKAT/` directory and the five-module split:
   `AST.lean`, `Config.lean`, `Action.lean`, `Semantics.lean`, `Operators.lean`.
2. Add `lean/DyNetKAT/DyNetKAT/AST.lean` with the `DyNetKAT` inductive above.
3. Add `Config.lean` per §7 above (`structure Config := proc pending handled`
   with `pending, handled : List CtxPkt`, ordering: head = current/newest).
4. Add `Action.lean` with `inductive Action` (incl. `rcfg` label, §14).
5. Add `Semantics.lean` with `Step : Config → Action → Config → Prop` (Fig. 8).
6. Add `Operators.lean` with δ, π_n, rcfg const, ⌊⌊, | | (Eq. 6).

---

## 14. `Action.lean` — action labels (Figure 8)

**Task scope:** Design ONLY `Action.lean` - the labeled transition labels `gamma`
from Figure 8 (printed p. 9-10, section II-B). This specifies the `Action`
inductive type: its constructors, the exact Lean type of every argument, the
paper-evidence justification for each, explicit dependencies on existing
modules, and the **distinction from process syntax** (the `DyNetKAT` inductive
in `AST.lean`, section 2). Figure 8's `Step` relation itself is **not** designed
here - only the label type that the `Step` relation is indexed by.

> Note: section 6 above first introduced the `Action` type as a summary (lines 303-311).
> That summary is the source of truth for the four constructor shapes; section 14
> below is the detailed, evidence-backed design of the same type, adding exact
> argument types, the action-label-vs-process-syntax distinction (14.2), the
> relationship to `Step` (14.4), module dependencies (14.5), decidability
> (14.6), and ambiguity flags (14.7).

---

### 14.1 Paper source

- **Figure 8** (printed p. 9-10, section II-B): the labeled transition system
  `(d, H, H') goes-to (d', H'', H''')` is the least relation closed under the SOS rules.
- **Label grammar (the single line at the foot of Fig. 8):**
  gamma ::= (sigma, sigma') | x!q | x?q | rcfg(x, q)
- **section III-A, p. 14, Definition 6** ("DyNetKAT Normal Forms"): normal forms
  contain communication steps c_j ::= x?q | x!q | rcfg(x, q) - the same q symbol,
  confirming q is a single class of argument shared with the label grammar.
- **section III-A "Soundness" (p. 14-15, Lemma 10/11 setup):** the bisimulation
  clause restates the grammar with r in place of q:
  "... with gamma ::= (sigma, sigma') | x?r | x!r | rcfg(x, r)". The symbol-name
  variance (q vs. r) is purely notational.
- **Axioms A12-A15 (p. 13):** z, y in NetKAT-dupfree; the communication in A12 is
  (x?z;p)|(x!z;q) = rcfg_{x,z};(p||q), where the term constant rcfg_{x,z} is
  paired with the label rcfg(x,z) and z in NetKAT-dupfree.
- **Axiom (A10) / prefix set "at" (p. 14):** at ::= alpha*pi | x?z | x!z | rcfg_{x,z}
  - the communication members reuse the same NetKAT-dupfree argument.

**Key prose (printed p. 9, section II-B):**

> "The rule labels gamma range over pairs of packets (sigma, sigma') or
> communication/reconfiguration-like actions of shape x!q, x?q
> or rcfg(x, q), depending on the context."

So there are exactly four label shapes in Figure 8 - no more, no less.
There is no label for D||D, D+_D, X, or bottom; those are process-syntax
constructors whose transitions are re-labeled by the child rules (e.g.
(cpol_+), (cpol_||), (cpolX) are labeled by the child's gamma, inherited).

---

### 14.2 Distinction: action labels vs. process syntax

This is the central discipline for `Action.lean` and the most frequently
mis-modeled point:

- **Process syntax** (`AST.lean`, section 2, Eq. 1): the `DyNetKAT` inductive
  with 7 constructors (bottom, N;D, x?N;D, x!N;D, D||D, D+_D, X). It has
  **no** `rcfg` constructor (Eq. 1 has none). It also has **no** action labels;
  it is a term language.
- **Action labels** (`Action.lean`, Fig. 8): the *range of the label* gamma,
  i.e. what appears on the transition arrow. `rcfg(x, q)` appears **here**, as a
  label, even though it is *not* a term constructor of `DyNetKAT`.
- **Extended term constant** (`Operators.lean`, Eq. 6 / A12): `rcfg_{x,z};D` is
  a *prefix* of the extended term language `D_e`. It is a 3-ary term
  (`Channel -> NetKAT -> DyNetKAT -> DyNetKAT`), stepped by the `(rcfg_x,z)` rule
  (Eq. 4) emitting the *label* `rcfg(x,z)`.

Conflating the first two (or the label with the constant) is exactly the
ambiguity section 5 resolves. The table makes the three roles disjoint:

| `rcfg` occurrence | Module | Role | Arity |
|---|---|---|---|
| `rcfg(x, q)` | `Action.lean` | label on the transition (synchronization output) | `Channel -> NetKAT -> Action` |
| `x?N;D`, `x!N;D` (and `N;D`) | `AST.lean` | process-syntax prefix (Eq. 1) | `Channel -> NetKAT -> DyNetKAT -> DyNetKAT` |
| `rcfg_{x,z};D` | `Operators.lean` | extended term-constant prefix (Eq. 6) | `Channel -> NetKAT -> DyNetKAT -> DyNetKAT` |

`Action.lean` carries **only** the label variant (first row).

---

### 14.3 The `Action` inductive (constructors + argument types)

```lean
/-- Action labels gamma of Figure 8 (printed p. 9-10, II-B / III-A).
    gamma ::= (sigma, sigma') | x!q | x?q | rcfg(x, q)
    These index the labeled transition relation (d, H, H') -> (d', H'', H''');
    they are NOT process syntax -- see DyNetKAT.AST.DyNetKAT (Eq. 1) for the
    term language and Operators.lean for the extended rcfg_{x,z} constant. -/
inductive Action
  | packet : CtxPkt → CtxPkt → Action   -- gamma = (sigma, sigma')  packet flow via NetKAT
  | recv   : Channel → NetKAT → Action   -- gamma = x?q  asynchronous receive
  | send   : Channel → NetKAT → Action   -- gamma = x!q  asynchronous send
  | rcfg   : Channel → NetKAT → Action   -- gamma = rcfg(x, q)  synchronization / reconfig
```

Constructor table (four constructors, matching the grammar verbatim - none
omitted, none added):

| # | Constructor | Lean signature | Paper label | Argument-type evidence |
|---|---|---|---|---|
| 1 | `packet` | `CtxPkt -> CtxPkt -> Action` | `(sigma, sigma')` | p. 9 II-B: "pairs of packets"; `(cpol_;v)` rule (p. 10): `sigma' in [[p]](sigma::h)`, cons `sigma' :: H'`, consume `sigma :: H` |
| 2 | `recv` | `Channel -> NetKAT -> Action` | `x?q` | p. 8 II-A: `x?N` with `N in NetKAT-dupfree`; Fig. 8 `q` = same symbol family as II-A `N` |
| 3 | `send` | `Channel -> NetKAT -> Action` | `x!q` | p. 8 II-A: `x!N` with `N in NetKAT-dupfree` |
| 4 | `rcfg` | `Channel -> NetKAT -> Action` | `rcfg(x, q)` | p. 9 II-B prose + label grammar; p. 14 Def. 6 (same q); p. 13-14 A12-A15 (z in NetKAT-dupfree) |

#### Argument 1 of `recv`/`send`/`rcfg` - `Channel`

- Type: `Channel := String` (countably infinite), as fixed in section 3.
- Justification: section II-A ("x ranges over channel names"); the same `x` appears
  in `x?N`/`x!N` (Eq. 1) and in `rcfg(x, q)` (Fig. 8).
- Section 5 commits `Channel := String` with no `Fintype` and `DecidableEq`
  (Lean 4 core). `Action.lean` reuses `Channel` from `AST.lean` - it is
  defined/imported there, not redefined here (see 14.5).

#### Argument 2 of `recv`/`send`/`rcfg` - `NetKAT` (the dup-free fragment)

This is the single non-obvious type decision and is resolved by paper evidence,
not invention:

- section II-A (p. 8): "x?N and x!N ... N in NetKAT-dupfree." Explicitly dup-free.
- Fig. 8 label grammar uses `q` - the **same** symbol as in `x?q`/`x!q`, which
  section II-A pins to `NetKAT-dupfree`. The bisimulation clause (p. 14) restates
  the grammar with `r` in place of `q`, the obvious notational variant.
- Axioms A12-A15 (p. 13): `z, y in NetKAT-dupfree`; A12 communication pairs a
  label `rcfg(x,z)` with `z in NetKAT-dupfree`.
- Def. 6 (p. 14): `c_j ::= x?q | x!q | rcfgx,q with q denoting terms in
  NetKAT-dupfree`.

**Decision:** the second argument of `recv`/`send`/`rcfg` is the existing `NetKAT`
type (the dup-free fragment) from `NetKAT/AST.lean:89`. **No** separate "full
NetKAT" type is introduced. This is consistent with section 5's resolution and
with section 2's `recv`/`send` constructors (which also take `NetKAT`).

**Ambiguity flagged (not invented here):** the ar5iv text extraction is garbled
about whether the label's communication argument uses the same symbol as
section II-A's `N`. The paper's own restatements - Def. 6 (p. 14), the
bisimulation clause (p. 14), and the axiom text A12-A15 (p. 13) - all pin it
to `NetKAT-dupfree`. The symbol-name variance (q/r/z) is purely notational and
carries no semantic distinction. No definition is invented to paper over this;
the type is fixed by the three independent citations above.

#### Argument types of `packet` - `CtxPkt`

- Both arguments are `CtxPkt := Packet FieldName FieldValueEnum`
  (`NetKAT/Packet.lean:148`).
- Evidence: p. 9 section II-B "pairs of packets (sigma, sigma')" and
  `(cpol_;v)` (p. 10): the rule conses `sigma'` onto `H'` and consumes
  `sigma :: H`, i.e. both sigma and sigma' are packets. `[[p]]` (NetKAT
  `Semantics`, `NetKAT/Semantics.lean:61`) is over `CtxPkt`, and the
  `(cpol_;v)` premise `sigma' in [[p]](sigma::h)` therefore ranges over
  `CtxPkt`.
- `CtxPkt` is the concrete 4-field fixture already used by every NetKAT
  module. The paper's packet is the parameterized `Packet FieldType Value`
  (Def. 1, p. 5); **flag** (14.7) the parameterization as a future refactor,
  not invented here.

---

### 14.4 Relationship to `Step` (Figure 8) - what `Action` does NOT carry

`Action.lean` defines **only** the label type. It does **not** define the
transition relation `Step : Config -> Action -> Config -> Prop`. That lives in
`Semantics.lean` (section 13, deferred). The label grammar is the *range*;
`Step` is the *relation indexed by* that range. Mapping each label to its
emitting rule in Figure 8:

- `Action.packet sigma sigma'` - label emitted by `(cpol_;v)` when
  `sigma' in [[p]](sigma)` (the `p; q` prefix). A *dropped* packet (the
  `(cpol_;v)` rule applied to `[[p]](sigma) = empty`) is handled in
  `Config`/rule-guard logic in `Semantics.lean`, **not** by inventing a
  separate `.drop` label - the paper emits no label for the deadlocked
  (empty-output) branch; the `Step` relation simply has no `(packet ...)`
  witness for that branch. **Flag (14.7):** whether the drop branch should
  carry a distinct label is an open `Semantics.lean` question, not an
  `Action.lean` decision.
- `Action.recv x q` / `Action.send x q` - labels of `(cpol_recv)` /
  `(cpol_send)` (section II-B labels `x?q` / `x!q`). They are also the
  *trigger* for synchronization: paired with a matching `send`/`recv` on the
  same channel+policy, the synchronization rules `(cpol_?! )` / `(cpol?!)` emit
  `Action.rcfg x q`.
- `Action.rcfg x q` - the *output* label of the synchronization rules
  `(cpol_?! )` / `(cpol?!)` and of the axiom-pinpointing constant
  `(rcfg_x,z)` (Eq. 4).

So `rcfg` as a *label* is **produced by** synchronization; `rcfg_{x,z}` as a
*term* (Eq. 6) steps via `(rcfg_x,z)` emitting the label `rcfg(x,z)`. Both
share the `(Channel, NetKAT)` argument shape and are resolved to the same
`Channel`/`NetKAT` types - but they live in different modules and have
different arities (label = 2 args; term constant = 3 args incl. `DyNetKAT`).

---

### 14.5 Module dependencies for `Action.lean`

`Action.lean` imports (and only imports) the modules that define its argument
types - a strict subset, so that `Action.lean` compiles independently of the
yet-unimplemented `Config.lean`/`Semantics.lean`:

| Imported symbol | File:lines | Kind |
|---|---|---|
| `Action` itself | `Action.lean` (new) | - |
| `Channel` (`abbrev Channel := String`) | `AST.lean` (section 3 owns it) | type alias; `DecidableEq` from `String` |
| `CtxPkt := Packet FieldName FieldValueEnum` | `NetKAT/Packet.lean:148` | concrete packet type |
| `NetKAT` (dup-free) | `NetKAT/AST.lean:89-97` (8 constructors) | term type |
| `Packet` (parameterized model) | `NetKAT/Packet.lean:36` | generic basis of `CtxPkt` |
| `FieldName` | `NetKAT/Packet.lean:117-145` | via `CtxPkt` |
| `FieldValueEnum` | `NetKAT/Packet.lean:132-145` | via `CtxPkt` |

**What `Action.lean` itself depends on (the type only):**
`AST.lean` (for `Channel`) + `NetKAT/Packet.lean` (for `CtxPkt`) +
`NetKAT/AST.lean` (for `NetKAT`). It does **not** depend on
`NetKAT/Semantics.lean` or `Config.lean` - those are consumed by the *rules*
in `Semantics.lean` (the `(cpol_;v)` premise, the `H`/`H'` lists), not by the
label type.

**Note on `Channel` ownership (why `Action.lean` imports `AST.lean`):**
Section 3 and 4 fix `Channel` and `Var` as `abbrev`s. Their canonical home is
`AST.lean` (alongside `DyNetKAT`), because both `Action.lean` and `AST.lean`
(and eventually `Semantics.lean`) need `Channel`, and there is no
lower-dependency module than `AST.lean` that can own them. `Action.lean`
therefore imports `AST.lean`. This is recorded here because the task is
`Action.lean`-specific: `Channel` is owned by `AST.lean`, not redefined.

### 14.6 Decidability / instances

- `String` (hence `Channel` and `Var`) has `DecidableEq` in Lean 4 core -
  channel/var equality is decidable without extra work.
- `NetKAT` is an inductive without a derived `DecidableEq` in the current
  `AST.lean` (`inductive NetKAT` at `NetKAT/AST.lean:89` has no
  `deriving DecidableEq`). For `Action` equality (needed by `delta_L` action-set
  membership in `Operators.lean`) the label type should derive
  `Repr`/`DecidableEq` once the `NetKAT` argument does, or `Action` equality is
  deferred until `NetKAT` derives it. **Flag (14.7):** do not assume
  `DecidableEq Action` is available without `deriving` on `NetKAT`; no
  instance is synthesized here.
- `CtxPkt` has `[Fintype CtxPkt]` (`NetKAT/Packet.lean:158-161`), so the
  `(sigma, sigma')` packet-flow labels live over a finite domain - relevant to
  branching finiteness (Lemma 8) downstream, not to `Action.lean` itself.

---

### 14.7 Ambiguities flagged (do not invent) - continued from section 10

1. **rcfg in three syntactic roles.** Resolved (not invented): the *label*
   `rcfg(x, q)` is in `Action.lean`; the *term constant* `rcfg_{x,z};D` is in
   `Operators.lean`; the process prefixes `x?N;D`/`x!N;D` are in `AST.lean`.
   §14.2 makes the roles disjoint. No single constructor plays more than one
   role.

2. **Symbol-name variance (q vs r vs z) for the communication argument.**
   §II-A uses `N`; Fig. 8 uses `q`; Def. 6 and the bisimulation clause use `r`;
   A12-A15 use `z`. Three independent paper citations pin all of these to
   `NetKAT-dupfree` (§14.3 Argument 2). The variance is notational only; no
   type is invented to reconcile the names.

3. **`packet` label's packet type: `CtxPkt` vs parameterized `Packet F V`.**
   The paper uses the parameterized `Packet FieldType Value` (Def. 1, p. 5).
   The design uses the concrete `CtxPkt = Packet FieldName FieldValueEnum`
   for consistency with all existing modules. **Flag:** parameterizing
   `Action.packet` over an abstract packet type would require parameterizing
   `Config` and `Step` together (they share the packet type). That is a
   future refactor of all three modules, **not** done here. No partial
   parameterization is invented for `Action.lean` alone.

4. **No `DecidableEq Action` synthesized.** `NetKAT` does not currently
   `deriving DecidableEq`. `Action` equality is therefore **not** assumed
   available in `Action.lean`. Downstream `delta_L : Set Action`
   (Operators.lean) must be defined set-theoretically. Resolving this (adding
   `deriving DecidableEq` to `NetKAT` + `Action`) is deferred to implementation,
   not invented here.

5. **Empty packet list `H = []`.** Out of scope for `Action.lean` (it is a
   `Config`/rule-guard issue in `Semantics.lean`): when `H` is empty, the
   `(cpol_;v)`/`(cpol_;x)` rules are not enabled. `Action.packet` is still a
   well-defined constructor; it is simply *unemitted* by those rules in the
   empty-list state. No special "empty" label is invented.

6. **Drop branch label.** Whether the empty-output `(cpol_;x)` branch should
   carry a distinct label (e.g. a `.drop` constructor) is **not** decided here.
   The paper emits no label for it in the rule text; the `Step` relation has no
   `(packet ...)` witness for that branch. `Action.lean` therefore has **no**
   `.drop` constructor. If a later `Semantics.lean` design needs one, that is a
   separate (explicitly-flagged) addition to `Action`, not an invention now.

7. **Action-label arity vs term-constant arity (rcfg).** The label
   `rcfg(x, q)` has arity `(Channel, NetKAT)`; the term constant `rcfg_{x,z};D`
   has arity `(Channel, NetKAT, DyNetKAT)`. Both are resolved to the same
   `Channel`/`NetKAT` types, but they are **distinct types** (`Action` vs
   `DyNetKAT`) with distinct arities. No unification is invented.

---

### 14.8 Summary (design decisions, non-invented)

1. `Action` is an inductive with **exactly four** constructors - `packet`,
   `recv`, `send`, `rcfg` - matching the foot-of-Fig.8 label grammar
   `gamma ::= (sigma, sigma') | x!q | x?q | rcfg(x, q)` verbatim (none omitted,
   none added).
2. `Action.packet : CtxPkt -> CtxPkt -> Action` - both args are the concrete
   `CtxPkt` (`NetKAT/Packet.lean:148`); paper p. 9 II-B + `(cpol_;v)` rule.
3. `Action.recv`/`send`/`rcfg : Channel -> NetKAT -> Action` - channel is
   `Channel := String` (section 3); policy is the existing dup-free `NetKAT`
   (`NetKAT/AST.lean:89`); paper II-A + Def. 6 + A12-A15. No "full NetKAT" type.
4. `Action.lean` defines the **label type only**; the `Step` relation that
   *uses* it lives in `Semantics.lean` (deferred, §13).
5. `Action` is distinct from process syntax (`AST.lean`) and from the extended
   `rcfg_{x,z};D` constant (`Operators.lean`); the *label* `rcfg(x, q)` is the
   only `rcfg` in this module.
6. Imports: `AST.lean` (Channel), `NetKAT/Packet.lean` (CtxPkt),
   `NetKAT/AST.lean` (NetKAT). No dependency on `NetKAT/Semantics.lean` or
   `Config.lean`.
7. No `sorry`/`axiom`/invented semantics: every constructor and argument type
   is cited to the paper (§4.4 of `AGENTS.md`: "do not invent semantics").

---

*End of design document. This is a design artifact only; no Lean files were
created or modified. See HANDOFF.md for the Phase 2 kickoff status.
