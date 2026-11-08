# SOS and Bisimulation Audit

This report compares the paper’s Figure 8 and Definition 2 with all relevant Lean sources, including untracked files. Source excerpts below are verbatim, taken from the current source. Line numbers are included for navigation and are not part of the Lean declarations.

## Figure 8 correspondence

The paper’s configurations are `(d,H,H')`: current process, pending packets, and successfully handled packets. Lean uses a structure with the same three fields. Its `Step` relation is parameterized by `RecEnv`.

Verbatim declarations from `DyNetKAT/DyNetKAT/Config.lean:11-15`:

```lean
structure Config where
  proc : DyNetKAT
  pending : List CtxPkt
  handled : List CtxPkt
```

Verbatim action constructors from `DyNetKAT/DyNetKAT/Action.lean:9-14`:

```lean
inductive Action : Type
  | packet : CtxPkt → CtxPkt → Action
  | recv : Channel → NetKAT → Action
  | send : Channel → NetKAT → Action
  | rcfg : Channel → NetKAT → Action
```

The rule inventory from `DyNetKAT/DyNetKAT/Semantics.lean` is:

| Constructor | Paper role | Lean lines | Audit |
|---|---|---:|---|
| `cpol_seq_ok` | `(cpol_;check)` | 14–24 | Premise invokes the NetKAT relational semantics. Input pending head is removed; output prepends to handled. |
| `cpol_choice_l`, `cpol_choice_r` | Choice propagation | 26–48 | Each branch propagates an arbitrary action and destination histories. |
| `cpol_par_l`, `cpol_par_r` | Parallel interleaving | 50–72 | Steps either component while retaining the other. |
| `cpol_left_merge` | Left-merge | 74–85 | A left step transitions to parallel composition of the residual and right operand. |
| `cpol_comm_merge_recv_send`, `cpol_comm_merge_send_recv` | Communication-merge | 87–121 | Matches a receive/send pair and emits one `rcfg` action. |
| `cpol_recv`, `cpol_send`, `cpol_rcfg` | Prefix actions | 123–154 | Prefix performs one action then continues without changing histories. |
| `cpol_var` | `(cpolX)` | 156–167 | Unfolds a named variable through an explicit environment lookup. |
| `cpol_sync_recv_send`, `cpol_sync_send_recv` | Parallel synchronization | 169–203 | Synchronizes complementary actions within `parallel`, producing residual parallel composition. |
| `cpol_project` | Projection | 205–218 | Positive depth decrements on each transition. |
| `cpol_restrict` | Restriction | 220–237 | Packet and `rcfg` actions always pass; communication actions must not belong to the restricted set. |

The communication-merge rules and the parallel synchronization rules are distinct. Both pair send/receive actions but have different source process constructors (`commMerge` versus `parallel`).

Figure 8 itself contains the packet-processing, variable-unfolding, two choice, two parallel-interleaving, receive, send, and two parallel-synchronization rules. `cpol_left_merge`, the two `cpol_comm_merge_*` constructors, `cpol_project`, and `cpol_restrict` correspond to the extended semantics introduced later in the paper (equations (2)-(5)), not Figure 8. Thus the `Step` inductive combines the Figure 8 core and extended rules in one relation.

## Exact SOS excerpts

Base packet-processing constructor (`Semantics.lean:13-24`):

```lean
inductive Step (env : RecEnv) : Config → Action → Config → Prop
  | cpol_seq_ok
      (p : DyNetKAT.NetKAT.NetKAT) (q : DyNetKAT)
      (sigma sigma' : CtxPkt)
      (pendingTail handled : List CtxPkt)
      (evaluates : DyNetKAT.NetKAT.Semantics p sigma sigma') :
      Step env
        (show Config from
          { proc := .nSeq p q, pending := sigma :: pendingTail, handled := handled })
        (show Action from Action.packet sigma sigma')
         (show Config from
           { proc := q, pending := pendingTail, handled := sigma' :: handled })
```

Variable constructor (`Semantics.lean:156-167`):

```lean
  | cpol_var
      (name : Var) (body body' : DyNetKAT) (action : Action)
      (pending pending' handled handled' : List CtxPkt)
      (definition : env.lookup name = some body)
      (step : Step env
        (show Config from { proc := body, pending := pending, handled := handled })
        action
        (show Config from { proc := body', pending := pending', handled := handled' })) :
      Step env
        (show Config from { proc := .var name, pending := pending, handled := handled })
        action
        (show Config from { proc := body', pending := pending', handled := handled' })
```

Restriction constructor (`Semantics.lean:220-237`):

```lean
  | cpol_restrict
      (actions : Set CommunicationAction)
      (p p' : DyNetKAT) (action : Action)
      (pending pending' handled handled' : List CtxPkt)
      (allowed : match action with
        | .packet _ _ => True
        | .recv x r => CommunicationAction.recv x r ∉ actions
        | .send x r => CommunicationAction.send x r ∉ actions
        | .rcfg _ _ => True)
      (step : Step env
        (show Config from { proc := p, pending := pending, handled := handled })
        action
        (show Config from { proc := p', pending := pending', handled := handled' })) :
      Step env
        (show Config from { proc := .restrict actions p, pending := pending, handled := handled })
        action
        (show Config from
          { proc := .restrict actions p', pending := pending', handled := handled' })
```

## Definition 2 comparison

Paper Definition 2 defines a symmetric relation over policies and requires matching the same label and resulting histories, with related residual policies. Lean’s `IsBisimulation` expresses this for a fixed environment and explicitly includes both the symmetry clause and transition matching.

Verbatim declarations from `Bisimulation.lean:9-27`:

```lean
def IsBisimulation (env : RecEnv) (R : DyNetKAT → DyNetKAT → Prop) : Prop :=
  (∀ p q, R p q → R q p) ∧
  ∀ p q, R p q →
    ∀ (pending handled : List CtxPkt) (action : Action)
      (p' : DyNetKAT) (pending' handled' : List CtxPkt),
      Step env
        (show Config from { proc := p, pending := pending, handled := handled })
        action
        (show Config from { proc := p', pending := pending', handled := handled' }) →
      ∃ q',
        Step env
          (show Config from { proc := q, pending := pending, handled := handled })
          action
          (show Config from { proc := q', pending := pending', handled := handled' }) ∧
        R p' q'

/-- Two processes are bisimilar when some bisimulation relates them. -/
def Bisimilar (env : RecEnv) (p q : DyNetKAT) : Prop :=
  ∃ R, IsBisimulation env R ∧ R p q
```

The definition is operationally close to the paper. Differences worth stating aloud: Lean fixes an environment for every comparison; the paper notation suppresses recursive-definition context. Lean defines bisimilarity by existence of a bisimulation but does not separately define a “largest” relation object. Symmetry plus one-direction matching gives the other direction.

Theorems `Bisimilar.refl`, `.symm`, and `.trans` are proved at `Bisimulation.lean:29-66`. Congruence is represented by individual theorems: choice lines 68 and 109; parallel lines 150 and 214; left merge 278 and 314; communication merge 345 and 393; prefixes 441, 472, 503, 534; restriction 565; projection 617. There is no top-level theorem named “bisimilarity is a congruence,” and there is no derivation relation for the paper’s equational axiom system.

## Recursion environment: mathematical justification

Lean’s `Var` is a name, not a recursive tree containing its own definition. `RecEnv` supplies the interpretation separately:

Verbatim `RecEnv.lean:9-19`:

```lean
abbrev RecEnv : Type := Var → Option DyNetKAT

/-- Look up the defining body for a recursive variable. -/
def RecEnv.lookup (env : RecEnv) (name : Var) : Option DyNetKAT := env name

/-- The environment with no recursive definitions. -/
def RecEnv.empty : RecEnv := fun _ => none

/-- Add the unique definition for `name`, replacing any previous entry. -/
def RecEnv.define (env : RecEnv) (name : Var) (body : DyNetKAT) : RecEnv :=
  fun candidate => if candidate = name then some body else env candidate
```

This avoids encoding potentially cyclic recursive equations as an inductive syntax tree. Lookup is total and optional, so malformed or partial environments can be represented rather than ruled out by the type. The variable SOS rule permits a transition only when the lookup succeeds and the body can make the same step. Thus environment-relative bisimilarity compares processes under one shared interpretation of every free recursion name. This is semantically necessary: the same syntax `.var "X"` can have different transitions under environments mapping `X` to different bodies.

The environment parameter is not an assertion that the paper requires partial recursive specifications. It is an explicit Lean modeling choice that makes the rule total at the type level while representing undefined variables as having no `cpol_var` derivation. `WellFormed` adds definedness and guarded-body obligations separately; it is not an invariant enforced by `RecEnv` or by `Step`.

The paper’s `(cpolX)` rule is written with a syntactic recursive equation premise, rendered in the PDF as `X,p` above the transition. `Step.cpol_var` makes that implicit equation explicit as `definition : env.lookup name = some body`. The paper rule should not be confused with a global coinductive recursive binding construct. Lean’s rule unfolds one step by delegation to the body; it does not itself prove that recursive definitions exist, are unique, guarded, or productive. `RecEnv.define` replaces a previous binding for a name, while uniqueness is not enforced as a separate proposition because the environment is a function.

Definedness support appears in `Definedness.lean`: `recursiveVars` (6–18), `Defined` (22–23), `ReachableVar` (27–32), `ClosedDefined` (35–36), and `WellFormed` (140–143). Helper theorems establish closure propagation and guarded bodies (51–74, 145–181). These do not establish branching finiteness or AIP soundness.

## Executable packet-transition correspondence

The executable path deliberately distinguishes `none` (unsupported computation) from `some ∅` (supported computation with no transitions). `packetTransitions` returns a finite multiset for the pending packet head using the executable evaluator.

Verbatim declarations from `NetKATBridge.lean:24-40`:

```lean
theorem execute_packet_step
    (env : RecEnv) (p : NetKAT) (continuation : DyNetKAT)
    (sigma sigma' : CtxPkt) (pendingTail handled : List CtxPkt)
    (outputs : Finset CtxPkt)
    (evaluates : execute p sigma = .supported outputs)
    (produced : sigma' ∈ outputs) :
    Step env
      ({ proc := .nSeq p continuation,
         pending := sigma :: pendingTail,
         handled := handled } : Config)
      (Action.packet sigma sigma')
      ({ proc := continuation,
         pending := pendingTail,
         handled := sigma' :: handled } : Config) := by
  apply Step.cpol_seq_ok
  exact (execute_supported_iff_semantics p sigma sigma' outputs evaluates).mp produced
```

`packetTransitions_sound` (`Executable.lean:57-88`) proves every enumerated pair is a `Step`. `packetTransitions_complete` (`Executable.lean:90-119`) proves every `Step` from an `nSeq` configuration has a corresponding enumerated result. These are fully proved exact correspondences for that packet-processing fragment. They do not establish the paper’s equational soundness, ground-completeness, or bisimulation theorem.

The evaluator is proved total for the current `NetKAT` inductive, so `.unsupported` is a defensive result type rather than an outcome reachable for a well-typed current policy: `execute_correct` proves existence of a `.supported B` for every `p` and packet. The transition enumerator still distinguishes `none` from `some ∅` at its interface, and its results are finite multisets. `packetTransitions_complete` relies on `execute_correct`; it does not enumerate transitions for arbitrary DyNetKAT constructors.

## Congruence theorem inventory

The following are theorem declarations with proofs in `Bisimulation.lean`; their exact complete source text (including proof terms) is authoritative at the cited line. The declarations are listed here so the coverage boundary is explicit:

```lean
theorem Bisimilar.choice_left (env : RecEnv) {p q r : DyNetKAT}
    (hpq : Bisimilar env p q) :
    Bisimilar env (.choice p r) (.choice q r)

theorem Bisimilar.choice_right (env : RecEnv) {p q r : DyNetKAT}
    (hpq : Bisimilar env p q) :
    Bisimilar env (.choice r p) (.choice r q)

theorem Bisimilar.parallel_right (env : RecEnv) {p q r : DyNetKAT}
    (hpq : Bisimilar env p q) :
    Bisimilar env (.parallel p r) (.parallel q r)

theorem Bisimilar.parallel_left (env : RecEnv) {p q r : DyNetKAT}
    (hpq : Bisimilar env p q) :
    Bisimilar env (.parallel r p) (.parallel r q)

theorem Bisimilar.leftMerge_left (env : RecEnv) {p q r : DyNetKAT}
    (hpq : Bisimilar env p q) :
    Bisimilar env (.leftMerge p r) (.leftMerge q r)

theorem Bisimilar.leftMerge_right (env : RecEnv) {p q r : DyNetKAT}
     (hpq : Bisimilar env p q) :
     Bisimilar env (.leftMerge r p) (.leftMerge r q)

theorem Bisimilar.commMerge_right (env : RecEnv) {p q r : DyNetKAT}
    (hpq : Bisimilar env p q) :
    Bisimilar env (.commMerge p r) (.commMerge q r)

theorem Bisimilar.commMerge_left (env : RecEnv) {p q r : DyNetKAT}
    (hpq : Bisimilar env p q) :
    Bisimilar env (.commMerge r p) (.commMerge r q)

theorem Bisimilar.nSeq_left (env : RecEnv) {n : NetKAT} {p q : DyNetKAT}
    (hpq : Bisimilar env p q) :
    Bisimilar env (.nSeq n p) (.nSeq n q)

theorem Bisimilar.recv_left (env : RecEnv) {x : Channel} {n : NetKAT}
    {p q : DyNetKAT} (hpq : Bisimilar env p q) :
    Bisimilar env (.recv x n p) (.recv x n q)

theorem Bisimilar.send_left (env : RecEnv) {x : Channel} {n : NetKAT}
    {p q : DyNetKAT} (hpq : Bisimilar env p q) :
    Bisimilar env (.send x n p) (.send x n q)

theorem Bisimilar.rcfgPrefix_left (env : RecEnv) {x : Channel} {n : NetKAT}
    {p q : DyNetKAT} (hpq : Bisimilar env p q) :
    Bisimilar env (.rcfgPrefix x n p) (.rcfgPrefix x n q)

theorem Bisimilar.restrict (env : RecEnv) {actions : Set CommunicationAction}
    {p q : DyNetKAT} (hpq : Bisimilar env p q) :
    Bisimilar env (.restrict actions p) (.restrict actions q)

theorem Bisimilar.project (env : RecEnv) {n : Nat} {p q : DyNetKAT}
    (hpq : Bisimilar env p q) :
    Bisimilar env (.project n p) (.project n q)
```

These are verbatim declaration statements, not complete declaration blocks: each source theorem also includes a proof body. For complete verbatim bodies consult `Bisimulation.lean` at the start lines shown above (respectively 68, 109, 150, 214, 278, 314, 345, 393, 441, 472, 503, 534, 565, 617). This report does not present reconstructed proof text as verbatim. The set covers each binary operator argument position and each unary/prefix context implemented; it does not establish preservation under arbitrary substitution for recursion variables, nor a single theorem for contexts generated by the paper’s entire equational derivability relation.
