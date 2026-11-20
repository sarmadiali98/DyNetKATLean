------------------------------------------------------------------------
-- DyNetKAT process syntax (Eq. 1, paper p. 8, §II-C "DyNetKAT Syntax")
--
-- Per the DyNetKAT paper (arXiv:2102.10035v4):
--   Eq. 1, p. 8:   D ::= ⊥ | N;D | x?N;D | x!N;D | D‖D | D⊕D | X
--   Eq. 6, p. 14:  Dₑ ::= ... | Dₑ⌊⌊Dₑ | Dₑ|Dₑ | ...
--   where N ranges over NetKAT⁻ᵈᵘᵖ (the existing `NetKAT` inductive in
--   `NetKAT/AST.lean`), x ranges over channel names, and X ranges over a
--   (countably infinite) set of recursive variables.
--
-- Design decisions (per docs/PROCESS_AST_DESIGN.md):
--   1. `Channel := String` — countably infinite channel names (§II-C),
--      no `Fintype` (the paper does not bound channels); `DecidableEq`
--      comes from Lean core `String`.
--   2. `Var := String` — named recursion variables, matching the JSON
--      `recursive_variables` schema. The defining equation `X ≜ d` is a
--      well-formedness property of a separate environment (`RecEnv`),
--      NOT encoded in the `var` constructor.
--   3. The `NetKAT` argument of `nSeq`/`recv`/`send`/`rcfgPrefix` reuses the existing
--      dup-free `NetKAT` type verbatim (§II-C: `N ∈ NetKAT⁻ᵈᵘᵖ`).
--   4. Eq. (1) has no reconfiguration prefix. The distinct `rcfgPrefix`
--      constructor below represents the extended term `rcfg_{x,N};D_e`
--      from Eq. (6); `Action.rcfg` remains the Figure 8 action label.
--   5. Restriction sets exclude packet and `rcfg` labels by construction
--      (Eq. 6, p. 14).
--   6. Trailing `; ⊥` is omitted in the paper "whenever clear from the
--      context" (§II-C); here every sequence carries an explicit
--      continuation, and bare `N` is expressed via `policy` below.
------------------------------------------------------------------------

import DyNetKAT.NetKAT.AST

-- The `NetKAT` inductive is `DyNetKAT.NetKAT.NetKAT`; open its namespace so
-- that `NetKAT.fieldTest`, `NetKAT.id`, … resolve below.
open DyNetKAT.NetKAT

-- The module lives at `DyNetKAT/DyNetKAT/AST.lean`, so declarations in the
-- namespace `DyNetKAT.DyNetKAT` repeat the `DyNetKAT` component (exactly as
-- `NetKAT/AST.lean` repeats `NetKAT`).  The resulting `dupNamespace` linter
-- warnings are cosmetic; they are silenced locally for this new file only.
set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT

------------------------------------------------------------------------
-- Channel names and recursion variables (§II-C)
------------------------------------------------------------------------

/-- Channel names `x` (§II-C: "x ranges over channel names").

    Countably infinite (all finite strings over a finite alphabet), with
    decidable equality from Lean core `String`.  No `Fintype` instance is
    provided: the paper does not bound the set of channels. -/
abbrev Channel : Type := String

/-- Recursion-variable names `X` (§II-C: "X over a (countably infinite)
    set of recursive variables", each with a unique defining equation
    `X ≜ d`).

    The binding `X ≜ d` lives in a separate environment (`RecEnv`), applied
    when unfolding via the `cpolX` rule (Fig. 8); it is deliberately NOT
    stored in the `var` constructor, which would make the type a graph
    rather than an inductive tree. -/
abbrev Var : Type := String

/-- The action forms admitted in restriction sets ℒ (Eq. 6, p. 14):
    communications `x?N` and `x!N`, with `N ∈ NetKAT⁻ᵈᵘᵖ`. Packet and
    reconfiguration labels are intentionally not members of this type. -/
inductive CommunicationAction (schema : PacketSchema := ctxSchema) : Type
  | recv : Channel → NetKAT schema → CommunicationAction schema
  | send : Channel → NetKAT schema → CommunicationAction schema

------------------------------------------------------------------------
-- The DyNetKAT inductive (Eq. 1 base syntax plus rcfg prefix from Eq. 6)
------------------------------------------------------------------------

/-- DyNetKAT process syntax — Eq. (1), p. 8, §II-C, with the extended
    reconfiguration prefix from Eq. (6), p. 14:

    `D_e ::= ⊥ | N;D_e | x?N;D_e | x!N;D_e | rcfg_{x,N};D_e
             | D_e‖D_e | D_e⊕D_e | D_e⌊⌊D_e | D_e|D_e | X`

    - `deadlock`   : ⊥        — "a dummy policy without behaviour"
    - `nSeq`       : N;D      — NetKAT policy applied to the current packet,
                                then the next packet is fetched for D
    - `recv`       : x?N;D    — receive a NetKAT⁻ᵈᵘᵖ policy through channel x
    - `send`       : x!N;D    — send a NetKAT⁻ᵈᵘᵖ policy through channel x
    - `rcfgPrefix` : rcfg_{x,N};D — extended reconfiguration prefix (Eq. 6),
                                    distinct from the `Action.rcfg` label
    - `parallel`   : D‖D      — asynchronous parallel composition
    - `choice`     : D⊕D      — non-deterministic choice
    - `leftMerge`   : D⌊⌊D     — left-merge operator (Eq. 6)
    - `commMerge`   : D|D      — communication-merge operator (Eq. 6)
    - `restrict`   : δ_ℒ(D)   — restriction to communication actions (Eq. 6)
    - `project`    : π_n(D)   — projection to depth n (Eq. 6)
    - `var`        : X        — recursive variable (unfolded via `X ≜ d`)

    The `NetKAT` argument is the existing dup-free `NetKAT` type
    (`NetKAT/AST.lean`), per §II-C and Eq. (6): `N ∈ NetKAT⁻ᵈᵘᵖ`. -/
inductive DyNetKAT (schema : PacketSchema := ctxSchema) : Type
  | deadlock   : DyNetKAT schema  -- ⊥      (Eq. 1)
  | nSeq       : NetKAT schema → DyNetKAT schema → DyNetKAT schema  -- N;D    (Eq. 1)
  | recv       : Channel → NetKAT schema → DyNetKAT schema → DyNetKAT schema  -- x?N;D  (Eq. 1)
  | send       : Channel → NetKAT schema → DyNetKAT schema → DyNetKAT schema  -- x!N;D  (Eq. 1)
  | rcfgPrefix : Channel → NetKAT schema → DyNetKAT schema → DyNetKAT schema  -- rcfg_{x,N};D (Eq. 6)
  | parallel   : DyNetKAT schema → DyNetKAT schema → DyNetKAT schema  -- D‖D    (Eq. 1)
  | choice     : DyNetKAT schema → DyNetKAT schema → DyNetKAT schema  -- D⊕D    (Eq. 1)
  | leftMerge  : DyNetKAT schema → DyNetKAT schema → DyNetKAT schema  -- D⌊⌊D   (Eq. 6)
  | commMerge  : DyNetKAT schema → DyNetKAT schema → DyNetKAT schema  -- D|D    (Eq. 6)
  | restrict   : Set (CommunicationAction schema) → DyNetKAT schema → DyNetKAT schema  -- δ_ℒ(D) (Eq. 6)
  | project    : Nat → DyNetKAT schema → DyNetKAT schema  -- π_n(D) (Eq. 6)
  | var        : Var → DyNetKAT schema  -- X      (Eq. 1)

------------------------------------------------------------------------
-- Shorthand constructors
------------------------------------------------------------------------

/-- A bare NetKAT policy `N` as a DyNetKAT process.

    §II-C: "we do not explicitly specify the trailing `; ⊥` whenever clear
    from the context."  Eq. (1) itself only produces processes of the shape
    `N;D`, so a policy written without a trailing continuation denotes
    `N; ⊥`.  This shorthand makes that convention explicit. -/
def policy {schema : PacketSchema} (N : NetKAT schema) : DyNetKAT schema := .nSeq N .deadlock

/-- Non-deterministic choice over a finite domain `P` (§II-C syntactic
    sugar `⊕_{p∈P} p`): an iterated binary `⊕` with `⊥` as the neutral
    element.  The empty choice is `⊥`. -/
def choiceOf {schema : PacketSchema} : List (DyNetKAT schema) → DyNetKAT schema
  | [] => .deadlock
  | d :: ds => .choice d (choiceOf ds)

------------------------------------------------------------------------
-- Concrete examples (paper §II-C / Fig. 5 style fragments)
------------------------------------------------------------------------

/-- `⊥` — the dummy policy. -/
example : DyNetKAT := .deadlock

/-- A NetKAT policy `tpSrc = v8; drop` applied to the current packet. -/
example : DyNetKAT := .nSeq (NetKAT.fieldTest .tpSrc .v8) .deadlock

/-- `x?N; ⊥` — receive a policy through channel "ctrl" and apply it. -/
example : DyNetKAT := .recv "ctrl" (NetKAT.completeAssignExpr (fun _ => .v8)) .deadlock

/-- `x!N; ⊥` — send a policy through channel "ctrl". -/
example : DyNetKAT := .send "ctrl" NetKAT.id .deadlock

/-- `rcfg_{x,N};D` — the extended reconfiguration prefix, not an action label. -/
example : DyNetKAT := .rcfgPrefix "ctrl" NetKAT.id .deadlock

/-- `D‖D` — parallel composition of two policies. -/
example : DyNetKAT :=
  .parallel (.nSeq NetKAT.id .deadlock) (.nSeq NetKAT.drop .deadlock)

/-- `D⊕D` — non-deterministic choice. -/
example : DyNetKAT :=
  .choice (.nSeq NetKAT.id .deadlock) (.nSeq NetKAT.drop .deadlock)

/-- A recursive variable `X`. -/
example : DyNetKAT := .var "Switch"

end DyNetKAT.DyNetKAT
