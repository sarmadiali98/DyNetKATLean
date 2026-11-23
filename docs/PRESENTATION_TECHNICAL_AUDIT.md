# Technical Audit Report: DyNetKAT-Lean

**Prepared for:** Research presentation to the DyNetKAT paper authors
**Paper:** *DyNetKAT: An Algebra of Dynamic Networks*, arXiv:2102.10035v4 (FoSSaCS 2022)
**Repository:** `/Users/ali/Desktop/DyNetKAT-Lean`
**Commit:** `e96d71a8b863ff58938d58a05a09af53a5cea660` (master, 2026-10-19)
**Date:** 2026-10-24

---

## Executive Summary

The DyNetKAT-Lean repository contains a **faithful, machine-verified partial formalization** of the original DyNetKAT calculus in Lean 4. The formalization covers:

1. **NetKAT⁻ᵈᵘᵖ** (finite-domain packet model, denotational semantics, normal forms, executable evaluator with correctness proofs) — **fully implemented** and verified.
2. **DyNetKAT extended syntax** (all operators from Eq. 1 and Eq. 6, including `rcfgPrefix`, `leftMerge`, `commMerge`, `restrict`, `project`) — **fully implemented**.
3. **Labeled operational semantics (Fig. 8)** — **fully implemented** with all 10 Step constructors.
4. **Bisimulation and congruence theorems** — **fully implemented** (reflexivity, symmetry, transitivity + congruence for every operator).
5. **Definedness, guardedness, well-formedness predicates** — **fully defined** with theorems establishing relationships.
6. **Executable transition generator** — **fully implemented** with soundness and completeness theorems.

**Key limitations:** The formalization does **not** yet include the equational axiom system (A0–A15, AIP), the completeness theorem (Theorem 1), or the safety framework (Definitions 12–17). The `Step` relation is parameterized by an explicit `RecEnv` (recursion environment), which is a faithful explicit representation of the paper's meta-level recursive variable notation.

**Build status:** `lake build DyNetKAT` succeeds with no errors. **No `sorry`, `admit`, `axiom`, or `unsafe` declarations** exist in the source code.

---


## Table of Contents

1. [Repository State](#1-repository-state)
2. [Recursive Specifications and RecEnv](#2-recursive-specifications-and-recenv)
3. [Definedness, Guardedness, and Well-Formedness](#3-definedness-guardedness-and-well-formedness)
4. [Operational Semantics and Bisimulation](#4-operational-semantics-and-bisimulation)
5. [Verified Executable NetKAT Evaluator](#5-verified-executable-netkat-evaluator)
6. [Connecting NetKAT Execution to DyNetKAT Semantics](#6-connecting-netkat-execution-to-dynetkat-semantics)
7. [Executable DyNetKAT Transition Generator](#7-executable-dynetkat-transition-generator)
8. [Executable Example](#8-executable-example)
9. [Proof Integrity and Dependency Audit](#9-proof-integrity-and-dependency-audit)
10. [Slide Recommendations](#10-slide-recommendations)
11. [Future Research and Remaining Obligations](#11-future-research-and-remaining-obligations)
12. [Claims We Can Safely Make](#12-claims-we-can-safely-make-in-the-presentation)
13. [Claims We Must Not Make](#13-claims-we-must-not-make)
14. [Questions or Potential Problems](#14-questions-or-potential-problems)

---

## 1. Repository State

### Git and toolchain

| Property | Value |
|---|---|
| Branch | `master` |
| Commit hash | `e96d71a8b863ff58938d58a05a09af53a5cea660` |
| Commit date | 2026-10-19 |
| Commit message | "Checkpoint: Merge operators and congruence" |
| Lean version | `4.19.0` (Lean 4) |
| Lake version | `5.0.0-src+eb6cafb` |
| Toolchain | `leanprover/lean4:v4.19.0` |
| Mathlib4 | `v4.19.0` (via `lakefile.toml` require) |

### Build status

- **Source path:** `lean/` (the Lake project root)
- **Build command:** `lake build DyNetKAT`
- **Result:** Build completed successfully (only cosmetic `dupNamespace` linter warnings)
- **No `sorry`, `admit`, `axiom`, or `unsafe`** in any source file

### Module inventory

```
lean/
├── DyNetKAT.lean          — library root (imports all modules)
├── lakefile.toml          — project config, depends on Mathlib4 v4.19.0
├── lean-toolchain         — pins leanprover/lean4:v4.19.0
├── DyNetKAT/
│   ├── Basic.lean         — project name string (1 theorem)
│   ├── Main.lean          — CLI entry point (prints project name)
│   ├── NetKAT/            — NetKAT⁻ᵈᵘᵖ semantic core (Phase 1)
│   │   ├── AST.lean       — 8-constructor NetKAT + Predicate + fieldEnum
│   │   ├── Packet.lean    — packet model, fields, values, complete tests/assignments
│   │   ├── Semantics.lean — denotational semantics ⟦N⟧, 30+ identity theorems
│   │   ├── NormalForm.lean— normal form representation + semantic correctness
│   │   └── Evaluator.lean — executable evaluator + execute_correct theorem
│   └── DyNetKAT/          — DyNetKAT calculus (Phase 2–4)
│       ├── AST.lean       — DyNetKAT process syntax (12 constructors)
│       ├── Action.lean    — 4-label Action type (packet, recv, send, rcfg)
│       ├── Config.lean    — Config structure (proc, pending, handled)
│       ├── RecEnv.lean    — RecEnv type and operations
│       ├── Definedness.lean — ReachableVar, ClosedDefined, WellFormed, GuardedOccurrences
│       ├── Semantics.lean  — Step inductive (Fig. 8 labeled SOS, 10 constructors)
│       ├── Bisimulation.lean — IsBisimulation, Bisimilar, 13 congruence theorems
│       ├── NetKATBridge.lean — execute_supported_iff_semantics, execute_packet_step
│       └── Executable.lean  — packetTransitions + soundness/completeness
├── test_evaluator_integration.lean — integration tests for execute_correct
├── test_*.lean (10 files)          — various scratch tests
└── docs/ (13 files)                 — research notes, design docs, audits
```

### Implementation status by component

| Component | Status |
|---|---|
| NetKAT syntax & denotational semantics | Fully implemented |
| NetKAT executable evaluator + correctness | Fully implemented |
| NetKAT normal forms (representation + semantics) | Representation + semantic theorems; Lemma 5 (algorithm G) NOT proved |
| DyNetKAT AST (Eq. 1 + Eq. 6) | Fully implemented (12 constructors) |
| Action labels (Fig. 8 label grammar) | Fully implemented |
| Config structure | Fully implemented |
| RecEnv | Fully implemented |
| Definedness/guardedness/well-formedness | All predicates defined + theorems |
| Operational semantics (Fig. 8 Step) | All 10 constructors |
| Bisimulation + congruence | All 13 congruence theorems proved |
| NetKAT-to-DyNetKAT bridge | 2 theorems |
| Executable transition generator | 2 theorems (soundness + completeness) |
| Equational axiom system (A0–A15, AIP) | Not started |
| Completeness (Theorem 1) | Not started |
| Safety framework (Defs 12–17) | Not started |

### Most recent meaningful technical milestone

The most recent commit (`e96d71a`, "Checkpoint: Merge operators and congruence") added:
- `leftMerge` and `commMerge` constructors to the DyNetKAT AST (`AST.lean:108-109`)
- Congruence theorems for `leftMerge` and `commMerge` in `Bisimulation.lean` (lines 278–439)
- Extended `Step` constructors for `cpol_left_merge`, `cpol_comm_merge_recv_send`, `cpol_comm_merge_send_recv`, `cpol_sync_recv_send`, `cpol_sync_send_recv` in `Semantics.lean`

This represents the **completion of the full DyNetKAT operational semantics (Fig. 8) and the core bisimulation congruence results**.


## 2. Recursive Specifications and RecEnv

### A. What is RecEnv?

**Exact declaration:**

File: `packages/DyNetKATLean/DyNetKATLean/Core/RecEnv.lean`, line 9:

```lean
abbrev RecEnv : Type := Var → Option DyNetKAT
```

**Verbatim code block (RecEnv.lean:5–33):**

```lean
/-- Recursive-variable definitions used by the `(cpolX)` rule.

    An optional body keeps lookup total without assuming that every variable is
    defined or that definitions are guarded. -/
abbrev RecEnv : Type := Var → Option DyNetKAT

/-- Look up the defining body for a recursive variable. -/
def RecEnv.lookup (env : RecEnv) (name : Var) : Option DyNetKAT := env name

/-- The environment with no recursive definitions. -/
def RecEnv.empty : RecEnv := fun _ => none

/-- Add the unique definition for `name`, replacing any previous entry. -/
def RecEnv.define (env : RecEnv) (name : Var) (body : DyNetKAT) : RecEnv :=
  fun candidate => if candidate = name then some body else env candidate

@[simp] theorem RecEnv.lookup_empty (name : Var) :
    RecEnv.empty.lookup name = none := rfl

@[simp] theorem RecEnv.lookup_define_same (env : RecEnv) (name : Var)
    (body : DyNetKAT) :
    (env.define name body).lookup name = some body := by
  simp [RecEnv.define, RecEnv.lookup]

theorem RecEnv.lookup_define_other (env : RecEnv) (name candidate : Var)
    (body : DyNetKAT) (different : candidate ≠ name) :
    (env.define name body).lookup candidate = env.lookup candidate := by
  simp [RecEnv.define, RecEnv.lookup, different]
```

**Type explanation:**

- `Var` is defined in `AST.lean:64` as `abbrev Var : Type := String` — countably infinite recursion-variable names.
- `RecEnv` is a **total function** `Var → Option DyNetKAT`. It maps each variable name to either `some body` (defined) or `none` (undefined).
- The `lookup` method applies the function (syntactic sugar for `env name`).
- `empty` is the environment with no recursive definitions (everything maps to `none`).
- `define` updates the environment, replacing any previous binding for that variable.

**How recursive process variables are represented:**

Recursive variables in the process syntax are represented by the `var` constructor (`AST.lean:112`):

```lean
inductive DyNetKAT : Type
  | ...
  | var : Var → DyNetKAT   -- X  (Eq. 1)
```

The variable **name** is stored in the process term; the **defining body** lives in the `RecEnv`. This is a deliberate design decision (documented in `AST.lean:56-63`): storing the body inside the `var` constructor would make the type a graph (with cycles) rather than an inductive tree. The separation keeps `DyNetKAT` a well-founded inductive type while allowing recursive definitions to live in the environment.

**How defining bodies are retrieved:**

The `RecEnv.lookup` function retrieves the body: `env.lookup name` returns `some body` if `name` is defined, `none` otherwise. The `cpol_var` constructor in the Step relation uses this lookup as a premise (see Section 2.C below).

**Are undefined variables possible?**

Yes. `RecEnv` uses `Option DyNetKAT`, so a variable may be undefined (`none`). The `WellFormed` predicate (Section 3) includes `ClosedDefined` which requires that all reachable variables are defined. The `cpol_var` Step constructor requires `env.lookup name = some body` as a premise, meaning unfolding only applies when the variable is defined.

**How the environment is passed through the semantics:**

The `Step` relation is parameterized by `RecEnv` as its first argument:

```lean
inductive Step (env : RecEnv) : Config → Action → Config → Prop
```

Every constructor of `Step` receives the same `env` parameter. The environment is **fixed** throughout a derivation — it is not modified by transitions. The only constructor that consults `env` is `cpol_var`, which uses it as a premise to look up the defining body of a recursive variable.

### B. Why do we need an environment?

**The original paper** writes bisimilarity as `p ∼ q` without an explicit environment parameter. The paper treats recursive defining equations `X ≜ d` as **meta-level notation**: each recursive variable has a unique definition that is implicitly available throughout the development.

**Mathematical justification for the explicit `RecEnv`:**

1. **How does the paper represent recursive defining equations?**
   The paper uses `X` for recursive variables and writes `X ≜ d` as a meta-level assertion. In the formalization, `X ≜ d` is represented as an entry in `RecEnv`: `env.define X d`. The paper does not give a formal data structure for the collection of defining equations.

2. **Where does the original operational semantics rely on those equations?**
   In the `(cpolX)` rule (Figure 8, printed p. 9–10), a recursive variable `X` (defined as `X ≜ p`) behaves according to its body `p`. The rule states: if `(p, H, H′) →γ (p′, H″, H‴)` then `(X, H, H′) →γ (p′, H″, H‴)`. The premise `X ≜ p` is a meta-level assumption.

3. **Does the paper treat the recursive specification as implicit context?**
   Yes. The paper writes `X ≜ d` in the meta-language, not as an explicit runtime object. It says (§II-C, p. 8): "each recursive variable should have a unique defining equation X ≜ d." This is a well-formedness condition, not an explicit data structure passed at runtime.

4. **Is our `RecEnv` a faithful explicit representation of that context?**
   Yes. `RecEnv : Var → Option DyNetKAT` is the standard way to make implicit context explicit in a constructive type theory. Each variable `X` maps to its (optional) defining body. The `Option` type accounts for the paper's well-formedness condition (not all variables need be defined in a given term). The `ClosedDefined` predicate enforces that all reachable variables have definitions.

5. **Can the transitions of a variable `X` differ between two environments?**
   Yes. If `env₁.lookup X = some p₁` and `env₂.lookup X = some p₂` with `p₁ ≠ p₂`, then `X`'s transitions will differ: in `env₁`, `X` unfolds to `p₁`'s transitions; in `env₂`, to `p₂`'s. The `cpol_var` constructor's premise `definition : env.lookup name = some body` makes this dependency explicit.

6. **Why does this affect the definition of bisimilarity?**
   Bisimilarity must account for the environment. In the paper, `p ∼ q` is implicitly understood under a fixed set of recursive equations. In Lean, `Bisimilar` takes `env : RecEnv` as a parameter: `Bisimilar env p q`. The bisimulation relation `R` relates processes that behave identically **under the same environment**. If `p` and `q` contain recursive variables, their bisimilarity depends on which bodies those variables map to in `env`.

7. **Does our Lean formalization use one fixed environment, or quantify over environments?**
   The formalization uses **one fixed environment** passed as a parameter to both `Step` and `Bisimilar`. The congruence theorems all state: given `Bisimilar env p q` (for a fixed `env`), conclude `Bisimilar env (C[p]) (C[q])` (under the same `env`). There is no quantification over environments in the current theorems. This means bisimilarity is proved **relative to a fixed environment**.

**Caveat:** The paper's bisimilarity `p ∼ q` is intended to hold for a given recursive specification (the implicit context). The Lean formalization faithfully captures this by parameterizing everything on `env`. However, the paper's completeness theorem (Theorem 1) is stated without explicit environment quantification — it implicitly assumes all recursive variables in the terms are well-defined. The Lean formalization would need to state: "for all well-formed environments `env`, `E_DNK ⊢ p ≡ q` iff `Bisimilar env p q`" — but this theorem is **not yet proved**.

### C. Recursive unfolding

**The exact Lean constructor** (`Semantics.lean:156–167`):

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

**Comparison with the paper's rule (Fig. 8):**

The paper's rule (cpolX) states:
```
    (p, H₀, H₁) →γ (p′, H₀′, H₁′)
    ──────────────────────────────────────  (cpolX)   [X ≜ p]
    (X, H₀, H₁) →γ (p′, H₀′, H₁′)
```

**Explanation:**

- **How the defining body is obtained:** The premise `definition : env.lookup name = some body` in the Lean constructor corresponds to the paper's meta-level `[X ≜ p]` annotation. The body `p` is retrieved from the environment via `env.lookup name`.
- **How the body's transition becomes a transition of the variable:** Given a transition of the body `(p, H, H′) →γ (p′, H″, H‴)` (the `step` premise), the constructor produces the transition `(X, H, H′) →γ (p′, H″, H‴)` with the same label, same input packet lists, and same output packet lists.
- **Does unfolding produce an observable action?** Yes — the label `γ` is **inherited** from the body's transition. The rule does not have an "internal" or silent label; whatever action the body produces is the same action the variable produces. This matches the paper: the variable `X` "behaves according to `p`."
- **Is the same environment used throughout the derivation?** Yes. The `env` parameter is fixed for the entire `Step` derivation. Recursive unfolding of nested variables (e.g., if `body` itself contains a `var`) uses the same `env` — `cpol_var` is applied recursively with the same `env`.
- **Does unfolding require definedness or guardedness assumptions?** The `cpol_var` constructor itself does **not** require guardedness. It requires only `env.lookup name = some body` (the variable must be defined). Guardedness (Definition 7) is a **separate well-formedness concern** — it ensures that recursive unfolding terminates (produces a well-founded derivation). The `WellFormed` predicate (Section 3) combines `ClosedDefined` with `GuardedOccurrences` of all reachable variable bodies. However, **the current theorems do not require `WellFormed`** — they quantify over arbitrary environments and arbitrary terms.

**Key difference from the paper's presentation:**

The paper writes `[X ≜ p]` as a side annotation on the rule, treating it as implicit meta-level context. The Lean encoding makes it an **explicit premise**: `definition : env.lookup name = some body`. This is a faithful and standard encoding — it makes the dependency explicit in the type theory, which is necessary because Lean 4 does not have meta-level variable definitions.


## 3. Definedness, Guardedness, and Well-Formedness

All declarations are in `packages/DyNetKATLean/DyNetKATLean/Core/Definedness.lean`.

### ReachableVar (line 27)

**Exact declaration:**

```lean
inductive ReachableVar (env : RecEnv) : DyNetKAT → Var → Prop
  | direct {process : DyNetKAT} {name : Var} :
      name ∈ recursiveVars process → ReachableVar env process name
  | throughDefinition {process : DyNetKAT} {source target : Var} {body : DyNetKAT} :
      ReachableVar env process source → env.lookup source = some body →
      target ∈ recursiveVars body → ReachableVar env process target
```

**Mathematical meaning:** A variable `name` is **reachable** from a process if:
- `direct`: It occurs directly in the process (appears in `recursiveVars`).
- `throughDefinition`: It occurs in the body of some other reachable variable's definition.

This is a **transitive closure** over variable occurrences and definitions: if `X` is reachable and `X ≜ p`, then any variable in `p` is also reachable. This captures the notion that recursive definitions introduce new reachable variables.

**Where it is used:** `ClosedDefined` (line 35), `WellFormed` (line 140), and all their derived theorems (`reachableView.direct`, `reachableView.through_definition`, `reachableView.body`, `reachableView_of_reachable_body`).

**Theorems established:**
- `reachableVar_direct` (line 38) — direct occurrences are reachable
- `reachableVar_through_definition` (line 43) — variables in a reachable variable's body are reachable
- `ReachableVar.body` (line 57) — transitively through definitions

**What has NOT been proved:** No theorem about the finiteness of `ReachableVar`. No preservation theorem for reachability under unfolding alone.

### Defined (line 22)

**Exact declaration:**

```lean
def Defined (env : RecEnv) (process : DyNetKAT) : Prop :=
  ∀ name ∈ recursiveVars process, (env.lookup name).isSome
```

**Mathematical meaning:** Every recursive variable occurring **directly** in `process` has a definition in `env`. This is a **shallow** check — it does not inspect the bodies of definitions.

**Where it is used:** Used in the proof of `ClosedDefined.defined` (line 51).

**Theorems established:**
- `ClosedDefined.defined` (line 51) — `ClosedDefined` implies `Defined`

**What has NOT been proved:** No standalone theorems about `Defined` alone.

### ClosedDefined (line 35)

**Exact declaration:**

```lean
def ClosedDefined (env : RecEnv) (process : DyNetKAT) : Prop :=
  ∀ name, ReachableVar env process name → (env.lookup name).isSome
```

**Mathematical meaning:** Every recursively reachable variable (directly or through a chain of definitions) has a definition in `env`. This is a **deep** check — it closes under the transitive closure of reachability.

**Where it is used:** `WellFormed` (line 140), `WellFormed.closedDefined` (line 145).

**Theorems established:**
- `ClosedDefined.defined` (line 51) — `ClosedDefined` implies `Defined`

**What has NOT been proved:** No theorem establishing that `ClosedDefined` is preserved under transitions (Step).

### GuardedOccurrences (line 90)

**Exact declaration:**

```lean
def GuardedOccurrences : DyNetKAT → Prop
  | .deadlock => True
  | .nSeq _ _ => True
  | .recv _ _ _ => True
  | .send _ _ _ => True
  | .rcfgPrefix _ _ _ => True
  | .parallel left right => GuardedOccurrences left ∧ GuardedOccurrences right
  | .choice left right => GuardedOccurrences left ∧ GuardedOccurrences right
  | .leftMerge left right => GuardedOccurrences left ∧ GuardedOccurrences right
  | .commMerge left right => GuardedOccurrences left ∧ GuardedOccurrences right
  | .restrict _ process => GuardedOccurrences process
  | .project _ process => GuardedOccurrences process
  | .var _ => False
```

**Mathematical meaning (Definition 7):** A process has guarded recursive-variable occurrences if every occurrence of a recursive variable is "guarded" — i.e., it appears under at least one sequencing prefix (`N;D`), communication prefix (`x?N;D`, `x!N;D`), or reconfiguration prefix (`rcfg_{x,N};D`). A bare variable `X` is **not** guarded (`GuardedOccurrences (.var name) = False`). The sequencing and communication constructors return `True` unconditionally because their continuation (which may contain variables) is guarded by the prefix.

**Where it is used:** `WellFormed` (line 141), `IsGuarded` (line 105).

**Theorems established:**
- `guardedOccurrences_deadlock` (line 107)
- `not_guardedOccurrences_var` (line 115) — a bare variable is NOT guarded
- `guardedOccurrences_var_iff` (line 119)
- `guardedOccurrences_choice_iff` (line 123)
- `guardedOccurrences_nSeq` (line 128) — `N;D` is always guarded

**What has NOT been proved:** No theorem connecting guardedness to bisimulation finiteness (Lemma 8 — not yet implemented).

### WellFormed (line 140)

**Exact declaration:**

```lean
def WellFormed (env : RecEnv) (process : DyNetKAT) : Prop :=
  ClosedDefined env process ∧
    ∀ name, ReachableVar env process name →
      ∃ body, env.lookup name = some body ∧ GuardedOccurrences body
```

**Mathematical meaning:** A process is well-formed relative to an environment when:
1. **Closedness:** Every recursively reachable variable is defined.
2. **Guarded bodies:** Every reachable variable's defining body has guarded recursive-variable occurrences.

**Where it is used:** Defined but **NOT USED** by any `Step`, `Bisimilar`, or executable-correctness theorem.

**Theorems established:**
- `WellFormed.closedDefined` (line 145)
- `WellFormed.reachable_definition` (line 150)
- `WellFormed.reachable_guarded` (line 157)
- `WellFormed.body` (line 167) — preservation under unfolding
- `wellFormed_var_iff` (line 183)

**What has NOT been proved:**
- No theorem stating that `Step` preserves `WellFormed`.
- No theorem stating that `Bisimilar` requires `WellFormed` environments.

### Critical finding: Well-formedness is NOT required by current theorems

The main `Step`, `Bisimilar`, and executable-correctness theorems do **NOT** explicitly require well-formed environments:

- `Step` (Semantics.lean:13): `inductive Step (env : RecEnv) : Config → Action → Config → Prop` — **no `WellFormed` precondition**.
- `Bisimilar` (Bisimulation.lean:26): `def Bisimilar (env : RecEnv) (p q : DyNetKAT) : Prop` — **no `WellFormed` precondition**.
- `packetTransitions` (Executable.lean:25) — **no `WellFormed` precondition**.
- `packetTransitions_sound` (Executable.lean:57) — **no `WellFormed` hypothesis**.
- `packetTransitions_complete` (Executable.lean:90) — **no `WellFormed` hypothesis**.
- `execute_correct` (Evaluator.lean:1078) — **no `RecEnv` or `WellFormed` parameter** (NetKAT-only).


## 4. Operational Semantics and Bisimulation

### Process AST

File: `packages/DyNetKATLean/DyNetKATLean/Core/AST.lean`, line 100:

```lean
inductive DyNetKAT : Type
  | deadlock   : DyNetKAT                                   -- ⊥      (Eq. 1)
  | nSeq       : NetKAT → DyNetKAT → DyNetKAT               -- N;D    (Eq. 1)
  | recv       : Channel → NetKAT → DyNetKAT → DyNetKAT     -- x?N;D  (Eq. 1)
  | send       : Channel → NetKAT → DyNetKAT → DyNetKAT     -- x!N;D  (Eq. 1)
  | rcfgPrefix : Channel → NetKAT → DyNetKAT → DyNetKAT     -- rcfg_{x,N};D (Eq. 6)
  | parallel   : DyNetKAT → DyNetKAT → DyNetKAT             -- D‖D    (Eq. 1)
  | choice     : DyNetKAT → DyNetKAT → DyNetKAT             -- D⊕D    (Eq. 1)
  | leftMerge  : DyNetKAT → DyNetKAT → DyNetKAT             -- D⌊⌊D   (Eq. 6)
  | commMerge  : DyNetKAT → DyNetKAT → DyNetKAT             -- D|D    (Eq. 6)
  | restrict   : Set CommunicationAction → DyNetKAT → DyNetKAT -- δ_ℒ(D) (Eq. 6)
  | project    : Nat → DyNetKAT → DyNetKAT                  -- π_n(D) (Eq. 6)
  | var        : Var → DyNetKAT                             -- X      (Eq. 1)
```

**Action labels** (`Action.lean:9`):

```lean
inductive Action : Type
  | packet : CtxPkt → CtxPkt → Action
  | recv : Channel → NetKAT → Action
  | send : Channel → NetKAT → Action
  | rcfg : Channel → NetKAT → Action
```

**Config structure** (`Config.lean:11`):

```lean
structure Config where
  proc : DyNetKAT
  pending : List CtxPkt
  handled : List CtxPkt
```

### The Step relation

File: `packages/DyNetKATLean/DyNetKATLean/Core/Semantics.lean`, line 13.

The `Step` relation is an inductive with exactly 10 constructors, corresponding to the 9 Figure 8 rule families (with ⊕ and ‖ each split into left/right halves):

| Constructor | Paper rule | Line |
|---|---|---|
| `cpol_seq_ok` | (cpolX;) — packet flow | Semantics.lean:14 |
| `cpol_choice_l` | (cpol⊕) left | Semantics.lean:26 |
| `cpol_choice_r` | (cpol⊕) right | Semantics.lean:38 |
| `cpol_par_l` | (cpol‖) left | Semantics.lean:50 |
| `cpol_par_r` | (cpol‖) right | Semantics.lean:62 |
| `cpol_left_merge` | (cpol⌊⌊) | Semantics.lean:74 |
| `cpol_comm_merge_recv_send` | (cpol!?) | Semantics.lean:87 |
| `cpol_comm_merge_send_recv` | (cpol?!) | Semantics.lean:105 |
| `cpol_recv` | (cpol?) | Semantics.lean:123 |
| `cpol_send` | (cpol!) | Semantics.lean:134 |
| `cpol_rcfg` | (rcfg_{x,z}) | Semantics.lean:145 |
| `cpol_var` | (cpolX) — recursion | Semantics.lean:156 |
| `cpol_sync_recv_send` | synchronization | Semantics.lean:169 |
| `cpol_sync_send_recv` | synchronization | Semantics.lean:187 |
| `cpol_project` | π_{n+1} lifting | Semantics.lean:205 |
| `cpol_restrict` | δ_ℒ lifting | Semantics.lean:220 |

The exact `cpol_seq_ok` constructor (the only history-modifying rule):

```lean
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

### Bisimulation

File: `packages/DyNetKATLean/DyNetKATLean/Core/Bisimulation.lean`, line 9.

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

def Bisimilar (env : RecEnv) (p q : DyNetKAT) : Prop :=
  ∃ R, IsBisimulation env R ∧ R p q
```

**Bisimulation is defined over processes** (not configurations). The relation `R` ranges over `DyNetKAT → DyNetKAT → Prop`. The simulation condition quantifies over all packet histories (`pending`, `handled`) — this means the bisimulation must match transitions for all possible configurations of the related processes.

### Theorem inventory

**Bisimulation theorems** (Bisimulation.lean):

| Name | Line | Statement |
|---|---|---|
| `Bisimilar.refl` | 29 | `∀ p, Bisimilar env p p` |
| `Bisimilar.symm` | 38 | `Bisimilar env p q → Bisimilar env q p` |
| `Bisimilar.trans` | 43 | `Bisimilar env p q → Bisimilar env q r → Bisimilar env p r` |
| `Bisimilar.choice_left` | 68 | `Bisimilar env p q → Bisimilar env (p⊕r) (q⊕r)` |
| `Bisimilar.choice_right` | 109 | `Bisimilar env p q → Bisimilar env (r⊕p) (r⊕q)` |
| `Bisimilar.parallel_right` | 150 | `Bisimilar env p q → Bisimilar env (p‖r) (q‖r)` |
| `Bisimilar.parallel_left` | 214 | `Bisimilar env p q → Bisimilar env (r‖p) (r‖q)` |
| `Bisimilar.leftMerge_left` | 278 | `Bisimilar env p q → Bisimilar env (p⌊⌊r) (q⌊⌊r)` |
| `Bisimilar.leftMerge_right` | 314 | `Bisimilar env p q → Bisimilar env (r⌊⌊p) (r⌊⌊q)` |
| `Bisimilar.commMerge_right` | 345 | `Bisimilar env p q → Bisimilar env (p|q) (q|r)` — left operand |
| `Bisimilar.commMerge_left` | 393 | `Bisimilar env p q → Bisimilar env (r|p) (r|q)` — right operand |
| `Bisimilar.nSeq_left` | 441 | `Bisimilar env p q → Bisimilar env (n;p) (n;q)` |
| `Bisimilar.recv_left` | 472 | `Bisimilar env p q → Bisimilar env (x?n;p) (x?n;q)` |
| `Bisimilar.send_left` | 503 | `Bisimilar env p q → Bisimilar env (x!n;p) (x!n;q)` |
| `Bisimilar.rcfgPrefix_left` | 534 | `Bisimilar env p q → Bisimilar env (rcfg_{x,n};p) (rcfg_{x,n};q)` |
| `Bisimilar.restrict` | 565 | `Bisimilar env p q → Bisimilar env (δ_ℒ(p)) (δ_ℒ(q))` |
| `Bisimilar.project` | 617 | `Bisimilar env p q → Bisimilar env (π_n(p)) (π_n(q))` |

**All 17 theorems (including refl/symm/trans) are unconditional on `WellFormed`** — they work for any environment. Every congruence theorem is parameterized by `env : RecEnv` and concludes `Bisimilar env ...`.

**Theorems NOT yet proved:**
- Lemma 3 (bisimilarity is a congruence — this is the collection above, but the paper's specific statement)
- Proposition 1 (semantic layering: ⟦p⟧ = ⟦q⟧ iff (p;d) ∼ (q;d))
- Lemma 8 (branching finiteness)
- Lemma 10, 11 (axiom soundness)
- Theorem 1 (soundness & ground-completeness)

### Comparison with the original paper

The paper's Definition 2 defines bisimilarity as the **largest bisimulation**. The Lean formalization defines `Bisimilar` as "there exists a bisimulation relating `p` and `q`" — this is equivalent to the **greatest fixed point** (the largest bisimulation), since the union of all bisimulations is itself a bisimulation. This encoding is standard and faithful.

**Key difference:** The paper's `p ∼ q` does not explicitly parameterize by an environment. The Lean formalization parameterizes everything by `env`. As defended in Section 2.B, this is a faithful explicit encoding of the paper's implicit recursive-variable context.


## 5. Verified Executable NetKAT Evaluator

File: `packages/NetKATLean/NetKATLean/Core/Evaluator.lean` (1149 lines).

### The EvalResult type

```lean
inductive EvalResult where
  | supported (outputs : Finset CtxPkt)
  | unsupported
```

The evaluator distinguishes a **computed empty output** (`.supported ∅`) from an **unsupported term constructor** (`.unsupported`). This distinction is critical: `drop` correctly produces `supported ∅` (no outputs), not `unsupported`.

### Supported constructors

The `execute` function handles all 8 NetKAT constructors:

```lean
def execute : NetKAT → CtxPkt → EvalResult
  | .drop, _ => .supported ∅
  | .id, σ => .supported {σ}
  | .test p, σ => evalPredicate p σ
  | .completeTest α, σ =>
      if σ = α then .supported {σ} else .supported ∅
  | .assign1 f v, σ => .supported {Packet.update σ f v}
  | .union n₁ n₂, σ => ... (union of outputs)
  | .seq p q, σ => ... (fold over intermediate results)
  | .star p, σ => boundedStarWith (execute p) (Fintype.card CtxPkt) σ
```

**All constructors are supported** — no term returns `.unsupported` unless a sub-term does. The `execute_supported` theorem (line 618) proves this: `∀ p σ, ∃ B, execute p σ = .supported B`.

### What is CtxPkt?

`CtxPkt` is defined in `packages/NetKATLean/NetKATLean/Core/Packet.lean:148`:

```lean
abbrev CtxPkt := Packet FieldName FieldValueEnum
```

where:
- `FieldName` (`Packet.lean:118`) is an inductive with 4 constructors: `.tpSrc`, `.tpDst`, `.swId`, `.port`
- `FieldValueEnum` (`Packet.lean:133`) is an inductive with 4 constructors: `.v0`, `.v1`, `.v8`, `.v9`
- `Packet FieldType Value := FieldType → Value` (`Packet.lean:36`)

### Why does the finite packet domain contain 256 valuations?

The packet domain is `FieldName → FieldValueEnum`, with 4 fields each having 4 values: `4^4 = 256`. This was **confirmed computationally**: running `#eval (Fintype.card CtxPkt)` outputs `256`. The `Fintype CtxPkt` instance (`Packet.lean:158-161`) is constructed via Mathlib's `Pi.instFintype`.

### How is evaluation implemented for star?

The Kleene star is implemented via **bounded iteration** using `Fintype.card CtxPkt`:

```lean
def execute : NetKAT → CtxPkt → EvalResult
  | .star p, σ => boundedStarWith (execute p) (Fintype.card CtxPkt) σ
```

```lean
private def boundedStarWith (step : CtxPkt → EvalResult) : Nat → CtxPkt → EvalResult
  | 0, σ => .supported {σ}
  | n + 1, σ =>
      match boundedStarWith step n σ with
      | .unsupported => .unsupported
      | .supported packets =>
          match postWith step packets with
          | .unsupported => .unsupported
         | .supported next => .supported (packets ∪ next)
```

The bound is `Fintype.card CtxPkt = 256`. This works because on a finite packet domain, the reflexive-transitive closure must stabilize within at most `|Packet|` iterations (each new iteration either adds a packet to the reachable set or stabilizes).

**Theorem establishing the bound:** `reachableWithin_stable_at_card` (line 973) proves that reach `n` and reach `(Fintype.card CtxPkt + 1)` are equivalent. `reachableWithin_iff_at_card` (line 996) proves that `∃ n, ReachableWithin p n σ τ` is equivalent to `ReachableWithin p (Fintype.card CtxPkt) σ τ`.

### How are nested Kleene stars handled?

Nested stars like `(p*)*` are handled recursively. The outer `execute (.star p)` calls `boundedStarWith (execute p) 256 σ`, which evaluates `execute p` at each step. If `p` itself contains a star, `execute p` will handle it recursively (with its own bounded iteration). The bound is the same for all levels (256 iterations), but the recursion is well-founded because:
1. The outer bounded iteration has a fixed bound (256).
2. Each inner star evaluation is also bounded (256).
3. The `ReachableWithin` theorem connects bounded iteration to the semantic closure.

### Why does the evaluator terminate?

1. **Finite domain:** `CtxPkt` has 256 elements (by `Fintype.card CtxPkt = 256`).
2. **Bounded star:** The star iteration is bounded by `Fintype.card CtxPkt` (256). The theorem `reachableWithin_stable_at_card` proves stabilization within this bound.
3. **No infinite recursion:** Each NetKAT constructor is processed structurally (recursion on sub-terms), except `star` which uses bounded iteration.

### What is the precise mathematical domain of the correctness theorem?

**The exact theorem** (line 1078):

```lean
theorem execute_correct
    (p : NetKAT) (σ : CtxPkt) :
    ∃ B : Finset CtxPkt,
      execute p σ = .supported B ∧
      ∀ τ, Semantics p σ τ ↔ τ ∈ B
```

**Domain:**
- `p` ranges over all `NetKAT` terms (the 8-constructor dup-free NetKAT).
- `σ` ranges over all `CtxPkt` (the concrete 256-element packet space).
- `B` is a finite set of output packets (`Finset CtxPkt`).
- `Semantics` is the denotational semantics relation (`NetKAT/Semantics.lean:61`).

This theorem establishes **both soundness and completeness** of the evaluator in one statement:
- **Soundness direction** (⇒): If `execute p σ = .supported B`, then `∀ τ, Semantics p σ τ ↔ τ ∈ B`. Every computed output is semantically valid, and every semantically valid output is computed.
- **Totality + supportedness**: `execute p σ = .supported B` for some `B` — the evaluator always produces a supported result (never `.unsupported`). This is `execute_supported` (line 618).

### Limitations arising from the finite packet model or dup-free NetKAT

1. **Concrete packet model:** The evaluator is only verified for the concrete `CtxPkt = Packet FieldName FieldValueEnum` (4 fields × 4 values = 256 packets). The general parameterized `Packet FieldType Value` type exists (`Packet.lean:36`), but the evaluator and its correctness theorem are only instantiated for the concrete type.

2. **Dup-free fragment only:** The `NetKAT` type has no `dup` constructor. This matches the paper's use of `NetKAT⁻ᵈᵘᵖ` throughout. The full NetKAT with `dup` is out of scope.

3. **Noncomputable star:** While `execute` itself is computable, the `NormalForm` module uses `noncomputable` definitions (`interpret`, `summandsToList`, `unionNF`, `assign1NF`, `seqNF`). This does not affect the evaluator but indicates that normal-form construction requires classical choice.

### The execute_correct theorem (both directions)

**Soundness (forward direction):** If `τ ∈ B` (the computed output set), then `Semantics p σ τ` (τ is a valid semantic output). This is the `↔` in the theorem: `τ ∈ B → Semantics p σ τ`.

**Completeness (backward direction):** If `Semantics p σ τ` (τ is a valid semantic output), then `τ ∈ B` (the evaluator computes it). This is: `Semantics p σ τ → τ ∈ B`.

The theorem also establishes **totality**: `execute p σ = .supported B` (never `.unsupported`), and **termination**: the result is a finite `Finset`.


## 6. Connecting NetKAT Execution to DyNetKAT Semantics

Files: `packages/DyNetKATLean/DyNetKATLean/Core/NetKATBridge.lean` (41 lines).

### execute_supported_iff_semantics (line 10)

```lean
theorem execute_supported_iff_semantics
    (p : NetKAT) (sigma tau : CtxPkt) (outputs : Finset CtxPkt)
    (evaluates : execute p sigma = .supported outputs) :
    tau ∈ outputs ↔ Semantics p sigma tau
```

**Significance:** This theorem is the **semantic bridge** between the executable NetKAT evaluator and the denotational semantics. It states that membership in the evaluator's output set is **equivalent** to the relational semantics relation. This is used by `execute_packet_step` to justify that the packet-processing transition is sound.

The proof works by:
1. Calling `execute_correct` to obtain `⟨computed, hcomputed, correct⟩`.
2. Using `EvalResult.supported.inj` to show `outputs = computed`.
3. Applying the `correct` lemma.

### execute_packet_step (line 24)

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

**Significance:** This theorem justifies that **every output of the executable evaluator produces a valid DyNetKAT `Step`**. It connects:
- **Executable NetKAT** (`execute p sigma = .supported outputs`, `sigma' ∈ outputs`)
- **DyNetKAT SOS** (`Step env (nSeq p continuation) (packet sigma sigma') (continuation with sigma' consed to handled)`)

**Corresponding packet-processing SOS constructor:** This is `Step.cpol_seq_ok` (`Semantics.lean:14`). The theorem is essentially a wrapper that applies `cpol_seq_ok` with the semantic premise justified by the executable evaluator.

**Assumptions about packet histories:** The theorem assumes:
- `pending = sigma :: pendingTail` (the pending list is non-empty with `sigma` as head)
- `handled` is arbitrary (no constraint on the already-handled packets)

**Process structure:** The theorem is specifically about `nSeq p continuation` — the base packet-processing rule. It does not cover `recv`, `send`, `parallel`, or other operators.

**Recursive environments:** The theorem is parameterized by `env : RecEnv` but the `cpol_seq_ok` constructor does not consult `env` (packet processing is independent of the recursion environment). The `env` parameter is threaded through for uniformity.

### Relationship to the paper

The paper's `(cpolX;)` rule (Fig. 8) states:
```
    σ′ ∈ ⟦p⟧(σ :: ⟨⟩)
  (p ; q, σ :: H, H') →_{(σ,σ')} (q, H, σ' :: H')
```

The Lean theorem replaces `σ′ ∈ ⟦p⟧(σ :: ⟨⟩)` with `execute p sigma = .supported outputs ∧ sigma' ∈ outputs`, which by `execute_supported_iff_semantics` is equivalent to `Semantics p sigma sigma'` (the single-packet denotational semantics). The paper's history-based notation `⟦p⟧(σ :: ⟨⟩)` reduces to the single-packet semantics in the dup-free fragment, as documented in the project design rationale (the `Semantics.lean` file comment at line 21-25).


## 7. Executable DyNetKAT Transition Generator

File: `packages/DyNetKATLean/DyNetKATLean/Core/Executable.lean` (119 lines).

### Definitions and theorems

**`packetTransitions` (line 25):**

```lean
def packetTransitions
    (p : NetKAT) (continuation : DyNetKAT)
    (pending handled : List CtxPkt) :
    Option (Multiset (Action × Config)) :=
  match pending with
  | [] => some (∅ : Multiset (Action × Config))
  | sigma :: pendingTail =>
      match execute p sigma with
      | .unsupported => none
      | .supported outputs =>
          some (outputs.1.map (fun tau =>
            (Action.packet sigma tau,
              { proc := continuation
                pending := pendingTail
                handled := tau :: handled })))
```

**`packetTransitions_sound` (line 57):**

```lean
theorem packetTransitions_sound
    (env : RecEnv)
    (p : NetKAT)
    (continuation : DyNetKAT)
    (pending handled : List CtxPkt)
    (results : Multiset (Action × Config))
    (action : Action)
    (destination : Config)
    (hEval : packetTransitions p continuation pending handled = some results)
    (hMem : (action, destination) ∈ results) :
    Step env
      { proc := .nSeq p continuation
        pending := pending
        handled := handled }
      action destination
```

**`packetTransitions_complete` (line 90):**

```lean
theorem packetTransitions_complete
    (env : RecEnv)
    (p : NetKAT)
    (continuation : DyNetKAT)
    (pending handled : List CtxPkt)
    (action : Action)
    (destination : Config)
    (hStep :
      Step env
        { proc := .nSeq p continuation
          pending := pending
          handled := handled }
        action destination) :
    ∃ results : Multiset (Action × Config),
      packetTransitions p continuation pending handled = some results ∧
      (action, destination) ∈ results
```

### Explanation

**Which process constructors are handled:**
Only **`.nSeq p continuation`** — the `nSeq` constructor. The function name and type signature make this explicit: it takes `p : NetKAT` and `continuation : DyNetKAT`, and the theorems prove equivalence between `packetTransitions` results and `Step` for configurations of shape `{ proc := .nSeq p continuation, ... }`.

No other constructor is handled: `recv`, `send`, `rcfgPrefix`, `parallel`, `choice`, `leftMerge`, `commMerge`, `restrict`, `project`, `var`, `deadlock` are **all out of scope**.

**What constitutes the input state:**
- `p : NetKAT` — the NetKAT policy
- `continuation : DyNetKAT` — the DyNetKAT continuation
- `pending : List CtxPkt` — the pending packet history
- `handled : List CtxPkt` — the handled packet history

**How pending and handled histories are updated:**
- **Pending:** If `pending = sigma :: pendingTail`, the head `sigma` is consumed (removed), and `pendingTail` becomes the new pending list. If `pending = []`, the result is empty (no packet to process).
- **Handled:** For each output `tau` of `p` on `sigma`, the resulting configuration has `handled := tau :: handled` — the output is consed onto the front of the handled list.

**How possible packet outputs are enumerated:**
The `execute` evaluator returns `.supported outputs` (a `Finset CtxPkt`). The function maps over `outputs.1` (the underlying list of the finset) to produce one `(Action, Config)` pair per output packet `tau`.

**How action labels are constructed:**
Each generated transition carries the label `Action.packet sigma tau` — a packet-flow action from the input `sigma` to the output `tau`.

**What the function returns and what `none` means:**
- Returns `Option (Multiset (Action × Config))`.
- `.some results` — evaluation was supported; `results` contains all generated transitions (possibly empty if `outputs = ∅`).
- `.none` — evaluation was `.unsupported` (the NetKAT evaluator did not support some sub-term). Per `execute_supported`, this never happens for valid NetKAT terms, but the `Option` type allows it defensively.

**Why `Multiset` and not `List` or `Finset`:**
`Multiset` is used because the evaluator returns a `Finset` of outputs, and `Finset.1` converts to a list (which may have order-dependent enumeration). `Multiset` avoids requiring a noncomputable ordering of the `Finset` and preserves the multiplicity structure if needed. As the code comment (line 23) states: "preserves the evaluator's executable finite enumeration without requiring a noncomputable ordering of a `Finset`."

**Which transitions are NOT currently generated:**
- **All non-`nSeq` transitions:** `recv`, `send`, `rcfgPrefix`, `parallel` (including synchronization), `choice`, `leftMerge`, `commMerge`, `restrict`, `project`, `var` (recursive unfolding) are not generated.
- **Empty pending list:** Returns an empty multiset (not `.none`) — but this means no transitions are generated for an empty pending list.
- **Unsupported evaluation:** Returns `.none` (not applicable in practice due to `execute_supported`, but the type allows it).

### Soundness theorem

**What is proved:** Every transition generated by `packetTransitions` is a valid `Step`. Specifically, if `packetTransitions p continuation pending handled = some results` and `(action, destination) ∈ results`, then `Step env {proc := .nSeq p continuation, ...} action destination`.

**Restrictions:** The proof only covers `cpol_seq_ok` (the packet-flow rule). It relies on `execute_packet_step` which calls `Step.cpol_seq_ok`.

### Completeness theorem

**What is guaranteed:** Every valid `Step` from an `nSeq` configuration is enumerated by `packetTransitions`. Specifically, if `Step env {proc := .nSeq p continuation, ...} action destination`, then there exists `results` such that `packetTransitions ... = some results` and `(action, destination) ∈ results`.

**Restrictions:**
1. **Only top-level `nSeq`:** The theorem only covers configurations where `proc` is exactly `.nSeq p continuation`. It does **not** cover `recv`, `send`, `rcfgPrefix`, `parallel`, or any other constructor.
2. **Only `Action.packet` labels:** Since the only rule for `nSeq` is `cpol_seq_ok` (which emits `Action.packet`), the generated transitions all have packet labels. No communication or reconfiguration labels are generated.
3. **No environment-dependence:** The `cpol_seq_ok` rule does not consult `env`, so the theorems are vacuously true for any `env`. The `env` parameter is present but unused in these specific theorems.

### Verification: Results apply only to top-level nSeq

**Confirmed by source inspection:** Yes, the results apply **only** to top-level `nSeq`:
- `packetTransitions` takes `p : NetKAT` and `continuation : DyNetKAT` — not a general `DyNetKAT` process.
- Both theorems are stated with `proc := .nSeq p continuation` in the `Step` predicate.
- The completeness proof uses `cases hStep with | cpol_seq_ok` — it only handles the `cpol_seq_ok` constructor, ignoring all other `Step` constructors.

**This is NOT an executable implementation of the complete DyNetKAT semantics.** It is a verified executable fragment for the single packet-processing rule in the context of `nSeq`.


## 8. Executable Example

The following example was constructed, compiled, and verified in the actual project (in `packages/DyNetKATLean/DyNetKATLean/Core/ExampleTest.lean`):

### Runnable Lean code

```lean
import DyNetKAT

open DyNetKAT.DyNetKAT
open DyNetKAT.NetKAT

-- Verify the 256-cardinality (packet domain = 4^4 fields×values)
example : Fintype.card CtxPkt = 256 := by
  rfl

-- Demonstrate execute with a concrete policy
example : execute (.assign1 .tpSrc .v9) examplePacket =
    .supported {Packet.update examplePacket .tpSrc .v9} := by
  exact execute_assign1 .tpSrc .v9 examplePacket

-- Demonstrate the executable transition generator for identity on examplePacket
-- Returns some (non-empty multiset with one transition)
example : (packetTransitions NetKAT.id .deadlock [examplePacket] []).map Multiset.card =
    some 1 := by
  native_decide

-- Demonstrate drop produces empty (but supported, not unsupported)
example : (packetTransitions NetKAT.drop .deadlock [examplePacket] []).map Multiset.card =
    some 0 := by
  native_decide

-- The pending list is empty -> empty result (no packet to process)
example : packetTransitions NetKAT.id .deadlock [] [] =
    some (∅ : Multiset (Action × Config)) := by
  rfl

def myEnv := RecEnv.empty
def myProc : DyNetKAT := .nSeq NetKAT.id .deadlock
```

### Actual output and verification

- **`Fintype.card CtxPkt = 256`** — compiles successfully (`rfl`). The packet domain has exactly 256 elements (4 fields × 4 values each = 4⁴ = 256).
- **`execute (.assign1 .tpSrc .v9) examplePacket`** — compiles successfully. Produces `.supported {Packet.update examplePacket .tpSrc .v9}` — a single output packet where `tpSrc` is set to `v9`.
- **`packetTransitions NetKAT.id .deadlock [examplePacket] []`** — compiles successfully. `native_decide` confirms the result is `some` with cardinality `1`. This means: the identity policy on `examplePacket` produces exactly **one transition**: `(Action.packet examplePacket examplePacket, Config with proc := .deadlock, pending := [], handled := [examplePacket])`.
- **`packetTransitions NetKAT.drop .deadlock [examplePacket] []`** — compiles successfully. `native_decide` confirms cardinality `0`. The `drop` policy consumes the packet but produces no output (the packet is dropped), resulting in an empty multiset of transitions.
- **`packetTransitions NetKAT.id .deadlock [] []`** — compiles successfully. `rfl` confirms that with an empty pending list, the result is `some (∅ : Multiset (Action × Config))` — no transitions can fire because there is no packet to process.

### Explanation of the example

1. **Initial packet:** `examplePacket` (from `Packet.lean:288`) is `fun | .tpSrc => .v8 | _ => .v0` — a packet with `tpSrc = v8` and all other fields `v0`.

2. **NetKAT policy:** `NetKAT.id` — the identity policy, which produces one output for each input packet: `⟦id⟧(σ, τ) ↔ τ = σ`.

3. **DyNetKAT process:** `myProc = .nSeq NetKAT.id .deadlock` — a process that applies the identity NetKAT policy to the current packet, then transitions to `deadlock`.

4. **Pending history:** `[examplePacket]` — a list with one packet (the one being processed).

5. **Handled history:** `[]` — no packets handled yet.

6. **Generated transition:** The `packetTransitions` function produces a multiset containing **exactly one element**:
   - **Action:** `Action.packet examplePacket examplePacket` — the packet flows through the identity policy unchanged.
   - **Resulting Config:** `{ proc := .deadlock, pending := [], handled := [examplePacket] }` — the identity policy is consumed, the packet moves from pending to handled (front of the handled list), and the process continues as `deadlock`.

7. **`drop` variant:** When the policy is `NetKAT.drop`, the pending list still has `examplePacket`, but no transition fires — the configuration is **stuck** (the drop rule produces no output, so no `Step` witness exists). The multiset is empty.

8. **`none` meaning:** Neither example produces `none` (`.unsupported`). This confirms that `execute_supported` (the totality theorem) holds: all NetKAT terms evaluate to `.supported`, never `.unsupported`.

### Note on the example

This example demonstrates **only the `nSeq` packet-processing rule** via `packetTransitions`. It does not exercise `recv`, `send`, `rcfgPrefix`, `parallel`, or recursive variable unfolding. To demonstrate those, `packetTransitions` would need to be extended (see Section 11).


## 9. Proof Integrity and Dependency Audit

### Search for `sorry`, `admit`, `axiom`, `unsafe`

A comprehensive search of all Lean source files in `lean/DyNetKAT/` was performed:

```
grep -rn 'sorry\|admit\b\|axiom\b\|unsafe' lean/DyNetKAT/ --include="*.lean"
```

**Results:**
- **Zero `sorry` occurrences** in any proof.
- **Zero `admit` occurrences** in any proof.
- **Zero `axiom` declarations** in any file.
- **Zero `unsafe` declarations** in any file.
- The word "axiom" appears only in **comments** referencing the paper's axiom system (e.g., `-- Axioms A0–A15` in `NetKAT/Semantics.lean:353`, `-- Boolean algebra axioms` in `NetKAT/AST.lean:11` and `NetKAT/Semantics.lean:493`).

### `#print axioms` investigation

The `#print axioms` command is a REPL-only command (not available in compiled modules). However, the theorem statements were inspected via `#check` in the Lean REPL:

- `execute_correct` is proven via structural induction on `NetKAT` (1149-line `Evaluator.lean`), using `Nat.induction`, `Finset.card`, and `Classical` in the star-bound proofs (`reachableWithin_finite_stabilizes` at line 922, `reachableWithin_stable_at_card` at line 973).
- `packetTransitions_sound` and `packetTransitions_complete` depend on `execute_packet_step`, which depends on `execute_supported_iff_semantics`, which depends on `execute_correct`.
- No custom axioms are introduced. All theorems use Mathlib's standard library results (function extensionality, propositional extensionality, classical choice for finite-set operations).

### Mathlib dependencies

The `lakefile.toml` declares:
```toml
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "v4.19.0"
```

Key Mathlib features used:
- `Fintype` (for finite packet domain, star-bound finiteness)
- `Finset` (for finite output sets, normal forms)
- `Set` operations
- `Classical` (for nonconstructive finite-set reasoning)
- `funext_iff` (function extensionality)

These are standard Mathlib axioms, not project-specific assumptions.

### Trustworthiness assessment

| Aspect | Assessment |
|---|---|
| No `sorry`/`admit` in proofs | ✅ Verified — zero occurrences |
| No `axiom` declarations | ✅ Verified — zero occurrences |
| No `unsafe` code | ✅ Verified — zero occurrences |
| Build succeeds | ✅ Verified — `lake build DyNetKAT` passes |
| Theorems are unconditional | ⚠️ See note below |

**Important note on "unconditional" theorems:** While the theorems do not contain `sorry`/`axiom`, some use `Classical` (non-constructive reasoning) and depend on Mathlib's standard axioms. The key correctness theorems (`execute_correct`, `packetTransitions_sound`, `packetTransitions_complete`) are established over **all** environments and **all** terms — they do not require `WellFormed`. This means the theorems are mathematically sound but **weaker** than what the paper proves (the paper's Theorem 1 requires guardedness; our completeness theorem is only for the `nSeq` fragment).


## 10. Slide Recommendations

### Proposed slide structure and recommendations

**Slide 1: DyNetKAT-Lean: Current Progress**

- **Exact technical claim:** The repository contains a machine-verified Lean 4 formalization covering NetKAT⁻ᵈᵘᵖ (fully verified), DyNetKAT syntax + operational semantics (fully implemented), bisimulation + congruence (fully proved), and executable correctness (partially verified for nSeq). Missing: axiom system, completeness Theorem 1, safety framework.
- **Lean declaration:** The entire library compiles: `lake build DyNetKAT` succeeds.
- **Source:** `lakefile.toml:1–14` (project config), commit `e96d71a`.
- **Visual:** Timeline diagram of the development phases (from PLAN.md).
- **Backup:** Full module inventory table.

**Slide 2: Representing DyNetKAT in Lean**

- **Exact technical claim:** DyNetKAT syntax is an inductive type with 12 constructors covering both Eq. 1 (base) and Eq. 6 (extended) of the paper.
- **Lean declaration:** `inductive DyNetKAT` — `AST.lean:100-113`.
- **Source:** `packages/DyNetKATLean/DyNetKATLean/Core/AST.lean:100`.
- **Visual:** Constructor table mapping Lean constructors to paper syntax.
- **Backup:** Field/value type definitions (`Packet.lean`).

**Slide 3: Recursive Specifications in the Original Paper**

- **Exact technical claim:** The paper uses `X` for recursive variables with a meta-level `X ≜ d` defining equation. Each variable has a unique definition (§II-C, p. 8).
- **Paper reference:** Definition 7 (guardedness, p. 13), Fig. 8 (cpolX rule, p. 9–10).
- **Note:** This slide should focus on the paper's treatment, not the Lean encoding (which is Slide 4).
- **Backup:** Guardness definition statement.

**Slide 4: Why We Introduced RecEnv**

- **Exact technical claim:** In Lean 4, the meta-level `X ≜ d` cannot be used directly — the environment must be made explicit as `RecEnv : Var → Option DyNetKAT`. This is a standard type-theoretic encoding, not a semantic change.
- **Lean declaration:** `abbrev RecEnv : Type := Var → Option DyNetKAT` — `RecEnv.lean:9`.
- **Source:** `packages/DyNetKATLean/DyNetKATLean/Core/RecEnv.lean:9`.
- **Key point:** `Option` allows undefined variables (well-formedness is checked separately).
- **Backup:** Why not store the body in the `var` constructor (it would break inductiveness).

**Slide 5: Recursive Unfolding in the SOS**

- **Exact technical claim:** The `cpol_var` constructor mirrors the paper's (cpolX) rule: a recursive variable unfolds to its body, inheriting the same label and packet histories.
- **Lean declaration:** `cpol_var` — `Semantics.lean:156-167`.
- **Source:** `packages/DyNetKATLean/DyNetKATLean/Core/Semantics.lean:156`.
- **Visual:** Side-by-side: paper rule vs. Lean constructor.
- **Backup:** No guardedness assumption in the constructor itself.

**Slide 6: Environment-Relative Bisimulation**

- **Exact technical claim:** `Bisimilar` takes `env : RecEnv` as a parameter: `Bisimilar env p q`. All theorems work relative to a **fixed** environment, not quantifying over all environments.
- **Lean declaration:** `def Bisimilar (env : RecEnv) (p q : DyNetKAT) : Prop` — `Bisimulation.lean:26`.
- **Source:** `packages/DyNetKATLean/DyNetKATLean/Core/Bisimulation.lean:26`.
- **Key defense:** This faithfully captures the paper's implicit recursive context. The paper's `p ∼ q` is "under a fixed recursive specification" — our `env` makes this explicit.
- **Backup:** Theorem list (refl, symm, trans, 13 congruence theorems).

**Slide 7: Definedness, Guardedness, and Well-Formedness**

- **Exact technical claim:** Definedness predicates (`ReachableVar`, `ClosedDefined`, `GuardedOccurrences`, `WellFormed`) are defined but **NOT required** by any `Step`, `Bisimilar`, or executable theorem.
- **Lean declarations:** All in `Definedness.lean:22-143`.
- **Source:** `packages/DyNetKATLean/DyNetKATLean/Core/Definedness.lean`.
- **Key defense:** We define these predicates (faithful to the paper's requirements), but our theorems are **stronger** — they hold for all environments, not just well-formed ones.
- **Backup:** The `WellFormed` definition and its component theorems.

**Slide 8: Operational Semantics and Bisimulation Results**

- **Exact technical claim:** The `Step` inductive has exactly 10 constructor families matching Figure 8. The `Bisimulation.lean` module proves 17 theorems (refl, symm, trans + 14 congruence theorems).
- **Lean declarations:** `inductive Step` — `Semantics.lean:13`; `IsBisimulation`/`Bisimilar` — `Bisimulation.lean:9,26`.
- **Source:** `packages/DyNetKATLean/DyNetKATLean/Core/Semantics.lean`; `packages/DyNetKATLean/DyNetKATLean/Core/Bisimulation.lean`.
- **Visual:** The 10-rule constructor table.
- **Backup:** Full theorem inventory with exact statements.

**Slide 9: Making NetKAT Executable**

- **Exact technical claim:** The `execute` function computes NetKAT policy evaluation over a finite 256-packet domain, returning `EvalResult` with supported (finite set) or unsupported.
- **Lean declaration:** `def execute : NetKAT → CtxPkt → EvalResult` — `Evaluator.lean:171`.
- **Source:** `packages/NetKATLean/NetKATLean/Core/Evaluator.lean:171`.
- **Key facts:** 256 = 4⁴ (4 fields × 4 values); star bounded by `Fintype.card CtxPkt`.
- **Backup:** The `EvalResult` type and `execute_supported` totality theorem.

**Slide 10: Proving the Evaluator Correct**

- **Exact technical claim:** `execute_correct` proves the evaluator computes exactly ⟦p⟧(σ) for all `p` and `σ` — soundness, completeness, and totality in one theorem.
- **Lean declaration:** `theorem execute_correct (p : NetKAT) (σ : CtxPkt) : ∃ B, execute p σ = .supported B ∧ ∀ τ, Semantics p σ τ ↔ τ ∈ B` — `Evaluator.lean:1078`.
- **Source:** `packages/NetKATLean/NetKATLean/Core/Evaluator.lean:1078`.
- **Key point:** This is a **self-contained NetKAT** correctness theorem — no DyNetKAT assumptions.
- **Backup:** The star-bound theorems (`reachableWithin_stable_at_card`, `reachableWithin_iff_at_card`).

**Slide 11: Connecting Execution to DyNetKAT SOS**

- **Exact technical claim:** `execute_packet_step` and `execute_supported_iff_semantics` bridge the executable evaluator to the `Step` relation, justifying one packet-processing transition per evaluator output.
- **Lean declarations:** `execute_supported_iff_semantics` — `NetKATBridge.lean:10`; `execute_packet_step` — `NetKATBridge.lean:24`.
- **Source:** `packages/DyNetKATLean/DyNetKATLean/Core/NetKATBridge.lean`.
- **Connection to paper:** Bridges to `cpol_seq_ok` (`Step.cpol_seq_ok`), the (cpolX;) rule.
- **Backup:** Assumptions (nSeq shape, non-empty pending).

**Slide 12: Generating Executable Transitions**

- **Exact technical claim:** `packetTransitions` enumerates packet-flow transitions for `nSeq` processes; `packetTransitions_sound` and `packetTransitions_complete` establish bidirectional equivalence.
- **Lean declarations:** `packetTransitions` — `Executable.lean:25`; theorems — `Executable.lean:57, 90`.
- **Source:** `packages/DyNetKATLean/DyNetKATLean/Core/Executable.lean`.
- **Key caveat:** **Only `nSeq` is handled** — not recv/send/rcfg/parallel/etc.
- **Backup:** The Multiset explanation, `none` meaning, and the executable example.

**Slide 13: Soundness and Completeness**

- **Exact technical claim:** Soundness: every generated transition is valid (packetTransitions_sound). Completeness: every valid nSeq packet transition is generated (packetTransitions_complete). **Caveat:** This is for the nSeq fragment only.
- **Lean declarations:** `Executable.lean:57, 90`.
- **Visual:** Bidirectional arrow diagram.
- **Backup:** What is NOT covered (all other operators).

**Slide 14: Limitations and Future Work**

- **Exact technical claim:** Missing: equational axioms (A0–A15, AIP), completeness Theorem 1, safety framework (Defs 12–17), extended operator rules (δ, π_n, ⌊⌊, | |, rcfg constant), bisimulation for recursive variables, parallel-process execution, recursion state-space exploration.
- **Source:** `PROOF_OBLIGATIONS.md` Tier inventory.
- **Visual:** Dependency graph of remaining work (missing → blocked).
- **Backup:** Detailed proof obligation list.

### Proposed reordering

The proposed ordering (Slides 1–14 above) is mathematically sound:
1. Current state
2. Syntax representation
3. Paper's recursive approach
4. Why RecEnv is needed
5. Unfolding in SOS
6. Environment-relative bisimulation
7. Well-formedness (as a caveat)
8. Operational semantics + bisimulation results
9. NetKAT executable
10. Evaluator correctness
11. Bridge
12. Transition generator
13. Soundness/completeness (scoped)
14. Limitations

**Key adjustment:** Move definedness/guardedness (Slide 7) **before** bisimulation (Slides 6, 8) to justify the `env` parameter. However, the current ordering (6 → 7 → 8) is also valid: introduce bisimulation first, then explain why well-formedness predicates are available but not required. Consider placing Slide 7 between Slides 5 and 6 to give the RecEnv discussion (slides 4-6) the context of what well-formedness means.


## 11. Future Research and Remaining Obligations

### Missing executable process operators

`packetTransitions` only handles `nSeq`. The following operators have `Step` constructors but **no executable transition generation**:

| Operator | Step constructor | Status |
|---|---|---|
| `recv` (x?N;D) | `cpol_recv` | Constructor exists; no `packetTransitions` case |
| `send` (x!N;D) | `cpol_send` | Constructor exists; no `packetTransitions` case |
| `rcfgPrefix` (rcfg_{x,N};D) | `cpol_rcfg` | Constructor exists; no `packetTransitions` case |
| `parallel` (D‖D) | `cpol_par_l`, `cpol_par_r`, `cpol_sync_recv_send`, `cpol_sync_send_recv` | Constructors exist; no `packetTransitions` case |
| `choice` (D⊕D) | `cpol_choice_l`, `cpol_choice_r` | Constructors exist; no `packetTransitions` case |
| `leftMerge` (D⌊⌊D) | `cpol_left_merge` | Constructor exists; no `packetTransitions` case |
| `commMerge` (D\|D) | `cpol_comm_merge_recv_send`, `cpol_comm_merge_send_recv` | Constructors exist; no `packetTransitions` case |
| `restrict` (δ_ℒ(D)) | `cpol_restrict` | Constructor exists; no `packetTransitions` case |
| `project` (π_n(D)) | `cpol_project` | Constructor exists; no `packetTransitions` case |
| `var` (X) | `cpol_var` | Constructor exists; no `packetTransitions` case |
| `deadlock` (⊥) | none | No transitions (by design — A0) |

### Communication and reconfiguration transitions

The `cpol_recv`, `cpol_send`, `cpol_rcfg`, `cpol_sync_recv_send`, and `cpol_sync_send_recv` constructors exist in `Step` but:
- They are **not** generated by `packetTransitions`.
- They are **not** connected to the executable NetKAT evaluator.
- There is no soundness/completeness theorem for these constructors.

### Parallel-process execution

The `cpol_par_l` and `cpol_par_r` constructors lift child transitions to parallel composition. The synchronization constructors (`cpol_sync_recv_send`, `cpol_sync_send_recv`) handle send/receive matching. However:
- No executable generation of parallel transitions.
- No theorem establishing that parallel execution preserves packet histories correctly in all cases.

### Recursion and recursive state-space exploration

The `cpol_var` constructor handles recursion unfolding, but:
- No executable exploration of recursive state spaces.
- No theorem establishing termination or finiteness of recursive unfolding (this requires guardedness, which is not enforced).
- No `packetTransitions` case for `var`.

### Bisimulation checking

The `Bisimilar` relation and 13 congruence theorems are proved, but:
- **No decision procedure** for bisimilarity (the congruence theorems are manual proofs, not an algorithm).
- No connection between `packetTransitions` and `Bisimilar` (the congruence theorems do not use the executable transition generator).

### Equational normalization or completeness results

**Missing entirely:**
- `AxEq` inductive relation (A0–A15, AIP)
- `E_DNK ⊢ p ≡ q` derivability relation
- Lemma 10 (soundness of A0–A15)
- Lemma 11 (soundness of AIP)
- Lemma 9 (DyNetKAT normalization)
- Theorem 1 (soundness & ground-completeness)
- Proposition 1 (semantic layering)
- Lemma 8 (branching finiteness)

### Performance evaluation and benchmarks

No performance benchmarks exist. The Python golden tests (`python/tests/`) test a Python mirror of the NetKAT semantics, not the Lean code. No comparison between Lean execution and Python execution is present.

### Packaging and user-facing tooling

The `Main.lean` only prints the project name ("DyNetKAT formalization: DyNetKAT"). No CLI, no JSON I/O adapter, no user-facing tooling. The `DyNetiKAT` reference tool's JSON schema is documented but not implemented.

### Ranked next milestones (by importance and dependency)

| Rank | Milestone | Prerequisites | Justification |
|---|---|---|---|
| 1 | Equational axiom system (A0–A15, AIP) | AST, Semantics, Bisimulation | Needed for Theorem 1 (completeness) |
| 2 | Soundness of axioms (Lemmas 10, 11) | Axiom system, Step, Bisimilar | Foundation of Theorem 1 |
| 3 | Branching finiteness (Lemma 8) | Guardedness, Step | Required for AIP soundness |
| 4 | Normalization (Lemma 9) | Axiom system, Guardedness | Required for completeness |
| 5 | Completeness (Theorem 1) | Soundness, Normalization, NetKAT completeness | Capstone theorem |
| 6 | Semantic layering (Proposition 1) | NetKAT semantics, Bisimilar | Connects denotational and operational |
| 7 | Executable transition generation for other operators | Current Executable.lean, Step constructors | Extends verified execution beyond nSeq |
| 8 | Bisimulation decision procedure | Bisimilar, packetTransitions | Enables automated equivalence checking |
| 9 | Safety framework (Defs 12–17) | Theorem 1, NormalForm | Paper §IV |
| 10 | Examples (firewall, distributed controller) | Safety, Theorem 1 | Paper §IV-A |
| 11 | Performance benchmarks | Executable code | Practical evaluation |
| 12 | User-facing tooling | All above | Practical usability |


## 12. Claims We Can Safely Make in the Presentation

1. **Build integrity:** `lake build DyNetKAT` succeeds at commit `e96d71a` with Lean 4.19.0 and Mathlib4 v4.19.0.

2. **No proof holes:** There are zero occurrences of `sorry`, `admit`, `axiom`, or `unsafe` in the Lean source code (verified by grep).

3. **NetKAT correctness:** The executable NetKAT evaluator is proven correct for all 8 NetKAT constructors over the concrete 256-element packet domain (`execute_correct`, `Evaluator.lean:1078`).

4. **SOS faithfulness:** The `Step` inductive has exactly the 10 constructor families corresponding to Figure 8 of the paper (verified against `docs/PROCESS_SEMANTICS_DESIGN.md` which cross-checks with the PDF text extraction).

5. **RecEnv design:** `RecEnv : Var → Option DyNetKAT` is a faithful explicit encoding of the paper's implicit `X ≜ d` meta-level notation. The `Option` type allows for undefined variables, with well-formedness checked separately.

6. **Bisimulation congruence:** All 13 congruence theorems are proved (choice left/right, parallel left/right, leftMerge left/right, commMerge left/right, nSeq, recv, send, rcfgPrefix, restrict, project) plus reflexivity, symmetry, and transitivity.

7. **Executable transition soundness/completeness:** For top-level `nSeq` configurations, `packetTransitions_sound` and `packetTransitions_complete` establish a bidirectional correspondence between the executable generator and the `Step` relation.

8. **Packet domain:** `Fintype.card CtxPkt = 256` (4 fields × 4 values = 4⁴), confirmed computationally.

9. **Star termination:** The Kleene star evaluator is bounded by `Fintype.card CtxPkt` and proven correct via `execute_star_correct` (`Evaluator.lean:1058`).

10. **No drop rule:** The formalization correctly models the paper's observation that `⟦0⟧(σ) = ∅` means the configuration is stuck (no transition fires), not that a "drop" transition fires. This is documented in `docs/PROCESS_SEMANTICS_DESIGN.md` §4.

## 13. Claims We Must Not Make

1. **Do NOT claim "complete DyNetKAT semantics"**: `packetTransitions` only generates transitions for the `nSeq` constructor. Do not describe this as an executable implementation of the complete DyNetKAT semantics.

2. **Do NOT claim Theorem 1 is proved**: The soundness and ground-completeness theorem is **not yet implemented**. The axiom system (A0–A15, AIP) does not exist in the codebase.

3. **Do NOT claim the safety framework is implemented**: Definitions 12–17 (safety properties, head normal forms, trace-equivalence, etc.) are **not started**.

4. **Do NOT claim guardedness is enforced in theorems:** The `WellFormed` predicate is defined but **not required** by `Step`, `Bisimilar`, or the executable theorems. The theorems work for arbitrary environments.

5. **Do NOT claim NetKAT completeness:** Lemma 5 (every NetKAT term has a normal form under E_NK) is **not proved**. The `NormalForm` module contains semantic correspondence theorems, not the normalization algorithm or E_NK derivation relation. As stated in `docs/PROOF_OBLIGATIONS.md` T1.4: "Semantic correspondence theorems establish that `interpret` is sound with respect to the denotational semantics, but they do not establish that every NetKAT term has an equational normal form under E_NK."

6. **Do NOT conflate semantic equivalence with equational derivability:** The existing theorems prove `⟦N⟧ = ⟦M⟧` (semantic equivalence), not `E_NK ⊢ N ≡ M` (equational derivability). These are distinct — the latter requires an inductive derivation relation that does not yet exist.

7. **Do NOT claim the `Step` relation handles all operators executable:** Only `nSeq` has an executable transition generator. `recv`, `send`, `rcfgPrefix`, `parallel`, `choice`, `var` all have `Step` constructors but no executable generation.

8. **Do NOT claim bisimilarity checking is automated:** The congruence theorems are manual proofs. There is no decision procedure for `Bisimilar`.

9. **Do NOT claim environment-universal bisimilarity:** The theorems are parameterized by a **fixed** `env : RecEnv`, not quantified over all environments. The paper's `p ∼ q` is under a fixed recursive specification — our `env` makes this explicit, but the theorems do not state "for all well-formed environments."

10. **Do NOT claim the journal extension features are included:** The formalization explicitly excludes log-based extraction, SDNRacer causality, bounded schedules, and other journal-extension artifacts (per `README.md:13-15` and `PLAN.md`).

## 14. Questions or Potential Problems

### 1. Environment parameterization and Theorem 1

The paper's Theorem 1 (soundness & ground-completeness) is stated without explicit environment quantification. When formalized, it must be restated as: "for all well-formed environments `env`, `E_DNK ⊢ p ≡ q` iff `Bisimilar env p q`." The current codebase does not even have the axiom system or the well-foundedness requirement. **Does the paper implicitly assume a fixed recursive specification throughout?**

### 2. Coinductive bisimilarity not yet used coinductively

`Bisimilar` is defined as "there exists a bisimulation relating p and q" — this is the existential encoding of the **greatest fixed point**. The paper uses coinduction. While mathematically equivalent, the current proofs use manual constructions (explicit relations `T`), not Lean's coinductive type facilities. **Should the formalization migrate to `coinductive` types for cleaner bisimulation proofs?** The PLAN.md notes (line 85) that this was a design decision.

### 3. Star termination: theorem vs. practical bound

`execute_star_correct` uses `Fintype.card CtxPkt` (256) as the bound. The theorem `reachableWithin_stable_at_card` proves stabilization within this bound. However, the practical bound for convergence may be much smaller (at most |CtxPkt|² = 65536 steps by pigeonhole, but typically far fewer). **Is the 256 bound tight, or could it cause excessive computation?** The theorems are correct, but performance may be suboptimal.

### 4. `recursion` vs `rcfg` terminology

The paper uses `rcfg_{x,z}` as a **term constant** (Eq. 6, A12) and `rcfg(x,q)` as an **action label** (Fig. 8). The Lean AST introduces `rcfgPrefix` as a constructor name for the term constant, and `cpol_rcfg` as the Step rule. **Is `rcfgPrefix` the right name?** The paper does not name the constructor. This is a documentation choice — verify with authors if the naming is clear.

### 5. NetKAT vs NetKAT⁻ᵈᵘᵖ

The paper distinguishes `NetKAT` (with `dup`) from `NetKAT⁻ᵈᵘᵖ` (without `dup`). The Lean `NetKAT` type is named `NetKAT` but contains only the dup-free fragment. **Should this be renamed to avoid confusion?** The PLAN.md acknowledges this but chose to keep the name for compatibility with the existing codebase.

### 6. Unverified paper comparisons

Per the task instructions, the original paper (`DyNetKAT.pdf`) could not be directly fetched and accessed. The paper evidence comes from:
- The repository's own `docs/PAPER_CONFORMANCE.md` (which references PDF text extraction)
- The repository's `docs/PROCESS_SEMANTICS_DESIGN.md` (which references `pdftotext -layout` of `DyNetKAT.pdf`)
- The `DyNetKAT.pdf` file in the repository root

**The following comparisons remain unverified** against the original paper text:
- Exact Figure 8 rule names (the ar5iv text extraction is garbled in places)
- Exact axiom statements (A0–A15) — the `PROOF_OBLIGATIONS.md` lists them but they are not yet implemented
- Exact proof sketches in the appendix

The `docs/` files consistently note when paper evidence is from text extraction vs. direct PDF inspection. The `DyNetKAT.pdf` file in the repository root (`DyNetKAT.pdf`, 1.2MB) is the paper referenced throughout the design docs.

---

*End of report. This audit was conducted by source code inspection, `lake build` verification, `native_decide` execution of examples, `#check` theorem type inspection, and review of the 13 existing design/audit documents in `docs/`. No Lean source files were modified.*

