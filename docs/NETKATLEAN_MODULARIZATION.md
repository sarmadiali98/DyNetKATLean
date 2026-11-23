# NetKATLean build and import boundary

Use `import NetKATLean` and `lake build NetKATLean`. The core depends on generic KATLean, pinned Mathlib v4.19.0 and Lean's standard libraries. It shares the Lean 4.19.0 Lake workspace. The four packet adapters are NetKATLean-owned and now live under `lean/NetKATLean/PacketAdapter/`. They provide packet lookup and update, Boolean diagram operations used by the packet compiler, packet encoding and relational closure. Their module names changed to avoid Lean prefix shadowing. Their declaration namespaces remain unchanged.

## Core import graph

The table lists every core module and its direct project-local imports. Bare names denote modules in `DyNetKAT.NetKAT`. External Lean and Mathlib edges are omitted.

| Module | Imports |
| --- | --- |
| `NetKATLean` | `HistoryEvaluator`, `KATLean`, `NativeEquations`, `SymbolicDerives` |
| `AST` | `Packet` |
| `Axioms` | `Interpretation` |
| `Decision` | `Evaluator`, `HistorySemantics`, `Symbolic` |
| `Denotation` | `KATLean`, `Semantics` |
| `Evaluator` | `Semantics` |
| `History` | `Packet`, `AST` |
| `HistoryEvaluator` | `History`, `HistorySemantics`, `Evaluator` |
| `HistorySemantics` | `Packet`, `AST`, `History`, `Semantics` |
| `Interpretation` | `Denotation`, `Decision` |
| `KATLean` | `Interpretation`, `Normalization` |
| `NativeEquations` | `KATLean.Native.Completeness`, `Axioms` |
| `NormalForm` | `Packet`, `AST`, `Semantics` |
| `Normalization` | `NormalForm`, `Axioms`, `Symbolic` |
| `Packet` | `NetKATLean.PacketAdapter.Packet` |
| `Semantics` | `Packet`, `AST` |
| `Symbolic` | `NetKATLean.PacketAdapter.Closure`, `KATLean.Native`, `Denotation` |
| `SymbolicDerives` | `Symbolic`, `Normalization` |
| `NetKATLean.PacketAdapter.Closure` | `NetKATLean.PacketAdapter.Symbolic` |
| `NetKATLean.PacketAdapter.Guard` | `KATLean.Native.Boolean` |
| `NetKATLean.PacketAdapter.Packet` | `KATLean.Relation` |
| `NetKATLean.PacketAdapter.Symbolic` | `NetKATLean.PacketAdapter.Guard`, `NetKATLean.PacketAdapter.Packet` |

Packet and AST define schemas and policy syntax. Semantics, HistorySemantics, Evaluator and HistoryEvaluator cover packet and history execution. Denotation and Interpretation connect policies to KATLean relations. Axioms defines E_NK, NormalForm and Normalization provide canonical forms, Symbolic compiles policies and invokes the native solver, and NativeEquations and SymbolicDerives translate solver and equational results into NetKAT derivations. The NetKAT-local KATLean module remains a compatibility facade. The v1.1 syntax parser contains a reusable policy parser alongside dynamic process, event and selector parsing. It stays with the dynamic frontend for this milestone.

## Algebraic foundation

`Derives.katSound` interprets E_NK in `KATLean.Rel`. Choice associativity, commutativity, zero and idempotence use Mathlib laws on that instance. Sequential associativity, units, annihilators and both distributivity rules use the same instance. Star unfolding delegates to `KATLean.star_unfold_left/right`; least fixed point rules use `KATLean.star_induction_left_add/right_add`. The Boolean/test cases use KATLean test embedding, injectivity, lattice maps, distribution, excluded middle, commutation, contradiction and idempotence. Packet rules use the packet model. The relational proof delegates the generic laws. History soundness transfers packet soundness through the history semantics bridge. Syntax-level normalization still has local derivation combinators for bounded star and finite sums, which assemble E_NK proof terms. This milestone changes no theorem proofs.

## Optional tooling and tests

The default closure excludes KATch, BackendCertificate, EquationalCertificate and Legacy. External replay scripts stay outside the library. The exhaustive `legacyNetkatEquiv` and `legacyNormalize` implementations stay in Legacy; E_NK, symbolic equivalence and the active `normalize` do not import it. Core modules still expose concrete evaluation, finite normal-form inspection and finite packet/pair constructions needed by the existing API and proofs. In particular, symbolic normalization materializes accepted pairs, and this boundary does not promise enumeration-free normalization.

`test_decision.lean` and `test_netkat_axioms.lean` use the public umbrella. `test_symbolic_netkat.lean` checks the symbolic solver and compiler directly. `test_netkatlean_import.lean` uses the public packet model, checks a field update and its semantics, and exercises a derivation, its KATLean interpretation, normalization and symbolic equivalence. Mixed packet-schema and KATLean derivation tests remain higher-layer integration coverage. Tests that compare against Legacy or KATch remain optional or full-workspace checks.

`scripts/verify-netkatlean.sh` checks the recursive local import closure and runs the four NetKAT tests in scratch space against only those compiled local modules and the external dependency libraries. The consumer independently imports the public umbrella there. This exercises import isolation with built artifacts; independent packaging, source relocation, release metadata, CI and Docker remain future work.
