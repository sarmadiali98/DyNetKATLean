# NetKATLean build and import boundary

Use `import NetKATLean` and `lake build NetKATLean`. The standalone Lake package lives in `packages/NetKATLean/`. Its only direct package dependency is the sibling `../KATLean`. The core imports Mathlib modules directly and uses Mathlib transitively through KATLean's exact pin. Lean 4.19.0 and the complete transitive revisions are locked. The integration workspace imports this package via `../packages/NetKATLean`.

The four packet adapters now live in the package's `NetKATLean/PacketAdapter/` directory. They provide packet lookup and update, diagram operations used by the packet compiler, packet encoding and relational closure. The public umbrella imports all 17 core modules through their dependency closure. The physical move preserves declaration namespaces, including `DyNetKAT.NetKAT` and `KATLean.NetKAT`. Old core-module imports migrate directly to the new paths.

## Core import graph

The table lists every core module and its direct project-local imports. Bare names denote modules in `NetKATLean.Core`. Each of those 17 modules moved from `DyNetKAT.NetKAT.<name>` to `NetKATLean.Core.<name>`. External Lean and Mathlib edges are omitted.

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

The eight owned tests are `test_netkatlean_import.lean`, `test_netkat_axioms.lean`, `test_decision.lean`, `test_symbolic_netkat.lean`, `test_katlean.lean`, `test_history.lean`, `test_history_semantics.lean`, and `test_history_evaluator.lean`. The history tests now import the NetKATLean umbrella. Dynamic and optional-backend regression tests stay in the integration workspace.

Run `./verify.sh build`, `./verify.sh smoke`, `./verify.sh test-all`, `./verify.sh verify`, and `./verify.sh consumer-test` from the package root. Verification audits the NetKATLean and KATLean import trees. The consumer uses a fresh Lake project with a path dependency on NetKATLean and verifies Lake's source and object search paths. The integration wrapper `scripts/verify-netkatlean.sh` delegates to the package verifier.

For a full integration test sweep from fresh build artifacts, run `lake build DyNetKATLean DyNetKAT dynetkat +DyNetKAT.Experimental +DyNetKAT.NetKAT.Legacy` from `lean/` first. The explicit optional targets refresh the certificates and exhaustive regression backend used by integration tests. Lean generates private declaration names from their module paths, so proof dependency tests now follow `_private.NetKATLean.*` in addition to the existing prefixes. The tested proof-dependency assertions and the public theorem API are preserved.

The locked package build, smoke test, all eight tests, import audit and separate Lake consumer passed. The consumer exercised packet construction and semantics, an E_NK derivation, the relational interpretation, normalization and native equivalence. Clean network-backed resolution also passed on Ubuntu from disk-backed scratch under `$HOME/.cache`. See the [extraction plan](PACKAGE_EXTRACTION_PLAN.md#realized-netkatlean-extraction).
