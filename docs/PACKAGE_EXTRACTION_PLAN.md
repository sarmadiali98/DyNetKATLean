# Standalone Lean package extraction plan

This plan follows the three modularization audits. [KATLean](KATLEAN_MODULARIZATION.md) owns generic Kleene algebra with tests and the native KAT decision machinery. [NetKATLean](NETKATLEAN_MODULARIZATION.md) owns packet schemas, packet adapters, policy semantics, E_NK, symbolic equivalence and normalization. [DyNetKATLean](DYNETKATLEAN_MODULARIZATION.md) owns the admissible dynamic source and residual domain, SOS, E_DNK and certified analysis. The default closures exclude the frontend, historical tool and benchmark infrastructure.

## Realized KATLean extraction

The package root is `packages/KATLean/`, physically separate from the integration workspace under `lean/` and ready to serve as the root of a future repository. All 26 generic sources in the inventory and the four KATLean tests moved there without changes to their content. Its manifest pins Mathlib to `c44e0c8ee63ca166450922a373c7409c5d26b00b` and locks its transitive Git dependencies. The integration manifest resolves KATLean through `../packages/KATLean`. NetKATLean resolves the same package through `../KATLean`.

The four NetKAT packet adapters now live under `packages/NetKATLean/NetKATLean/PacketAdapter/`. Their imports use `NetKATLean.PacketAdapter.{Packet,Guard,Symbolic,Closure}`; declaration namespaces remain `KATLean.NetKAT.*`. The remaining `DyNetKAT.NetKAT.*` core modules stay in place until NetKATLean extraction.

From the package root, run `lake build` and `./verify.sh smoke`, `./verify.sh test-all`, `./verify.sh verify`, and `./verify.sh consumer-test`. The consumer creates a fresh Lake project with a path dependency on this package and checks the resolved search paths before building examples with both public imports. The integration script `scripts/verify-katlean.sh` delegates to the package-owned verifier. Python is used only to construct and check the consumer fixture.

### Network-backed reproducibility

**NETWORK-BACKED REPRODUCIBILITY: PASS**

The earlier Work sandbox attempt failed because its DNS and network restrictions prevented Git from resolving GitHub. The same clean test passed from the Ubuntu host terminal through its configured local proxy. The host run started from a fresh copy of `packages/KATLean` with its `.lake` directory removed and ran:

```bash
env -u LEAN_PATH -u LEAN_SRC_PATH \
  MATHLIB_NO_CACHE_ON_UPDATE=1 \
  lake -v --keep-toolchain update

lake build
./verify.sh verify
./verify.sh consumer-test
```

Lake fetched Mathlib from GitHub and checked out the exact declared revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The transitive Git dependencies were fetched at their lockfile revisions. The build, package verification, and downstream consumer all passed after clean network resolution. All dependency versions and pins were preserved.

The earlier locked offline build also passed its smoke test, all four package tests, import audit, and Lake consumer against the pinned third-party cache.


## Realized NetKATLean extraction

The package root is `packages/NetKATLean/`. Its 22 source files are listed in the inventory below. All 17 former core modules use the exact mapping `DyNetKAT.NetKAT.X → NetKATLean.Core.X` for each listed core file `X.lean`. The four `NetKATLean.PacketAdapter` modules kept their module paths. The move preserved declaration namespaces. The integration workspace consumes the public `NetKATLean` library through a path dependency. The optional `Legacy`, `KATch`, `BackendCertificate` and `EquationalCertificate` remain in the integration workspace. Existing clients now import the new core module paths directly.

NetKATLean declares `../KATLean` and inherits its exact Mathlib pin and transitive Git locks. No extra Mathlib requirement is needed. Run the package-owned `./verify.sh` modes `build`, `smoke`, `test-all`, `verify`, and `consumer-test` from its root. The [NetKATLean boundary audit](NETKATLEAN_MODULARIZATION.md) gives the test inventory and consumer scope. Eight tests moved out of the integration workspace, leaving 43 there.

**Network-backed NetKATLean reproducibility: PASS.** The Ubuntu terminal transcript records two successful clean runs. An intervening run reached GitHub but hit the `/tmp` disk quota while writing the Mathlib clone. The final retry used disk-backed scratch under `$HOME/.cache` and printed `NETKATLEAN CLEAN NETWORK REPRODUCIBILITY: PASS`. The script verified the declared sibling KATLean path dependency, Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`, and the eight transitive Git revisions against the lockfile. The clean build, package verification and tests, and downstream consumer all passed. Dependency pins were preserved.

## Realized DyNetKATLean extraction

The package root is `packages/DyNetKATLean/`. The 48 sources in the inventory include the public umbrella and 47 dynamic modules. The umbrella retains its name. Each old `DyNetKAT.DyNetKAT.X` moved to `DyNetKATLean.Core.X`, with declaration namespaces preserved. The standalone prototype could retain the old paths because it had no sibling integration tree. In the realized split, the integration workspace still owns `DyNetKAT`, so Lean's top-level import resolution requires the distinct core prefix.

The package uses Lean 4.19.0 and declares only `../NetKATLean`. Its lock inherits sibling KATLean, Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`, and the same eight transitive Git revisions. The integration workspace consumes `../packages/DyNetKATLean`. The core import closure excludes frontend, CLI, examples, optional backends, Legacy and benchmark tooling. The case study declarations remain available from their existing explicit integration imports.

The package verification modes are `build`, `smoke`, `test-all`, `verify`, and `consumer-test` on `./verify.sh`. The package owns 28 relocated tests and one new paper-entry audit. The integration suite retains 15 tests. The clean network-backed gate passed on Ubuntu using fresh sibling package copies without Lake caches under `$HOME/.cache/dynetkat-tmp`. The run used `MATHLIB_NO_CACHE_ON_UPDATE=1 lake -v --keep-toolchain update`, verified the direct NetKATLean and inherited KATLean paths, and matched every Git checkout to its lockfile revision, including Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The pinned build, package verification, and isolated Lake consumer passed. The terminal reported `DYNETKATLEAN CLEAN NETWORK REPRODUCIBILITY: PASS`.

After this extraction is verified, committed, and pushed, rename the GitHub repository and the local checkout folder as a separate milestone. Update `origin`, hard-coded paths, documentation and clone instructions, and any affected package references. Run the complete verification suite after the rename, before Docker, CI, or release hardening.

## Prototype protocol

Run `python3 scripts/verify-package-independence.py` from the checkout. It creates an external temporary directory and three packages with fresh local build directories. Each package records the exact module, repository source, package-relative path, owner, compatibility naming, direct local and external imports, and SHA-256, together with its prototype module path, transformed imports and source hash, in its `source-manifest.json`. Each has its own Lake configuration and lock and a copy of the pinned Lean toolchain file. Each standalone consumer uses a normal Lake path dependency on its one public package. The verifier checks generated lock entries and the actual `LEAN_PATH` and `LEAN_SRC_PATH` supplied by Lake. It retains logs and manifests in the temporary directory.

The prototype uses an external copy of the nine pinned Git dependency checkouts and their cached dependency build artifacts. It verifies checkout revisions and preserves the recorded external pins in the generated locks. The cache defaults to the existing workspace's dependency cache and can be supplied with `--cache`. No project sources or build artifacts are served from the original workspace at build or consumer time. The offline prototype verifier generates locked manifests and runs `lake build`. The separate clean Ubuntu runs above verify network-backed resolution for all three extracted packages. For a released repository with access to the dependency remotes, resolve and verify the committed lock in a fresh checkout.

## Final layouts and pins

Preserve the three public umbrella imports and existing declaration namespaces. Drop the leading workspace directory `lean/` on extraction. Apply the following prototype module moves to the NetKAT core and rewrite imports of the moved modules.

| Current module | Prototype and proposed extracted module |
| --- | --- |
| `KATLean.NetKAT.{Packet,Guard,Symbolic,Closure}` | `NetKATLean.PacketAdapter.{Packet,Guard,Symbolic,Closure}` |
| Every core `DyNetKAT.NetKAT.X` in the inventory | `NetKATLean.Core.X` |
| Generic `KATLean.*` and the three umbrellas | Preserve module name |
| `DyNetKAT.DyNetKAT.X` | `DyNetKATLean.Core.X` in the realized package |

With Lean 4.19, the resolver selects the first search-path entry that contains the top-level module prefix, before checking the rest of the module path. The original-path standalone NetKAT build failed at `KATLean.NetKAT.Packet` and `KATLean.NetKAT.Guard` because Lean selected the generic KATLean package. NetKAT and the dynamic package also currently share the top-level `DyNetKAT` prefix. Moving the 17 NetKAT core modules under the NetKATLean prefix addresses that collision while preserving the 47 dynamic module paths in the original prototype. These are module-path changes only. The physical packages now use the non-colliding module paths. Old packet-adapter import shims would reintroduce the prefix collision or an upward dependency. Each package gets its own `lakefile.toml`, `lean-toolchain` and lock on Lake's manifest format. The toolchain is `leanprover/lean4:v4.19.0`. Pin Mathlib to `c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0), and retain the exact transitive Git pins from the current workspace manifest. Use reviewed immutable Git revisions for the lower packages once they are published. The prototypes use sibling path dependencies in place of these future Git pins.

| Package | Public target/import | Direct package requirements | Default source and test layout |
| --- | --- | --- | --- |
| KATLean | `KATLean`, with `KATLean.Native` also public | Mathlib | `KATLean.lean` and generic `KATLean/`. Own `test_katlean_import.lean`, `test_native_kat.lean`, `test_kat_completeness.lean` and `test_symbolic_kat.lean`. The public-import test also serves as the Lake consumer. |
| NetKATLean | `NetKATLean` | KATLean and Mathlib | `NetKATLean.lean`, `NetKATLean/Core/` and `NetKATLean/PacketAdapter/`. Own `test_netkatlean_import.lean`, `test_decision.lean`, `test_netkat_axioms.lean` and `test_symbolic_netkat.lean`. The public-import test also serves as the Lake consumer. |
| DyNetKATLean | `DyNetKATLean` | NetKATLean | `DyNetKATLean.lean` and `DyNetKATLean/Core/`. Generic KATLean arrives through NetKATLean. The public-import test `test_dynetkatlean_import.lean` also serves as the Lake consumer. |

The Lake library stanzas should enumerate the owned modules, as the prototype does, to keep source ownership explicit. The first DyNetKATLean test set is `test_dynetkatlean_import.lean`, `test_paper_domain.lean`, `test_typed_guardedness.lean`, `test_guarded_moves.lean`, `test_finite_projection.lean`, `test_equations.lean`, `test_equations_aip.lean`, `test_ground_completeness.lean`, `test_finite_abstraction.lean` and `test_trace_safety.lean`. Keep the controller and FatTree tests with their explicit examples, and the three v1.1 tests with the frontend. Port their legacy umbrella imports to `DyNetKATLean` in the extracted test tree. Review other `test_*.lean` imports before moving those tests. Keep mixed derivation and packet-schema cases as integration coverage. Move the NetKAT-local interpretation test `test_katlean.lean` with NetKAT tests when its integration assertions are confirmed by the extracted runner. Keep Legacy differential and external backend tests with their optional modules.

## Bottom-up migration

1. **KATLean.** Move the generic inventory and four owned tests. Keep both public imports and the exact Mathlib pin. Before wiring the combined workspace to the external KATLean revision, move the four packet adapters to `NetKATLean/PacketAdapter/` inside the combined workspace and update their imports. This preparatory relocation prevents top-level prefix shadowing as soon as KATLean leaves the workspace. Do not provide `KATLean.NetKAT.*` shims from generic KATLean. Remove the duplicate local KATLean target. Run KATLean build and tests, the fresh consumer, and the combined verification.
2. **NetKATLean.** Move the NetKAT core inventory, already relocated adapters, and four focused tests into the new repository. Place the 17 former `DyNetKAT.NetKAT.*` core files under `NetKATLean/Core/`. Rewrite their imports in the core, dynamic layer, frontend, examples, optional tools, and tests. Preserve declaration namespaces and the NetKAT-local KATLean compatibility facade. Pin KATLean and Mathlib and remove the combined workspace's duplicate NetKATLean target. Run the independently resolved build, focused tests and NetKAT consumer, then rebuild dynamic and optional integration tests. Leave Legacy and backend extras under explicit integration imports. Existing users of former fine-grained core module imports must migrate to the new paths or public umbrella.
3. **DyNetKATLean.** Move the dynamic inventory and consumer. Use the sibling NetKATLean dependency and its transitive Mathlib pin. Rebase core test imports against the public umbrella and check admission, SOS, branching, E_DNK, normalization, completeness and trace safety. Keep CLI, frontend, examples, metadata and the `DyNetKAT.lean` compatibility umbrella in the integration package, which owns the `DyNetKAT` prefix. Give the extracted core the `DyNetKATLean.Core` prefix so the two packages coexist without shadowing. Verify the fresh consumer, legacy umbrella, CLI and examples in the combined workspace. Keep benchmark scripts, fixtures, historical binaries and timing evidence with benchmark and integration tooling.

## Extraction issues

| Issue | Severity | Resolution |
| --- | --- | --- |
| Owned sources currently share one workspace | Requires source move | Move only the exact inventories, in dependency order, after the boundary commits. |
| `KATLean` split between KATLean and packet adapters | Requires module rename | Move the four adapters to `NetKATLean.PacketAdapter` and rewrite imports. |
| `DyNetKAT` split between core NetKAT and dynamic modules | Requires module rename | Move the 17 NetKAT core modules to `NetKATLean.Core` and rewrite imports. |
| Future separate integration package sharing `DyNetKAT` | Requires module rename if split | The extracted dynamic core now uses the `DyNetKATLean.Core` prefix and the integration workspace retains `DyNetKAT`. |
| Focused tests and historical consumers sometimes import the old umbrella | Minor cleanup | Use the owning public import for core tests and preserve the integration umbrella for mixed tests. |
| Independent release pins and clean CI/runtime caches remain to be established | Minor cleanup | Publish immutable lower-layer revisions and verify generated locks and clean installs in each new repository. |
| v1.1 compatibility, CLI, examples and optional comparisons live beside core sources | Minor cleanup | Keep explicit integration targets and their tests. The default mathematical closures do not depend on them. |

## Validation result

All three standalone builds and all three Lake consumer builds passed with the module paths above. Package and consumer build directories started empty. Lake resolved local dependencies within the temporary tree, and its source and object search paths excluded the shared workspace. The KATLean consumer checks the algebra, relation model and native solver. The NetKATLean consumer checks a port assignment, packet semantics, E_NK, interpretation, normalization and symbolic equivalence. The DyNetKATLean consumer checks admission, packet forwarding by SOS, residual admissibility, finite branching and head normalization.

## Exact source inventory

Paths below show the current repository layout. The NetKAT core moves still follow the module mapping above.

### KATLean

- `packages/KATLean/KATLean.lean`
- `packages/KATLean/KATLean/KAT.lean`
- `packages/KATLean/KATLean/Kleene.lean`
- `packages/KATLean/KATLean/Native.lean`
- `packages/KATLean/KATLean/Native/Automaton.lean`
- `packages/KATLean/KATLean/Native/Boolean.lean`
- `packages/KATLean/KATLean/Native/Completeness.lean`
- `packages/KATLean/KATLean/Native/Correctness.lean`
- `packages/KATLean/KATLean/Native/Decision.lean`
- `packages/KATLean/KATLean/Native/DerivativeAlgebra.lean`
- `packages/KATLean/KATLean/Native/DerivativeLabels.lean`
- `packages/KATLean/KATLean/Native/Derivatives.lean`
- `packages/KATLean/KATLean/Native/Equations.lean`
- `packages/KATLean/KATLean/Native/Explicit.lean`
- `packages/KATLean/KATLean/Native/FiniteSimulation.lean`
- `packages/KATLean/KATLean/Native/FiniteSystem.lean`
- `packages/KATLean/KATLean/Native/Language.lean`
- `packages/KATLean/KATLean/Native/Model.lean`
- `packages/KATLean/KATLean/Native/Ordering.lean`
- `packages/KATLean/KATLean/Native/Search.lean`
- `packages/KATLean/KATLean/Native/Symbolic.lean`
- `packages/KATLean/KATLean/Native/SymbolicSimulation.lean`
- `packages/KATLean/KATLean/Native/Syntax.lean`
- `packages/KATLean/KATLean/Native/TermModel.lean`
- `packages/KATLean/KATLean/Native/TestAlgebra.lean`
- `packages/KATLean/KATLean/Relation.lean`

### NetKATLean

- `packages/NetKATLean/NetKATLean.lean`
- `packages/NetKATLean/NetKATLean/Core/AST.lean`
- `packages/NetKATLean/NetKATLean/Core/Axioms.lean`
- `packages/NetKATLean/NetKATLean/Core/Decision.lean`
- `packages/NetKATLean/NetKATLean/Core/Denotation.lean`
- `packages/NetKATLean/NetKATLean/Core/Evaluator.lean`
- `packages/NetKATLean/NetKATLean/Core/History.lean`
- `packages/NetKATLean/NetKATLean/Core/HistoryEvaluator.lean`
- `packages/NetKATLean/NetKATLean/Core/HistorySemantics.lean`
- `packages/NetKATLean/NetKATLean/Core/Interpretation.lean`
- `packages/NetKATLean/NetKATLean/Core/KATLean.lean`
- `packages/NetKATLean/NetKATLean/Core/NativeEquations.lean`
- `packages/NetKATLean/NetKATLean/Core/NormalForm.lean`
- `packages/NetKATLean/NetKATLean/Core/Normalization.lean`
- `packages/NetKATLean/NetKATLean/Core/Packet.lean`
- `packages/NetKATLean/NetKATLean/Core/Semantics.lean`
- `packages/NetKATLean/NetKATLean/Core/Symbolic.lean`
- `packages/NetKATLean/NetKATLean/Core/SymbolicDerives.lean`
- `packages/NetKATLean/NetKATLean/PacketAdapter/Closure.lean`
- `packages/NetKATLean/NetKATLean/PacketAdapter/Guard.lean`
- `packages/NetKATLean/NetKATLean/PacketAdapter/Packet.lean`
- `packages/NetKATLean/NetKATLean/PacketAdapter/Symbolic.lean`

### DyNetKATLean

- `packages/DyNetKATLean/DyNetKATLean/Core/AST.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/Action.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/AnalysisStrategy.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/Approximation.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/Bisimulation.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/Config.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/Definedness.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/DependencySCC.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/Equations.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/EquationsAIP.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/Executable.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/FiniteAbstraction.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/FiniteBisimulation.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/FiniteBranching.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/FiniteClosure.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/FiniteProjection.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/GraphHead.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/GraphMoves.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/GraphNormalization.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/GraphPaths.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/GraphRestriction.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/GraphTail.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/Ground.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/GroundCompleteness.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/HeadNormalForm.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/MemoProjection.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/NetKATBridge.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/PaperDomain.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/ProcessGraph.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/Program.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/ProjectionDerivation.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/Reachability.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/RecEnv.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/RestrictionProjection.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/SafetyCheck.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/SafetyHead.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/SemanticBranching.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/Semantics.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/SequentialReachability.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/SourceTrace.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/TailExtraction.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/TightReachability.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/TraceEnvironment.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/TraceEquations.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/TraceSafety.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/TraceSafetyCheck.lean`
- `packages/DyNetKATLean/DyNetKATLean/Core/TypedGuardedness.lean`
- `packages/DyNetKATLean/DyNetKATLean.lean`
