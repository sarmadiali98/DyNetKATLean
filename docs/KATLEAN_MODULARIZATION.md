# First KATLean boundary

| Source roots | Ownership and dependency rationale |
| --- | --- |
| `KATLean.lean`, `KATLean/{Kleene,KAT,Relation}.lean` | KATLean. Mathlib Kleene laws, Boolean test embeddings and the relational model. |
| `KATLean/Native.lean`, all `KATLean/Native/*.lean` | KATLean. Generic typed KAT syntax, Boolean diagrams, derivatives, automata, finite search, model correctness and completeness. |
| `packages/NetKATLean/NetKATLean/PacketAdapter/{Packet,Guard,Symbolic,Closure}.lean` | Future NetKATLean. Packet lookup and updates, diagram operations used by the packet adapter, packet encodings and relational closure. These four files moved out of the KATLean prefix during physical extraction. Guard's rename and projection operations are candidates for later reuse if another consumer needs them. |
| `DyNetKAT/NetKAT/*.lean` | Future NetKATLean. Packet schemas, policies and history, semantics and evaluators, E_NK, normalization and certificates. NativeEquations and SymbolicDerives translate generic KAT machinery to NetKAT. Keep Legacy and the KATch/BackendCertificate/EquationalCertificate workflow in compatibility or optional backend targets. |
| `DyNetKAT/DyNetKAT/*.lean`, `DyNetKAT/{Basic,Experimental,Main}.lean`, `DyNetKAT.lean` | Future DyNetKATLean and its executable targets. The dynamic core owns recursion, SOS, projections, graph algorithms, equations, bisimulation and safety. Main dispatches the CLI. Experimental is an opt-in umbrella for external backend tooling. |
| `DyNetKAT/Frontend/V11*.lean`, `DyNetKAT/Examples/*.lean` | DyNetKATLean adapters and case studies. V11 loading combines packet schema and guarded program admission. Batch and Main depend on that boundary. FatTree and DistributedControllers exercise the dynamic layer. |
| `scripts/`, `python/`, `docs/` | Top-level development, integration and benchmark tooling. Keep the historical timing and KATch replay tools outside the mathematical libraries. Keep the Lean benchmark phase executable outside the public imports. |

The generic KAT code uses Mathlib and Lean/Std. The existing Lake workspace pins Lean 4.19.0 and Mathlib v4.19.0 in the toolchain and manifest. The `KATLean` import exposes the algebra and relation model. Import `KATLean.Native` for generic native decision and completeness. The KATLean Lake target builds those roots and all generic native modules. The earlier base umbrella imported packet modeling, which put NetKAT-specific code inside the generic import closure. The NetKAT packet facade already imports the packet model explicitly. No proof declarations or namespaces need to move for this checkpoint.

`DyNetKAT/NetKAT/Axioms.lean` proves `Derives.katSound` over KATLean's relation instance. The additive and multiplicative rules use Mathlib laws, the star rules use KATLean unfold and induction, and the Boolean rules use KATLean test embeddings and Boolean laws. Packet assignment, filter, overwrite and coverage rules use the packet model. Interpretation and normalization remain NetKAT clients. The NetKAT source modules have no imports into the dynamic process layer.

`test_native_kat.lean`, `test_kat_completeness.lean` and `test_symbolic_kat.lean` exercise the generic KAT library. `test_katlean.lean` mixes generic algebra examples with packet models, interpretation and normalization and remains integration coverage at this milestone. The new standalone import test takes over basic generic algebra coverage without the higher-layer import. NetKAT proofs and regressions belong with NetKAT, while process, frontend and case-study tests belong with DyNetKAT. Cross-layer semantic and optional-backend differential tests remain integration checks.

KATLean now lives in `packages/KATLean/` and the integration workspace consumes it as a Lake path dependency. See the [extraction plan](PACKAGE_EXTRACTION_PLAN.md) for the realized layout and verification commands. Docker, CI and publishing remain later work.

Run `scripts/verify-katlean.sh` to check import direction, build the generic library and run its four public-import tests. Removing the packet import exposed an incidental dependency on the Finset product API in Native.Explicit and Native.Decision. Both now import Mathlib's Finset product module directly.

The optional-backend integration tests are `test_backend_certificate.lean` and `test_katch_differential.lean`. The legacy comparison and normalization tests explicitly import `DyNetKAT.NetKAT.Legacy`. The v1.1 tests exercise syntax/loading, bounded reachability and waypointing through the frontend. Python tests and scripts remain workspace checks; the generic KAT library builds with the Lean toolchain and its pinned Mathlib dependency alone.

The native-to-NetKAT substitution example now lives in the derivation integration test. The symbolic KAT regression test imports only the generic library, including its explicit differential oracle.

The downstream-style smoke was also run from a scratch directory using a `LEAN_PATH` containing the cached Mathlib dependency libraries and a copy of only the generic KATLean compiled modules. The same public-import test passed without local NetKAT or DyNetKAT artifacts on its import path.
