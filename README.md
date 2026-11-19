# DyNetKAT-Lean

## Symbolic native KAT

`KATLean.Native` decides the pure KAT equational theory using reduced ordered
Boolean decision trees and symbolic partial derivatives.
`decideEquiv_iff_equational` characterizes derivability from the KAT rules and
`decideEquiv_iff_algebraicallyEquivalent` characterizes equality in every
abstract KATLean model. `nativeSolver_derives` yields a NetKAT derivation
under any substitution of primitive actions and tests.

`netkatNativeEquiv` adds executable symbolic equivalence for the current
dup-free NetKAT AST. KATLean → native KAT → symbolic packet frontend →
NetKAT equivalence → E_NK → E_DNK is the resulting proof path.
`netkatNativeEquiv_correct` is independent of KATch, concrete packet
enumeration and Boolean valuation enumeration. The E_NK completeness proof
uses symbolic closure and the field-level partition axiom. The public
`netkatEquiv` and `netkatIsZero` APIs serve graph normalization and safety
through the symbolic checker. `legacyNetkatEquiv` is the regression oracle.

See the [symbolic frontend and dependency audit](docs/NETKAT_AUDIT.md).

See [NATIVE_KAT.md](docs/NATIVE_KAT.md) for the theorem chain and proof construction.

### Native KAT decision layer

`import KATLean.Native` provides a verified partial-derivative equivalence
engine for the pure KAT equational theory over the native finite alphabets.
Its soundness and completeness proofs use no `CtxPkt` enumeration or KATch.
Boolean guards are canonical decision trees; the solver explores satisfiable
symbolic regions instead of abstract truth assignments.
See [NATIVE_KAT.md](docs/NATIVE_KAT.md) for the exact theorem scope and tests.

The symbolic frontend interprets packet equations such as assignment
overwrite before comparing the encoded relations through `KATLean.Native`.
Graph and safety checks share the symbolic zero checker. Lemma 5 and
DyNetKAT packet-head normalization use the same symbolic packet compiler
and exact star fixed point. They emit the paper's complete-pair branches
from accepting diagram paths. `CtxPkt` supplies the concrete field schema
and execution model. The exhaustive equivalence checker and normalizer are
regression oracles. KATch remains experimental.

Faithful Lean 4 formalization of the **original DyNetKAT calculus**:
*DyNetKAT: An Algebra of Dynamic Networks* (arXiv:2102.10035v4, FoSSaCS 2022).

## Goal

A complete Lean 4 formalization of the mathematics in the original DyNetKAT
paper, together with a usable implementation of the original DyNetiKAT
analysis workflow. The target includes sound and ground-complete equational
theories, guarded recursion, the full safety framework, and dynamic
reachability and waypointing over general finite packet domains.

See the [roadmap](PLAN.md) for current coverage, the finite-depth projection
workstream and the release criteria. The journal extension on log extraction,
causality and bounded schedules is outside the paper scope.

### Verified language boundary

The raw Lean AST provides syntax for the SOS and proof infrastructure.
`Program` admits entries in the paper source grammar with closed, guarded
recursive declarations. `Program.Residual` additionally carries an SOS path
from its admitted source. Compiled states carry both source and graph
reachability. Use the APIs in `Program.lean` for transitions, projection,
discovery, equivalence and safety queries. Raw graph tables, head and tail
forms, and solver models are internal helper syntax.

The [semantic-domain audit](docs/PAPER_CONFORMANCE.md#source-grammar-and-sos-residual-closure)
lists the source constructors, reachability conditions and classified examples.

KATLean supplies the Mathlib-based algebra beneath the NetKAT layer.
It proves the KA/test laws and dup-free packet laws and connects the
current AST and evaluator to a packet-relation model. `Derives` justifies
its KA, Boolean and packet laws directly through KATLean. Its semantic
soundness, Lemma 5 and the E_DNK packet-prefix import follow that proof chain.
Import `KATLean` for the algebra or `DyNetKAT.NetKAT.KATLean` for the
current NetKAT bridge. See [KATLEAN.md](docs/KATLEAN.md) for Figure 4
coverage, general-schema work and the optional full NetKAT history/dup extension.

The core formalization follows the source grammar, `Program` / reachable
`Residual` boundary, SOS semantics, KATLean, dup-free E_NK, E_DNK and
certified analysis. KATch is an optional experiment and comparison point.
Core equivalence theorems use Lean proofs over the native symbolic packet
layer.

## Structure

```
DyNetKAT-Lean/
├── lean/          # Lean 4 formalization (trusted semantic core)
├── python/        # Auxiliary scripts & golden tests (untrusted adapter)
├── docs/          # Research notes, conformance mapping, proof roadmap
├── scripts/       # Build & validation scripts
├── PLAN.md        # Phased roadmap
└── README.md      # This file
```

## Project Policies

- Mathematical references use [arXiv:2102.10035v4](https://arxiv.org/abs/2102.10035v4).
  The [conformance inventory](docs/PAPER_CONFORMANCE.md) maps these references to
  the FoSSaCS 2022 edition. Tool parity targets
  [DyNetiKAT v1.1](https://gitlab.utwente.nl/fmt/dynetikat/-/tree/v1.1).
- Lean 4 is the trusted semantic core. Python is limited to auxiliary scripts,
  golden-value checks, and experiments; it does not carry research-critical
  semantics.
- Preserve the paper's syntax, semantics, equations, and per-packet
  consistency. Distinguish paper definitions from implementation choices and
  extensions, and state finite-domain, termination, or boundedness assumptions
  explicitly.
- Do not use `axiom`, `sorry`, or `admit` as substitutes for proofs. Any
  temporary proof hole must be isolated and explained. Record mathematical
  findings and design conflicts in the relevant `docs/` files.
- Use Lean 4 / Lake, `UpperCamelCase` for types and constructors, and
  `lowerCamelCase` for definitions and theorems. Use Python 3 type hints,
  `snake_case`, and deterministic serialization.

## Building

```bash
cd lean
lake build DyNetKAT    # authoritative Lean build
```

## Testing

```bash
cd python
python3 -m pytest -q   # Python auxiliary tests
```

Combined check:
```bash
./scripts/verify.sh
```

A no-argument `lake build` that reports `[0/0]` does not compile the library;
always validate the explicit `DyNetKAT` target. If the system Python lacks
pytest, use a virtual environment and install `pytest>=8` there.

## Checking safety on a recursive graph

`compileGraph env p support` checks that the supplied finite set contains
every variable in the root and in the bodies of the supported definitions.
Each variable must be defined. The returned graph stores the translated
definitions and uses references to represent recursion.

Use `safetyCheckGraph G R ingress egress` on a closed graph in the paper's
head/tail fragment. It reports initial isolation (34) and post-reconfiguration
reachability (35) separately. The results distinguish failed extraction from
an evaluated condition. Raw graph nodes and labels can be checked with
`validateProcessGraph`.

`compileAndSafetyCheckGraph` compiles first, then eliminates the restriction
of communication actions and checks the resulting graph. Its preprocessor
supports recursive sequential terms.

For raw parallel terms and merges, use
`compileNormalizeAndSafetyCheckGraph env p support candidate R ingress egress`.
With an already compiled graph, use
`normalizeAndSafetyCheckGraph G candidate R ingress egress`.
A `NormalizationCandidate n` supplies `n + 1` indexed process derivatives,
their outgoing packet and reconfiguration edges, and an order for evaluating
references needed in the current step. The initial derivative is index zero.
Each later index needs an incoming edge from an earlier index. The checker
validates every row against the SOS under the outer communication restriction
before building the sequential graph.

The Boolean validator accepts some certificate exactly when the restricted
derivative set is finite and the graph satisfies `NormalizationAdmissible`.
Every reachable derivative must be free of restriction constructors in its
own syntax. One reference order must cover the references inspected during
a single step from those derivatives, and each label in that order can
consult only earlier entries. A restriction encountered during this
one-step traversal fails validation. Prefix continuations, the right
operand of left merge, and the body of a zero projection are skipped
during the traversal.

Use `normalizeCertifiedGraph` or `safetyCheckCertifiedGraph` when a Lean
proof of `NormalizationExact` is available. This accepts exact tables for
finite systems with active reference cycles or nested restrictions.
`exists_exactNormalization_iff` proves that such a table exists exactly
when the restricted derivative set is finite. This existence theorem
uses classical reasoning over the SOS. The executable renderer consumes
the supplied table and its proof.

The [graph safety regressions](lean/test_graph_safety.lean) include the
original parallel firewall and its two-state certificate. The
[admissibility regressions](lean/test_normalization_admissibility.lean)
cover silent and productive cycles and nested restriction sets.

## Optional / experimental tooling

`import DyNetKAT` exposes the core formalization. To use the former
backend exports, use `import DyNetKAT.Experimental` or import
`DyNetKAT.NetKAT.KATch`, `BackendCertificate` or `EquationalCertificate`
explicitly. Their existing declaration names and APIs are preserved.

KATch is an optional, untrusted external experiment, comparison point
and possible future accelerator. The replay driver, candidate checkers,
equational checker and tests remain available. Their proof obligations
belong to those experiments. Project completion, E_NK/E_DNK, normalization,
completeness and certified analysis require no KATch installation.
The [NetKAT audit](docs/NETKAT_AUDIT.md#optional--experimental-tooling)
records the common fragment, finite-domain restrictions and replay results.


Build the optional Lean exports before running backend fixtures or the full
Lean regression sweep on a fresh checkout.

```bash
cd lean
lake build DyNetKAT.Experimental
for f in test_*.lean; do
  lake env lean "$f" || exit 1
done
```

Core-only verification uses `lake build DyNetKAT`. Python replay integration
tests skip when the optional Lean target has not been built. The full suite
with that target built exercises the preserved replay infrastructure using
subprocess doubles and needs no KATch installation.
