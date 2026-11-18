# KATLean foundation for E_NK

## Scope and dependencies

KATLean supplies the algebra used by the dup-free NetKAT layer beneath
DyNetKAT. The mathematical reference is Figure 4 of
[arXiv:2102.10035v4](https://arxiv.org/pdf/2102.10035v4), 22 May 2021.
Figure 11 contains the separate E_DNK equations.

The repository pins Lean and Mathlib v4.19.0. The Mathlib revision recorded
in `lean/lake-manifest.json` is
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.
`Mathlib.Algebra.Order.Kleene` supplies `IdemSemiring`, `KStar` and
`KleeneAlgebra`. The implementation instantiates those classes for packet
relations. All generic algebra uses the existing classes.

| Module | Responsibility |
|---|---|
| `lean/KATLean/Kleene.lean` | Paper order, unfold equations and both induction formulations |
| `lean/KATLean/KAT.lean` | Injective Boolean test embedding and all six BA laws |
| `lean/KATLean/Relation.lean` | Relational Mathlib KA instance and Boolean packet-set tests |
| `lean/KATLean/NetKAT/Packet.lean` | Field-indexed packet interface and the dup-free packet laws |
| `lean/KATLean.lean` | Public algebra import surface |
| `lean/DyNetKAT/NetKAT/KATLean.lean` | CtxPkt instance, AST interpretation, evaluator and derivation bridges |
| `lean/test_katlean.lean` | Generic and concrete law tests and axiom audit |

`import KATLean` depends only on Mathlib. The bridge imports the existing
NetKAT normalization modules. Neither path imports DyNetKAT process
semantics, KATch, or its certificate/replay adapters. The `DyNetKAT` umbrella
imports the bridge. The core import closure excludes `KATch`,
`BackendCertificate`, `EquationalCertificate` and `Experimental`.

The paper-facing architecture runs from the source grammar through
`Program` / reachable `Residual`, SOS, KATLean, dup-free NetKAT E_NK,
E_DNK and certified analysis. The algebraic proof path is NetKAT interpreted
in KATLean and validated by Lean theorems. Full NetKAT with `dup` and its
history-changing semantics is outside current DyNetKAT scope. Existing
dup-free history lemmas support the packet/SOS correspondence.

## KA conformance and inequalities

In Mathlib, `IdemSemiring` extends `Semiring` and `SemilatticeSup`, with
`a + b = a ⊔ b`. `KATLean.order_iff_add` proves
`a ≤ b ↔ a + b = b` from `add_eq_right_iff_le`.
`Rel.le_iff` identifies this order with pointwise relation inclusion.

Mathlib's `KleeneAlgebra` fields give `one_le_kstar`,
`mul_kstar_le_kstar`, `kstar_mul_le_kstar`,
`mul_kstar_le_self` and `kstar_mul_le_self`. The last two preserve a
multiplicatively stable upper bound. Derived `kstar_mul_le` and
`mul_kstar_le` include a smaller base term. `kstar_mono` proves star
monotonicity. `kstar_le_of_mul_le_right/left` give the corresponding
least prefixed-point laws with an identity lower bound.

The table follows the paper's operand order. Entries in the first eleven
rows are already provided by Mathlib. The remaining rows are derived
in KATLean from Mathlib's laws.

| Paper KA axiom | Declaration or theorem |
|---|---|
| KA-PLUS-ASSOC | `add_assoc`, reversed for the printed orientation |
| KA-PLUS-COMM | `add_comm` |
| KA-PLUS-ZERO | `add_zero` |
| KA-PLUS-IDEM | `add_idem` |
| KA-SEQ-ASSOC | `mul_assoc`, reversed for the printed orientation |
| KA-ONE-SEQ | `one_mul` |
| KA-SEQ-ONE | `mul_one` |
| KA-SEQ-DIST-L | `mul_add` |
| KA-SEQ-DIST-R | `add_mul` |
| KA-ZERO-SEQ, left annihilation | `zero_mul` |
| KA-ZERO-SEQ, right annihilation, printed with the same name | `mul_zero` |
| KA-UNROLL-L | `KATLean.star_unfold_left` proves `1 + p * p∗ = p∗` |
| KA-UNROLL-R | `KATLean.star_unfold_right` proves `1 + p∗ * p = p∗` |
| KA-LFP-L | `KATLean.star_induction_left`, from `kstar_mul_le` |
| KA-LFP-R | `KATLean.star_induction_right`, from `mul_kstar_le` |

The induction hypotheses are exactly `q + p * r ≤ r` and
`p + q * r ≤ q`. `add_le_iff` splits each hypothesis into its base
and stability inequalities. The conclusions are `p∗ * q ≤ r` and
`p * r∗ ≤ q`. The theorems `star_induction_left_add` and
`star_induction_right_add` express these as equations using only
addition and star. Their hypotheses and conclusions match the order
encoding in the existing `Derives.lfpL` and `Derives.lfpR`.

The unfold equations require both bounds. The upper bound follows from
the class fields. The lower bound follows from leastness applied to
`1 + p * p∗` or `1 + p∗ * p`. Thus the equations hold for every Mathlib
Kleene algebra, independently of the packet interpretation.

## Boolean tests

`KAT K B` requires `KleeneAlgebra K` and `BooleanAlgebra B`. Its injective
`embed : B → K` preserves bottom, top, join and meet as zero, one,
addition and multiplication. Complement belongs to `B`, and its images
satisfy excluded middle and contradiction.

Mathlib's `BoundedLatticeHom` and `SupBotHom` were inspected. A KA has
joins, but has no required meets or top on all programs. A bounded
lattice hom into the program algebra would require extra structure.
A join/bottom hom alone would omit the meet/top embedding laws. The
small `KAT` structure records precisely the four laws and injectivity.

All six paper BA laws are derived algebraically for any such embedding.

| Paper BA axiom | KATLean theorem |
|---|---|
| BA-PLUS-DIST | `KAT.plus_distrib` |
| BA-PLUS-ONE | `KAT.plus_one` |
| BA-EXCL-MID | `KAT.excluded_middle` |
| BA-SEQ-COMM | `KAT.test_commute` |
| BA-CONTRA | `KAT.contradiction` |
| BA-SEQ-IDEM | `KAT.test_idempotent` |

`KAT.order_iff` proves that the embedding preserves and reflects order.
`Rel.tests` instantiates the test algebra with `Set Packet`, embedded as
the diagonal relation restricted to the set.

## Packet algebra

`PacketModel Field Value Packet` allows a value type `Value f` for each
field. It records lookup and update, together with the laws that lookup
observes an update on its field, other fields are preserved, writing back
the observed value is identity, the last same-field write wins, and
distinct-field writes commute. These are structure hypotheses, proved
when instantiating a packet representation.

`filter f v` is a Boolean test for `lookup f packet = v`.
`assign f v` is the graph of `update f v`. Relation multiplication
executes its left operand first. Star is Mathlib's
`Relation.ReflTransGen`. The KA instance proves both induction fields
by induction on that closure.

| Paper packet axiom | Status and KATLean theorem |
|---|---|
| PA-MOD-MOD-COMM | Proved, `PacketModel.assign_commute`, requires distinct fields |
| PA-MOD-FILTER-COMM | Proved, `PacketModel.assign_filter_commute`, requires distinct fields |
| PA-MOD-FILTER | Proved, `PacketModel.assign_filter` |
| PA-FILTER-MOD | Proved, `PacketModel.filter_assign` |
| PA-MOD-MOD | Proved, `PacketModel.overwrite` |
| PA-CONTRA | Proved, `PacketModel.filter_contradiction`, requires distinct values |
| PA-MATCH-ALL | Proved, `PacketModel.match_all`, summed over `Fintype (Value f)` |
| PA-DUP-FILTER-COMM | Not covered. Requires a full history model with `dup` |

`PacketModel.filter_commute` and `filter_idempotent` are instances of
the BA laws. They also establish identical-field simplification.
PA-MATCH-ALL needs finiteness only for the selected field's value
domain. The other theorems impose no global field/value enumeration.

## Existing NetKAT connection

`ctxPacketModel` instantiates the interface for the current `CtxPkt`.
Its lookup/update laws reuse `Packet.get_update_same`,
`get_update_diff`, `update_id`, `update_update_same` and
`update_update_diff`. `ctx_lookup` and `ctx_update` expose the
definitional agreement with the current API.

`predicateInterp` interprets false, true, field equality, conjunction,
disjunction and negation in the Boolean algebra of packet sets.
`predicateInterp_correct` proves agreement with `Predicate.holds`.
`katInterp` interprets every existing dup-free AST constructor using
the KA operations, including nested star. Complete tests embed their
existing valuation predicate.

`katInterp_correct` proves agreement with `Semantics` for all packets.
Its star case explicitly identifies the existing `StarClosure` with
Mathlib reflexive-transitive closure. `execute_katInterp` proves that
the evaluator returns a supported finite set containing exactly the
related output packets.

`Derives.katSound` proves equality of interpretations for every existing
`Derives` proof. This first bridge uses the already verified
`Derives.sound` theorem and interpretation correctness. The existing
rule induction and normalization proof remain in place.
`normalize_katInterp` applies the bridge to `normalize_derives`, so
the current Lemma 5 result has algebraic validity in KATLean.

Later refactoring can route the KA cases through Mathlib and the two
induction wrappers, BA cases through `KAT`, and packet cases through
`PacketModel`. Predicate and complete-test elaboration rules still
require their interpretation lemmas. Replacing the existing soundness
proof with those cases is separate work. Abstract KATLean validity
alone does not establish syntactic derivability or completeness for a
general packet schema.

## DyNetKAT integration

KATLean equations concern packet-policy meanings. They provide a checked
algebraic interpretation of E_NK under the current E_DNK packet-prefix
import boundary. Public process APIs still require `Program` and
reachable `Residual` evidence. Observable send, receive and
reconfiguration payloads retain their syntactic equality condition.

## Optional / experimental tooling

KATch is an external comparison point and possible future accelerator.
It is untrusted and carries no premise of a core theorem. The existing
replay and certificate modules are exposed by
`DyNetKAT.Experimental`. They import the core algebra and evaluator;
the core has no reverse import. KATLean, E_NK, E_DNK, normalization,
completeness, certified analysis and release criteria stand independently
of those modules or the external executable.

The optional experiments may ask KATch for candidate evidence. Their
Lean checkers validate that evidence using the existing proved evaluator
or derivations. Experimental results and performance measurements are
recorded separately in the [NetKAT audit](NETKAT_AUDIT.md#optional--experimental-tooling).

## Verification and remaining work

`test_katlean.lean` covers the KA equations and inequalities, all BA
families, packet commutation and overwrite, both matching-test laws,
contradiction and finite exhaustiveness, a concrete policy equation,
nested star interpretation, evaluator outputs, derivation soundness and
normalization validity. It prints axioms for the induction, embedding,
packet and bridge results. Direct module checks and the full project
suite accompany the checkpoint.

Remaining core work includes general-schema AST/evaluator/normalization
bridges and deliberate reuse of KATLean laws inside the existing Derives
soundness proof. The packet interface supports dependent values, while
the existing executable AST and Lemma 5 theorem remain on CtxPkt.

The full history/dup model and PA-DUP-FILTER-COMM remain optional
supporting NetKAT extensions, outside the current DyNetKAT release scope.
