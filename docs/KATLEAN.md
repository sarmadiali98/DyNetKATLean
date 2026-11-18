# KATLean foundation for E_NK

## Native decision layer

`KATLean.Native` builds on this algebra without importing the NetKAT AST,
concrete packets, Derives or process semantics. It decides guarded-string
equivalence and equality in all relational KATLean interpretations, with proved
partial-derivative correctness, finite closure, soundness and completeness.
See [NATIVE_KAT.md](NATIVE_KAT.md) for exact scope, construction comparisons,
Boolean-alphabet costs and the remaining abstract equational-completeness gap.

The intended path is KATLean → native solver → packet-aware symbolic frontend
→ NetKAT Derives/E_NK → E_DNK. The generic solver is delivered; the packet-aware
frontend is pending. Existing fixed-model evaluator and normalization imports
below remain legacy dependencies, not dependencies of native correctness.

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
| `lean/DyNetKAT/NetKAT/Interpretation.lean` | CtxPkt instance, AST interpretation and evaluator correctness, below Derives |
| `lean/DyNetKAT/NetKAT/Axioms.lean` | Existing Derives and its KATLean rule induction |
| `lean/DyNetKAT/NetKAT/KATLean.lean` | Compatibility import surface and normalization interpretation theorem |
| `lean/test_katlean.lean` | Generic and concrete law tests and axiom audit |
| `lean/test_katlean_derives.lean` | Derivation regressions, proof dependency checks, packet-prefix import and payload boundary |

`import KATLean` depends only on Mathlib. The lower interpretation imports
the existing NetKAT decision/evaluator modules. The compatibility surface also imports
normalization. Neither path imports DyNetKAT process
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

`Derives.katSound`, defined in `Axioms.lean`, proves equality of
interpretations by induction on all 40 constructors. The KA cases call
Mathlib laws on the KATLean relation algebra and KATLean's unfold and
induction theorems. The BA cases call the Boolean embedding laws and
all six KAT laws. The seven packet cases call `ctxPacketModel`'s
KATLean packet theorems. Congruence uses equality, including complement
congruence obtained through the injective test embedding.

`Derives.sound` now follows from `Derives.katSound` and
`katInterp_eq_iff`. Its semantic theorem statement is preserved.
`Derives.historySound` continues to transfer that result through the
existing dup-free history correspondence.

The import order is Mathlib, KATLean, `Interpretation`, `Axioms`,
normalization, then the `NetKAT.KATLean` compatibility surface.
`Interpretation` imports no derivation or normalization module. It
proves its semantic bridge by AST induction. This gives an acyclic
foundation for the derivation induction.

`normalize_katInterp` applies `Derives.katSound` to the existing
`normalize_derives` theorem. Lemma 5's derivation is interpreted in the
same algebra. The normalization algorithm and supported fragment keep
their existing definitions. Algebraic validity alone does not establish
syntactic derivability or general-schema completeness.

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
bridges. The packet interface supports dependent values, while
the existing executable AST and Lemma 5 theorem remain on CtxPkt.

The full history/dup model and PA-DUP-FILTER-COMM remain optional
supporting NetKAT extensions, outside the current DyNetKAT release scope.

## Derives rule audit

The baseline proof path below records the audit before refactoring. A means pure
KA, B means Boolean/test algebra, C means packet algebra, D means structural
or congruence, and E means normalization-specific syntax elaboration. There
are no additional rule families. All algebraic cases now use the declarations
in the final theorem column directly.
The complete-test expansion keeps its syntax-specific bridge.

| Derives rule | Class and source | Baseline proof path | Available theorem / direct reuse | Reuse |
|---|---|---|---|---|
| `refl` | D, Equality reflexivity | Semantic iff reflexivity | `Eq.refl` | Direct |
| `symm` | D, Equality symmetry | Semantic iff symmetry | `Eq.symm` | Direct |
| `trans` | D, Equality transitivity | Semantic iff transitivity | `Eq.trans` | Direct |
| `unionCongr` | D, Union congruence | Pointwise disjunction | `congrArg₂ on KATLean addition` | Direct |
| `seqCongr` | D, Composition congruence | Existential composition | `congrArg₂ on KATLean multiplication` | Direct |
| `starCongr` | D, Star congruence | Local StarClosure.map induction | `congrArg on Mathlib KStar` | Direct |
| `notCongr` | D, Complement congruence on tests | Compare diagonal semantics | `Rel.tests.injective and Boolean complement` | Direct |
| `testFalse` | B, Test zero embedding | Predicate evaluator simplification | `Rel.tests.map_bot` | Direct |
| `testTrue` | B, Test one embedding | Predicate evaluator simplification | `Rel.tests.map_top` | Direct |
| `testOr` | B, Join embedding | Predicate evaluator simplification | `Rel.tests.map_sup` | Direct |
| `testAnd` | B, Meet embedding | Existential test composition | `Rel.tests.map_inf` | Direct |
| `completeTestExpand` | E, Complete-test syntax elaboration | completeTestExpr_correct | `Keep syntax-specific semantic bridge` | Syntax-specific bridge |
| `plusAssoc` | A, KA-PLUS-ASSOC | union_assoc | `add_assoc in KATLean.Rel` | Direct |
| `plusComm` | A, KA-PLUS-COMM | union_comm | `add_comm in KATLean.Rel` | Direct |
| `plusZero` | A, KA-PLUS-ZERO | Semantic simplification | `add_zero in KATLean.Rel` | Direct |
| `plusIdem` | A, KA-PLUS-IDEM | union_idem | `add_idem in KATLean.Rel` | Direct |
| `seqAssoc` | A, KA-SEQ-ASSOC | Existential reassociation | `mul_assoc in KATLean.Rel` | Direct |
| `oneSeq` | A, KA-ONE-SEQ | seq_id_left | `one_mul in KATLean.Rel` | Direct |
| `seqOne` | A, KA-SEQ-ONE | seq_id_right | `mul_one in KATLean.Rel` | Direct |
| `seqDistL` | A, KA-SEQ-DIST-L | seq_distrib_left | `mul_add in KATLean.Rel` | Direct |
| `seqDistR` | A, KA-SEQ-DIST-R | seq_distrib_right | `add_mul in KATLean.Rel` | Direct |
| `zeroSeq` | A, KA-ZERO-SEQ, left | seq_drop_left | `zero_mul in KATLean.Rel` | Direct |
| `seqZero` | A, KA-ZERO-SEQ, right | seq_drop_right | `mul_zero in KATLean.Rel` | Direct |
| `unrollL` | A, KA-UNROLL-L | Local StarClosure cases | `KATLean.star_unfold_left` | Direct |
| `unrollR` | A, KA-UNROLL-R | Local StarClosure.snoc/last | `KATLean.star_unfold_right` | Direct |
| `lfpL` | A, KA-LFP-L | starLfpLeft closure induction | `KATLean.star_induction_left_add` | Direct |
| `lfpR` | A, KA-LFP-R | starLfpRight closure induction | `KATLean.star_induction_right_add` | Direct |
| `baPlusDist` | B, BA-PLUS-DIST | Semantic simplification and aesop | `KAT.plus_distrib` | Direct |
| `baPlusOne` | B, BA-PLUS-ONE | Semantic simplification | `KAT.plus_one` | Direct |
| `baExclMid` | B, BA-EXCL-MID | Boolean evaluator case split | `KAT.excluded_middle` | Direct |
| `baSeqComm` | B, BA-SEQ-COMM | Semantic conjunction commutation | `KAT.test_commute` | Direct |
| `baContra` | B, BA-CONTRA | Semantic simplification | `KAT.contradiction` | Direct |
| `baSeqIdem` | B, BA-SEQ-IDEM | Semantic simplification | `KAT.test_idempotent` | Direct |
| `paModModComm` | C, PA-MOD-MOD-COMM | assign_comm_diff and semantic simplification | `PacketModel.assign_commute` | Direct |
| `paModFilterComm` | C, PA-MOD-FILTER-COMM | Lookup/update case reasoning | `PacketModel.assign_filter_commute` | Direct |
| `paModFilter` | C, PA-MOD-FILTER | assign_test_same_field | `PacketModel.assign_filter` | Direct |
| `paFilterMod` | C, PA-FILTER-MOD | Local update_same_of_eq | `PacketModel.filter_assign` | Direct |
| `paModMod` | C, PA-MOD-MOD | Packet.update_update_same | `PacketModel.overwrite` | Direct |
| `paContra` | C, PA-CONTRA | paContra_sem | `PacketModel.filter_contradiction` | Direct |
| `paMatchAll` | C, PA-MATCH-ALL | paMatchAll_sem finite value cases | `PacketModel.match_all plus syntax-to-sum bridge` | Direct |



## Duplication and dependency audit

| Baseline duplication | Disposition |
|---|---|
| Local `StarClosure.map`, `snoc`, `last` in Axioms | Removed after equality congruence and KATLean unfold reuse |
| Semantic case proofs for 15 KA, six BA and seven PA laws | Replaced by the rule induction in `Derives.katSound` |
| `starLfpLeft`, `starLfpRight` | Kept as public compatibility wrappers around KATLean inequality induction |
| `paContra_sem`, `paMatchAll_sem` | Kept as public compatibility wrappers through KATLean-backed soundness |
| Private `update_same_of_eq` in Axioms | Removed after `PacketModel.filter_assign` reuse |
| Complete-test expansion | Kept as syntax-specific elaboration using `completeTestExpr_correct` |
| PA-MATCH-ALL list | Kept as syntax-specific elaboration. `matchAll_katInterp` identifies its four-value list with the finite KATLean sum |
| Low-level semantic identities in Semantics | Kept for compatibility and independent evaluator/interpretation correctness. Derives algebraic cases bypass these proofs |
| `Below`, finite-sum and Boolean normalization derivations | Kept because they construct syntactic Derives proofs. Equality in one model does not replace those proof terms |
| `normalize_correct` and normal-form membership proofs | Kept as construction-specific semantic proofs supporting normalization/completeness. Derived normalization soundness also follows through `normalize_derives` and the new soundness chain |

The focused regression inspects Lean proof-body constants. It requires
the 11 inherited semiring laws, four KATLean star theorems, four test
embedding laws, six KAT laws and all seven packet laws in
`Derives.katSound`. It rejects a dependency on `Derives.sound` in that
proof and checks the reverse soundness dependency. It also checks
`normalize_katInterp` and the E_DNK `Equations.netkat_sound` import chain.
The axiom audit covers semantic/algebraic soundness, representative law
families, normalization and the packet-prefix theorem. Remaining
independent reasoning is confined to syntax elaboration, normalization
construction and the lower semantic/evaluator layer listed above.
