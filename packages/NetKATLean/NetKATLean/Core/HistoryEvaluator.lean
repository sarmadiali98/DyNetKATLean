------------------------------------------------------------------------
-- History-level executable evaluator (H4)
--
-- A thin adapter over the existing packet-level evaluator `execute`
-- (NetKAT/Evaluator.lean): a policy is executed on the HEAD packet of a
-- nonempty history, and every computed output packet τ is paired with
-- the UNCHANGED original history tail:
--
--   executeHistory p ⟨σ, h⟩ =
--     match execute p σ with
--     | .supported outputs => .supported { ⟨τ, h⟩ | τ ∈ outputs }
--     | .unsupported       => .unsupported
--
-- No second NetKAT evaluation algorithm is implemented, and the
-- (countably infinite) history domain is never enumerated: outputs are
-- produced by `Finset.image` over the finite packet-level output set.
-- There is no `Fintype History` instance (see NetKAT/History.lean).
--
-- Correctness is reduced to two existing results, not reproved here:
--
--   - `execute_correct`      (packet-level evaluator correctness), and
--   - `historySemantics_iff_packetSemantics` (H3C, full unconditional
--     packet/history correspondence).
--
-- The main theorem `executeHistory_correct` is unconditional: the
-- evaluator is always supported and its computed output set is EXACTLY
-- the set of `HistorySemantics` outputs.
------------------------------------------------------------------------

import NetKATLean.Core.History
import NetKATLean.Core.HistorySemantics
import NetKATLean.Core.Evaluator

namespace DyNetKAT.NetKAT

/-! ## The result type -/

/-- Result of evaluating a NetKAT policy on a packet history.

    `supported` deliberately distinguishes a computed (possibly empty)
    set of output histories from an evaluator that does not support a
    term constructor: `.unsupported` is never an empty successful
    result. -/
inductive HistoryEvalResult where
  | supported (outputs : Finset History)
  | unsupported
  deriving DecidableEq

/-! ## The evaluator -/

/-- Execute a NetKAT policy on a nonempty packet history.

    The existing packet-level evaluator `execute` runs on the head
    packet; every output packet `τ` is lifted to the history
    `⟨τ, h.tail⟩`, so every output history retains the exact original
    tail.  The adapter is total on all eight dup-free NetKAT
    constructors because `execute` is (`execute_supported`). -/
def executeHistory
    (p : NetKAT) (h : History) : HistoryEvalResult :=
  match execute p h.head with
  | .supported outputs =>
      .supported (outputs.image fun τ => ⟨τ, h.tail⟩)
  | .unsupported =>
      .unsupported

/-! ## The adapter equation -/

/-- The adapter equation: once the packet-level evaluation of the head
    packet is supported with output set `A`, the history evaluator
    computes exactly the packet outputs paired with the original tail. -/
theorem executeHistory_eq_image
    (p : NetKAT) (h : History) (A : Finset CtxPkt)
    (hA : execute p h.head = .supported A) :
    executeHistory p h = .supported (A.image fun τ => ⟨τ, h.tail⟩) := by
  simp [executeHistory, hA]

/-! ## Totality -/

/-- **The history evaluator is supported for every policy and history.**

    Reuses the packet-level totality theorem `execute_supported`; no
    additional assumptions. -/
theorem executeHistory_supported
    (p : NetKAT) (h : History) :
    ∃ B : Finset History,
      executeHistory p h = .supported B := by
  obtain ⟨A, hA⟩ := execute_supported p h.head
  exact ⟨A.image fun τ => ⟨τ, h.tail⟩, executeHistory_eq_image p h A hA⟩

/-! ## Correctness -/

/-- **Main correctness theorem (H4).**  The history evaluator is always
    supported, and its computed output set is EXACTLY the set of
    history-semantic outputs:

    `∀ h', HistorySemantics p h h' ↔ h' ∈ B`

    The theorem is unconditional: no semantic correctness hypotheses.

    Proof strategy (reusing existing results, nothing reproved):

    1. Obtain the packet-level output set `A` from `execute_correct
       p h.head`, together with its exactness `corrA`.
    2. The history output set is `A.image (fun τ => ⟨τ, h.tail⟩)` —
       every output packet `τ` paired with the original tail.
    3. Membership is characterized by `Finset.mem_image`.
    4. The full H3C correspondence
       `historySemantics_iff_packetSemantics p h.head h'.head h.tail
       h'.tail` converts `HistorySemantics p h h'` into
       `h'.tail = h.tail ∧ Semantics p h.head h'.head` and back.
    5. Both directions follow: a history-semantic output has the
       original tail, so its head packet lies in `A`; conversely a
       member of the image comes from a packet `τ ∈ A`, which is
       semantically reachable, and pairing with the original tail
       makes it history-semantic. -/
theorem executeHistory_correct
    (p : NetKAT) (h : History) :
    ∃ B : Finset History,
      executeHistory p h = .supported B ∧
      ∀ h', HistorySemantics p h h' ↔ h' ∈ B := by
  obtain ⟨σ, t⟩ := h
  obtain ⟨A, hA, corrA⟩ := execute_correct p σ
  refine ⟨A.image fun τ => (⟨τ, t⟩ : History), executeHistory_eq_image p ⟨σ, t⟩ A hA, ?_⟩
  letI : DecidableEq (History ctxSchema.Packet) := History.instDecidableEqHistory
  rintro ⟨τ', t'⟩
  rw [Finset.mem_image]
  constructor
  · -- History-semantic output ⇒ membership in the executable output set.
    intro hc
    obtain ⟨htail, hsem⟩ :=
      (historySemantics_iff_packetSemantics p σ τ' t t').mp hc
    exact ⟨τ', (corrA τ').mp hsem, by rw [htail]⟩
  · -- Membership in the executable output set ⇒ history-semantic output.
    rintro ⟨τ, hτ, heq⟩
    obtain ⟨eτ, et⟩ := history_mk_eq heq
    rw [eτ] at hτ
    rw [← et]
    exact (historySemantics_iff_packetSemantics p σ τ' t t).mpr
      ⟨rfl, (corrA τ').mpr hτ⟩

/-! ## Tail preservation and output characterization -/

/-- **Exact output-tail preservation.**  Every history in a supported
    evaluation output retains the exact original tail. -/
theorem executeHistory_preserves_tail
    (p : NetKAT) (h h' : History) (B : Finset History)
    (hmem : h' ∈ B)
    (heval : executeHistory p h = .supported B) :
    h'.tail = h.tail := by
  obtain ⟨B', hex, corr⟩ := executeHistory_correct p h
  have hB : B = B' := HistoryEvalResult.supported.inj (heval.symm.trans hex)
  exact historySemantics_preserves_tail p h h'
    ((corr h').mpr (by rw [← hB]; exact hmem))

/-- **Output characterization.**  The generated histories are exactly the
    packet-evaluator outputs (characterized semantically via
    `execute_correct`) paired with the original tail:

    `h' ∈ B ↔ ∃ τ, Semantics p h.head τ ∧ h' = ⟨τ, h.tail⟩` -/
theorem executeHistory_outputs_characterization
    (p : NetKAT) (h : History) (B : Finset History)
    (heval : executeHistory p h = .supported B) (h' : History) :
    h' ∈ B ↔ ∃ τ : CtxPkt, Semantics p h.head τ ∧ h' = ⟨τ, h.tail⟩ := by
  obtain ⟨A, hA, corrA⟩ := execute_correct p h.head
  have hB : B = A.image fun τ => ⟨τ, h.tail⟩ :=
    HistoryEvalResult.supported.inj
      (heval.symm.trans (executeHistory_eq_image p h A hA))
  rw [hB, Finset.mem_image]
  constructor
  · rintro ⟨τ, hτ, heq⟩
    exact ⟨τ, (corrA τ).mpr hτ, heq.symm⟩
  · rintro ⟨τ, hsem, heq⟩
    exact ⟨τ, (corrA τ).mp hsem, heq.symm⟩

end DyNetKAT.NetKAT
