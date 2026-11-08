import DyNetKAT

------------------------------------------------------------------------
-- Checks for the history-based NetKAT semantics
-- (`DyNetKAT.NetKAT.HistorySemantics`).
--
-- Run with:  lake env lean test_history_semantics.lean   (from lean/)
--
-- The semantic relation is a proposition, so the checks are lightweight
-- Lean proofs/examples rather than `#eval`s.  They demonstrate that the
-- relation genuinely operates over whole histories (head + tail), not
-- merely singleton packets.
--
-- The H3A section at the end checks the packet/history correspondence
-- for the star-free fragment (`HistoryStarFree`): history-level and
-- packet-level semantics agree, and the tail packet is preserved.
--
-- The H3B section checks the general Kleene-star correspondence through
-- `historySemantics_star_iff_packetSemantics` (one-step hypothesis).
--
-- The final H3C section checks the FULL UNCONDITIONAL correspondence
-- `historySemantics_iff_packetSemantics`: all eight constructors,
-- nested stars included, no hypotheses at all.
------------------------------------------------------------------------

open DyNetKAT.NetKAT

------------------------------------------------------------------------
-- Histories: a singleton and a two-packet history
------------------------------------------------------------------------

-- A singleton history: the paper's `σ :: ⟨⟩` (the SOS evaluation input
-- of rule `(cpolX;)`, Figure 8, p. 10).
def hSingle : History := History.singleton examplePacket

-- A history with at least two packets:
-- `examplePacket :: (examplePacket9 :: [])`.
def hTwo : History := ⟨examplePacket, [examplePacket9]⟩

example : hSingle.toList = [examplePacket] := rfl
example : hTwo.tail = [examplePacket9] := rfl
example : hTwo.toList = [examplePacket, examplePacket9] := rfl

------------------------------------------------------------------------
-- Identity preserves the entire history (singleton and multi-packet)
------------------------------------------------------------------------

example : HistorySemantics .id hSingle hSingle := rfl

example : HistorySemantics .id hTwo hTwo := rfl

------------------------------------------------------------------------
-- A matching test preserves the whole history
------------------------------------------------------------------------

-- `tpSrc = v8` holds on the head of `hTwo`, so the *entire* two-packet
-- history (head and tail) is preserved.
example : HistorySemantics (NetKAT.fieldTest .tpSrc .v8) hTwo hTwo :=
  historySem_test_true _ hTwo rfl

-- The same test fails on a head with tpSrc = v9: no output history at
-- all, whatever the requested output.
example (h' : History) :
    ¬ HistorySemantics (NetKAT.fieldTest .tpSrc .v8)
        (History.singleton examplePacket9) h' := by
  intro hc
  have hsat := (historySem_test _ _ _).mp hc
  have hhead : examplePacket9 FieldName.tpSrc = FieldValueEnum.v8 := hsat.2
  simp [examplePacket9] at hhead

------------------------------------------------------------------------
-- Assignment: head changes, tail preserved
------------------------------------------------------------------------

-- Generic form: the output history is exactly `⟨σ[f:=v], tail h⟩`.
example (f : FieldName) (v : FieldValueEnum) (h : History) :
    HistorySemantics (.assign1 f v) h ⟨Packet.update h.head f v, h.tail⟩ := rfl

-- On the two-packet history: the head is updated, the second packet
-- (the tail) is preserved verbatim.
example :
    HistorySemantics (.assign1 .tpSrc .v9) hTwo
      ⟨Packet.update examplePacket .tpSrc .v9, [examplePacket9]⟩ := rfl

example :
    (⟨Packet.update examplePacket .tpSrc .v9, [examplePacket9]⟩ : History).tail
      = [examplePacket9] := rfl

-- The tail-preservation theorem applied concretely.
example (f : FieldName) (v : FieldValueEnum) (h h' : History)
    (hc : HistorySemantics (.assign1 f v) h h') : h'.tail = h.tail :=
  historySem_assign1_tail f v h h' hc

------------------------------------------------------------------------
-- A simple sequence: assign, then test the assigned value
------------------------------------------------------------------------

-- `(tpSrc ← v9) ; (tpSrc = v9)` maps the singleton history to the
-- singleton history of the updated packet.
example :
    HistorySemantics (.seq (.assign1 .tpSrc .v9) (NetKAT.fieldTest .tpSrc .v9))
      hSingle (History.singleton (Packet.update examplePacket .tpSrc .v9)) := by
  refine ⟨History.singleton (Packet.update examplePacket .tpSrc .v9), ?_, ?_⟩
  · rfl
  · exact historySem_test_true _ _
      (by simp [satHistory, History.singleton, Packet.update])

-- Sequencing preserves the tail across both steps: on the two-packet
-- history, `(tpSrc ← v9) ; id` yields the two-packet history with the
-- updated head and the unchanged second packet.
example :
    HistorySemantics (.seq (.assign1 .tpSrc .v9) .id) hTwo
      ⟨Packet.update examplePacket .tpSrc .v9, [examplePacket9]⟩ := by
  refine ⟨⟨Packet.update examplePacket .tpSrc .v9, [examplePacket9]⟩, ?_, ?_⟩
  · rfl
  · rfl

------------------------------------------------------------------------
-- Star: zero iterations included
------------------------------------------------------------------------

example : HistorySemantics (.star .id) hTwo hTwo := historySem_star_refl _ _

-- One iteration of an assignment is also in the star.
example :
    HistorySemantics (.star (.assign1 .tpSrc .v9)) hTwo
      ⟨Packet.update examplePacket .tpSrc .v9, [examplePacket9]⟩ :=
  historySem_star_step _ _ _ _ rfl (historySem_star_refl _ _)

------------------------------------------------------------------------
-- H2: tail preservation for every dup-free policy
------------------------------------------------------------------------

-- The central theorem, at full generality: every dup-free NetKAT policy
-- preserves the tail of every (nonempty) history.
example (p : NetKAT) (h h' : History) (hs : HistorySemantics p h h') :
    h'.tail = h.tail :=
  historySemantics_preserves_tail p h h' hs

-- The output history of the tests below: head updated, two-packet tail
-- (`examplePacket9`) preserved verbatim.
def hTwoUpdated : History :=
  ⟨Packet.update examplePacket .tpSrc .v9, [examplePacket9]⟩

example : hTwoUpdated.tail = hTwo.tail := rfl

-- Assignment on the two-packet history: the tail survives.
example : hTwoUpdated.tail = hTwo.tail :=
  historySemantics_preserves_tail (.assign1 .tpSrc .v9) hTwo hTwoUpdated rfl

-- Sequential composition `(tpSrc ← v9) ; id` on the two-packet history:
-- the tail of the result equals the original tail.
example : hTwoUpdated.tail = hTwo.tail :=
  historySemantics_preserves_tail (.seq (.assign1 .tpSrc .v9) .id) hTwo
    hTwoUpdated ⟨hTwoUpdated, rfl, rfl⟩

-- Union on the two-packet history: the left branch (assignment) fires,
-- and the tail is preserved; the drop branch produces nothing.
example : hTwoUpdated.tail = hTwo.tail :=
  historySemantics_preserves_tail (.union (.assign1 .tpSrc .v9) .drop) hTwo
    hTwoUpdated (Or.inl rfl)

-- A one-step Kleene-star derivation on the two-packet history: the tail
-- is preserved.
example : hTwoUpdated.tail = hTwo.tail :=
  historySemantics_preserves_tail (.star (.assign1 .tpSrc .v9)) hTwo
    hTwoUpdated (historySem_star_step _ _ _ _ rfl (historySem_star_refl _ _))

-- Zero iterations of Kleene star: the history is unchanged, so the tail
-- is trivially preserved (on the two-packet history, not a singleton).
example : hTwo.tail = hTwo.tail :=
  historySemantics_preserves_tail (.star .id) hTwo hTwo
    (historySem_star_refl _ _)

-- Two iterations inside a star of a union: the first iteration fires the
-- v9-assignment, the second the v8-assignment; the tail never moves.
-- The closure argument covers every finite derivation, not just one step.
def hTwoTwice : History :=
  ⟨Packet.update (Packet.update examplePacket .tpSrc .v9) .tpSrc .v8,
    [examplePacket9]⟩

example : hTwoTwice.tail = hTwo.tail :=
  historySemantics_preserves_tail
    (.star (.union (.assign1 .tpSrc .v9) (.assign1 .tpSrc .v8))) hTwo hTwoTwice
    (historySem_star_step _ _ _ _ (Or.inl rfl)
      (historySem_star_step _ _ _ _ (Or.inr rfl) (historySem_star_refl _ _)))

-- The sequential-composition characterization: the intermediate history
-- of `(tpSrc ← v9) ; id` on the two-packet history has the original tail.
example :
    ∃ k, HistorySemantics (.assign1 .tpSrc .v9) hTwo k ∧
         HistorySemantics .id k hTwoUpdated ∧ k.tail = hTwo.tail :=
  historySemantics_seq_intermediate_tail (.assign1 .tpSrc .v9) .id hTwo
    hTwoUpdated ⟨hTwoUpdated, rfl, rfl⟩

------------------------------------------------------------------------
-- H3A: packet/history correspondence for the star-free fragment
--
-- `HistoryStarFree p` rules out Kleene star at every nesting depth; on
-- this fragment the history relation and the packet-level `Semantics`
-- coincide, with the output history keeping the *entire* input packet
-- list (`h' = h`), not just its tail.
--
-- All examples below use two-packet histories.  No Kleene-star
-- correspondence is claimed here (H3B).
------------------------------------------------------------------------

-- A second two-packet history whose head packet is `examplePacket9`.
def hTwo9 : History := ⟨examplePacket9, [examplePacket]⟩

example : hTwo9.tail = [examplePacket] := rfl
example : hTwo9.toList = [examplePacket9, examplePacket] := rfl

-- Star-free derivations for the examples below.
def sfId : HistoryStarFree .id := .id

def sfTest8 : HistoryStarFree (NetKAT.fieldTest .tpSrc .v8) := .test _

def sfTest9 : HistoryStarFree (NetKAT.fieldTest .tpSrc .v9) := .test _

def sfComplete : HistoryStarFree (.completeTest completeTestTpSrc8) :=
  .completeTest _

def sfAssign : HistoryStarFree (.assign1 .tpSrc .v9) := .assign1 _ _

def sfUnion : HistoryStarFree (.union (.assign1 .tpSrc .v9) .drop) :=
  .union _ _ (.assign1 _ _) .drop

def sfSeq :
    HistoryStarFree (.seq (.assign1 .tpSrc .v9) (NetKAT.fieldTest .tpSrc .v9)) :=
  .seq _ _ (.assign1 _ _) (.test _)

def sfNested :
    HistoryStarFree
      (.seq (.union (.assign1 .tpSrc .v9) .drop)
            (.union (NetKAT.fieldTest .tpSrc .v9) (.assign1 .tpDst .v1))) :=
  .seq _ _ (.union _ _ (.assign1 _ _) .drop)
    (.union _ _ (.test _) (.assign1 _ _))

-- 1. Identity: both semantics preserve the two-packet history.
example :
    HistorySemantics .id hTwo hTwo ↔
      hTwo.tail = hTwo.tail ∧ Semantics .id examplePacket examplePacket :=
  historySemantics_iff_packetSemantics_starFree .id sfId examplePacket
    examplePacket [examplePacket9] [examplePacket9]

-- 2. Matching field test (`tpSrc = v8` holds on the head of `hTwo`):
--    both semantics preserve the two-packet history.
example :
    HistorySemantics (NetKAT.fieldTest .tpSrc .v8) hTwo hTwo ↔
      hTwo.tail = hTwo.tail ∧
      Semantics (NetKAT.fieldTest .tpSrc .v8) examplePacket examplePacket :=
  historySemantics_iff_packetSemantics_starFree _ sfTest8 examplePacket
    examplePacket [examplePacket9] [examplePacket9]

-- 3. Nonmatching field test (`tpSrc = v8` fails on the head of `hTwo9`):
--    neither semantics produces an output; the correspondence transfers
--    the failure from the packet level to the history level.
example :
    ¬ HistorySemantics (NetKAT.fieldTest .tpSrc .v8) hTwo9 hTwo9 := by
  intro hc
  have hcorr :=
    (historySemantics_iff_packetSemantics_starFree
      (NetKAT.fieldTest .tpSrc .v8) sfTest8 examplePacket9 examplePacket9
      [examplePacket] [examplePacket]).mp hc
  have hf : Predicate.eval (.pFieldEq ⟨FieldName.tpSrc, FieldValueEnum.v8⟩)
      examplePacket9 = true :=
    (packetSem_test _ _ _).mp hcorr.2 |>.1
  simp [Predicate.eval, examplePacket9] at hf

-- A matching test on the other two-packet history: both semantics
-- preserve it, second packet included.
example :
    HistorySemantics (NetKAT.fieldTest .tpSrc .v9) hTwo9 hTwo9 ↔
      hTwo9.tail = hTwo9.tail ∧
      Semantics (NetKAT.fieldTest .tpSrc .v9) examplePacket9 examplePacket9 :=
  historySemantics_iff_packetSemantics_starFree _ sfTest9 examplePacket9
    examplePacket9 [examplePacket] [examplePacket]

-- 4. Complete test: `completeTestTpSrc8` matches the head of `hTwo`
--    exactly, so both semantics preserve the two-packet history.
example :
    HistorySemantics (.completeTest completeTestTpSrc8) hTwo hTwo ↔
      hTwo.tail = hTwo.tail ∧
      Semantics (.completeTest completeTestTpSrc8) examplePacket examplePacket :=
  historySemantics_iff_packetSemantics_starFree _ sfComplete examplePacket
    examplePacket [examplePacket9] [examplePacket9]

-- 5. Assignment: the head packet is updated at both levels while the
--    second packet (`examplePacket9`) is preserved verbatim.
example :
    HistorySemantics (.assign1 .tpSrc .v9) hTwo hTwoUpdated ↔
      hTwoUpdated.tail = hTwo.tail ∧
      Semantics (.assign1 .tpSrc .v9) examplePacket
        (Packet.update examplePacket .tpSrc .v9) :=
  historySemantics_iff_packetSemantics_starFree _ sfAssign examplePacket
    (Packet.update examplePacket .tpSrc .v9) [examplePacket9] [examplePacket9]

-- 6. Union: the assignment branch fires and `drop` produces nothing, at
--    both levels, with the second packet unchanged.
example :
    HistorySemantics (.union (.assign1 .tpSrc .v9) .drop) hTwo hTwoUpdated ↔
      hTwoUpdated.tail = hTwo.tail ∧
      Semantics (.union (.assign1 .tpSrc .v9) .drop) examplePacket
        (Packet.update examplePacket .tpSrc .v9) :=
  historySemantics_iff_packetSemantics_starFree _ sfUnion examplePacket
    (Packet.update examplePacket .tpSrc .v9) [examplePacket9] [examplePacket9]

-- 7. Sequential composition: `(tpSrc ← v9) ; (tpSrc = v9)` updates the
--    head and keeps the two-packet tail, at both levels.
example :
    HistorySemantics (.seq (.assign1 .tpSrc .v9) (NetKAT.fieldTest .tpSrc .v9))
        hTwo hTwoUpdated ↔
      hTwoUpdated.tail = hTwo.tail ∧
      Semantics (.seq (.assign1 .tpSrc .v9) (NetKAT.fieldTest .tpSrc .v9))
        examplePacket (Packet.update examplePacket .tpSrc .v9) :=
  historySemantics_iff_packetSemantics_starFree _ sfSeq examplePacket
    (Packet.update examplePacket .tpSrc .v9) [examplePacket9] [examplePacket9]

-- 8. Nested expression combining union and sequence:
--    `(tpSrc ← v9 + 0) ; (tpSrc = v9 + tpDst ← v1)`.  The assignment
--    branch fires first, then the matching test branch; the second
--    packet is unchanged at both levels.
example :
    HistorySemantics
      (.seq (.union (.assign1 .tpSrc .v9) .drop)
            (.union (NetKAT.fieldTest .tpSrc .v9) (.assign1 .tpDst .v1)))
      hTwo hTwoUpdated ↔
      hTwoUpdated.tail = hTwo.tail ∧
      Semantics
      (.seq (.union (.assign1 .tpSrc .v9) .drop)
            (.union (NetKAT.fieldTest .tpSrc .v9) (.assign1 .tpDst .v1)))
      examplePacket (Packet.update examplePacket .tpSrc .v9) :=
  historySemantics_iff_packetSemantics_starFree _ sfNested examplePacket
    (Packet.update examplePacket .tpSrc .v9) [examplePacket9] [examplePacket9]

-- Reverse direction of the correspondence: a packet-level derivation
-- lifts to the history level with the unchanged two-packet tail.
example :
    HistorySemantics (.seq (.assign1 .tpSrc .v9) (NetKAT.fieldTest .tpSrc .v9))
      hTwo hTwoUpdated :=
  (historySemantics_iff_packetSemantics_starFree _ sfSeq examplePacket
    (Packet.update examplePacket .tpSrc .v9)
    [examplePacket9] [examplePacket9]).mpr
    ⟨rfl, ⟨Packet.update examplePacket .tpSrc .v9, rfl, ⟨rfl, rfl⟩⟩⟩

-- 9. The star-free tail consequence: the packet-level output relation
--    agrees with the history-level semantics while the second packet
--    remains unchanged (`hTwoUpdated.tail = hTwo.tail = [examplePacket9]`).
example : hTwoUpdated.tail = hTwo.tail :=
  historySemantics_packetSemantics_starFree_tail (.assign1 .tpSrc .v9) sfAssign
    examplePacket (Packet.update examplePacket .tpSrc .v9)
    [examplePacket9] [examplePacket9] rfl

-- Generic form of the star-free tail consequence.
example (p : NetKAT) (hp : HistoryStarFree p) (σ τ : CtxPkt)
    (h h' : List CtxPkt) (hc : HistorySemantics p ⟨σ, h⟩ ⟨τ, h'⟩) :
    h' = h :=
  historySemantics_packetSemantics_starFree_tail p hp σ τ h h' hc

 ------------------------------------------------------------------------
 -- H3B: the general Kleene-star packet/history correspondence
 --
 -- `historySemantics_star_iff_packetSemantics` needs only a ONE-STEP
 -- correspondence hypothesis for the star body; the body may be any
 -- NetKAT policy (nested stars included).  The one-step hypotheses used
 -- below are instances of H3A for star-free bodies.
 --
 -- All examples use two-packet histories and establish the
 -- correspondence THROUGH the new theorem (both directions), not by
 -- proving history-level star properties in isolation.  No executable
 -- enumeration is involved.
 ------------------------------------------------------------------------

 -- Generic one-step correspondence for a star-free body, obtained from H3A.
 def starFreeStep (p : NetKAT) (hp : HistoryStarFree p) :
     ∀ (σ τ : CtxPkt) (h h' : List CtxPkt),
       HistorySemantics p ⟨σ, h⟩ ⟨τ, h'⟩ ↔ h' = h ∧ Semantics p σ τ :=
   fun σ τ h h' => historySemantics_iff_packetSemantics_starFree p hp σ τ h h'

 def sfAssignV8 : HistoryStarFree (.assign1 .tpSrc .v8) := .assign1 _ _

 def sfUnionAssigns :
     HistoryStarFree (.union (.assign1 .tpSrc .v9) (.assign1 .tpSrc .v8)) :=
   .union _ _ (.assign1 _ _) (.assign1 _ _)

 -- The one-step history semantics of the sequential body
 -- `(tpSrc ← v9) ; (tpSrc = v9)` on the two-packet history, via H3A.
 def hSeqStep :
     HistorySemantics (.seq (.assign1 .tpSrc .v9) (NetKAT.fieldTest .tpSrc .v9))
       hTwo hTwoUpdated :=
   (historySemantics_iff_packetSemantics_starFree _ sfSeq examplePacket
     (Packet.update examplePacket .tpSrc .v9)
     [examplePacket9] [examplePacket9]).mpr
     ⟨rfl, ⟨Packet.update examplePacket .tpSrc .v9, rfl, ⟨rfl, rfl⟩⟩⟩

 -- A third two-packet history: head with `tpSrc` updated to v8 (the
 -- v8-branch endpoint of the union star below).
 def hTwoV8 : History :=
   ⟨Packet.update examplePacket .tpSrc .v8, [examplePacket9]⟩

 example : hTwoV8.tail = hTwo.tail := rfl

 -- 1. Zero iterations of the star (`F⁰(h) = {h}`): the correspondence
 --    reduces both sides to reflexivity; the two-packet history is
 --    preserved verbatim.
 example :
     hTwo.tail = hTwo.tail ∧
       Semantics (.star (.assign1 .tpSrc .v9)) examplePacket examplePacket :=
   (historySemantics_star_iff_packetSemantics _ (starFreeStep _ sfAssign)
     examplePacket examplePacket [examplePacket9] [examplePacket9]).mp
     (historySem_star_refl _ _)

 example :
     HistorySemantics (.star (.assign1 .tpSrc .v9)) hTwo hTwo :=
   (historySemantics_star_iff_packetSemantics _ (starFreeStep _ sfAssign)
     examplePacket examplePacket [examplePacket9] [examplePacket9]).mpr
     ⟨rfl, star_refl _ _⟩

 -- 2. One iteration: `(tpSrc ← v9)*` maps the two-packet history to the
 --    updated-head history at both levels; the second packet survives.
 example :
     hTwoUpdated.tail = hTwo.tail ∧
       Semantics (.star (.assign1 .tpSrc .v9)) examplePacket
         (Packet.update examplePacket .tpSrc .v9) :=
   (historySemantics_star_iff_packetSemantics _ (starFreeStep _ sfAssign)
     examplePacket (Packet.update examplePacket .tpSrc .v9)
     [examplePacket9] [examplePacket9]).mp
     (historySem_star_step _ _ _ _ rfl (historySem_star_refl _ _))

 example :
     HistorySemantics (.star (.assign1 .tpSrc .v9)) hTwo hTwoUpdated :=
   (historySemantics_star_iff_packetSemantics _ (starFreeStep _ sfAssign)
     examplePacket (Packet.update examplePacket .tpSrc .v9)
     [examplePacket9] [examplePacket9]).mpr
     ⟨rfl, star_step _ _ _ rfl⟩

 -- 3. Two iterations of a star over a union: the first iteration fires
 --    the v9-assignment branch, the second the v8-branch; the head is
 --    updated twice while the second packet never moves.  The closure
 --    argument covers the two-step derivation, not a fixed bound.
 example :
     hTwoTwice.tail = hTwo.tail ∧
       Semantics
         (.star (.union (.assign1 .tpSrc .v9) (.assign1 .tpSrc .v8)))
         examplePacket
         (Packet.update (Packet.update examplePacket .tpSrc .v9) .tpSrc .v8) :=
   (historySemantics_star_iff_packetSemantics _ (starFreeStep _ sfUnionAssigns)
     examplePacket
     (Packet.update (Packet.update examplePacket .tpSrc .v9) .tpSrc .v8)
     [examplePacket9] [examplePacket9]).mp
     (historySem_star_step _ _ _ _ (Or.inl rfl)
       (historySem_star_step _ _ _ _ (Or.inr rfl) (historySem_star_refl _ _)))

 example :
     HistorySemantics
       (.star (.union (.assign1 .tpSrc .v9) (.assign1 .tpSrc .v8)))
       hTwo hTwoTwice :=
   (historySemantics_star_iff_packetSemantics _ (starFreeStep _ sfUnionAssigns)
     examplePacket
     (Packet.update (Packet.update examplePacket .tpSrc .v9) .tpSrc .v8)
     [examplePacket9] [examplePacket9]).mpr
     ⟨rfl, StarClosure.step (Or.inl rfl)
       (StarClosure.step (Or.inr rfl) (StarClosure.refl _))⟩

 -- 4. Star over a union, one iteration through the other branch
 --    (`tpSrc ← v8`): the v8-branch fires at both levels on the
 --    two-packet history.
 example :
     hTwoV8.tail = hTwo.tail ∧
       Semantics
         (.star (.union (.assign1 .tpSrc .v9) (.assign1 .tpSrc .v8)))
         examplePacket (Packet.update examplePacket .tpSrc .v8) :=
   (historySemantics_star_iff_packetSemantics _ (starFreeStep _ sfUnionAssigns)
     examplePacket (Packet.update examplePacket .tpSrc .v8)
     [examplePacket9] [examplePacket9]).mp
     (historySem_star_step _ _ _ _ (Or.inr rfl) (historySem_star_refl _ _))

 example :
     HistorySemantics
       (.star (.union (.assign1 .tpSrc .v9) (.assign1 .tpSrc .v8)))
       hTwo hTwoV8 :=
   (historySemantics_star_iff_packetSemantics _ (starFreeStep _ sfUnionAssigns)
     examplePacket (Packet.update examplePacket .tpSrc .v8)
     [examplePacket9] [examplePacket9]).mpr
     ⟨rfl, StarClosure.step (Or.inr rfl) (StarClosure.refl _)⟩

 -- 5. Star over a sequential composition `(tpSrc ← v9) ; (tpSrc = v9)`:
 --    one iteration updates the head and passes the test, at both
 --    levels, with the two-packet tail intact.
 example :
     hTwoUpdated.tail = hTwo.tail ∧
       Semantics
         (.star (.seq (.assign1 .tpSrc .v9) (NetKAT.fieldTest .tpSrc .v9)))
         examplePacket (Packet.update examplePacket .tpSrc .v9) :=
   (historySemantics_star_iff_packetSemantics _ (starFreeStep _ sfSeq)
     examplePacket (Packet.update examplePacket .tpSrc .v9)
     [examplePacket9] [examplePacket9]).mp
     (historySem_star_step _ _ _ _ hSeqStep (historySem_star_refl _ _))

 example :
     HistorySemantics
       (.star (.seq (.assign1 .tpSrc .v9) (NetKAT.fieldTest .tpSrc .v9)))
       hTwo hTwoUpdated :=
   (historySemantics_star_iff_packetSemantics _ (starFreeStep _ sfSeq)
     examplePacket (Packet.update examplePacket .tpSrc .v9)
     [examplePacket9] [examplePacket9]).mpr
     ⟨rfl, star_step _ _ _
       ⟨Packet.update examplePacket .tpSrc .v9, rfl, ⟨rfl, rfl⟩⟩⟩

 -- 6. The star-free-body corollary
 --    (`historySemantics_star_iff_packetSemantics_starFreeBody`): the
 --    H3A one-step hypothesis is discharged automatically; both
 --    directions on the two-packet history.
 example :
     HistorySemantics (.star (.assign1 .tpSrc .v9)) hTwo hTwoUpdated ↔
       hTwoUpdated.tail = hTwo.tail ∧
       Semantics (.star (.assign1 .tpSrc .v9)) examplePacket
         (Packet.update examplePacket .tpSrc .v9) :=
   historySemantics_star_iff_packetSemantics_starFreeBody _ sfAssign
     examplePacket (Packet.update examplePacket .tpSrc .v9)
     [examplePacket9] [examplePacket9]

 example :
     HistorySemantics (.star (.assign1 .tpSrc .v9)) hTwo hTwoUpdated :=
   (historySemantics_star_iff_packetSemantics_starFreeBody _ sfAssign
     examplePacket (Packet.update examplePacket .tpSrc .v9)
     [examplePacket9] [examplePacket9]).mpr ⟨rfl, star_step _ _ _ rfl⟩

 -- 7. Explicit verification that the history tail remains unchanged:
 --    the forward direction of the general theorem yields `h' = h` —
 --    the WHOLE packet list is preserved, second packet included.
 example (p : NetKAT)
     (hstep : ∀ (σ τ : CtxPkt) (h h' : List CtxPkt),
       HistorySemantics p ⟨σ, h⟩ ⟨τ, h'⟩ ↔ h' = h ∧ Semantics p σ τ)
     (σ τ : CtxPkt) (h h' : List CtxPkt)
     (hc : HistorySemantics (.star p) ⟨σ, h⟩ ⟨τ, h'⟩) :
     h' = h :=
   ((historySemantics_star_iff_packetSemantics p hstep σ τ h h').mp hc).1

 example : hTwoTwice.tail = hTwo.tail := rfl

 example : hTwoV8.tail = hTwo.tail := rfl

 -- Reusability for nested stars: the general theorem applies verbatim to
 -- a body that is itself a star, given the one-step correspondence for
 -- that body.  (H3C will discharge such hypotheses unconditionally.)
 example (q : NetKAT)
     (hstepQ : ∀ (σ τ : CtxPkt) (h h' : List CtxPkt),
       HistorySemantics (.star q) ⟨σ, h⟩ ⟨τ, h'⟩ ↔
         h' = h ∧ Semantics (.star q) σ τ)
     (σ τ : CtxPkt) (h h' : List CtxPkt) :
     HistorySemantics (.star (.star q)) ⟨σ, h⟩ ⟨τ, h'⟩ ↔
       h' = h ∧ Semantics (.star (.star q)) σ τ :=
   historySemantics_star_iff_packetSemantics _ hstepQ σ τ h h'

 ------------------------------------------------------------------------
 -- H3C: the full unconditional packet/history correspondence
 --
 -- `historySemantics_iff_packetSemantics` takes NO hypothesis: no
 -- star-freeness, no termination, no iteration bounds, no finite
 -- history domains, no definedness or recursive environments.  Every
 -- example below goes THROUGH the theorem on two-packet histories and
 -- demonstrates both directions of the correspondence (an `iff` example
 -- discharges both at once; `.mp`/`.mpr` examples make each direction
 -- explicit).  No executable enumeration is involved.
 ------------------------------------------------------------------------

 -- 1. The five primitive constructors.

 -- 1a. `drop`: no output history at either level (forward direction —
 --     the backward direction is vacuous since `⟦0⟧ = ∅`).
 example (τ : CtxPkt) (h' : List CtxPkt) :
     ¬ HistorySemantics .drop ⟨examplePacket, [examplePacket9]⟩ ⟨τ, h'⟩ :=
   fun hc => ((historySemantics_iff_packetSemantics .drop examplePacket τ
     [examplePacket9] h').mp hc).2

 -- 1b. `id`: both directions at once.
 example :
     HistorySemantics .id hTwo hTwo ↔
       hTwo.tail = hTwo.tail ∧ Semantics .id examplePacket examplePacket :=
   historySemantics_iff_packetSemantics .id examplePacket examplePacket
     [examplePacket9] [examplePacket9]

 -- 1c. Matching field test (`tpSrc = v8` holds on the head of `hTwo`):
 --     both directions preserve the two-packet history.
 example :
     HistorySemantics (NetKAT.fieldTest .tpSrc .v8) hTwo hTwo ↔
       hTwo.tail = hTwo.tail ∧
       Semantics (NetKAT.fieldTest .tpSrc .v8) examplePacket examplePacket :=
   historySemantics_iff_packetSemantics _ examplePacket examplePacket
     [examplePacket9] [examplePacket9]

 -- 1c'. Failing field test (`tpSrc = v8` fails on the head of `hTwo9`):
 --      the theorem transfers the packet-level failure to the history
 --      level (forward direction).
 example :
     ¬ HistorySemantics (NetKAT.fieldTest .tpSrc .v8) hTwo9 hTwo9 := by
   intro hc
   have hcorr :=
     (historySemantics_iff_packetSemantics _ examplePacket9 examplePacket9
       [examplePacket] [examplePacket]).mp hc
   have hf : Predicate.eval (.pFieldEq ⟨FieldName.tpSrc, FieldValueEnum.v8⟩)
       examplePacket9 = true :=
     (packetSem_test _ _ _).mp hcorr.2 |>.1
   simp [Predicate.eval, examplePacket9] at hf

 -- 1d. Complete test: `completeTestTpSrc8` matches the head of `hTwo`
 --     exactly; both directions preserve the two-packet history.
 example :
     HistorySemantics (.completeTest completeTestTpSrc8) hTwo hTwo ↔
       hTwo.tail = hTwo.tail ∧
       Semantics (.completeTest completeTestTpSrc8) examplePacket examplePacket :=
   historySemantics_iff_packetSemantics _ examplePacket examplePacket
     [examplePacket9] [examplePacket9]

 -- 1e. Assignment: the head is updated and the second packet survives,
 --     at both levels, both directions.
 example :
     HistorySemantics (.assign1 .tpSrc .v9) hTwo hTwoUpdated ↔
       hTwoUpdated.tail = hTwo.tail ∧
       Semantics (.assign1 .tpSrc .v9) examplePacket
         (Packet.update examplePacket .tpSrc .v9) :=
   historySemantics_iff_packetSemantics _ examplePacket
     (Packet.update examplePacket .tpSrc .v9) [examplePacket9] [examplePacket9]

 -- 2. Union: the assignment branch fires and `drop` produces nothing,
 --    at both levels, both directions.
 example :
     HistorySemantics (.union (.assign1 .tpSrc .v9) .drop) hTwo hTwoUpdated ↔
       hTwoUpdated.tail = hTwo.tail ∧
       Semantics (.union (.assign1 .tpSrc .v9) .drop) examplePacket
         (Packet.update examplePacket .tpSrc .v9) :=
   historySemantics_iff_packetSemantics _ examplePacket
     (Packet.update examplePacket .tpSrc .v9) [examplePacket9] [examplePacket9]

 -- 3. Sequence: `(tpSrc ← v9) ; (tpSrc = v9)` updates the head and keeps
 --    the two-packet tail, at both levels, both directions.
 example :
     HistorySemantics (.seq (.assign1 .tpSrc .v9) (NetKAT.fieldTest .tpSrc .v9))
         hTwo hTwoUpdated ↔
       hTwoUpdated.tail = hTwo.tail ∧
       Semantics (.seq (.assign1 .tpSrc .v9) (NetKAT.fieldTest .tpSrc .v9))
         examplePacket (Packet.update examplePacket .tpSrc .v9) :=
   historySemantics_iff_packetSemantics _ examplePacket
     (Packet.update examplePacket .tpSrc .v9) [examplePacket9] [examplePacket9]

 -- 4. Star of an assignment.  Forward: a one-iteration history-level
 --    derivation yields the packet-level star semantics.
 example :
     hTwoUpdated.tail = hTwo.tail ∧
       Semantics (.star (.assign1 .tpSrc .v9)) examplePacket
         (Packet.update examplePacket .tpSrc .v9) :=
   (historySemantics_iff_packetSemantics _ examplePacket
     (Packet.update examplePacket .tpSrc .v9)
     [examplePacket9] [examplePacket9]).mp
     (historySem_star_step _ _ _ _ rfl (historySem_star_refl _ _))

 -- 4 (backward): the packet-level star derivation lifts to the history
 -- level with the two-packet tail intact.
 example :
     HistorySemantics (.star (.assign1 .tpSrc .v9)) hTwo hTwoUpdated :=
   (historySemantics_iff_packetSemantics _ examplePacket
     (Packet.update examplePacket .tpSrc .v9)
     [examplePacket9] [examplePacket9]).mpr
     ⟨rfl, star_step _ _ _ rfl⟩

 -- 5. Star of a union, forward: two iterations (v9-branch, then
 --    v8-branch); the two-packet tail never moves.
 example :
     hTwoTwice.tail = hTwo.tail ∧
       Semantics
         (.star (.union (.assign1 .tpSrc .v9) (.assign1 .tpSrc .v8)))
         examplePacket
         (Packet.update (Packet.update examplePacket .tpSrc .v9) .tpSrc .v8) :=
   (historySemantics_iff_packetSemantics _ examplePacket
     (Packet.update (Packet.update examplePacket .tpSrc .v9) .tpSrc .v8)
     [examplePacket9] [examplePacket9]).mp
     (historySem_star_step _ _ _ _ (Or.inl rfl)
       (historySem_star_step _ _ _ _ (Or.inr rfl) (historySem_star_refl _ _)))

 -- 5 (backward): the two-step packet-level closure lifts to the history
 -- level.
 example :
     HistorySemantics
       (.star (.union (.assign1 .tpSrc .v9) (.assign1 .tpSrc .v8)))
       hTwo hTwoTwice :=
   (historySemantics_iff_packetSemantics _ examplePacket
     (Packet.update (Packet.update examplePacket .tpSrc .v9) .tpSrc .v8)
     [examplePacket9] [examplePacket9]).mpr
     ⟨rfl, StarClosure.step (Or.inl rfl)
       (StarClosure.step (Or.inr rfl) (StarClosure.refl _))⟩

 -- 6. Star of a sequential composition, forward: one iteration updates
 --    the head and passes the test, two-packet tail intact.
 example :
     hTwoUpdated.tail = hTwo.tail ∧
       Semantics
         (.star (.seq (.assign1 .tpSrc .v9) (NetKAT.fieldTest .tpSrc .v9)))
         examplePacket (Packet.update examplePacket .tpSrc .v9) :=
   (historySemantics_iff_packetSemantics _ examplePacket
     (Packet.update examplePacket .tpSrc .v9)
     [examplePacket9] [examplePacket9]).mp
     (historySem_star_step _ _ _ _ hSeqStep (historySem_star_refl _ _))

 -- 6 (backward): the packet-level star of the sequence lifts to the
 -- history level.
 example :
     HistorySemantics
       (.star (.seq (.assign1 .tpSrc .v9) (NetKAT.fieldTest .tpSrc .v9)))
       hTwo hTwoUpdated :=
   (historySemantics_iff_packetSemantics _ examplePacket
     (Packet.update examplePacket .tpSrc .v9)
     [examplePacket9] [examplePacket9]).mpr
     ⟨rfl, star_step _ _ _
       ⟨Packet.update examplePacket .tpSrc .v9, rfl, ⟨rfl, rfl⟩⟩⟩

 -- 7. Nested star `star (star p)`: the correspondence is now
 --    UNCONDITIONAL — no one-step hypothesis needs to be discharged by
 --    hand (contrast with the H3B section above).  Both directions at
 --    once through the theorem.
 example :
     HistorySemantics (.star (.star (.assign1 .tpSrc .v9))) hTwo hTwoUpdated ↔
       hTwoUpdated.tail = hTwo.tail ∧
       Semantics (.star (.star (.assign1 .tpSrc .v9))) examplePacket
         (Packet.update examplePacket .tpSrc .v9) :=
   historySemantics_iff_packetSemantics _ examplePacket
     (Packet.update examplePacket .tpSrc .v9) [examplePacket9] [examplePacket9]

 -- 7 (forward, explicit derivation): an outer star taking one inner-star
 -- step maps to the packet level through the theorem.
 example :
     hTwoUpdated.tail = hTwo.tail ∧
       Semantics (.star (.star (.assign1 .tpSrc .v9))) examplePacket
         (Packet.update examplePacket .tpSrc .v9) :=
   (historySemantics_iff_packetSemantics _ examplePacket
     (Packet.update examplePacket .tpSrc .v9)
     [examplePacket9] [examplePacket9]).mp
     (historySem_star_step (.star (.assign1 .tpSrc .v9)) hTwo hTwoUpdated
       hTwoUpdated
       (historySem_star_step (.assign1 .tpSrc .v9) hTwo hTwoUpdated hTwoUpdated
         rfl (historySem_star_refl _ _))
       (historySem_star_refl _ _))

 -- 7 (backward, explicit derivation): the nested packet-level closure
 -- lifts to the nested history-level star.
 example :
     HistorySemantics (.star (.star (.assign1 .tpSrc .v9))) hTwo hTwoUpdated :=
   (historySemantics_iff_packetSemantics _ examplePacket
     (Packet.update examplePacket .tpSrc .v9)
     [examplePacket9] [examplePacket9]).mpr
     ⟨rfl, StarClosure.step
       (StarClosure.step rfl (StarClosure.refl _)) (StarClosure.refl _)⟩

 -- 8. Mixed expression with nested star, union and sequence:
 --    `star ((tpSrc ← v9 + 0) ; (tpDst ← v1)*)`.  Forward: one outer
 --    iteration whose union branch fires and whose inner star takes zero
 --    steps; the two-packet tail is preserved.
 example :
     hTwoUpdated.tail = hTwo.tail ∧
       Semantics
         (.star (.seq (.union (.assign1 .tpSrc .v9) .drop)
                      (.star (.assign1 .tpDst .v1))))
         examplePacket (Packet.update examplePacket .tpSrc .v9) :=
   (historySemantics_iff_packetSemantics _ examplePacket
     (Packet.update examplePacket .tpSrc .v9)
     [examplePacket9] [examplePacket9]).mp
     (historySem_star_step
       (.seq (.union (.assign1 .tpSrc .v9) .drop) (.star (.assign1 .tpDst .v1)))
       hTwo hTwoUpdated hTwoUpdated
       ⟨hTwoUpdated, Or.inl rfl, historySem_star_refl _ _⟩
       (historySem_star_refl _ _))

 -- 8 (backward): the mixed packet-level derivation lifts to the history
 -- level.
 example :
     HistorySemantics
       (.star (.seq (.union (.assign1 .tpSrc .v9) .drop)
                    (.star (.assign1 .tpDst .v1))))
       hTwo hTwoUpdated :=
   (historySemantics_iff_packetSemantics _ examplePacket
     (Packet.update examplePacket .tpSrc .v9)
     [examplePacket9] [examplePacket9]).mpr
     ⟨rfl, star_step _ _ _
       ⟨Packet.update examplePacket .tpSrc .v9, Or.inl rfl, StarClosure.refl _⟩⟩

 -- 9. A nontrivial nested-star history-level derivation: an outer star
 --    of `star (union ...)` whose inner star takes two iterations
 --    (v9-branch, then v8-branch).  The head is updated twice while the
 --    second packet never moves.
 def nestedStarDeriv :
     HistorySemantics
       (.star (.star (.union (.assign1 .tpSrc .v9) (.assign1 .tpSrc .v8))))
       hTwo hTwoTwice :=
   historySem_star_step
     (.star (.union (.assign1 .tpSrc .v9) (.assign1 .tpSrc .v8)))
     hTwo hTwoTwice hTwoTwice
     (historySem_star_step (.union (.assign1 .tpSrc .v9) (.assign1 .tpSrc .v8))
       hTwo hTwoUpdated hTwoTwice (Or.inl rfl)
       (historySem_star_step (.union (.assign1 .tpSrc .v9) (.assign1 .tpSrc .v8))
         hTwoUpdated hTwoTwice hTwoTwice (Or.inr rfl)
         (historySem_star_refl _ _)))
     (historySem_star_refl _ _)

 -- 9 (explicit whole-tail check): the forward direction of the theorem
 -- yields the WHOLE packet list equality `hTwoTwice.tail = hTwo.tail`
 -- — the entire original history tail `[examplePacket9]` remains
 -- unchanged after the nontrivial nested-star derivation.
 example :
     hTwoTwice.tail = hTwo.tail ∧
       Semantics
         (.star (.star (.union (.assign1 .tpSrc .v9) (.assign1 .tpSrc .v8))))
         examplePacket
         (Packet.update (Packet.update examplePacket .tpSrc .v9) .tpSrc .v8) :=
   (historySemantics_iff_packetSemantics _ examplePacket
     (Packet.update (Packet.update examplePacket .tpSrc .v9) .tpSrc .v8)
     [examplePacket9] [examplePacket9]).mp nestedStarDeriv

 -- 10. The H3C corollary (`historySemantics_preserves_packetList`):
 --     every history-level derivation — nested stars included, no
 --     hypotheses — preserves the entire packet list.  Generic form and
 --     the concrete nested-star derivation above.
 example (p : NetKAT) (σ τ : CtxPkt) (h h' : List CtxPkt)
     (hc : HistorySemantics p ⟨σ, h⟩ ⟨τ, h'⟩) :
     h' = h :=
   historySemantics_preserves_packetList p σ τ h h' hc

 example : hTwoTwice.tail = hTwo.tail :=
   historySemantics_preserves_packetList _ _ _ _ _ nestedStarDeriv
