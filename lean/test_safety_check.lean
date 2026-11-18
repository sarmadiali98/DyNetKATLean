import DyNetKAT

 ------------------------------------------------------------------------
 -- Standalone tests for the S5B formal safety-checking criterion
 -- (`DyNetKAT.DyNetKAT.SafetyCheck`, paper §V, Eqs. (34)–(35)).
 --
 -- Run with:  lake env lean test_safety_check.lean   (from lean/)
 --
 -- Executable checks use the existing verified evaluator and the
 -- verified zero checker `netkatIsZero` over the finite `CtxPkt`
 -- domain.  Correctness is carried by the machine-checked theorems of
 -- `SafetyCheck.lean` (`checkCondition34_correct`,
 -- `checkCondition35_correct`, `checkCondition34_headSpec`,
 -- `checkCondition35_tailHeadSpec`, `safetyCheck_supported`,
 -- `safetyCheck_pipeline_semantic`); the propositional `example`s below
 -- apply those theorems directly.  No `native_decide` is used.
 --
 -- Fixture: the paper's stateful firewall shape (§V).  `in := port =
 -- ext`, `out := port = int`, `R = {rcfg_{secConReq,1}}`; the initial
 -- configuration keeps ext-packets at ext, and the configuration after
 -- the reconfiguration forwards ext to int.
 ------------------------------------------------------------------------

 set_option linter.dupNamespace false

 namespace DyNetKAT.DyNetKAT.SafetyCheckTests

 open DyNetKAT.NetKAT

 ------------------------------------------------------------------------
 -- Fixtures
 ------------------------------------------------------------------------

 /-- Ingress predicate `in := port = ext` (ext encoded as v8). -/
 abbrev ingressP : NetKAT := NetKAT.fieldTest .port .v8

 /-- Egress predicate `out := port = int` (int encoded as v9). -/
 abbrev egressP : NetKAT := NetKAT.fieldTest .port .v9

 /-- Initial configuration policy: packets at ext stay at ext. -/
 abbrev Hinit : NetKAT :=
   NetKAT.seq (NetKAT.fieldTest .port .v8) (NetKAT.assign1 .port .v8)

 /-- Post-reconfiguration configuration policy: ext forwards to int. -/
 abbrev Hpost : NetKAT :=
   NetKAT.seq (NetKAT.fieldTest .port .v8) (NetKAT.assign1 .port .v9)

 /-- The paper's reconfiguration-event set `R = {rcfg_{secConReq,1}}`. -/
 abbrev Rsec : ReconfigSet := {("secConReq", NetKAT.id)}

 /-- The initial DyNetKAT process: initial configuration, then the
     reconfiguration on `secConReq`, then the new configuration. -/
 def firewallInit : DyNetKAT :=
   .nSeq Hinit (.rcfgPrefix "secConReq" NetKAT.id (.nSeq Hpost .deadlock))

 /-- Variant whose INITIAL configuration already forwards ext to int
     (condition (34) must fail). -/
 def firewallBad34 : DyNetKAT :=
   .nSeq Hpost (.rcfgPrefix "secConReq" NetKAT.id (.nSeq Hpost .deadlock))

 /-- Variant whose POST-reconfiguration configuration still blocks the
     flow (condition (35) must fail). -/
 def firewallBad35 : DyNetKAT :=
   .nSeq Hinit (.rcfgPrefix "secConReq" NetKAT.id (.nSeq Hinit .deadlock))

 /-- A packet at port ext. -/
 def extPacket : CtxPkt := fun
   | .port => .v8
   | _ => .v0

 /-- A packet at port int. -/
 def intPacket : CtxPkt := fun
   | .port => .v9
   | _ => .v0

 theorem extPacket_update : Packet.update extPacket .port .v9 = intPacket := by
   funext f
   cases f <;> simp [extPacket, intPacket, Packet.update]

 /-- Verdict helpers for the executable checks. -/
 def c34holds (ingress egress : NetKAT) (D : DyNetKAT) : Bool :=
   checkCondition34 ingress egress D == some true

 def c35holds (ingress egress : NetKAT) (R : ReconfigSet) (D : DyNetKAT) : Bool :=
   checkCondition35 ingress egress R D == some true

 def c34notEvaluable (ingress egress : NetKAT) (D : DyNetKAT) : Bool :=
   checkCondition34 ingress egress D == none

 def c35notEvaluable (ingress egress : NetKAT) (R : ReconfigSet) (D : DyNetKAT) : Bool :=
   checkCondition35 ingress egress R D == none

 ------------------------------------------------------------------------
 -- 1. Initial condition (34) succeeds on the firewall fixture.
 ------------------------------------------------------------------------

 #eval c34holds ingressP egressP firewallInit                          -- true

 ------------------------------------------------------------------------
 -- 2. Initial condition (34) fails when the initial configuration
 --    already forwards ext to int.
 ------------------------------------------------------------------------

 #eval c34holds ingressP egressP firewallBad34                         -- false
 #eval checkCondition34 ingressP egressP firewallBad34 == some false   -- true

 ------------------------------------------------------------------------
 -- 3. Post-reconfiguration condition (35) succeeds on the firewall
 --    fixture.
 ------------------------------------------------------------------------

 #eval c35holds ingressP egressP Rsec firewallInit                     -- true

 ------------------------------------------------------------------------
 -- 4. Post-reconfiguration condition (35) fails when the
 --    post-reconfiguration configuration still blocks the flow.
 ------------------------------------------------------------------------

 #eval c35holds ingressP egressP Rsec firewallBad35                    -- false
 #eval checkCondition35 ingressP egressP Rsec firewallBad35 == some false  -- true

 ------------------------------------------------------------------------
 -- 5. Zero NetKAT policy: the zero checker and the property policy with
 --    a zero core.
 ------------------------------------------------------------------------

 #eval netkatIsZero .drop == true                                      -- true
 #eval netkatIsZero (reachabilityPolicy ingressP .drop egressP) == true    -- true

 ------------------------------------------------------------------------
 -- 6. Nonzero NetKAT policy: the property policy with the forwarding
 --    core is nonzero.
 ------------------------------------------------------------------------

 #eval netkatIsZero .id == false                                       -- true
 #eval netkatIsZero (reachabilityPolicy ingressP Hpost egressP) == false   -- true

 ------------------------------------------------------------------------
 -- 7. Supported preprocessing: the firewall fixture preprocesses
 --     successfully, and the preprocessing conditions hold
 --     propositionally.
 ------------------------------------------------------------------------

 #eval (preprocess RecEnv.empty firewallInit).isSome                   -- true

 def firewallInitFragment : PreprocessFragment firewallInit :=
   PreprocessFragment.nSeq Hinit _
     (PreprocessFragment.rcfgPrefix "secConReq" NetKAT.id _
       (PreprocessFragment.nSeq Hpost _ PreprocessFragment.deadlock))

 theorem firewallInit_conditions :
     PreprocessingConditions RecEnv.empty firewallInit :=
   ⟨firewallInitFragment, PreprocessFragment.defined _ _ firewallInitFragment⟩

 #eval (preprocess RecEnv.empty firewallBad34).isSome                  -- true
 #eval (preprocess RecEnv.empty firewallBad35).isSome                  -- true

 ------------------------------------------------------------------------
 -- 8. Unsupported preprocessing: recursive variables and parallel
 --    composition fail explicitly.
 ------------------------------------------------------------------------

 #eval (preprocess RecEnv.empty (.var "Switch")).isNone                -- true
 #eval (preprocess RecEnv.empty
         (.parallel (.nSeq NetKAT.id .deadlock) .deadlock)).isNone    -- true

 ------------------------------------------------------------------------
 -- 9. Successful head and tail extraction on the supported fixture.
 ------------------------------------------------------------------------

 #eval (head firewallInit).isSome                                      -- true
 #eval (tail Rsec firewallInit).isSome                                 -- true
 #eval (do
         let q ← preprocess RecEnv.empty firewallInit
         let Q ← tail Rsec q
         head Q).isSome                                                -- true

 ------------------------------------------------------------------------
 -- 10. Failure propagation without conflating unsupported input with
 --     zero: extraction failure is `none`, never a zero verdict, and
 --     preprocessing failure is reported as `preprocessFailure`.
 ------------------------------------------------------------------------

 -- `head` fails on parallel composition: `none`, not `some true`.
 #eval c34notEvaluable ingressP egressP
         (.parallel (.nSeq NetKAT.id .deadlock) .deadlock)             -- true
 -- `tail` fails on recursive variables: `none`, not `some true`.
 #eval c35notEvaluable ingressP egressP Rsec (.var "Switch")           -- true
 -- Preprocessing failure yields `preprocessFailure` on both conditions.
 #eval Internal.safetyCheck RecEnv.empty (.var "Switch") Rsec ingressP egressP ==
         ⟨Cond34Result.preprocessFailure, Cond35Result.preprocessFailure⟩  -- true

 ------------------------------------------------------------------------
 -- Full pipeline verdicts on the fixtures (executable level).
 ------------------------------------------------------------------------

 #eval Internal.safetyCheck RecEnv.empty firewallInit Rsec ingressP egressP
 -- { initialCondition := Cond34Result.isZero true,
 --   postReconfigurationCondition := Cond35Result.nonzero true }

 #eval Internal.safetyCheck RecEnv.empty firewallBad34 Rsec ingressP egressP ==
         ⟨Cond34Result.isZero false, Cond35Result.nonzero true⟩        -- true

 #eval Internal.safetyCheck RecEnv.empty firewallBad35 Rsec ingressP egressP ==
         ⟨Cond34Result.isZero true, Cond35Result.nonzero false⟩        -- true

 -- The paper's combined claim holds exactly on the correct fixture.
 #eval (Internal.safetyCheck RecEnv.empty firewallInit Rsec ingressP egressP).bothHold    -- true
 #eval (Internal.safetyCheck RecEnv.empty firewallBad34 Rsec ingressP egressP).bothHold   -- false
 #eval (Internal.safetyCheck RecEnv.empty firewallBad35 Rsec ingressP egressP).bothHold   -- false

 ------------------------------------------------------------------------
 -- Propositional checks: applications of the machine-checked theorems.
 ------------------------------------------------------------------------

 -- End-to-end extraction-level theorem on the firewall fixture: the
 -- pipeline evaluates exactly the two verified zero checks.
 example :
     ∃ q Q H₁ H₂,
       preprocess RecEnv.empty firewallInit = some q ∧ head q = some H₁ ∧
       tail Rsec q = some Q ∧ head Q = some H₂ ∧
       Internal.safetyCheck RecEnv.empty firewallInit Rsec ingressP egressP =
         ⟨Cond34Result.isZero (netkatIsZero (reachabilityPolicy ingressP H₁ egressP)),
          Cond35Result.nonzero
            (!netkatIsZero (reachabilityPolicy ingressP H₂ egressP))⟩ :=
   safetyCheck_supported RecEnv.empty firewallInit Rsec ingressP egressP
     firewallInit_conditions

 -- End-to-end semantic theorem on the firewall fixture (the full
 -- statement is inferred from the theorem).
 example :=
   safetyCheck_pipeline_semantic RecEnv.empty firewallInit Rsec ingressP
     egressP firewallInit_conditions

-- Concrete relational-transition reading of (34) for the fixture: the
-- initial configuration admits NO transition from an ext-packet to an
-- int-packet, hence the checker returns `true`.
example :
    netkatIsZero (reachabilityPolicy ingressP Hinit egressP) = true := by
  simp only [ingressP, egressP, NetKAT.fieldTest]
  rw [netkatIsZero_reachabilityPolicy_tests_true_iff]
  intro σ κ hH hpair
  obtain ⟨ρ, h₁, h₂⟩ := seq_sem _ _ σ κ |>.mp hH
  have hρ : σ = ρ := (sem_test_iff _ σ ρ).mp h₁ |>.2
  subst hρ
  have hκ : κ = Packet.update σ .port .v8 := h₂
  subst hκ
  have h8 : σ .port = .v8 := decide_eq_true_iff.mp hpair.1
  have h9 : (Packet.update σ .port .v8) .port = .v9 :=
    decide_eq_true_iff.mp hpair.2
  have h9' : (Packet.update σ .port .v8) .port = .v8 :=
    Packet.get_update_same σ .port .v8
  rw [h9'] at h9
  exact absurd h9 (by decide)

-- Concrete relational-transition reading of (35) for the fixture: the
-- post-reconfiguration configuration admits the ext-packet `extPacket`
-- reaching the int-packet `intPacket`, hence the checker returns
-- `true` (the policy is nonzero).
example :
    netkatIsZero (reachabilityPolicy ingressP Hpost egressP) = false := by
  simp only [ingressP, egressP, NetKAT.fieldTest]
  rw [netkatIsZero_reachabilityPolicy_tests_false_iff]
  refine ⟨extPacket, intPacket, ⟨extPacket, ⟨rfl, rfl⟩, ?_⟩, rfl, rfl⟩
  exact extPacket_update.symm

 -- Extraction failure is never a zero verdict (condition 34).
 example (D : DyNetKAT) (h : head D = none) :
     checkCondition34 ingressP egressP D = none ∧
       checkCondition34 ingressP egressP D ≠ some true := by
   refine ⟨checkCondition34_none ingressP egressP D h, ?_⟩
   rw [checkCondition34_none ingressP egressP D h]
   simp

 -- Extraction failure is never a zero verdict (condition 35).
 example (D : DyNetKAT) (h : tail Rsec D = none) :
     checkCondition35 ingressP egressP Rsec D = none ∧
       checkCondition35 ingressP egressP Rsec D ≠ some true := by
   refine ⟨checkCondition35_none_tail ingressP egressP Rsec D h, ?_⟩
   rw [checkCondition35_none_tail ingressP egressP Rsec D h]
   simp

 -- Preprocessing failure is reported, never interpreted as a verdict.
 example : Internal.safetyCheck RecEnv.empty (.var "Switch") Rsec ingressP egressP =
     ⟨Cond34Result.preprocessFailure, Cond35Result.preprocessFailure⟩ :=
   safetyCheck_preprocessFailure RecEnv.empty (.var "Switch") Rsec ingressP
     egressP rfl

 -- The combined claim is the conjunction of the two separate verdicts.
 example (r : SafetyCheckResult) :
     r.bothHold = true ↔
       (r.initialCondition = Cond34Result.isZero true ∧
         r.postReconfigurationCondition = Cond35Result.nonzero true) :=
   bothHold_true_iff r

 end DyNetKAT.DyNetKAT.SafetyCheckTests
