import DyNetKATLean

 ------------------------------------------------------------------------
 -- Executable checks for the verified core `tail` extraction
 -- (`DyNetKAT.DyNetKAT.TailExtraction`, paper Eqs. (29)–(33)).
 --
 -- Run with:  lake env lean test_tail_extraction.lean   (from lean/)
 --
 -- The pipeline quantity `head (tail R d)` is compared with the expected
 -- NetKAT policy using the verified semantic-equivalence checker
 -- `netkatEquiv` (`DyNetKAT.NetKAT.Decision`), evaluated over the finite
 -- packet domain.  The extracted process is also compared structurally
 -- with the expected process (up to restriction-set representation,
 -- which these tests never exercise).  Unsupported expressions must
 -- fail explicitly (`none`), never silently yield a process.
 ------------------------------------------------------------------------

 set_option linter.dupNamespace false

 namespace DyNetKAT.DyNetKAT.TailExtractionTests

 open DyNetKAT.NetKAT

 /-- Test-local structural equality on processes (restriction sets are
     compared by a placeholder `true` because `Set` has no decidable
     equality; no test below produces `.restrict` nodes). -/
 def procEq : DyNetKAT → DyNetKAT → Bool
   | .deadlock, .deadlock => true
   | .nSeq a b, .nSeq a' b' => a == a' && procEq b b'
   | .recv x a b, .recv x' a' b' => x == x' && a == a' && procEq b b'
   | .send x a b, .send x' a' b' => x == x' && a == a' && procEq b b'
   | .rcfgPrefix x a b, .rcfgPrefix x' a' b' => x == x' && a == a' && procEq b b'
   | .choice a b, .choice a' b' => procEq a a' && procEq b b'
   | .parallel a b, .parallel a' b' => procEq a a' && procEq b b'
   | .leftMerge a b, .leftMerge a' b' => procEq a a' && procEq b b'
   | .commMerge a b, .commMerge a' b' => procEq a a' && procEq b b'
   | .restrict _ b, .restrict _ b' => procEq b b'
   | .project n b, .project n' b' => n == n' && procEq b b'
   | .var x, .var x' => x == x'
   | _, _ => false

 /-- `tail R d` succeeds and its result is the expected process
     (structurally, up to restriction-set representation). -/
 def tailEq (R : ReconfigSet) (d expected : DyNetKAT) : Bool :=
   match tail R d with
   | some q => procEq q expected
   | none => false

 /-- `head (tail R d)` succeeds and its result is semantically
     equivalent to `expected` (checked with the verified NetKAT
     equivalence checker). -/
 def tailHeadEquiv (R : ReconfigSet) (d : DyNetKAT) (expected : NetKAT) : Bool :=
   match tail R d with
   | some Q =>
       match head Q with
       | some H => netkatEquiv H expected
       | none => false
   | none => false

 /-- `tail R d` fails explicitly (returns `none`). -/
 def tailFails (R : ReconfigSet) (d : DyNetKAT) : Bool :=
   match tail R d with
   | some _ => false
   | none => true

 /-- The full S4B + S5A + S4A pipeline on an executable input:
     `preprocess`, then `tail`, then `head`, then the verified NetKAT
     equivalence check. -/
 def preprocessedTailHeadEquiv (R : ReconfigSet) (p : DyNetKAT) (expected : NetKAT) : Bool :=
   match preprocess RecEnv.empty p with
   | some q => tailHeadEquiv R q expected
   | none => false

 -- Abbreviations for the tests.
 abbrev N1 : NetKAT := NetKAT.fieldTest .tpSrc .v8
 abbrev N2 : NetKAT := NetKAT.fieldTest .tpDst .v9
 abbrev Rc : ReconfigSet := {("c", NetKAT.id)}
 abbrev Rcd : ReconfigSet := {("c", NetKAT.id), ("d", NetKAT.id)}

 -- 1. Eq. (29): tail(⊥, R) = ⊥.
 #eval tailEq ∅ .deadlock .deadlock                                    -- true

 -- 2. Eq. (30): tail(N;D, R) = tail(D, R); with D = ⊥ the result is ⊥.
 #eval tailEq ∅ (.nSeq N1 .deadlock) .deadlock                         -- true
 -- A deeper prefix is skipped entirely:
 #eval tailEq ∅ (.nSeq N1 (.nSeq N2 .deadlock)) .deadlock              -- true

 -- 3. Eq. (32): tail(rcfg_c;D, {rcfg_c}) = D ⊕ tail(D, R); with
 --    D = N;⊥ and tail(D,R) = ⊥ the result is (N;⊥) ⊕ ⊥.
 #eval tailEq Rc (.rcfgPrefix "c" NetKAT.id (.nSeq N1 .deadlock))
                (.choice (.nSeq N1 .deadlock) .deadlock)               -- true

 -- 4. Pipeline quantity head(tail(R,·)) on the stateful-firewall shape:
 --    the policy after the reconfiguration is extracted; the policy
 --    before it is not.
 #eval tailHeadEquiv Rc (.rcfgPrefix "c" NetKAT.id (.nSeq N1 .deadlock)) N1    -- true
 #eval tailHeadEquiv Rc (.nSeq N1 (.rcfgPrefix "c" NetKAT.id (.nSeq N2 .deadlock)))
                       N2                                                      -- true

 -- 5. Two reconfigurations, both in R: policies after each are summed
 --    (Eq. (31) distributes over the choice structure of the result).
 #eval tailHeadEquiv Rcd
         (.rcfgPrefix "c" NetKAT.id (.nSeq N1 (.rcfgPrefix "d" NetKAT.id (.nSeq N2 .deadlock))))
         (NetKAT.union N1 N2)                                              -- true

 -- 6. Only `c` in R: the `d`-reconfiguration blocks the deeper policy
 --    (Eq. (33)), so only N1 is extracted.
 #eval tailHeadEquiv Rc
         (.rcfgPrefix "c" NetKAT.id (.nSeq N1 (.rcfgPrefix "d" NetKAT.id (.nSeq N2 .deadlock))))
         N1                                                                -- true

 -- 7. A reconfiguration in R followed by a reconfiguration not in R:
 --    the continuation after the second event contributes nothing.
 #eval tailHeadEquiv Rc
         (.rcfgPrefix "c" NetKAT.id (.rcfgPrefix "d" NetKAT.id (.nSeq N1 .deadlock)))
         .drop                                                             -- true

 -- 8. No reconfiguration at all: tail is ⊥ and head(⊥) = 0 (Eq. (29)).
 #eval tailHeadEquiv ∅ (.nSeq N1 .deadlock) .drop                       -- true

 -- 9. Choice: only the branch whose reconfiguration is in R
 --    contributes (the other branch yields ⊥ by Eq. (33)).
 #eval tailHeadEquiv Rc
         (.choice (.rcfgPrefix "c" NetKAT.id (.nSeq N1 .deadlock))
                  (.nSeq N2 .deadlock))
         N1                                                                -- true

 -- 10. Unsupported expressions fail explicitly — never a silent ⊥:
 --     recv/send are communication prefixes, NOT deadlock (⊥).
 #eval tailFails ∅ (.recv "c" NetKAT.id .deadlock)                      -- true
 #eval tailFails ∅ (.send "c" NetKAT.id .deadlock)                      -- true
 -- Parallel composition is not assumed normalized.
 #eval tailFails ∅ (.parallel (.nSeq NetKAT.id .deadlock)
                              (.nSeq NetKAT.id .deadlock))              -- true
 -- Left-merge / communication-merge / restriction / projection.
 #eval tailFails ∅ (.leftMerge (.nSeq NetKAT.id .deadlock)
                              (.nSeq NetKAT.id .deadlock))              -- true
 #eval tailFails ∅ (.commMerge (.nSeq NetKAT.id .deadlock)
                              (.nSeq NetKAT.id .deadlock))              -- true
 #eval tailFails ∅ (.restrict {} (.nSeq NetKAT.id .deadlock))           -- true
 #eval tailFails ∅ (.project 1 (.nSeq NetKAT.id .deadlock))             -- true
 -- Recursive variables are not resolved.
 #eval tailFails ∅ (.var "Switch")                                      -- true

 -- 11. Failure propagation through supported shapes with unsupported
 --     subterms.
 #eval tailFails ∅ (.nSeq NetKAT.id (.var "Switch"))                    -- true
 #eval tailFails ∅ (.choice (.nSeq NetKAT.id .deadlock) (.var "Switch")) -- true
 -- Eq. (32) propagates failure from the continuation when the event is
 -- in R: the unsupported continuation is never silently embedded.
 #eval tailFails Rc (.rcfgPrefix "c" NetKAT.id (.var "Switch"))         -- true

 -- 12. Eq. (33) is faithful to the paper: with the event outside R the
 --     result is ⊥ regardless of the continuation (the paper's equation
 --     does not inspect it).
 #eval tailEq ∅ (.rcfgPrefix "c" NetKAT.id (.var "Switch")) .deadlock   -- true

 -- 13. Full pipeline: S4B preprocessing (restriction δ) removes the
 --     communication prefix, then tail + head extract the post-
 --     reconfiguration policy.  The receive branch is blocked to ⊥, so
 --     only N1 (after rcfg_c) survives.
 #eval preprocessedTailHeadEquiv Rc
         (.choice (.rcfgPrefix "c" NetKAT.id (.nSeq N1 .deadlock))
                  (.recv "d" NetKAT.id (.nSeq N2 .deadlock)))
         N1                                                               -- true
 -- Preprocessing fails explicitly on recursive variables (H6A): the
 -- pipeline never silently resolves them.
 #eval (preprocess RecEnv.empty (.var "Switch")).isNone                 -- true

 -- 14. Spec-level spot checks (machine-checked propositions).
 example : TailSupported (schema := ctxSchema) (.rcfgPrefix "c" NetKAT.id (.nSeq NetKAT.id .deadlock)) :=
   TailSupported.rcfgPrefix "c" NetKAT.id _
     (TailSupported.nSeq NetKAT.id _ TailSupported.deadlock)

 example (R : ReconfigSet) :
     tail R (.nSeq NetKAT.id .deadlock) = some .deadlock ↔
       TailSpec R (.nSeq NetKAT.id .deadlock) .deadlock :=
   tail_spec_iff R _ _

 end DyNetKAT.DyNetKAT.TailExtractionTests
