import DyNetKATLean

------------------------------------------------------------------------
-- Executable checks for the verified core `head` extraction
-- (`DyNetKAT.DyNetKAT.SafetyHead`, paper Eqs. (29)–(32)).
--
-- Run with:  lake env lean test_safety_head.lean   (from lean/)
--
-- The extracted policies are compared with the expected NetKAT policies
-- using the verified semantic-equivalence checker `netkatEquiv`
-- (`DyNetKAT.NetKAT.Decision`), evaluated over the finite packet domain
-- (256 packets).  Unsupported expressions must fail explicitly (`none`),
-- never silently yield a policy.
------------------------------------------------------------------------

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.SafetyHeadTests

open DyNetKAT.NetKAT

/-- `head d` succeeds and its result is semantically equivalent to
    `expected` (checked with the verified NetKAT equivalence checker). -/
def headEquiv (d : DyNetKAT) (expected : NetKAT) : Bool :=
  match head d with
  | some H => netkatEquiv H expected
  | none => false

/-- `head d` fails explicitly (returns `none`). -/
def headFails (d : DyNetKAT) : Bool :=
  match head d with
  | some _ => false
  | none => true

-- 1. Deadlock: head(⊥) = 0  (Eq. 29; NetKAT 0 is `.drop`).
#eval headEquiv .deadlock .drop                                        -- true

-- 2. One packet-processing prefix: head(N;⊥) = N + head(⊥) ≡ N  (Eq. 30).
#eval headEquiv (.nSeq (NetKAT.fieldTest .tpSrc .v8) .deadlock)
                 (NetKAT.fieldTest .tpSrc .v8)                         -- true

-- A two-step prefix: head(N₁;N₂;⊥) = N₁ + (N₂ + 0) ≡ N₁ + N₂.
#eval headEquiv (.nSeq (NetKAT.fieldTest .tpSrc .v8)
                   (.nSeq (NetKAT.fieldTest .tpDst .v9) .deadlock))
                 (NetKAT.union (NetKAT.fieldTest .tpSrc .v8)
                               (NetKAT.fieldTest .tpDst .v9))          -- true

-- 3. Choice between two packet-processing prefixes:
--    head(D₁ ⊕ D₂) = head(D₁) + head(D₂) ≡ N₁ + N₂  (Eq. 31).
#eval headEquiv (.choice (.nSeq (NetKAT.fieldTest .tpSrc .v8) .deadlock)
                         (.nSeq (NetKAT.fieldTest .tpDst .v9) .deadlock))
                 (NetKAT.union (NetKAT.fieldTest .tpSrc .v8)
                               (NetKAT.fieldTest .tpDst .v9))          -- true

-- 4. Reconfiguration prefix: head(rcfg_{x,N};D) = 0  (Eq. 32).
#eval headEquiv (.rcfgPrefix "ctrl" NetKAT.id .deadlock) .drop         -- true

-- 5. Unsupported expressions fail explicitly — never a silent zero:
-- recv/send are communication prefixes, NOT deadlock (⊥).
#eval headFails (.recv "ctrl" NetKAT.id .deadlock)                     -- true
#eval headFails (.send "ctrl" NetKAT.id .deadlock)                     -- true
-- Parallel composition is not assumed normalized.
#eval headFails (.parallel (.nSeq NetKAT.id .deadlock)
                           (.nSeq NetKAT.id .deadlock))                -- true
-- Left-merge / communication-merge / restriction / projection.
#eval headFails (.leftMerge (.nSeq NetKAT.id .deadlock)
                            (.nSeq NetKAT.id .deadlock))               -- true
#eval headFails (.commMerge (.nSeq NetKAT.id .deadlock)
                             (.nSeq NetKAT.id .deadlock))              -- true
#eval headFails (.restrict {} (.nSeq NetKAT.id .deadlock))             -- true
#eval headFails (.project 1 (.nSeq NetKAT.id .deadlock))               -- true
-- Recursive variables are not resolved.
#eval headFails (.var "Switch")                                        -- true
-- Failure propagates through supported shapes with unsupported subterms.
#eval headFails (.nSeq NetKAT.id (.var "Switch"))                      -- true
#eval headFails (.choice (.nSeq NetKAT.id .deadlock) (.var "Switch"))  -- true

end DyNetKAT.DyNetKAT.SafetyHeadTests
