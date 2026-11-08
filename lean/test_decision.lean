import DyNetKAT

namespace DyNetKAT.NetKAT

/- Executable checks of the verified NetKAT semantic-equivalence checker.

   These run through the Lean interpreter (the kernel cannot reduce the
   well-founded-compiled `execute`, so `decide`/`rfl` are not usable here;
   the verified guarantees come from `netkatEquiv_correct`, which is proved
   unconditionally in `DyNetKAT.NetKAT.Decision`). -/

-- A policy is equivalent to itself.
#eval netkatEquiv .drop .drop                       -- true
#eval netkatEquiv tpSrc8Test tpSrc8Test             -- true

-- `drop` and `.test .pFalse` are equivalent.
#eval netkatEquiv .drop (.test .pFalse)             -- true

-- `id` and `drop` are not equivalent.
#eval netkatEquiv .id .drop                         -- false

-- Sequencing commutes with a single-field assignment against `id`.
#eval netkatEquiv (.seq (.assign1 .tpSrc .v8) .id)
                   (.seq .id (.assign1 .tpSrc .v8)) -- true

-- A union agrees with its reassociated form.
#eval netkatEquiv (.union (.union .id .drop) tpSrc8Test)
                   (.union .id (.union .drop tpSrc8Test)) -- true

------------------------------------------------------------------------
-- Verified NetKAT zero checker (`netkatIsZero`)
--
-- The guarantees come from `netkatIsZero_correct`, proved unconditionally
-- in `DyNetKAT.NetKAT.Decision` via `netkatEquiv_correct`.
------------------------------------------------------------------------

-- `drop` denotes the empty relation: zero.
#eval netkatIsZero .drop                              -- true

-- The always-false predicate test denotes the empty relation: zero.
#eval netkatIsZero (.test .pFalse)                    -- true

-- `id` relates every packet to itself: not zero.
#eval netkatIsZero .id                                -- false

-- Sequential contradictory tests on one field:
-- (tpSrc = v8); (tpSrc = v9) admits no packet: zero.
#eval netkatIsZero (.seq (NetKAT.fieldTest .tpSrc .v8)
                         (NetKAT.fieldTest .tpSrc .v9)) -- true

end DyNetKAT.NetKAT
