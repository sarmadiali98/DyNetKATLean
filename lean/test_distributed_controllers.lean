import DyNetKAT.Examples.DistributedControllers

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.DistributedControllers

open DyNetKAT.NetKAT TraceSafety

-- Fig. 10's packet output sets before and after the two updates.
#guard execute (forwarding initialTables) (packet 2) ==
  .supported {packet 2, packet 6, packet 8, packet 12, packet 16}
#guard execute (forwarding afterS6) (packet 2) ==
  .supported {packet 2, packet 6, packet 8, packet 11}
#guard execute (forwarding afterS4S6) (packet 2) ==
  .supported {packet 2, packet 6, packet 8, packet 11, packet 15}

private def headers : CtxPkt := fun _ => .v9

#guard execute (forwarding afterS4S6) (place 2 headers) ==
  .supported {place 2 headers, place 6 headers, place 8 headers, place 11 headers, place 15 headers}

#guard independentInitialReconfigurations.contains installS6
#guard independentAfterS6Reconfigurations.contains installS4
#guard !independentAfterS6Reconfigurations.contains installS6

-- The synchronized controllers can deactivate in either order.
#guard phaseReconfigurations (0, 0) == [disableS1, disableS2]
#guard phaseReconfigurations (1, 0) == [disableS2]
#guard phaseReconfigurations (0, 1) == [disableS1]
#guard phaseReconfigurations (1, 1) == [acknowledge]
#guard phaseReconfigurations (2, 2) == [installS3, installS4]
#guard execute (forwarding (phaseTables (4, 4))) (packet 1) ==
  .supported {packet 1, packet 5, packet 8, packet 11, packet 15}
#guard execute (forwarding (phaseTables (4, 4))) (packet 2) == .supported {packet 2}

-- The general finite-word checker's verdicts use the correctness bridge.
-- The executable regressions above evaluate the relevant one-step rows and
-- policies without materializing the complete table of abstract definitions.
example : checkIndependent [[breach]] = true :=
  (checkIndependent_correct _).mpr (by
    intro w mem
    obtain rfl := List.mem_singleton.mp mem
    exact independent_initial_isolation)

example : checkIndependent [breachWord] = false := independent_checker_breach
example : checkSynchronized [breachWord] = true := synchronized_checker_isolation
example : checkSynchronized [installationWord] = false := synchronized_checker_installation

#print axioms independent_admitted
#print axioms synchronized_admitted
#print axioms independent_breach_steps
#print axioms independent_initial_isolation
#print axioms independent_eq28_fails
#print axioms independent_reachable
#print axioms synchronized_barrier
#print axioms synchronized_order
#print axioms synchronized_isolation
#print axioms synchronized_eq28
#print axioms synchronized_reachable
#print axioms synchronized_unreachable
#print axioms independent_headTail_verdict
#print axioms synchronized_headTail_verdict
#print axioms synchronized_projection_derives
#print axioms independent_checker_breach
#print axioms synchronized_checker_installation

open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if [`DyNetKAT.NetKAT.Legacy, `DyNetKAT.Experimental, `DyNetKAT.NetKAT.KATch,
        `DyNetKAT.NetKAT.BackendCertificate, `DyNetKAT.NetKAT.EquationalCertificate,
        `KATLean.Native.Explicit].contains mod then
      throwError "controller examples import {mod}"

end DyNetKAT.DyNetKAT.DistributedControllers
