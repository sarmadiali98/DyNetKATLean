import DyNetKAT

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.FatTree.Tests

open DyNetKAT.NetKAT

private def c := benchmark 1

#guard [3, 4, 5, 6, 7, 8].map (fun m => (switches m).length) ==
  [99, 208, 375, 612, 931, 1344]

#guard linked (.tor c.source) c.sourceLower
#guard linked c.sourceLower c.oldFirewall
#guard linked c.newFirewall c.newCore
#guard linked c.newCore c.destinationUpper
#guard !linked (.tor c.source) c.newCore

#guard c.hop .initial c.sourceLower c.destination == some c.oldFirewall
#guard (c.hop .firewallInstalled c.newCore c.destination).isNone
#guard c.hop .coreUpdated c.newCore c.destination == some c.destinationUpper
#guard (c.hop .coreUpdated c.destinationUpper c.destination).isNone
#guard c.hop .final c.sourceLower c.destination == some c.newFirewall

private def outgoing (ssh : Bool) := c.routePacket .final ssh 2

#guard (execute c.firewall (outgoing true)).outputs.map Finset.card == some 0
#guard (execute c.firewall (outgoing false)).outputs.map Finset.card == some 1
#guard (c.updates .final).length == 4

example : c.program.Trace (c.updates .initial ++
    [.packet (c.routePacket .initial false 0) (c.routePacket .initial false 6)]) :=
  c.nonSSH_trace .initial

example : c.program.Trace (c.updates .coreUpdated ++
    [.packet (c.routePacket .coreUpdated false 0) (c.routePacket .coreUpdated false 6)]) :=
  c.nonSSH_trace .coreUpdated

example : (benchmark 5).program.Trace ((benchmark 5).updates .final ++
    [.packet ((benchmark 5).routePacket .final false 0)
      ((benchmark 5).routePacket .final false 6)]) :=
  (benchmark 5).nonSSH_trace .final

example : netkatNativeEquivFinite
    (.union (benchmark 6).endpointsRelation (benchmark 6).waypointRelation)
    (benchmark 6).waypointRelation = true :=
  (benchmark 6).waypoint_verdict

example : ¬ c.program.Trace (c.updates .final ++
    [.packet (c.routePacket .initial true 0) (c.routePacket .final true 6)]) := by
  intro h
  exact c.ssh_isolation _ h _ rfl (List.mem_append_right _ List.mem_cons_self)

private def finalSelectors : List (ReconfigSet (schema 3)) :=
  [{(Migration.channel .initial, c.payload .initial .firewallInstalled)},
   {(Migration.channel .firewallInstalled, c.payload .firewallInstalled .coreUpdated)},
   {(Migration.channel .coreUpdated, c.payload .coreUpdated .destinationUpdated)},
   {(Migration.channel .destinationUpdated, c.payload .destinationUpdated .final)}]

example : projectedReachability c.compiled Migration.checks (fun _ => Migration.checks) 5 finalSelectors .id .id =
    some true := by
  apply (projectedReachability_correct c.compiled Migration.checks c.support c.valid 5
    finalSelectors .id .id).mpr
  let p := c.routePacket .final false 0
  let q := c.routePacket .final false 6
  refine ⟨p, p, q, q, rfl, ⟨c.updates .final ++ [.packet p q], ?_, c.nonSSH_trace .final, ?_⟩, rfl⟩
  · refine ⟨c.updates .final, [], ?_, by simp, rfl⟩
    refine ⟨[_], _, rfl, .last (Finset.mem_singleton_self _), ?_⟩
    refine ⟨[_], _, rfl, .last (Finset.mem_singleton_self _), ?_⟩
    refine ⟨[_], _, rfl, .last (Finset.mem_singleton_self _), ?_⟩
    exact ⟨[_], [], rfl, .last (Finset.mem_singleton_self _), rfl⟩
  · exact Nat.le_refl 5

#guard TraceSafety.check c.compiled Migration.checks c.support c.valid
  [[.packet (c.routePacket .initial true 0) (c.routePacket .initial true 6)]]

#print axioms Migration.admission
#print axioms Migration.migration_reachable
#print axioms Migration.nonSSH_forwarding
#print axioms Migration.nonSSH_trace
#print axioms Migration.ssh_isolation
#print axioms Migration.final_waypoint
#print axioms Migration.certified_ssh_word
#print axioms shortest_routing
#print axioms distance_lower_bound

end DyNetKAT.DyNetKAT.FatTree.Tests
