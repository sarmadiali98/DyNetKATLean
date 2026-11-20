import DyNetKAT.DyNetKAT.Reachability
import DyNetKAT.DyNetKAT.TraceSafetyCheck
import DyNetKAT.NetKAT.SymbolicDerives
import Mathlib.Tactic.DeriveFintype

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.FatTree

open DyNetKAT.NetKAT

abbrev Pod (m : Nat) := Fin (2 * m)
abbrev Index (m : Nat) := Fin m
abbrev Endpoint (m : Nat) := Pod m × Index m × Index m

/-- The two levels of aggregation distinguish the lower switches adjacent
to the ToRs from the upper switches adjacent to the cores. -/
inductive Switch (m : Nat)
  | tor (endpoint : Endpoint m)
  | lower (pod : Pod m) (index : Index m)
  | upper (pod : Pod m) (index : Index m)
  | core (row column : Index m)
  deriving DecidableEq, Fintype

/-- Undirected physical adjacency, expressed as a directed Boolean test. -/
def linked {m : Nat} : Switch m → Switch m → Bool
  | .tor (p, i, _), .lower q j | .lower q j, .tor (p, i, _) =>
      decide (p = q ∧ i = j)
  | .lower p _, .upper q _ | .upper q _, .lower p _ =>
      decide (p = q)
  | .upper _ i, .core j _ | .core j _, .upper _ i =>
      decide (i = j)
  | _, _ => false

theorem linked_symm {m : Nat} (u v : Switch m) : linked u v = linked v u := by
  cases u <;> cases v <;> rfl

inductive Field
  | location | port | source | destination | ssh
  deriving DecidableEq, Fintype

/-- At a switch, an incident port is named by its neighbor. The remaining
port value denotes local delivery. Source and destination are separate
endpoint fields and do not change when the packet crosses a link. -/
def Value (m : Nat) : Field → Type
  | .location => Switch m
  | .port => Option (Switch m)
  | .source | .destination => Endpoint m
  | .ssh => Bool

instance (m : Nat) (f : Field) : Fintype (Value m f) := by
  cases f <;> simp only [Value] <;> infer_instance

instance (m : Nat) (f : Field) : DecidableEq (Value m f) := by
  cases f <;> simp only [Value] <;> infer_instance

abbrev schema (m : Nat) := PacketSchema.ofFields Field (Value m)

def endpoints (m : Nat) : List (Endpoint m) :=
  (List.finRange (2 * m)).flatMap fun p =>
    (List.finRange m).flatMap fun i => (List.finRange m).map fun j => (p, i, j)

def switches (m : Nat) : List (Switch m) :=
  let aggregation := (List.finRange (2 * m)).flatMap fun p =>
    (List.finRange m).flatMap fun i => [Switch.lower p i, Switch.upper p i]
  let cores := (List.finRange m).flatMap fun i => (List.finRange m).map (Switch.core i)
  (endpoints m).map Switch.tor ++ aggregation ++ cores

def topology (m : Nat) : NetKAT (schema m) :=
  ((switches m).flatMap fun u =>
    (switches m).filterMap fun v =>
      if linked u v then
        some (.seq (NetKAT.fieldTestFor .location u)
          (.seq (NetKAT.fieldTestFor .port (some v))
            (.seq (.assign1 .location v) (.assign1 .port (some u)))))
      else none).foldr .union .drop

/-- Destination-based routing. The selected source-side upper switch can
change with the last update. A core belongs to the row of that upper
switch, so each cross-pod route has the same six hops. -/
def nextHop {m : Nat} (row column : Index m) (destination : Endpoint m) :
    Switch m → Option (Switch m)
  | .tor (p, i, j) =>
      if (p, i, j) = destination then none else some (.lower p i)
  | .lower p i =>
      if p = destination.1 then
        if i = destination.2.1 then some (.tor destination)
        else some (.upper p row)
      else some (.upper p row)
  | .upper p i =>
      if p = destination.1 then some (.lower p destination.2.1)
      else some (.core i column)
  | .core i _ => some (.upper destination.1 i)

theorem nextHop_linked {m : Nat} (row column : Index m) (destination : Endpoint m)
    (u v : Switch m) (h : nextHop row column destination u = some v) :
    linked u v = true := by
  rcases destination with ⟨p, i, j⟩
  cases u with
  | tor e =>
      rcases e with ⟨q, k, l⟩
      simp only [nextHop, Prod.fst, Prod.snd] at h
      split at h
      · contradiction
      · cases h
        simp [linked]
  | lower q k =>
      simp only [nextHop, Prod.fst, Prod.snd] at h
      split at h
      · split at h
        · rename_i hp hi
          cases h
          simp [linked, hp, hi]
        · cases h
          simp [linked]
      · cases h
        simp [linked]
  | upper q k =>
      simp only [nextHop, Prod.fst, Prod.snd] at h
      split at h <;> cases h <;> simp [linked]
  | core k l =>
      cases h
      simp [linked]

/-- Distance to a ToR in the physical graph, before policy filtering. -/
def distance {m : Nat} (d : Endpoint m) : Switch m → Nat
  | .tor e => if e = d then 0 else if e.1 = d.1 then
      if e.2.1 = d.2.1 then 2 else 4 else 6
  | .lower p i => if p = d.1 then if i = d.2.1 then 1 else 3 else 5
  | .upper p _ => if p = d.1 then 2 else 4
  | .core _ _ => 3

theorem nextHop_decreases {m : Nat} (row column : Index m) (d : Endpoint m)
    (u v : Switch m) (hop : nextHop row column d u = some v) :
    distance d u = distance d v + 1 := by
  rcases d with ⟨p, i, j⟩
  cases u with
  | tor e =>
    rcases e with ⟨q, k, l⟩
    simp only [nextHop, Prod.fst, Prod.snd] at hop
    split at hop
    · contradiction
    · rename_i ne
      obtain rfl := Option.some.inj hop.symm
      simp [distance, ne]
      split <;> simp_all <;> split <;> simp_all
  | lower q k =>
    simp only [nextHop, Prod.fst, Prod.snd] at hop
    split at hop
    · split at hop <;> rename_i same rack <;> cases hop <;> simp [distance, same, rack]
    · rename_i ne
      cases hop
      simp [distance, ne]
  | upper q k =>
    simp only [nextHop, Prod.fst, Prod.snd] at hop
    split at hop <;> rename_i h <;> cases hop <;> simp [distance, h]
  | core k l =>
    cases hop
    simp [distance]

private theorem tor_lower_distance {m : Nat} (d e : Endpoint m) :
    distance d (.tor e) ≤ distance d (.lower e.1 e.2.1) + 1 ∧
      distance d (.lower e.1 e.2.1) ≤ distance d (.tor e) + 1 := by
  by_cases he : e = d
  · subst e
    simp [distance]
  · by_cases hp : e.1 = d.1 <;> by_cases hi : e.2.1 = d.2.1 <;>
      simp [distance, he, hp, hi]

theorem link_distance {m : Nat} (d : Endpoint m) (u v : Switch m) (edge : linked u v = true) :
    distance d u ≤ distance d v + 1 := by
  cases u <;> cases v <;> try contradiction
  case tor.lower e p i =>
    rcases e with ⟨q, j, k⟩
    obtain ⟨rfl, rfl⟩ := of_decide_eq_true edge
    exact (tor_lower_distance d (q, j, k)).1
  case lower.tor p i e =>
    rcases e with ⟨q, j, k⟩
    obtain ⟨rfl, rfl⟩ := of_decide_eq_true edge
    exact (tor_lower_distance d (q, j, k)).2
  case lower.upper p i q j =>
    have he : p = q := of_decide_eq_true edge
    subst q
    by_cases hp : p = d.1 <;> by_cases hi : i = d.2.1 <;> simp [distance, hp, hi]
  case upper.lower p i q j =>
    have he : q = p := of_decide_eq_true edge
    subst q
    by_cases hp : p = d.1 <;> by_cases hi : j = d.2.1 <;> simp [distance, hp, hi]
  case upper.core p i j k =>
    by_cases hp : p = d.1 <;> simp [distance, hp]
  case core.upper i j p k =>
    by_cases hp : p = d.1 <;> simp [distance, hp]

/-- A physical walk has one edge per constructor, regardless of the policy
installed at either endpoint. -/
inductive PhysicalWalk {m : Nat} : Switch m → Switch m → Nat → Prop
  | refl (u) : PhysicalWalk u u 0
  | step : linked u v = true → PhysicalWalk v w n → PhysicalWalk u w (n + 1)

theorem distance_lower_bound {m : Nat} {d : Endpoint m} {u : Switch m} {n : Nat}
    (walk : PhysicalWalk u (.tor d) n) : distance d u ≤ n := by
  generalize eq : Switch.tor d = v at walk
  induction walk with
  | refl u => subst u; simp [distance]
  | @step u v w n edge rest ih =>
    have lower := link_distance d u v edge
    have tail := ih eq
    omega

/-- A walk chosen by the destination-based forwarding table. -/
inductive RoutedWalk {m : Nat} (row column : Index m) (d : Endpoint m) :
    Switch m → Nat → Prop
  | arrive : RoutedWalk row column d (.tor d) 0
  | step : nextHop row column d u = some v → RoutedWalk row column d v n →
      RoutedWalk row column d u (n + 1)

theorem shortest_routing {m : Nat} (row column : Index m) (d : Endpoint m) (u : Switch m) :
    RoutedWalk row column d u (distance d u) := by
  generalize hn : distance d u = n
  induction n using Nat.strong_induction_on generalizing u with
  | h n ih =>
    cases hop : nextHop row column d u with
    | none =>
      have terminal : u = .tor d := by
        cases u with
        | tor e =>
          rcases e with ⟨p, i, j⟩
          simpa [nextHop] using hop
        | lower p i =>
          by_cases hp : p = d.1 <;> by_cases hi : i = d.2.1 <;> simp [nextHop, hp, hi] at hop
        | upper p i =>
          by_cases hp : p = d.1 <;> simp [nextHop, hp] at hop
        | core i j => simp [nextHop] at hop
      subst u
      simp [distance] at hn
      subst n
      exact .arrive
    | some v =>
      have dec := nextHop_decreases row column d u v hop
      have path := ih (distance d v) (by omega) v rfl
      rw [← hn, dec]
      exact .step hop path

theorem RoutedWalk.physical {m : Nat} {row column : Index m} {d : Endpoint m}
    {u : Switch m} {n : Nat} (path : RoutedWalk row column d u n) :
    PhysicalWalk u (.tor d) n := by
  induction path with
  | arrive => exact .refl _
  | step h _ ih => exact .step (nextHop_linked _ _ _ _ _ h) ih

variable {m : Nat}

private theorem mem_endpoints (d : Endpoint m) : d ∈ endpoints m := by
  rcases d with ⟨p, i, j⟩
  simp [endpoints]

theorem mem_switches (u : Switch m) : u ∈ switches m := by
  cases u with
  | tor d => exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr
      ⟨d, mem_endpoints d, rfl⟩))
  | lower p i => simp [switches]
  | upper p i => simp [switches]
  | core i j => simp [switches]

abbrev Packet (m : Nat) := (schema m).Packet

def packet (location : Switch m) (port : Option (Switch m)) (source destination : Endpoint m)
    (ssh : Bool) : Packet m
  | .location => location
  | .port => port
  | .source => source
  | .destination => destination
  | .ssh => ssh

private def deliver (u : Switch m) (port : Option (Switch m)) (p : Packet m) : Packet m :=
  packet u port (p .source) (p .destination) (p .ssh)

private theorem sum_sem (rules : List (NetKAT (schema m))) (p q : Packet m) :
    Semantics (rules.foldr .union .drop) p q ↔ ∃ rule ∈ rules, Semantics rule p q := by
  induction rules with
  | nil => simp [Semantics]
  | cons r rs ih => simp [Semantics, ih]

private def cable (u v : Switch m) : NetKAT (schema m) :=
  .seq (NetKAT.fieldTestFor .location u)
    (.seq (NetKAT.fieldTestFor .port (some v))
      (.seq (.assign1 .location v) (.assign1 .port (some u))))

private theorem cable_sem (u v : Switch m) (p q : Packet m) :
    Semantics (cable u v) p q ↔ p .location = u ∧ p .port = some v ∧
      q = deliver v (some u) p := by
  have eq : (schema m).model.update .port (some u)
      ((schema m).model.update .location v p) = deliver v (some u) p := by
    funext f
    cases f <;> simp [PacketSchema.ofFields, Function.update, deliver, packet]
  constructor
  · rintro ⟨a, locTest, b, portTest, c, rfl, rfl⟩
    obtain ⟨hu, ha⟩ := (fieldTestFor_sem Field.location u p a).mp locTest
    subst a
    obtain ⟨hv, hb⟩ := (fieldTestFor_sem Field.port (some v) p b).mp portTest
    subst b
    exact ⟨hu, hv, eq⟩
  · rintro ⟨hu, hv, rfl⟩
    exact ⟨p, (fieldTestFor_sem Field.location u p p).mpr ⟨hu, rfl⟩,
      p, (fieldTestFor_sem Field.port (some v) p p).mpr ⟨hv, rfl⟩, _, rfl, eq.symm⟩

theorem topology_sem (p q : Packet m) :
    Semantics (topology m) p q ↔
      ∃ v, linked (p .location) v = true ∧ p .port = some v ∧
        q = deliver v (some (p .location)) p := by
  unfold topology
  rw [sum_sem]
  simp only [List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨rule, ⟨u, _, v, _, hv⟩, hr⟩
    split at hv
    next link =>
      obtain rfl := Option.some.inj hv
      obtain ⟨loc, port, out⟩ := (cable_sem u v p q).mp hr
      exact ⟨v, loc.symm ▸ link, port, loc.symm ▸ out⟩
    next => contradiction
  · rintro ⟨v, link, port, out⟩
    refine ⟨cable (p .location) v, ⟨p .location, mem_switches _, v, mem_switches _, ?_⟩,
      (cable_sem _ _ p q).mpr ⟨rfl, port, out⟩⟩
    simp [link, cable]

/-- Each switch table tests location and destination, then writes only the
local output port. The filter is a policy so its exact guard is explicit. -/
def table (u : Switch m) (hop : Endpoint m → Option (Switch m))
    (filter : NetKAT (schema m) := .id) : NetKAT (schema m) :=
  .seq (NetKAT.fieldTestFor .location u) (.seq filter
    (((endpoints m).map fun d =>
      (NetKAT.seq (NetKAT.fieldTestFor (schema := schema m) Field.destination d) (.assign1 Field.port (hop d)) : NetKAT (schema m))).foldr .union .drop))

theorem table_sem (u : Switch m) (hop : Endpoint m → Option (Switch m))
    (filter : NetKAT (schema m)) (p q : Packet m) :
    Semantics (table u hop filter) p q ↔
      p .location = u ∧ ∃ r, Semantics filter p r ∧
        q = (schema m).model.update .port (hop (r .destination)) r := by
  constructor
  · rintro ⟨a, locTest, r, hf, hs⟩
    obtain ⟨hu, ha⟩ := (fieldTestFor_sem Field.location u p a).mp locTest
    subst a
    obtain ⟨rule, mem, h⟩ := (sum_sem _ r q).mp hs
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp mem
    obtain ⟨b, destTest, hq⟩ := h
    obtain ⟨hd, hb⟩ := (fieldTestFor_sem Field.destination d r b).mp destTest
    subst b
    exact ⟨hu, r, hf, hd.symm ▸ hq⟩
  · rintro ⟨hu, r, hf, hq⟩
    refine ⟨p, (fieldTestFor_sem Field.location u p p).mpr ⟨hu, rfl⟩, r, hf,
      (sum_sem _ r q).mpr ⟨_, List.mem_map.mpr ⟨r .destination, mem_endpoints _, rfl⟩,
        r, (fieldTestFor_sem Field.destination _ r r).mpr ⟨rfl, rfl⟩, hq⟩⟩

/-- Equal-length alternatives for the selected inter-pod flow. -/
structure Migration (m : Nat) where
  source : Endpoint m
  destination : Endpoint m
  differentPods : source.1 ≠ destination.1
  oldRow : Index m
  newRow : Index m
  distinctRows : oldRow ≠ newRow
  column : Index m

inductive Phase
  | initial | firewallInstalled | coreUpdated | destinationUpdated | final
  deriving DecidableEq, Fintype

namespace Phase

def name : Phase → String
  | .initial => "initial"
  | .firewallInstalled => "firewall-installed"
  | .coreUpdated => "core-updated"
  | .destinationUpdated => "destination-updated"
  | .final => "final"

def next : Phase → Option Phase
  | .initial => some .firewallInstalled
  | .firewallInstalled => some .coreUpdated
  | .coreUpdated => some .destinationUpdated
  | .destinationUpdated => some .final
  | .final => none

def ofName (s : String) : Option Phase :=
  if s = "initial" then some .initial
  else if s = "firewall-installed" then some .firewallInstalled
  else if s = "core-updated" then some .coreUpdated
  else if s = "destination-updated" then some .destinationUpdated
  else if s = "final" then some .final else none

@[simp] theorem ofName_name (i : Phase) : ofName i.name = some i := by
  cases i <;> decide

end Phase

namespace Migration

variable (c : Migration m)

def oldFirewall : Switch m := .upper c.source.1 c.oldRow
def newFirewall : Switch m := .upper c.source.1 c.newRow
def newCore : Switch m := .core c.newRow c.column
def destinationUpper : Switch m := .upper c.destination.1 c.newRow
def sourceLower : Switch m := .lower c.source.1 c.source.2.1

def firewall : NetKAT (schema m) :=
  let source := Predicate.pFieldEq (schema := schema m) ⟨Field.source, c.source⟩
  let destination := Predicate.pFieldEq (schema := schema m) ⟨Field.destination, c.destination⟩
  let nonSSH := Predicate.pFieldEq (schema := schema m) ⟨Field.ssh, false⟩
  .test (.pOr (.pNot source) (.pAnd source (.pAnd destination nonSSH)))

def filter (i : Phase) (u : Switch m) : NetKAT (schema m) :=
  if u = c.oldFirewall ∨ (i ≠ .initial ∧ u = c.newFirewall) then c.firewall else .id

def hop (i : Phase) (u : Switch m) (d : Endpoint m) : Option (Switch m) :=
  if d = c.destination ∧
      ((u = c.newCore ∧ (i = .initial ∨ i = .firewallInstalled)) ∨
        (u = c.destinationUpper ∧ (i = .initial ∨ i = .firewallInstalled ∨ i = .coreUpdated)))
  then none
  else nextHop (if i = .final ∧ u = c.sourceLower ∧ d = c.destination then c.newRow else c.oldRow)
    c.column d u

def flowTable (i : Phase) (u : Switch m) : NetKAT (schema m) :=
  table u (c.hop i u) (c.filter i u)

def forwarding (i : Phase) : NetKAT (schema m) :=
  ((switches m).map (c.flowTable i)).foldr .union .drop

def traversal (i : Phase) : NetKAT (schema m) :=
  .star (.seq (c.forwarding i) (topology m))

/-- Install the new firewall, update the new core and destination-side
aggregation, and finally change the source-side lower aggregation table. -/
def updateSwitch : Phase → Switch m
  | .initial => c.newFirewall
  | .firewallInstalled => c.newCore
  | .coreUpdated => c.destinationUpper
  | .destinationUpdated | .final => c.sourceLower

def channel (i : Phase) : Channel := "update-" ++ i.name
def payload (i j : Phase) : NetKAT (schema m) := c.flowTable j (c.updateSwitch i)
def event (i j : Phase) : Action (schema m) := .rcfg (channel i) (c.payload i j)

def permits (i : Phase) (p : Packet m) : Prop :=
  (p .location = c.oldFirewall ∨ (i ≠ .initial ∧ p .location = c.newFirewall)) →
    (p .source ≠ c.source ∨
      (p .source = c.source ∧ p .destination = c.destination ∧ p .ssh = false))

private theorem filter_sem (i : Phase) (p q : Packet m) :
    Semantics (c.filter i (p .location)) p q ↔ c.permits i p ∧ q = p := by
  unfold filter permits
  split
  · rename_i h
    simp only [firewall, Semantics, Predicate.holds, Predicate.eval, h, true_implies,
      Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
    exact and_congr_right (fun _ => eq_comm)
  · rename_i h
    simpa only [Semantics, h, false_implies, true_and] using (eq_comm : p = q ↔ q = p)

theorem hop_sem (i : Phase) (p q : Packet m) :
    Semantics (.seq (c.forwarding i) (topology m)) p q ↔
      c.permits i p ∧ ∃ v, c.hop i (p .location) (p .destination) = some v ∧
        q = deliver v (some (p .location)) p := by
  have updated (v : Option (Switch m)) (f : Field) :
      (schema m).model.update .port v p f =
        deliver (p .location) v p f := by
    cases f <;> simp [PacketSchema.ofFields, Function.update, deliver, packet]
  have rt (r : Packet m) : Semantics (c.forwarding i) p r ↔
      c.permits i p ∧ r = deliver (p .location) (c.hop i (p .location) (p .destination)) p := by
    unfold forwarding
    rw [sum_sem]
    constructor
    · rintro ⟨rule, mem, hr⟩
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp mem
      obtain ⟨loc, k, hk, out⟩ := (table_sem _ _ _ p r).mp hr
      subst u
      obtain ⟨ok, rfl⟩ := (c.filter_sem i p k).mp hk
      exact ⟨ok, out.trans (funext (updated _))⟩
    · rintro ⟨ok, out⟩
      refine ⟨_, List.mem_map.mpr ⟨p .location, mem_switches _, rfl⟩,
        (table_sem _ _ _ p r).mpr ⟨rfl, p, (c.filter_sem i p p).mpr ⟨ok, rfl⟩, ?_⟩⟩
      exact out.trans (funext (updated _)).symm
  constructor
  · rintro ⟨r, first, second⟩
    obtain ⟨ok, rfl⟩ := (rt r).mp first
    obtain ⟨v, _, port, out⟩ := (topology_sem _ q).mp second
    exact ⟨ok, v, port, out⟩
  · rintro ⟨ok, v, hop, out⟩
    refine ⟨_, (rt _).mpr ⟨ok, rfl⟩, (topology_sem _ q).mpr ⟨v, ?_, hop, out⟩⟩
    unfold Migration.hop at hop
    split at hop
    · contradiction
    · exact nextHop_linked _ _ _ _ _ hop

def row (i : Phase) : Index m := if i = .final then c.newRow else c.oldRow

def routePacket (i : Phase) (ssh : Bool) (position : Nat) : Packet m :=
  let sourceUpper := Switch.upper c.source.1 (c.row i)
  let core := Switch.core (c.row i) c.column
  let targetUpper := Switch.upper c.destination.1 (c.row i)
  let targetLower := Switch.lower c.destination.1 c.destination.2.1
  let (location, port) := match position with
    | 0 => (Switch.tor c.source, c.sourceLower)
    | 1 => (c.sourceLower, .tor c.source)
    | 2 => (sourceUpper, c.sourceLower)
    | 3 => (core, sourceUpper)
    | 4 => (targetUpper, core)
    | 5 => (targetLower, targetUpper)
    | _ => (.tor c.destination, targetLower)
  packet location (some port) c.source c.destination ssh

private theorem route_hop (i : Phase) (ssh : Bool) (k : Nat) (hk : k < 6) :
    c.hop i (c.routePacket i ssh k .location) c.destination =
      some (c.routePacket i ssh (k + 1) .location) := by
  have endpointsNe : c.source ≠ c.destination := fun eq => c.differentPods (congrArg Prod.fst eq)
  have positions : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases positions with rfl | rfl | rfl | rfl | rfl | rfl <;> cases i <;>
    simp [routePacket, packet, hop, nextHop, sourceLower, row, endpointsNe, c.differentPods,
      Ne.symm c.differentPods, newCore, destinationUpper, c.distinctRows]

private theorem route_terminal (i : Phase) (ssh : Bool) :
    c.hop i (c.routePacket i ssh 6 .location) c.destination = none := by
  simp [routePacket, packet, hop, nextHop, sourceLower, newCore, destinationUpper]

private theorem route_delivery (i : Phase) (ssh : Bool) (k : Nat) (hk : k < 6) :
    deliver (c.routePacket i ssh (k + 1) .location) (some (c.routePacket i ssh k .location))
      (c.routePacket i ssh k) = c.routePacket i ssh (k + 1) := by
  have positions : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases positions with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem route_nonSSH (i : Phase) (k : Nat) : c.permits i (c.routePacket i false k) := by
  have fields : c.routePacket i false k .source = c.source ∧
      c.routePacket i false k .destination = c.destination ∧
      c.routePacket i false k .ssh = false := by
    unfold routePacket
    split <;> exact ⟨rfl, rfl, rfl⟩
  exact fun _ => Or.inr fields

private theorem route_blocked (i : Phase) : ¬ c.permits i (c.routePacket i true 2) := by
  intro h
  have firewall : c.routePacket i true 2 .location = c.oldFirewall ∨
      (i ≠ .initial ∧ c.routePacket i true 2 .location = c.newFirewall) := by
    cases i <;> simp [routePacket, packet, row, oldFirewall, newFirewall]
  simpa [routePacket, packet] using h firewall

theorem forwarding_hop (i : Phase) (k : Nat) (hk : k < 6) :
    Semantics (.seq (c.forwarding i) (topology m))
      (c.routePacket i false k) (c.routePacket i false (k + 1)) := by
  apply (c.hop_sem i ..).mpr
  refine ⟨c.route_nonSSH i k, _, ?_, (c.route_delivery i false k hk).symm⟩
  exact c.route_hop i false k hk

private theorem walk (i : Phase) (start length : Nat) (valid : start + length ≤ 6) :
    Semantics (c.traversal i) (c.routePacket i false start)
      (c.routePacket i false (start + length)) := by
  induction length generalizing start with
  | zero => exact .refl _
  | succ n ih =>
    have rest := ih (start + 1) (by omega)
    rw [show start + 1 + n = start + (n + 1) by omega] at rest
    exact .step (c.forwarding_hop i start (by omega)) rest

theorem nonSSH_forwarding (i : Phase) :
    Semantics (c.traversal i) (c.routePacket i false 0) (c.routePacket i false 6) :=
  c.walk i 0 6 (by decide)

private theorem route_fields (i : Phase) (ssh : Bool) (k : Nat) :
    c.routePacket i ssh k .source = c.source ∧
    c.routePacket i ssh k .destination = c.destination ∧
    c.routePacket i ssh k .ssh = ssh := by
  unfold routePacket
  split <;> exact ⟨rfl, rfl, rfl⟩

private theorem route_out (i : Phase) (ssh : Bool) (k : Nat) (hk : k ≤ 6)
    (out : c.routePacket i ssh k .location = .tor c.destination) : k = 6 := by
  have endpointsNe : c.source ≠ c.destination := fun eq => c.differentPods (congrArg Prod.fst eq)
  have positions : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases positions with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [routePacket, packet, sourceLower] at out ⊢
  exact (endpointsNe (Switch.tor.inj out)).elim

private theorem on_route (i : Phase) (ssh : Bool) (k : Nat) (q : Packet m)
    (bounded : k ≤ if ssh then 2 else 6)
    (run : Semantics (c.traversal i) (c.routePacket i ssh k) q) :
    ∃ j, k ≤ j ∧ j ≤ (if ssh then 2 else 6) ∧ q = c.routePacket i ssh j := by
  generalize eq : c.routePacket i ssh k = p at run
  change StarClosure (Semantics (.seq (c.forwarding i) (topology m))) p q at run
  induction run generalizing k with
  | refl => exact ⟨k, le_rfl, bounded, eq.symm⟩
  | @step a b d first rest ih =>
    subst a
    obtain ⟨allow, v, hop, out⟩ := (c.hop_sem i _ _).mp first
    have dest := (c.route_fields i ssh k).2.1
    rw [dest] at hop
    have below : k < (if ssh then 2 else 6) := by
      cases ssh with
      | false =>
        change k ≤ 6 at bounded
        change k < 6
        by_contra! h
        have atEnd : k = 6 := by omega
        subst k
        rw [c.route_terminal i false] at hop
        contradiction
      | true =>
        change k ≤ 2 at bounded
        change k < 2
        by_contra! h
        have atFilter : k = 2 := by omega
        subst k
        exact c.route_blocked i allow
    have hopIndex : k < 6 := by cases ssh <;> simp at below <;> omega
    have next := Option.some.inj ((c.route_hop i ssh k hopIndex).symm.trans hop)
    have eqNext : c.routePacket i ssh (k + 1) = b := by
      rw [out, ← next, c.route_delivery i ssh k hopIndex]
    obtain ⟨j, lower, upper, out⟩ := ih (k + 1) (by omega) eqNext
    exact ⟨j, by omega, upper, out⟩

theorem ssh_isolated_at_phase (i : Phase) (q : Packet m)
    (run : Semantics (c.traversal i) (c.routePacket i true 0) q) :
    q .location ≠ .tor c.destination := by
  obtain ⟨k, _, bound, rfl⟩ := c.on_route i true 0 q (by decide) run
  change k ≤ 2 at bound
  intro out
  have atEnd := c.route_out i true k (by omega) out
  omega

/-- Effective system states after the controller and switch synchronize.
The four update labels retain the literal policy payload. -/
def body (i : Phase) : DyNetKAT (schema m) :=
  let packets := DyNetKAT.nSeq (c.traversal i) (.var i.name)
  match i.next with
  | none => packets
  | some j => .choice packets (.rcfgPrefix (channel i) (c.payload i j) (.var j.name))

def env : RecEnv (schema m) := fun name => (Phase.ofName name).map c.body

@[simp] theorem lookup_phase (i : Phase) : c.env.lookup i.name = some (c.body i) := by
  simp [env, RecEnv.lookup]

private theorem body_guarded (i : Phase) : GuardedOccurrences (c.body i) := by
  cases i <;> exact (by trivial)

private theorem body_syntax (i : Phase) : PaperSyntax true (c.body i) := by
  cases i <;> exact (by trivial)

private theorem body_names (i : Phase) {x : Var} (h : x ∈ recursiveVars (c.body i)) :
    ∃ j : Phase, x = j.name := by
  cases i <;> simp [body, Phase.next, recursiveVars] at h <;>
    first | exact ⟨_, h⟩ | exact h.elim (fun h => ⟨_, h⟩) (fun h => ⟨_, h⟩)

private theorem reachable_names (i : Phase) {x : Var}
    (h : ReachableVar c.env (.var i.name) x) : ∃ j : Phase, x = j.name := by
  induction h with
  | direct h => exact ⟨i, Finset.mem_singleton.mp h⟩
  | throughDefinition _ lookup occurs ih =>
    obtain ⟨j, rfl⟩ := ih
    have eq := RecEnv.lookup_unique lookup (c.lookup_phase j)
    subst_vars
    exact c.body_names j occurs

theorem admission (i : Phase) : PaperAdmissible true c.env (.var i.name) := by
  apply (paperAdmissible_iff ..).mpr
  refine ⟨trivial, fun x reachable => ?_⟩
  obtain ⟨j, rfl⟩ := c.reachable_names i reachable
  refine ⟨c.body j, ⟨c.lookup_phase j, c.body_syntax j,
    (typedPaperGuarded_iff_guardedOccurrences _).mpr (c.body_guarded j)⟩, ?_⟩
  exact fun _ h => RecEnv.lookup_unique h.1 (c.lookup_phase j)

def program : Program true c.env := ⟨.var Phase.initial.name, c.admission .initial⟩

theorem update_synchronizes (i j : Phase) (controller network : DyNetKAT (schema m))
    (pt hl : List (Packet m)) :
    Step c.env
      ⟨.parallel (.send (channel i) (c.payload i j) controller)
        (.recv (channel i) (c.payload i j) network), pt, hl⟩
      (c.event i j) ⟨.parallel controller network, pt, hl⟩ :=
  .cpol_sync_send_recv _ _ _ _ _ _ _ _ (.cpol_send _ _ _ _ _) (.cpol_recv _ _ _ _ _)

theorem migration_step (i j : Phase) (advance : i.next = some j) (pt hl : List (Packet m)) :
    Step c.env ⟨.var i.name, pt, hl⟩ (c.event i j) ⟨.var j.name, pt, hl⟩ := by
  apply Step.cpol_var i.name (c.body i) _ _ _ _ _ _ (c.lookup_phase i)
  simp only [body, advance]
  exact .cpol_choice_r _ _ _ _ _ _ _ _ (.cpol_rcfg _ _ _ _ _)

def updates (i : Phase) : List (Action (schema m)) :=
  let first := c.event .initial .firewallInstalled
  let second := c.event .firewallInstalled .coreUpdated
  let third := c.event .coreUpdated .destinationUpdated
  let fourth := c.event .destinationUpdated .final
  match i with
  | .initial => []
  | .firewallInstalled => [first]
  | .coreUpdated => [first, second]
  | .destinationUpdated => [first, second, third]
  | .final => [first, second, third, fourth]

theorem migration_reachable (i : Phase) (pt hl : List (Packet m)) :
    Steps c.env ⟨c.program.term, pt, hl⟩ (c.updates i) ⟨.var i.name, pt, hl⟩ := by
  have first := c.migration_step .initial .firewallInstalled rfl pt hl
  have second := c.migration_step .firewallInstalled .coreUpdated rfl pt hl
  have third := c.migration_step .coreUpdated .destinationUpdated rfl pt hl
  have fourth := c.migration_step .destinationUpdated .final rfl pt hl
  cases i
  · exact .nil _
  · exact .cons _ _ _ _ _ first (.nil _)
  · exact .cons _ _ _ _ _ first (.cons _ _ _ _ _ second (.nil _))
  · exact .cons _ _ _ _ _ first (.cons _ _ _ _ _ second (.cons _ _ _ _ _ third (.nil _)))
  · exact .cons _ _ _ _ _ first (.cons _ _ _ _ _ second
      (.cons _ _ _ _ _ third (.cons _ _ _ _ _ fourth (.nil _))))

theorem reachable_phase (i : Phase) : ∃ r : c.program.Residual, r.term = .var i.name :=
  ⟨c.program.afterTrace (c.migration_reachable i [] []), rfl⟩

theorem forwarding_step (i : Phase) (p q : Packet m) (pt hl : List (Packet m))
    (run : Semantics (c.traversal i) p q) :
    Step c.env ⟨.var i.name, p :: pt, hl⟩ (.packet p q) ⟨.var i.name, pt, q :: hl⟩ := by
  apply Step.cpol_var i.name (c.body i) _ _ _ _ _ _ (c.lookup_phase i)
  have step := Step.cpol_seq_ok (env := c.env) (c.traversal i) (.var i.name) p q pt hl
    ((historySemantics_singleton_iff_packetSemantics ..).mpr run)
  unfold body
  split
  · exact step
  · exact .cpol_choice_l _ _ _ _ _ _ _ _ step

theorem nonSSH_trace (i : Phase) :
    c.program.Trace (c.updates i ++ [.packet (c.routePacket i false 0) (c.routePacket i false 6)]) := by
  let pt := [c.routePacket i false 0]
  have earlier := c.migration_reachable i pt []
  have last := c.forwarding_step i _ _ [] [] (c.nonSSH_forwarding i)
  refine ⟨pt, [], ⟨.var i.name, [], [c.routePacket i false 6]⟩, ?_⟩
  have append {a b : Config (schema m)} {w : List (Action (schema m))}
      (steps : Steps c.env a w b) {d : Config (schema m)} {label : Action (schema m)}
      (step : Step c.env b label d) : Steps c.env a (w ++ [label]) d := by
    induction steps with
    | nil => exact .cons _ _ _ _ _ step (.nil _)
    | cons _ _ _ _ _ head _ ih => exact .cons _ _ _ _ _ head (ih step)
  exact append earlier last

private theorem phase_step_cases (i : Phase) {pt hl pt' hl' : List (Packet m)}
    {a : Action (schema m)} {q : DyNetKAT (schema m)}
    (h : Step c.env ⟨.var i.name, pt, hl⟩ a ⟨q, pt', hl'⟩) :
    (∃ p out, a = .packet p out ∧ q = .var i.name ∧ Semantics (c.traversal i) p out) ∨
    (∃ j, i.next = some j ∧ a = c.event i j ∧ q = .var j.name) := by
  cases h with
  | cpol_var _ b _ _ _ _ _ _ lookup hs =>
    have eq := RecEnv.lookup_unique lookup (c.lookup_phase i)
    subst b
    have packetCase (h : Step c.env ⟨.nSeq (c.traversal i) (.var i.name), pt, hl⟩ a
        ⟨q, pt', hl'⟩) :
        ∃ p out, a = .packet p out ∧ q = .var i.name ∧ Semantics (c.traversal i) p out := by
      obtain ⟨p, out, hp, hq, rel, _⟩ := nSeq_step_inv _ _ _ _ _ _ _ _ _ h
      exact ⟨p, out, hp, hq, (historySemantics_singleton_iff_packetSemantics ..).mp rel⟩
    cases hn : i.next with
    | none => exact Or.inl (packetCase (by simpa only [body, hn] using hs))
    | some j =>
      simp only [body, hn] at hs
      rcases choice_step_inv _ _ _ _ _ _ _ _ _ hs with hp | hu
      · exact Or.inl (packetCase hp)
      · obtain ⟨ha, hq, _, _⟩ := rcfgPrefix_step_inv _ _ _ _ _ _ _ _ _ _ hu
        exact Or.inr ⟨j, rfl, ha, hq⟩

/-- SSH isolation over every feasible source trace, including traces with
arbitrarily many packet transitions between or after updates. -/
theorem ssh_isolation (w : List (Action (schema m))) (run : c.program.Trace w)
    (out : Packet m) (egress : out .location = .tor c.destination) :
    .packet (c.routePacket .initial true 0) out ∉ w := by
  have all (i : Phase) (r : SourceTrace c.env (.var i.name) w) :
      .packet (c.routePacket .initial true 0) out ∉ w := by
    clear run
    induction w generalizing i with
    | nil => simp
    | cons a tail ih =>
      obtain ⟨q, head, rest⟩ := sourceTrace_cons_actionStep.mp r
      rcases c.phase_step_cases i head with ⟨p, reached, label, rfl, rel⟩ | ⟨j, _, label, rfl⟩
      · simp only [List.mem_cons, not_or]
        refine ⟨?_, ih i rest⟩
        intro bad
        rw [label] at bad
        obtain ⟨inputEq, outputEq⟩ := Action.packet.inj bad
        subst p
        subst reached
        exact c.ssh_isolated_at_phase i out rel egress
      · simp [label, event, ih j rest]
  exact all .initial run

private def tests (f : Field) (v : Value m f) : Predicate (schema m) := .pFieldEq ⟨f, v⟩

def ingress : Predicate (schema m) :=
  .pAnd (tests .location (.tor c.source))
    (.pAnd (tests .port (some c.sourceLower))
      (.pAnd (tests .source c.source) (tests .destination c.destination)))

def egress : Predicate (schema m) :=
  .pAnd (tests .location (.tor c.destination))
    (.pAnd (tests .port (some (.lower c.destination.1 c.destination.2.1)))
      (tests .destination c.destination))

def waypoint : Predicate (schema m) := tests .location c.newFirewall

private theorem ingress_fields (p : Packet m) :
    c.ingress.holds p ↔ p .location = .tor c.source ∧ p .port = some c.sourceLower ∧
      p .source = c.source ∧ p .destination = c.destination := by
  simp only [ingress, tests, Predicate.holds, Predicate.eval, Bool.and_eq_true, decide_eq_true_eq]

private theorem egress_fields (p : Packet m) :
    c.egress.holds p ↔ p .location = .tor c.destination ∧
      p .port = some (.lower c.destination.1 c.destination.2.1) ∧ p .destination = c.destination := by
  simp only [egress, tests, Predicate.holds, Predicate.eval, Bool.and_eq_true, decide_eq_true_eq]

def endpointsRelation : NetKAT (schema m) :=
  .seq (.test c.ingress) (.seq (c.traversal .final) (.test c.egress))

def waypointRelation : NetKAT (schema m) :=
  let hop := NetKAT.seq (c.forwarding .final) (topology m)
  .seq (.test c.ingress)
    (.seq (.star (.seq (.test (.pNot c.egress)) hop))
      (.seq (.test c.waypoint)
        (.seq (.star (.seq (.test (.pNot c.ingress)) hop)) (.test c.egress))))

private theorem guarded_walk (guard : Predicate (schema m)) (start length : Nat)
    (within : start + length ≤ 6)
    (guardHolds : ∀ k, start ≤ k → k < start + length → guard.holds (c.routePacket .final false k)) :
    Semantics (.star (.seq (.test guard) (.seq (c.forwarding .final) (topology m))))
      (c.routePacket .final false start) (c.routePacket .final false (start + length)) := by
  induction length generalizing start with
  | zero => exact .refl _
  | succ n ih =>
    have tail := ih (start + 1) (by omega) (fun k lo hi => guardHolds k (by omega) (by omega))
    rw [show start + 1 + n = start + (n + 1) by omega] at tail
    exact .step ⟨_, ⟨guardHolds start le_rfl (by omega), rfl⟩,
      c.forwarding_hop .final start (by omega)⟩ tail

theorem final_waypoint_inclusion (p q : Packet m)
    (h : Semantics c.endpointsRelation p q) : Semantics c.waypointRelation p q := by
  obtain ⟨a, ⟨hin, ha⟩, b, run, hout, hb⟩ := h
  subst a
  subst b
  have fields := (c.ingress_fields p).mp hin
  have start : p = c.routePacket .final (p .ssh) 0 := by
    funext f
    cases f
    · exact fields.1
    · exact fields.2.1
    · exact fields.2.2.1
    · exact fields.2.2.2
    · rfl
  have out := ((c.egress_fields q).mp hout).1
  cases ssh : p .ssh with
  | true =>
    have bad : Semantics (c.traversal .final) (c.routePacket .final true 0) q := by
      rwa [← ssh, ← start]
    exact (c.ssh_isolated_at_phase .final q bad out).elim
  | false =>
    have start' : p = c.routePacket .final false 0 := by simpa only [ssh] using start
    rw [start'] at run
    obtain ⟨k, _, bound, eq⟩ := c.on_route .final false 0 q (by decide) run
    change k ≤ 6 at bound
    have finish := c.route_out .final false k bound (eq ▸ out)
    subst k
    subst p
    subst q
    have before : ∀ k, 0 ≤ k → k < 0 + 2 →
        (Predicate.pNot c.egress).holds (c.routePacket .final false k) := by
      intro k _ less
      change (!c.egress.eval (c.routePacket .final false k)) = true
      rw [Bool.not_eq_true', Bool.eq_false_iff]
      intro h
      have bad := ((c.egress_fields _).mp h).1
      exact (by omega : k ≠ 6) (c.route_out .final false k (by omega) bad)
    have after : ∀ k, 2 ≤ k → k < 2 + 4 →
        (Predicate.pNot c.ingress).holds (c.routePacket .final false k) := by
      intro k lower upper
      change (!c.ingress.eval (c.routePacket .final false k)) = true
      rw [Bool.not_eq_true', Bool.eq_false_iff]
      intro h
      have bad := ((c.ingress_fields _).mp h).1
      have positions : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
      rcases positions with rfl | rfl | rfl | rfl <;> cases bad
    have middle : c.waypoint.holds (c.routePacket .final false 2) := by
      simp only [waypoint, tests, Predicate.holds, Predicate.eval, decide_eq_true_eq]
      rfl
    exact ⟨_, ⟨hin, rfl⟩, _, c.guarded_walk (.pNot c.egress) 0 2 (by decide) before,
      _, ⟨middle, rfl⟩, _, c.guarded_walk (.pNot c.ingress) 2 4 (by decide) after, hout, rfl⟩

theorem final_waypoint :
    NetKAT.Derives (.union c.endpointsRelation c.waypointRelation) c.waypointRelation := by
  apply (netkatNativeEquivFinite_iff_derives ..).mp
  apply (netkatNativeEquivFinite_correct ..).mpr
  intro p q
  exact ⟨fun h => h.elim (c.final_waypoint_inclusion p q) id, Or.inr⟩

theorem waypoint_verdict :
    netkatNativeEquivFinite (.union c.endpointsRelation c.waypointRelation) c.waypointRelation = true :=
  (netkatNativeEquivFinite_iff_derives ..).mpr c.final_waypoint

private def names : Finset Var := Finset.univ.image Phase.name

private theorem name_mem (i : Phase) : i.name ∈ names :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

def compiled : c.program.Compiled := ⟨names, by
  constructor
  · intro x hx
    obtain rfl := Finset.mem_singleton.mp hx
    exact name_mem .initial
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    refine ⟨c.body i, c.lookup_phase i, ?_⟩
    intro y hy
    obtain ⟨j, rfl⟩ := c.body_names i hy
    exact name_mem j⟩

theorem graph_nonSSH (i : Phase) :
    ∃ pt hl d,
      GSteps c.compiled.graph ⟨c.compiled.graph.root, pt, hl⟩
        (c.updates i ++ [.packet (c.routePacket i false 0) (c.routePacket i false 6)]) d :=
  (Program.Compiled.trace_iff c.program c.compiled _).mp (c.nonSSH_trace i)

def checks : RestrictionChecks (schema m) := fun _ _ => false

theorem support :
    ProjectionSupport c.compiled.graph (fun _ => checks)
      (ProjectionLive c.env c.program.term) := by
  apply toGraph_projectionSupport c.compiled.support c.program.admissible.1
  intro x b hx lookup
  obtain ⟨i, rfl⟩ := c.reachable_names .initial hx
  have eq := RecEnv.lookup_unique lookup (c.lookup_phase i)
  subst b
  cases i <;> exact (by trivial)

theorem valid : (c.compiled.initial checks).checked.Valid
    (ProjectionLive c.env c.program.term) :=
  toGProc_projectionValid trivial

theorem certified_ssh_word (prefixEvents : TraceSafety.Word (schema m)) (q : Packet m)
    (egress : q .location = .tor c.destination) :
    TraceSafety.check c.compiled checks c.support c.valid
      [prefixEvents ++ [.packet (c.routePacket .initial true 0) q]] = true := by
  apply (TraceSafety.check_correct ..).mpr
  intro w mem trace
  obtain rfl := List.mem_singleton.mp mem
  exact c.ssh_isolation _ trace q egress
    (List.mem_map.mpr ⟨_, List.mem_append_right _ List.mem_cons_self, rfl⟩)

end Migration

/-- First and last ToRs in generator order, and the first two distinct
source-side upper rows. The parameter describes every even pod count
starting at four, including all six paper sizes. -/
def benchmark (n : Nat) : Migration (n + 2) :=
  let lastPod : Pod (n + 2) := ⟨2 * (n + 2) - 1, by omega⟩
  let lastIndex : Index (n + 2) := ⟨n + 1, by omega⟩
  { source := (⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩)
    destination := (lastPod, lastIndex, lastIndex)
    differentPods := fun eq => by
      have h := congrArg Fin.val eq
      change 0 = 2 * (n + 2) - 1 at h
      omega
    oldRow := ⟨0, by omega⟩
    newRow := ⟨1, by omega⟩
    distinctRows := fun eq => Nat.zero_ne_one (congrArg Fin.val eq)
    column := ⟨0, by omega⟩ }

end DyNetKAT.DyNetKAT.FatTree
