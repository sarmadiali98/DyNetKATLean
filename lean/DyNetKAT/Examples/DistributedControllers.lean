import DyNetKAT.DyNetKAT.TraceSafetyCheck
import DyNetKAT.DyNetKAT.Reachability
import DyNetKAT.DyNetKAT.ProjectionDerivation

set_option linter.dupNamespace false

namespace DyNetKAT.DyNetKAT.DistributedControllers

open DyNetKAT.NetKAT TraceSafety

/-- A paper port numbered 1 through 16 is stored as the two base-four
digits of its predecessor, high digit in swId and low digit in port. -/
def digit (n : Nat) : FieldValueEnum :=
  match n % 4 with
  | 0 => .v0
  | 1 => .v1
  | 2 => .v8
  | _ => .v9

def portTest (n : Nat) : NetKAT :=
  .seq (.fieldTest .swId (digit ((n - 1) / 4))) (.fieldTest .port (digit (n - 1)))

def setPort (n : Nat) : NetKAT :=
  .seq (.assign1 .swId (digit ((n - 1) / 4))) (.assign1 .port (digit (n - 1)))

def edge (ingress egress : Nat) : NetKAT := .seq (portTest ingress) (setPort egress)

def packet (n : Nat) : CtxPkt := fun
  | .swId => digit ((n - 1) / 4)
  | .port => digit (n - 1)
  | _ => .v0

abbrev Route := Nat × Nat

def links : List Route := [(3, 5), (4, 6), (7, 8), (9, 11), (10, 12), (13, 15), (14, 16)]

def routePolicy (routes : List Route) : NetKAT :=
  routes.foldr (fun r p => .union (edge r.1 r.2) p) .drop

def topology : NetKAT := routePolicy links

abbrev Switch := Fin 6
abbrev Table := Fin 6
abbrev Tables := Switch → Table

def channel (s : Switch) : Channel := "upS" ++ toString (s.val + 1)

def originalRoute (s : Switch) : Option Route :=
  match s.val with
  | 0 => some (2, 4)
  | 1 => some (12, 14)
  | 4 => some (6, 7)
  | 5 => some (8, 10)
  | _ => none

def tableRoute (s : Switch) (t : Table) : Option Route :=
  match t.val with
  | 0 => originalRoute s
  | 1 => none
  | 2 => some (1, 3)
  | 3 => some (11, 13)
  | 4 => some (5, 7)
  | _ => some (8, 9)

def policy (s : Switch) (t : Table) : NetKAT :=
  (tableRoute s t).elim .drop (fun r => edge r.1 r.2)

def initialTables : Tables := fun _ => 0

def switchPolicies (t : Tables) : NetKAT :=
  (List.finRange 6).foldr (fun s p => .union (policy s (t s)) p) .drop

def forwarding (t : Tables) : NetKAT := .star (.seq (switchPolicies t) topology)

private def tableChar (t : Table) : Char :=
  match t.val with
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | _ => '5'

private def readTable (c : Char) : Table :=
  if c = '1' then 1 else if c = '2' then 2 else if c = '3' then 3 else
  if c = '4' then 4 else if c = '5' then 5 else 0

private theorem readTable_tableChar (t : Table) : readTable (tableChar t) = t := by
  have bound := t.isLt
  have cases : t.val = 0 ∨ t.val = 1 ∨ t.val = 2 ∨ t.val = 3 ∨ t.val = 4 ∨ t.val = 5 := by omega
  rcases cases with h | h | h | h | h | h <;> simp [tableChar, h, readTable, Fin.ext_iff] <;> rfl

def name (t : Tables) : Var := String.mk (List.ofFn (fun s => tableChar (t s)))

private def readTables (x : Var) : Tables := fun s =>
  readTable (x.toList[s.val]?.getD '0')

@[simp] private theorem readTables_name (t : Tables) : readTables (name t) = t := by
  funext s
  change readTable ((List.ofFn (fun s => tableChar (t s)))[s.val]?.getD '0') = t s
  simp only [List.getElem?_ofFn, s.isLt, dif_pos, Option.getD_some, readTable_tableChar]

def network (t : Tables) : DyNetKAT := .var (name t)

def updates (t : Tables) : List DyNetKAT :=
  (List.finRange 6).flatMap fun s =>
    (List.finRange 5).map fun i =>
      .recv (channel s) (policy s i.succ) (network (Function.update t s i.succ))

def body (t : Tables) : DyNetKAT :=
  .choice (.nSeq (forwarding t) (network t)) (choiceOf (updates t))

def env : RecEnv := fun x => some (body (readTables x))

@[simp] theorem lookup_network (t : Tables) : env.lookup (name t) = some (body t) := by
  simp [RecEnv.lookup, env]

private theorem choiceOf_formation (xs : List DyNetKAT)
    (h : ∀ p ∈ xs, PaperSyntax false p ∧ GuardedOccurrences p) :
    PaperSyntax false (choiceOf xs) ∧ GuardedOccurrences (choiceOf xs) := by
  induction xs with
  | nil => exact ⟨trivial, trivial⟩
  | cons p ps ih =>
    have hp := h p List.mem_cons_self
    have hps := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    exact ⟨⟨hp.1, hps.1⟩, ⟨hp.2, hps.2⟩⟩

private theorem body_formation (t : Tables) : PaperSyntax false (body t) ∧
    GuardedOccurrences (body t) := by
  have h := choiceOf_formation (updates t) (by
    intro p m
    simp only [updates, List.mem_flatMap, List.mem_map] at m
    obtain ⟨_, _, _, _, rfl⟩ := m
    exact ⟨trivial, trivial⟩)
  exact ⟨⟨trivial, h.1⟩, ⟨trivial, h.2⟩⟩

private theorem admitted {extended : Bool} {p : DyNetKAT} (sort : PaperSyntax extended p) :
    PaperAdmissible extended env p := by
  apply (paperAdmissible_iff ..).mpr
  refine ⟨sort, fun x _ => ⟨body (readTables x), ⟨rfl, ?_, ?_⟩, ?_⟩⟩
  · exact PaperSyntax.of_base (body_formation _).1
  · exact (typedPaperGuarded_iff_guardedOccurrences _).mpr (body_formation _).2
  · intro q h
    exact Option.some.inj h.1.symm

def notify (s : Switch) (t : Table) (next : DyNetKAT := .deadlock) : DyNetKAT :=
  .send (channel s) (policy s t) next

def independentC1 : DyNetKAT := .parallel (.parallel (notify 0 1) (notify 2 2)) (notify 4 4)
def independentC2 : DyNetKAT := .parallel (.parallel (notify 1 1) (notify 3 3)) (notify 5 5)

private def script (labels : List MoveLabel) : DyNetKAT :=
  labels.foldr MoveLabel.prefix .deadlock

private def sendUpdate (s : Switch) (t : Table) : MoveLabel := .send (channel s) (policy s t)

private def leftScript : List MoveLabel :=
  [sendUpdate 0 1, .send "syn" .id, sendUpdate 2 2, sendUpdate 4 4]

private def rightScript : List MoveLabel :=
  [sendUpdate 1 1, .recv "syn" .id, sendUpdate 3 3, sendUpdate 5 5]

def syncC1 : DyNetKAT := script leftScript
def syncC2 : DyNetKAT := script rightScript

def system (t : Tables) (c1 c2 : DyNetKAT) : DyNetKAT :=
  .parallel (.parallel (network t) c1) c2

theorem independent_admitted :
    BaseAdmissible env (system initialTables independentC1 independentC2) :=
  admitted (by trivial)

def independent : Program false env :=
  ⟨_, independent_admitted⟩

private def blocksChannel (ch : Channel) (p : NetKAT) : Bool :=
  ((List.finRange 6).map channel).contains ch || decide (ch = "syn" ∧ p = .id)

private def blocked : CommunicationAction → Bool
  | .send ch p | .recv ch p => blocksChannel ch p

/-- The Eq. (2) restriction for Fig. 7: block upSi sends/receives and
the individual syn communications of the identity policy. -/
def controllerRestriction : Set CommunicationAction := {a | blocked a = true}

def synchronizedTerm :=
  DyNetKAT.restrict controllerRestriction (system initialTables syncC1 syncC2)

theorem synchronized_admitted : PaperAdmissible true env synchronizedTerm :=
  admitted (by trivial)

def synchronized : Program true env :=
  ⟨_, synchronized_admitted⟩

theorem network_receive (t : Tables) (s : Switch) (i : Fin 5) (pt hl : List CtxPkt) :
    Step env ⟨network t, pt, hl⟩ (.recv (channel s) (policy s i.succ))
      ⟨network (Function.update t s i.succ), pt, hl⟩ := by
  apply Step.cpol_var _ _ _ _ _ _ _ _ (lookup_network t)
  apply Step.cpol_choice_r
  apply (choiceOf_step_iff ..).mpr
  refine ⟨_, ?_, Step.cpol_recv _ _ _ _ _⟩
  exact List.mem_flatMap.mpr ⟨s, List.mem_finRange s,
    List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩⟩

theorem network_forward (t : Tables) {i o : CtxPkt}
    (h : HistorySemantics (forwarding t) (.singleton i) (.singleton o)) (pt hl : List CtxPkt) :
    Step env ⟨network t, i :: pt, hl⟩ (.packet i o) ⟨network t, pt, o :: hl⟩ := by
  exact Step.cpol_var _ _ _ _ _ _ _ _ (lookup_network t)
    (Step.cpol_choice_l _ _ _ _ _ _ _ _ (Step.cpol_seq_ok _ _ _ _ _ _ h))


theorem updateLeft (t : Tables) (s : Switch) (i : Fin 5) (c₁ c₁' c₂ : DyNetKAT)
    (pt hl : List CtxPkt)
    (h : Step env ⟨c₁, pt, hl⟩ (.send (channel s) (policy s i.succ)) ⟨c₁', pt, hl⟩) :
    Step env ⟨system t c₁ c₂, pt, hl⟩ (.rcfg (channel s) (policy s i.succ))
      ⟨system (Function.update t s i.succ) c₁' c₂, pt, hl⟩ :=
  .cpol_par_l _ _ _ _ _ _ _ _ (.cpol_sync_recv_send _ _ _ _ _ _ _ _
    (network_receive t s i pt hl) h)

theorem updateRight (t : Tables) (s : Switch) (i : Fin 5) (c₁ c₂ c₂' : DyNetKAT)
    (pt hl : List CtxPkt)
    (h : Step env ⟨c₂, pt, hl⟩ (.send (channel s) (policy s i.succ)) ⟨c₂', pt, hl⟩) :
    Step env ⟨system t c₁ c₂, pt, hl⟩ (.rcfg (channel s) (policy s i.succ))
      ⟨system (Function.update t s i.succ) c₁ c₂', pt, hl⟩ :=
  .cpol_sync_recv_send _ _ _ _ _ _ _ _
    (.cpol_par_l _ _ _ _ _ _ _ _ (network_receive t s i pt hl)) h

theorem forwardSystem (t : Tables) (c₁ c₂ : DyNetKAT) {i o : CtxPkt} (pt hl : List CtxPkt)
    (h : HistorySemantics (forwarding t) (.singleton i) (.singleton o)) :
    Step env ⟨system t c₁ c₂, i :: pt, hl⟩ (.packet i o) ⟨system t c₁ c₂, pt, o :: hl⟩ :=
  .cpol_par_l _ _ _ _ _ _ _ _ (.cpol_par_l _ _ _ _ _ _ _ _ (network_forward t h pt hl))

def afterS6 : Tables := Function.update initialTables 5 5
def afterS4S6 : Tables := Function.update afterS6 3 3
def c2AfterS6 : DyNetKAT := .parallel (.parallel (notify 1 1) (notify 3 3)) .deadlock
def c2AfterS4S6 : DyNetKAT := .parallel (.parallel (notify 1 1) .deadlock) .deadlock

def s6Event : Action := .rcfg (channel 5) (policy 5 5)
def s4Event : Action := .rcfg (channel 3) (policy 3 3)

theorem independent_s6 (pt hl : List CtxPkt) :
    Step env ⟨independent.term, pt, hl⟩ s6Event
      ⟨system afterS6 independentC1 c2AfterS6, pt, hl⟩ :=
  updateRight _ 5 4 _ _ _ pt hl (.cpol_par_r _ _ _ _ _ _ _ _ (.cpol_send _ _ _ _ _))

theorem independent_s4 (pt hl : List CtxPkt) :
    Step env ⟨system afterS6 independentC1 c2AfterS6, pt, hl⟩ s4Event
      ⟨system afterS4S6 independentC1 c2AfterS4S6, pt, hl⟩ :=
  updateRight _ 3 2 _ _ _ pt hl (.cpol_par_l _ _ _ _ _ _ _ _
    (.cpol_par_r _ _ _ _ _ _ _ _ (.cpol_send _ _ _ _ _)))

def code (n : Nat) : FieldValueEnum × FieldValueEnum :=
  (digit ((n - 1) / 4), digit (n - 1))

def location (p : CtxPkt) : FieldValueEnum × FieldValueEnum :=
  (p .swId, p .port)

def place (n : Nat) (p : CtxPkt) : CtxPkt :=
  Packet.update (Packet.update p .swId (code n).1) .port (code n).2

@[simp] private theorem location_place (n : Nat) (p : CtxPkt) :
    location (place n p) = code n := rfl

private theorem place_place (n m : Nat) (p : CtxPkt) : place n (place m p) = place n p := by
  funext f
  cases f <;> rfl

theorem portTest_sem (n : Nat) (i o : CtxPkt) :
    Semantics (portTest n) i o ↔ i = o ∧ location i = code n := by
  simp only [portTest, seq_sem, fieldTest_sem, location, code, Prod.mk.injEq]
  constructor
  · rintro ⟨_, ⟨hi, rfl⟩, ho, rfl⟩
    exact ⟨rfl, hi, ho⟩
  · rintro ⟨rfl, hi, ho⟩
    exact ⟨i, ⟨hi, rfl⟩, ho, rfl⟩

private theorem edge_sem (r : Route) (i o : CtxPkt) :
    Semantics (edge r.1 r.2) i o ↔ location i = code r.1 ∧ o = place r.2 i := by
  simp only [edge, portTest_sem, setPort, seq_sem, assign1_sem]
  constructor
  · rintro ⟨_, ⟨rfl, h⟩, _, rfl, rfl⟩
    exact ⟨h, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨i, ⟨rfl, h⟩, _, rfl, rfl⟩

private theorem routePolicy_sem (rs : List Route) (i o : CtxPkt) :
    Semantics (routePolicy rs) i o ↔
      ∃ r ∈ rs, location i = code r.1 ∧ o = place r.2 i := by
  induction rs with
  | nil => simp [routePolicy, Semantics]
  | cons r rs ih =>
    change (Semantics (edge r.1 r.2) i o ∨ Semantics (routePolicy rs) i o) ↔ _
    rw [edge_sem, ih]
    simp only [List.mem_cons]
    aesop

private def switchRoutes (t : Tables) : List Route :=
  (List.finRange 6).filterMap fun s => tableRoute s (t s)

private theorem switchPolicies_eq (t : Tables) :
    ∀ i o, Semantics (switchPolicies t) i o ↔ Semantics (routePolicy (switchRoutes t)) i o := by
  intro i o
  unfold switchPolicies switchRoutes
  generalize List.finRange 6 = ss
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    change (Semantics (policy s (t s)) i o ∨ _) ↔ _
    rw [ih]
    unfold policy
    cases h : tableRoute s (t s) <;> simp [h, routePolicy, Semantics]

/-- Compose the switch and wire edges on the two location digits.
This list ranges over topology edges, independently of packet headers. -/
def hops (t : Tables) : List Route :=
  (switchRoutes t).flatMap fun r => links.filterMap fun l =>
    if code r.2 = code l.1 then some (r.1, l.2) else none

private theorem hop_sem (t : Tables) (i o : CtxPkt) :
    Semantics (.seq (switchPolicies t) topology) i o ↔
      ∃ r ∈ hops t, location i = code r.1 ∧ o = place r.2 i := by
  have hs : Semantics (switchPolicies t) i = Semantics (routePolicy (switchRoutes t)) i := by
    funext o
    exact propext (switchPolicies_eq t i o)
  simp only [seq_sem, hs, topology, routePolicy_sem, hops, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨_, ⟨r, hr, hi, rfl⟩, l, hl, join, rfl⟩
    refine ⟨(r.1, l.2), ⟨r, hr, l, hl, ?_⟩, hi, place_place ..⟩
    simpa [join]
  · rintro ⟨_, ⟨r, hr, l, hl, out⟩, hi, rfl⟩
    split at out
    next join =>
      obtain rfl := Option.some.inj out
      exact ⟨place r.2 i, ⟨r, hr, hi, rfl⟩, l, hl, join, (place_place ..).symm⟩
    next => contradiction

private theorem follows {t : Tables} {i o : Nat} (h : (i, o) ∈ hops t) (base : CtxPkt) :
    Semantics (.seq (switchPolicies t) topology) (place i base) (place o base) :=
  (hop_sem ..).mpr ⟨(i, o), h, location_place .., (place_place ..).symm⟩

private theorem history {p : NetKAT} {i o : CtxPkt} (h : Semantics p i o) :
    HistorySemantics p (.singleton i) (.singleton o) :=
  (historySemantics_iff_packetSemantics p i o [] []).mpr ⟨rfl, h⟩

private def closedPorts (t : Tables) (ns : List Nat) : Bool :=
  (hops t).all fun r => decide (code r.1 ∈ ns.map code → code r.2 ∈ ns.map code)

private theorem stays_in_ports {t : Tables} {ns : List Nat} (closed : closedPorts t ns = true)
    {i o : CtxPkt} (run : Semantics (forwarding t) i o) (inside : location i ∈ ns.map code) :
    location o ∈ ns.map code := by
  change StarClosure (Semantics (.seq (switchPolicies t) topology)) i o at run
  induction run with
  | refl => exact inside
  | step hop _ ih =>
    obtain ⟨r, mem, source, rfl⟩ := (hop_sem ..).mp hop
    have allowed := List.all_eq_true.mp closed r mem
    exact ih (of_decide_eq_true allowed (source ▸ inside))

private def walks (t : Tables) (start : Nat) : List Nat → Bool
  | [] => true
  | next :: rest => decide ((start, next) ∈ hops t) && walks t next rest

private theorem walk_cover {t : Tables} {start : Nat} {rest : List Nat}
    (walk : walks t start rest = true) {finish : Nat} (mem : finish ∈ start :: rest)
    (base : CtxPkt) :
    Semantics (forwarding t) (place start base) (place finish base) := by
  induction rest generalizing start with
  | nil =>
    obtain rfl := List.mem_singleton.mp mem
    exact .refl _
  | cons next rest ih =>
    rcases List.mem_cons.mp mem with rfl | later
    · exact .refl _
    · have both : decide ((start, next) ∈ hops t) = true ∧ walks t next rest = true := by simpa only [walks, Bool.and_eq_true] using walk
      exact .step (follows (of_decide_eq_true both.1) base) (ih both.2 later)

private theorem packet_with_location {t : Tables} {i o base : CtxPkt}
    (run : Semantics (forwarding t) i o) (n : Nat) (loc : location o = code n)
    (input : i .tpSrc = base .tpSrc ∧ i .tpDst = base .tpDst) : o = place n base := by
  change StarClosure (Semantics (.seq (switchPolicies t) topology)) i o at run
  induction run with
  | refl =>
    funext f
    cases f with
    | tpSrc => exact input.1
    | tpDst => exact input.2
    | swId => exact congrArg Prod.fst loc
    | port => exact congrArg Prod.snd loc
  | step hop _ ih =>
    obtain ⟨_, _, _, rfl⟩ := (hop_sem ..).mp hop
    exact ih loc input

private theorem exact_walk {t : Tables} {start : Nat} {rest : List Nat}
    (walk : walks t start rest = true) (closed : closedPorts t (start :: rest) = true)
    (base o : CtxPkt) :
    Semantics (forwarding t) (place start base) o ↔ ∃ n ∈ start :: rest, o = place n base := by
  constructor
  · intro h
    have loc := stays_in_ports closed h (by exact List.mem_map.mpr ⟨start, by simp, rfl⟩)
    obtain ⟨n, mem, loc⟩ := List.mem_map.mp loc
    exact ⟨n, mem, packet_with_location h n loc.symm ⟨rfl, rfl⟩⟩
  · rintro ⟨_, mem, rfl⟩
    exact walk_cover walk mem base

private theorem place_zero (n : Nat) : place n (fun _ => .v0) = packet n := by
  funext f
  cases f <;> rfl

theorem initial_outputs_at (base o : CtxPkt) :
    Semantics (forwarding initialTables) (place 2 base) o ↔
      ∃ n ∈ ([2, 6, 8, 12, 16] : List Nat), o = place n base :=
  exact_walk (by decide +kernel) (by decide +kernel) base o

theorem after_s6_outputs_at (base o : CtxPkt) :
    Semantics (forwarding afterS6) (place 2 base) o ↔
      ∃ n ∈ ([2, 6, 8, 11] : List Nat), o = place n base :=
  exact_walk (by decide +kernel) (by decide +kernel) base o

theorem after_s4_s6_outputs_at (base o : CtxPkt) :
    Semantics (forwarding afterS4S6) (place 2 base) o ↔
      ∃ n ∈ ([2, 6, 8, 11, 15] : List Nat), o = place n base :=
  exact_walk (by decide +kernel) (by decide +kernel) base o

theorem initial_outputs (o : CtxPkt) :
    Semantics (forwarding initialTables) (packet 2) o ↔
      ∃ n ∈ ([2, 6, 8, 12, 16] : List Nat), o = packet n := by
  simpa only [place_zero] using initial_outputs_at (fun _ => .v0) o

theorem after_s6_outputs (o : CtxPkt) :
    Semantics (forwarding afterS6) (packet 2) o ↔
      ∃ n ∈ ([2, 6, 8, 11] : List Nat), o = packet n := by
  simpa only [place_zero] using after_s6_outputs_at (fun _ => .v0) o

theorem after_s4_s6_outputs (o : CtxPkt) :
    Semantics (forwarding afterS4S6) (packet 2) o ↔
      ∃ n ∈ ([2, 6, 8, 11, 15] : List Nat), o = packet n := by
  simpa only [place_zero] using after_s4_s6_outputs_at (fun _ => .v0) o

theorem initial_forwarding : Semantics (forwarding initialTables) (packet 2) (packet 16) :=
  (initial_outputs _).mpr ⟨16, by simp, rfl⟩

theorem breach_forwarding : Semantics (forwarding afterS4S6) (packet 2) (packet 15) :=
  (after_s4_s6_outputs _).mpr ⟨15, by simp, rfl⟩

def breach : Letter := .packet (packet 2) (packet 15)
def breachTrace : List Action := [s6Event, s4Event, breach.action]

theorem independent_breach_steps :
    Steps env ⟨independent.term, [packet 2], []⟩ breachTrace
      ⟨system afterS4S6 independentC1 c2AfterS4S6, [], [packet 15]⟩ :=
  .cons _ _ _ _ _ (independent_s6 ..)
    (.cons _ _ _ _ _ (independent_s4 ..)
      (.cons _ _ _ _ _ (forwardSystem _ _ _ [] []
        (history breach_forwarding)) (.nil _)))

theorem independent_breach : independent.Trace breachTrace :=
  ⟨[packet 2], [], _, independent_breach_steps⟩

def afterBreach : independent.Residual := independent.afterTrace independent_breach_steps

theorem independent_unsafe : ¬ Safe independent
    [[.rcfg (channel 5) (policy 5 5), .rcfg (channel 3) (policy 3 3), breach]] := by
  intro safe
  exact safe [ .rcfg (channel 5) (policy 5 5), .rcfg (channel 3) (policy 3 3), breach]
    (by simp) independent_breach


private def nameEmbedding : Tables ↪ Var :=
  ⟨name, fun _ _ equal => by simpa only [readTables_name] using congrArg readTables equal⟩

private def names : Finset Var := (Finset.univ : Finset Tables).map nameEmbedding

private theorem name_mem (t : Tables) : name t ∈ names :=
  Finset.mem_map.mpr ⟨t, Finset.mem_univ _, rfl⟩

private theorem body_support (t : Tables) : recursiveVars (body t) ⊆ names := by
  have h (xs : List DyNetKAT) (covers : ∀ x ∈ xs, recursiveVars x ⊆ names) :
      recursiveVars (choiceOf xs) ⊆ names := by
    induction xs with
    | nil => simp [choiceOf, recursiveVars]
    | cons p ps ih =>
      change recursiveVars p ∪ recursiveVars (choiceOf ps) ⊆ names
      exact Finset.union_subset (covers p List.mem_cons_self)
        (ih (fun x m => covers x (List.mem_cons_of_mem _ m)))
  apply Finset.union_subset (Finset.singleton_subset_iff.mpr (name_mem t))
  apply h
  intro p m
  simp only [updates, List.mem_flatMap, List.mem_map] at m
  obtain ⟨s, _, i, _, rfl⟩ := m
  exact Finset.singleton_subset_iff.mpr (name_mem (Function.update t s i.succ))

private theorem script_closed (xs : List MoveLabel) : recursiveVars (script xs) = ∅ := by
  induction xs with
  | nil => rfl
  | cons l xs ih =>
    have aux : recursiveVars (l.prefix (script xs)) = recursiveVars (script xs) := by
      cases l with
      | visible l => cases l <;> rfl
      | recv | send => rfl
    exact aux.trans ih

private theorem system_support (t : Tables) (xs ys : List MoveLabel) :
    recursiveVars (system t (script xs) (script ys)) ⊆ names := by
  simp only [system, network, recursiveVars, script_closed, Finset.union_empty]
  exact Finset.singleton_subset_iff.mpr (name_mem t)

private theorem synchronized_support : FiniteSupport env synchronized.term names := by
  constructor
  · exact system_support initialTables leftScript rightScript
  · intro x mem
    obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp mem
    exact ⟨body t, lookup_network t, body_support t⟩

def synchronizedCompiled : synchronized.Compiled := ⟨names, synchronized_support⟩

private def controlGraph : ProcessGraph := synchronizedCompiled.graph

private theorem graph_label (t : Tables) :
    controlGraph.label (varNode (name t)) = toGProc (body t) := by
  change (toGraph env synchronized.term names synchronized_support).label _ = _
  rw [toGraph_label_varNode synchronized_support (name_mem t), lookup_network]
  rfl

/-- The pair counts the prefixes already executed in each controller. -/
abbrev Phase := Nat × Nat

private def phases : List Phase :=
  [(0, 0), (1, 0), (0, 1), (1, 1)] ++
    ([2, 3, 4] : List Nat).flatMap (fun l => ([2, 3, 4] : List Nat).map (l, ·))

def phaseTables (s : Phase) : Tables := fun i =>
  match i.val with
  | 0 => if s.1 > 0 then 1 else 0
  | 1 => if s.2 > 0 then 1 else 0
  | 2 => if s.1 > 2 then 2 else 0
  | 3 => if s.2 > 2 then 3 else 0
  | 4 => if s.1 > 3 then 4 else 0
  | _ => if s.2 > 3 then 5 else 0

def phaseTerm (s : Phase) : DyNetKAT :=
  system (phaseTables s) (script (leftScript.drop s.1)) (script (rightScript.drop s.2))

private def systemRow (t : Tables) (c₁ c₂ : DyNetKAT) : List SymbolicMove :=
  (localMoves (fun _ => localMoves (fun _ => none) (toGProc (body t)))
    (toGProc (system t c₁ c₂))).getD []

private def rawRow (s : Phase) : List SymbolicMove :=
  systemRow (phaseTables s) (script (leftScript.drop s.1)) (script (rightScript.drop s.2))

/-- Compute one row on demand from the current definition, using the
existing exact symbolic move scanner. -/
private theorem rawRow_exact (s : Phase) :
    MovesExact controlGraph (toGProc (phaseTerm s)) (rawRow s) := by
  let known := fun i => i = varNode (name (phaseTables s))
  let resolve := fun (_ : NodeId) => localMoves (fun _ => none) (toGProc (body (phaseTables s)))
  have noRef (l : MoveLabel) (p : DyNetKAT) :
      RestrictionChecksCorrect known (toGProc (l.prefix p)) none ∧
        (localMoves resolve (toGProc (l.prefix p))).isSome := by
    cases l with
    | visible l => cases l <;> exact ⟨trivial, rfl⟩
    | recv | send => exact ⟨trivial, rfl⟩
  have scriptReady (xs : List MoveLabel) :
      RestrictionChecksCorrect known (toGProc (script xs)) none ∧
        (localMoves resolve (toGProc (script xs))).isSome := by
    cases xs with
    | nil => exact ⟨trivial, rfl⟩
    | cons l xs => exact noRef l (script xs)
  have correct : RestrictionChecksCorrect known (toGProc (phaseTerm s)) none :=
    ⟨⟨rfl, (scriptReady _).1⟩, (scriptReady _).1⟩
  have found : (localMoves resolve (toGProc (phaseTerm s))).isSome := by
    have some_of_isSome {α : Type} (o : Option α) (h : o.isSome) : ∃ x, o = some x := by
      cases o with
      | none => contradiction
      | some x => exact ⟨x, rfl⟩
    obtain ⟨_, hx⟩ := some_of_isSome _ (scriptReady (leftScript.drop s.1)).2
    obtain ⟨_, hy⟩ := some_of_isSome _ (scriptReady (rightScript.drop s.2)).2
    change (localMoves resolve (.parallel (.parallel (.ref _) _) _) none).isSome
    simp only [localMoves, Option.map, hx, hy]
    rfl
  have equal : localMoves resolve (toGProc (phaseTerm s)) = some (rawRow s) := by
    unfold rawRow systemRow
    change localMoves resolve (toGProc (phaseTerm s)) =
      some ((localMoves resolve (toGProc (phaseTerm s))).getD [])
    cases he : localMoves resolve (toGProc (phaseTerm s)) <;> simp_all
  apply localMoves_exact_with (atRef := known) (resolve := resolve) ?_ correct equal
  intro i hi row hr
  change i = varNode (name (phaseTables s)) at hi
  subst i
  apply MovesExact.ref
  rw [graph_label]
  exact localMoves_exact (by simp) hr

private def visible : MoveLabel → Bool
  | .visible _ => true
  | _ => false

private def visibleRow (s : Phase) : List SymbolicMove :=
  (rawRow s).filter fun m => visible m.1

private def blockedOrVisible (m : SymbolicMove) : Bool :=
  match m.1 with
  | .send ch p | .recv ch p => blocksChannel ch p
  | .visible _ => true

private theorem verifiedRestriction :
    phases.all (fun s => (rawRow s).all blockedOrVisible) = true := by
  decide +kernel

private theorem visibleRow_exact {s : Phase} (valid : s ∈ phases)
    {p' : GProc} {a : Action} {pt hl pt' hl' : List CtxPkt}
    (step : GStep controlGraph ⟨toGProc (phaseTerm s), pt, hl⟩ a ⟨p', pt', hl'⟩)
    (allowed : actionAllowed controllerRestriction a) :
    ∃ l, (l, p') ∈ visibleRow s ∧ MoveLabel.Realizes l pt hl a pt' hl' := by
  obtain ⟨l, mem, hr⟩ := (rawRow_exact s ..).mp step
  refine ⟨l, List.mem_filter.mpr ⟨mem, ?_⟩, hr⟩
  have cover := List.all_eq_true.mp (List.all_eq_true.mp verifiedRestriction s valid) _ mem
  cases hr with
  | packet | rcfg => rfl
  | send | recv => exact (allowed cover).elim


/-- Fig. 7's control order, including the two possible deactivation
orders and the independent progress of the two installations. -/
def phaseEvents (s : Phase) : List ((Channel × NetKAT) × Phase) :=
  (if s.1 = 0 then [((channel 0, policy 0 1), (1, s.2))] else []) ++
  (if s.2 = 0 then [((channel 1, policy 1 1), (s.1, 1))] else []) ++
  (if s = (1, 1) then [(("syn", .id), (2, 2))] else []) ++
  (if s.1 = 2 then [((channel 2, policy 2 2), (3, s.2))] else []) ++
  (if s.1 = 3 then [((channel 4, policy 4 4), (4, s.2))] else []) ++
  (if s.2 = 2 then [((channel 3, policy 3 3), (s.1, 3))] else []) ++
  (if s.2 = 3 then [((channel 5, policy 5 5), (s.1, 4))] else [])

private def permittedRow (s : Phase) (m : SymbolicMove) : Bool :=
  match m.1 with
  | .visible (.packet p) =>
      decide (p = forwarding (phaseTables s)) && sameProcess m.2 (toGProc (phaseTerm s))
  | .visible (.rcfg ch p) =>
      (phaseEvents s).any fun e =>
        decide (e.1 = (ch, p) ∧ e.2 ∈ phases) && sameProcess m.2 (toGProc (phaseTerm e.2))
  | _ => false

private theorem verifiedRows :
    phases.all (fun s => (visibleRow s).all (permittedRow s)) = true := by
  decide +kernel

private def fromH1 (s : Phase) : List Nat := if s.1 = 0 then [2, 6, 8, 12, 16] else [2]
private def fromH3 (s : Phase) : List Nat := if s.1 ≤ 2 then [1] else [1, 5, 8, 11, 12, 15]

private theorem verifiedPorts :
    phases.all (fun s =>
      closedPorts (phaseTables s) (fromH1 s) && closedPorts (phaseTables s) (fromH3 s) &&
      decide (code 2 ∈ (fromH1 s).map code ∧ code 15 ∉ (fromH1 s).map code ∧
        code 1 ∈ (fromH3 s).map code ∧ code 16 ∉ (fromH3 s).map code)) = true := by
  decide +kernel

/-- Every packet observation has the indicated routing table. Each
reconfiguration follows a Fig. 7 control edge with its literal payload. -/
inductive PhaseTrace : Phase → List Action → Prop
  | nil (s) : PhaseTrace s []
  | packet {s i o w} : Semantics (forwarding (phaseTables s)) i o →
      PhaseTrace s w → PhaseTrace s (.packet i o :: w)
  | event {s x p next w} : ((x, p), next) ∈ phaseEvents s →
      PhaseTrace next w → PhaseTrace s (.rcfg x p :: w)

private theorem graph_phase_trace {s : Phase} (valid : s ∈ phases)
    {pt hl : List CtxPkt} {w : List Action} {target : GConfig}
    (run : GSteps controlGraph ⟨toGProc (phaseTerm s), pt, hl⟩ w target)
    (allowed : ∀ a ∈ w, actionAllowed controllerRestriction a) : PhaseTrace s w := by
  induction w generalizing s pt hl with
  | nil => exact .nil _
  | cons a w ih =>
    cases run with
    | cons _ mid _ _ _ step rest =>
      rcases mid with ⟨mid, ptMid, hlMid⟩
      obtain ⟨l, member, realizes⟩ := visibleRow_exact valid step (allowed a List.mem_cons_self)
      have check := List.all_eq_true.mp (List.all_eq_true.mp verifiedRows _ valid) _ member
      have tailAllowed : ∀ b ∈ w, actionAllowed controllerRestriction b :=
        fun b hb => allowed b (List.mem_cons_of_mem _ hb)
      cases realizes with
      | packet sem =>
        simp only [permittedRow, Bool.and_eq_true] at check
        have sem' := (historySemantics_iff_packetSemantics _ _ _ [] []).mp sem
        rw [of_decide_eq_true check.1] at sem'
        rw [sameProcess_sound check.2] at rest
        exact .packet sem'.2 (ih valid rest tailAllowed)
      | rcfg =>
        simp only [permittedRow, List.any_eq_true] at check
        obtain ⟨⟨label, next⟩, event, ok⟩ := check
        simp only [Bool.and_eq_true] at ok
        obtain ⟨rfl, nextValid⟩ := of_decide_eq_true ok.1
        rw [sameProcess_sound ok.2] at rest
        exact .event event (ih nextValid rest tailAllowed)
      | recv | send => simp [permittedRow] at check

theorem synchronized_order {w : List Action} (trace : synchronized.Trace w) :
    PhaseTrace (0, 0) w := by
  change SourceTrace env (.restrict controllerRestriction (phaseTerm (0, 0))) w at trace
  obtain ⟨⟨pt, hl, target, run⟩, allowed⟩ := sourceTrace_restrict_iff.mp trace
  have hc : Corr controlGraph env (phaseTerm (0, 0)) (toGProc (phaseTerm (0, 0))) :=
    toGraph_corr_of_subset _ _ _ synchronized_support _ (system_support ..)
  obtain ⟨_, graphRun, _⟩ := steps_to_gsteps _ _ _ _ _ run _ hc
  exact graph_phase_trace (by decide) graphRun allowed

/-- The isolation result is about logical ports and allows arbitrary
transport headers and arbitrarily many preceding packet actions. -/
def CrossRoute : Action → Prop
  | .packet i o =>
    (location i = code 2 ∧ location o = code 15) ∨
    (location i = code 1 ∧ location o = code 16)
  | _ => False

private theorem phase_trace_isolation {s w} (run : PhaseTrace s w) (valid : s ∈ phases)
    {a} (mem : a ∈ w) : ¬ CrossRoute a := by
  induction run with
  | nil => simp at mem
  | @packet s i o w sem run ih =>
    rcases List.mem_cons.mp mem with rfl | later
    · have check := List.all_eq_true.mp verifiedPorts s valid
      simp only [Bool.and_eq_true] at check
      obtain ⟨in1, out1, in3, out3⟩ := of_decide_eq_true check.2
      rintro (⟨hi, ho⟩ | ⟨hi, ho⟩)
      · exact out1 (ho ▸ stays_in_ports check.1.1 sem (hi ▸ in1))
      · exact out3 (ho ▸ stays_in_ports check.1.2 sem (hi ▸ in3))
    · exact ih valid later
  | @event s x p next w event run ih =>
    rcases List.mem_cons.mp mem with rfl | later
    · exact fun h => h
    · have edgesValid : phases.all (fun s => (phaseEvents s).all (fun e => decide (e.2 ∈ phases))) = true := by
        decide +kernel
      exact ih (of_decide_eq_true (List.all_eq_true.mp
        (List.all_eq_true.mp edgesValid s valid) _ event)) later

theorem synchronized_isolation {w : List Action} (trace : synchronized.Trace w)
    {a : Action} (mem : a ∈ w) : ¬ CrossRoute a :=
  phase_trace_isolation (synchronized_order trace) (by decide) mem


def disableS1 : Channel × NetKAT := (channel 0, policy 0 1)
def disableS2 : Channel × NetKAT := (channel 1, policy 1 1)
def acknowledge : Channel × NetKAT := ("syn", .id)
def installS3 : Channel × NetKAT := (channel 2, policy 2 2)
def installS5 : Channel × NetKAT := (channel 4, policy 4 4)
def installS4 : Channel × NetKAT := (channel 3, policy 3 3)
def installS6 : Channel × NetKAT := (channel 5, policy 5 5)

def eventAction (e : Channel × NetKAT) : Action := .rcfg e.1 e.2

private def closedPhase (s : Phase) : DyNetKAT := .restrict controllerRestriction (phaseTerm s)

private theorem close_event {p q : DyNetKAT} {e : Channel × NetKAT} {pt hl : List CtxPkt}
    (h : Step env ⟨p, pt, hl⟩ (eventAction e) ⟨q, pt, hl⟩) :
    Step env ⟨.restrict controllerRestriction p, pt, hl⟩ (eventAction e)
      ⟨.restrict controllerRestriction q, pt, hl⟩ :=
  .cpol_restrict _ _ _ _ _ _ _ _ trivial h

theorem synchronized_disableS1 (pt hl : List CtxPkt) :
    Step env ⟨synchronized.term, pt, hl⟩ (eventAction disableS1) ⟨closedPhase (1, 0), pt, hl⟩ := by
  apply close_event
  exact updateLeft (phaseTables (0, 0)) 0 0 _ _ _ pt hl (.cpol_send _ _ _ _ _)

theorem synchronized_disableS2 (pt hl : List CtxPkt) :
    Step env ⟨closedPhase (1, 0), pt, hl⟩ (eventAction disableS2) ⟨closedPhase (1, 1), pt, hl⟩ := by
  apply close_event
  exact updateRight (phaseTables (1, 0)) 1 0 _ _ _ pt hl (.cpol_send _ _ _ _ _)

theorem synchronized_barrier (pt hl : List CtxPkt) :
    Step env ⟨closedPhase (1, 1), pt, hl⟩ (eventAction acknowledge) ⟨closedPhase (2, 2), pt, hl⟩ := by
  apply close_event
  exact .cpol_sync_send_recv _ _ _ _ _ _ _ _
    (.cpol_par_r _ _ _ _ _ _ _ _ (.cpol_send _ _ _ _ _)) (.cpol_recv _ _ _ _ _)

theorem synchronized_no_early_barrier :
    ¬ synchronized.Trace [eventAction acknowledge] := by
  intro h
  cases synchronized_order h with
  | event mem _ =>
    have h₁ : ¬ "syn" = channel 0 := by decide +kernel
    have h₂ : ¬ "syn" = channel 1 := by decide +kernel
    simp [eventAction, acknowledge, phaseEvents, h₁, h₂] at mem

private theorem synchronized_installS3 (pt hl : List CtxPkt) :
    Step env ⟨closedPhase (2, 2), pt, hl⟩ (eventAction installS3) ⟨closedPhase (3, 2), pt, hl⟩ := by
  apply close_event
  exact updateLeft (phaseTables (2, 2)) 2 1 _ _ _ pt hl (.cpol_send _ _ _ _ _)

private theorem synchronized_installS5 (pt hl : List CtxPkt) :
    Step env ⟨closedPhase (3, 2), pt, hl⟩ (eventAction installS5) ⟨closedPhase (4, 2), pt, hl⟩ := by
  apply close_event
  exact updateLeft (phaseTables (3, 2)) 4 3 _ _ _ pt hl (.cpol_send _ _ _ _ _)

private theorem synchronized_installS4 (pt hl : List CtxPkt) :
    Step env ⟨closedPhase (4, 2), pt, hl⟩ (eventAction installS4) ⟨closedPhase (4, 3), pt, hl⟩ := by
  apply close_event
  exact updateRight (phaseTables (4, 2)) 3 2 _ _ _ pt hl (.cpol_send _ _ _ _ _)

private theorem synchronized_installS6 (pt hl : List CtxPkt) :
    Step env ⟨closedPhase (4, 3), pt, hl⟩ (eventAction installS6) ⟨closedPhase (4, 4), pt, hl⟩ := by
  apply close_event
  exact updateRight (phaseTables (4, 3)) 5 4 _ _ _ pt hl (.cpol_send _ _ _ _ _)

theorem final_outputs (o : CtxPkt) :
    Semantics (forwarding (phaseTables (4, 4))) (packet 1) o ↔
      ∃ n ∈ ([1, 5, 8, 11, 15] : List Nat), o = packet n := by
  have h := exact_walk (t := phaseTables (4, 4)) (start := 1) (rest := [5, 8, 11, 15])
    (by decide +kernel) (by decide +kernel) (fun _ => .v0) o
  simpa only [place_zero] using h

theorem synchronized_initial_forwarding :
    Step env ⟨synchronized.term, [packet 2], []⟩ (.packet (packet 2) (packet 16))
      ⟨synchronized.term, [], [packet 16]⟩ :=
  .cpol_restrict _ _ _ _ _ _ _ _ trivial (forwardSystem _ _ _ [] [] (history initial_forwarding))

def synchronizedUpdates : List (Channel × NetKAT) :=
  [disableS1, disableS2, acknowledge, installS3, installS5, installS4, installS6]

theorem synchronized_forwarding_steps :
    Steps env ⟨synchronized.term, [packet 1], []⟩
      (synchronizedUpdates.map eventAction ++ [.packet (packet 1) (packet 15)])
      ⟨closedPhase (4, 4), [], [packet 15]⟩ :=
  .cons _ _ _ _ _ (synchronized_disableS1 ..)
    (.cons _ _ _ _ _ (synchronized_disableS2 ..)
      (.cons _ _ _ _ _ (synchronized_barrier ..)
        (.cons _ _ _ _ _ (synchronized_installS3 ..)
          (.cons _ _ _ _ _ (synchronized_installS5 ..)
            (.cons _ _ _ _ _ (synchronized_installS4 ..)
              (.cons _ _ _ _ _ (synchronized_installS6 ..)
                (.cons _ _ _ _ _ (.cpol_restrict _ _ _ _ _ _ _ _ trivial
                  (forwardSystem _ _ _ [] [] (history ((final_outputs _).mpr ⟨15, by simp, rfl⟩))))
                  (.nil _))))))))

def afterInstallation : synchronized.Residual :=
  synchronized.afterTrace synchronized_forwarding_steps

def eventStages (es : List (Channel × NetKAT)) : List ReconfigSet :=
  es.map fun e => {e}

private theorem tailStages (es : List (Channel × NetKAT)) :
    TailSegments (eventStages es) (es.map eventAction) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    exact ⟨[eventAction e], es.map eventAction, rfl, TailWord.last (by simp), ih⟩

private theorem reachFromTrace {extended : Bool} {p : Program extended env}
    (es : List (Channel × NetKAT)) (i o : Nat) (bound : Option Nat)
    (trace : p.Trace (es.map eventAction ++ [.packet (packet i) (packet o)]))
    (budget : ReachabilityBudget bound (es.map eventAction ++ [.packet (packet i) (packet o)])) :
    EndpointReachable p bound (eventStages es) (portTest i) (portTest o) := by
  refine ⟨packet i, packet i, packet o, packet o,
    (portTest_sem ..).mpr ⟨rfl, rfl⟩, ?_, (portTest_sem ..).mpr ⟨rfl, rfl⟩⟩
  exact ⟨_, ⟨es.map eventAction, [], tailStages es, by simp, rfl⟩, trace, budget⟩

def independentUpdates : List (Channel × NetKAT) := [installS6, installS4]

theorem independent_reachable :
    EndpointReachable independent none (eventStages independentUpdates) (portTest 2) (portTest 15) :=
  reachFromTrace independentUpdates 2 15 none independent_breach trivial

theorem synchronized_reachable :
    EndpointReachable synchronized none (eventStages synchronizedUpdates) (portTest 1) (portTest 15) :=
  reachFromTrace synchronizedUpdates 1 15 none ⟨_, _, _, synchronized_forwarding_steps⟩ trivial

theorem synchronized_unreachable (bound : Option Nat) (stages : List ReconfigSet) :
    ¬ EndpointReachable synchronized bound stages (portTest 2) (portTest 15) := by
  rintro ⟨σ, i, o, τ, ingress, ⟨w, ⟨pre, head, _, _, rfl⟩, trace, _⟩, egress⟩
  have hi := (portTest_sem ..).mp ingress
  have ho := (portTest_sem ..).mp egress
  exact synchronized_isolation trace (by simp) (show CrossRoute (.packet i o) from
    Or.inl ⟨hi.1 ▸ hi.2, ho.2⟩)

theorem synchronized_safe_padded (A : Alphabet) (n : Nat) :
    Safe synchronized ((padded breach n).desugar A) := by
  apply (safe_padded_iff ..).mpr
  intro u _ _ trace
  exact synchronized_isolation trace (by simp) (show CrossRoute breach.action from Or.inl ⟨rfl, rfl⟩)

theorem synchronized_eq28 (A : Alphabet) (alphabet : UsesAlphabet synchronized A) (n : Nat) :
    EquationalSafety synchronized A ((padded breach n).desugar A) :=
  ((padded breach n).equational_iff synchronized A alphabet).mpr (synchronized_safe_padded A n)

def independentClosed : Program true env :=
  ⟨.restrict Set.univ independent.term, admitted ⟨rfl, PaperSyntax.of_base independent_admitted.2.1⟩⟩

theorem independent_closed_breach : independentClosed.Trace breachTrace := by
  apply sourceTrace_restrict_iff.mpr
  exact ⟨independent_breach, by simp [breachTrace, breach, s6Event, s4Event, actionAllowed, Letter.action]⟩

theorem independent_eq28_fails (A : Alphabet) (alphabet : UsesAlphabet independentClosed A) :
    ¬ EquationalSafety independentClosed A ((padded breach 2).desugar A) := by
  intro h
  obtain ⟨w, eq, covers⟩ := alphabet breachTrace independent_closed_breach
  have same : w = [.rcfg (channel 5) (policy 5 5), .rcfg (channel 3) (policy 3 3), breach] :=
    (List.map_injective_iff.mpr Letter.action_injective) eq
  subst w
  apply (padded_equational_iff independentClosed A alphabet breach 2).mp h
    [.rcfg (channel 5) (policy 5 5), .rcfg (channel 3) (policy 3 3)] rfl
    (fun a ha => covers a (List.mem_append_left [breach] ha))
  exact independent_closed_breach


private theorem packetParallel {p q : DyNetKAT} {i o : CtxPkt} {dst : DyNetKAT}
    (step : ActionStep env (.parallel p q) (.packet i o) dst) :
    (∃ r, ActionStep env p (.packet i o) r) ∨ (∃ r, ActionStep env q (.packet i o) r) := by
  unfold ActionStep at *
  cases step with
  | cpol_par_l _ _ _ _ _ _ _ _ step => exact .inl ⟨_, step⟩
  | cpol_par_r _ _ _ _ _ _ _ _ step => exact .inr ⟨_, step⟩

private theorem notify_noPacket {s : Switch} {t : Table} {i o : CtxPkt} {q : DyNetKAT}
    (step : ActionStep env (notify s t) (.packet i o) q) : False := by
  unfold ActionStep at step
  cases step

private theorem threeSends_noPacket {s₁ s₂ s₃ : Switch} {t₁ t₂ t₃ : Table}
    {i o : CtxPkt} {q : DyNetKAT}
    (step : ActionStep env (.parallel (.parallel (notify s₁ t₁) (notify s₂ t₂)) (notify s₃ t₃))
      (.packet i o) q) : False := by
  rcases packetParallel step with ⟨_, left⟩ | ⟨_, right⟩
  · rcases packetParallel left with ⟨_, head⟩ | ⟨_, middle⟩
    · exact notify_noPacket head
    · exact notify_noPacket middle
  · exact notify_noPacket right

private theorem network_packet_policy {t : Tables} {i o : CtxPkt} {q : DyNetKAT}
    (step : ActionStep env (network t) (.packet i o) q) :
    Semantics (forwarding t) i o := by
  unfold ActionStep at step
  cases step with
  | cpol_var _ _ _ _ _ _ _ _ decl run =>
    have eq := RecEnv.lookup_unique decl (lookup_network t)
    rw [eq] at run
    change Step env ⟨.choice (.nSeq (forwarding t) (network t)) (choiceOf (updates t)), _, _⟩
      (.packet i o) ⟨q, _, _⟩ at run
    cases run with
    | cpol_choice_l _ _ _ _ _ _ _ _ step =>
      cases step with
      | cpol_seq_ok _ _ _ _ _ _ h => exact ((historySemantics_iff_packetSemantics ..).mp h).2
    | cpol_choice_r _ _ _ _ _ _ _ _ step =>
      obtain ⟨p, mem, step⟩ := (choiceOf_step_iff ..).mp step
      simp only [updates, List.mem_flatMap, List.mem_map] at mem
      obtain ⟨_, _, _, _, rfl⟩ := mem
      cases step

private theorem independent_packet_policy {t : Tables} {i o : CtxPkt} {q : DyNetKAT}
    (step : ActionStep env (system t independentC1 independentC2) (.packet i o) q) :
    Semantics (forwarding t) i o := by
  change ActionStep env (.parallel (.parallel (network t) independentC1) independentC2)
    (.packet i o) q at step
  rcases packetParallel step with ⟨_, left⟩ | ⟨_, right⟩
  · rcases packetParallel left with ⟨_, net⟩ | ⟨_, ctrl⟩
    · exact network_packet_policy net
    · exact (threeSends_noPacket ctrl).elim
  · exact (threeSends_noPacket right).elim

theorem independent_initial_isolation : ¬ independent.Trace [breach.action] := by
  intro trace
  obtain ⟨_, step, _⟩ := sourceTrace_cons_actionStep.mp trace
  have route := independent_packet_policy step
  obtain ⟨n, mem, eq⟩ := (initial_outputs _).mp route
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl <;> exact (by decide +kernel : packet 15 ≠ packet _) eq

theorem independent_initial_forwarding :
    Step env ⟨independent.term, [packet 2], []⟩ (.packet (packet 2) (packet 16))
      ⟨independent.term, [], [packet 16]⟩ :=
  forwardSystem _ _ _ [] [] (history initial_forwarding)

private def reconfigurations (row : List SymbolicMove) : List (Channel × NetKAT) :=
  row.filterMap fun m =>
    match m.1 with
    | .visible (.rcfg ch payload) => some (ch, payload)
    | _ => none


/-- Observable events for regression inspection, computed by the verified
symbolic row scanner on the indicated Fig. 7 phase. -/
def phaseReconfigurations (s : Phase) : List (Channel × NetKAT) :=
  reconfigurations (visibleRow s)

def independentInitialReconfigurations : List (Channel × NetKAT) :=
  reconfigurations (systemRow initialTables independentC1 independentC2)

def independentAfterS6Reconfigurations : List (Channel × NetKAT) :=
  reconfigurations (systemRow afterS6 independentC1 c2AfterS6)


def breachWord : Word := [.rcfg (channel 5) (policy 5 5), .rcfg (channel 3) (policy 3 3), breach]

def installationWord : Word :=
  synchronizedUpdates.map (fun e => Letter.rcfg e.1 e.2) ++ [.packet (packet 1) (packet 15)]

private theorem independent_support : FiniteSupport env independent.term names := by
  constructor
  · have contained := name_mem initialTables
    simpa [independent, system, network, independentC1, independentC2, notify, recursiveVars]
      using contained
  · intro x mem
    obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp mem
    exact ⟨body t, lookup_network t, body_support t⟩

def independentCompiled : independent.Compiled := ⟨names, independent_support⟩

def checks : RestrictionChecks := fun _ => blocked

private theorem body_checks (t : Tables) (check : RestrictionChecks) :
    AllRestrictionChecksCorrect (toGProc (body t)) check := by
  have h (xs : List DyNetKAT)
      (covers : ∀ x ∈ xs, ∀ c, AllRestrictionChecksCorrect (toGProc x) c) :
      ∀ c, AllRestrictionChecksCorrect (toGProc (choiceOf xs)) c := by
    induction xs with
    | nil => intro _; trivial
    | cons p ps ih =>
      intro c
      exact ⟨covers p List.mem_cons_self _, ih (fun x m => covers x (List.mem_cons_of_mem _ m)) _⟩
  constructor
  · trivial
  · apply h
    intro x mem c
    simp only [updates, List.mem_flatMap, List.mem_map] at mem
    obtain ⟨_, _, _, _, rfl⟩ := mem
    trivial

private theorem controller_support {extended : Bool} (p : Program extended env) (c : p.Compiled) :
    ProjectionSupport c.graph (fun _ => checks) (ProjectionLive env p.term) := by
  apply toGraph_projectionSupport c.support p.admissible.1
  intro x b _ lookup
  have eq : b = body (readTables x) := Option.some.inj lookup.symm
  rw [eq]
  exact body_checks _ _

private theorem independent_valid :
    (independentCompiled.initial checks).checked.Valid (ProjectionLive env independent.term) :=
  toGProc_projectionValid ⟨⟨trivial, ⟨⟨trivial, trivial⟩, trivial⟩⟩, ⟨⟨trivial, trivial⟩, trivial⟩⟩

private theorem synchronized_valid :
    (synchronizedCompiled.initial checks).checked.Valid (ProjectionLive env synchronized.term) :=
  toGProc_projectionValid ⟨fun _ => Iff.rfl, ⟨⟨trivial, trivial⟩, trivial⟩⟩

/-- The existing certified finite-word safety checker on Fig. 6. -/
def checkIndependent (forbidden : List Word) : Bool :=
  check independentCompiled checks (controller_support _ _) independent_valid forbidden

/-- The same checker on Fig. 7 with the Eq. (2) filter. -/
def checkSynchronized (forbidden : List Word) : Bool :=
  check synchronizedCompiled checks (controller_support _ _) synchronized_valid forbidden

theorem checkIndependent_correct (ws : List Word) :
    checkIndependent ws = true ↔ Safe independent ws :=
  check_correct independentCompiled checks (controller_support _ _) independent_valid ws

theorem checkSynchronized_correct (ws : List Word) :
    checkSynchronized ws = true ↔ Safe synchronized ws :=
  check_correct synchronizedCompiled checks (controller_support _ _) synchronized_valid ws

theorem independent_checker_breach : checkIndependent [breachWord] = false := by
  apply Bool.eq_false_iff.mpr
  intro verdict
  exact independent_unsafe ((checkIndependent_correct _).mp verdict)

theorem synchronized_checker_isolation : checkSynchronized [breachWord] = true := by
  apply (checkSynchronized_correct _).mpr
  intro w mem trace
  obtain rfl := List.mem_singleton.mp mem
  exact synchronized_isolation trace (by simp [breachWord])
    (show CrossRoute breach.action from Or.inl ⟨rfl, rfl⟩)

theorem synchronized_checker_installation : checkSynchronized [installationWord] = false := by
  apply Bool.eq_false_iff.mpr
  intro verdict
  have safe := (checkSynchronized_correct _).mp verdict
  apply safe installationWord (by simp)
  rw [installationWord, List.map_append, List.map_map]
  exact ⟨_, _, _, synchronized_forwarding_steps⟩


/-- The head/tail implementation accepts the Fig. 10 witness at its
source trace length. The unbounded source theorem is independent of this depth. -/
theorem independent_headTail_verdict :
    projectedReachability independentCompiled checks (fun _ => checks) 3
      (eventStages independentUpdates) (portTest 2) (portTest 15) = some true :=
  (projectedReachability_correct independentCompiled checks (controller_support _ _)
    independent_valid ..).mpr
    (reachFromTrace independentUpdates 2 15 (some 3) independent_breach
      (by simp [ReachabilityBudget, independentUpdates]))

theorem synchronized_headTail_verdict :
    projectedReachability synchronizedCompiled checks (fun _ => checks) 8
      (eventStages synchronizedUpdates) (portTest 1) (portTest 15) = some true :=
  (projectedReachability_correct synchronizedCompiled checks (controller_support _ _)
    synchronized_valid ..).mpr
    (reachFromTrace synchronizedUpdates 1 15 (some 8) ⟨_, _, _, synchronized_forwarding_steps⟩
      (by simp [ReachabilityBudget, synchronizedUpdates]))

theorem synchronized_projection_derives (n : Nat) :
    ∃ q, renderProjection synchronizedCompiled.graph (fun _ => checks) n
      (synchronizedCompiled.initial checks).checked = some q ∧
      DerivesNoAIP env (.project n synchronized.term) q :=
  synchronizedCompiled.renderProjection_derives checks (controller_support _ _) synchronized_valid n

end DyNetKAT.DyNetKAT.DistributedControllers
