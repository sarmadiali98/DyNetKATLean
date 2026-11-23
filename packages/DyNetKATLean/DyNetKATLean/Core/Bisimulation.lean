import DyNetKATLean.Core.Semantics

namespace DyNetKAT.DyNetKAT

open DyNetKAT.NetKAT

variable {schema : PacketSchema}

/-- A symmetric process relation that matches labeled transitions while
    preserving both packet histories. -/
def IsBisimulation (env : RecEnv schema) (R : DyNetKAT schema → DyNetKAT schema → Prop) : Prop :=
  (∀ p q, R p q → R q p) ∧
  ∀ p q, R p q →
    ∀ (pending handled : List schema.Packet) (action : Action schema)
      (p' : DyNetKAT schema) (pending' handled' : List schema.Packet),
      Step env
        (show Config schema from { proc := p, pending := pending, handled := handled })
        action
        (show Config schema from { proc := p', pending := pending', handled := handled' }) →
      ∃ q',
        Step env
          (show Config schema from { proc := q, pending := pending, handled := handled })
          action
          (show Config schema from { proc := q', pending := pending', handled := handled' }) ∧
        R p' q'

/-- Two processes are bisimilar when some bisimulation relates them. -/
def Bisimilar (env : RecEnv schema) (p q : DyNetKAT schema) : Prop :=
  ∃ R, IsBisimulation env R ∧ R p q

theorem Bisimilar.refl (env : RecEnv schema) (p : DyNetKAT schema) : Bisimilar env p p := by
  refine ⟨fun p q => p = q, ?_, rfl⟩
  constructor
  · intro p q relation
    exact relation.symm
  · intro p q relation pending handled action p' pending' handled' step
    subst q
    exact ⟨p', step, rfl⟩

theorem Bisimilar.symm (env : RecEnv schema) {p q : DyNetKAT schema} (h : Bisimilar env p q) :
    Bisimilar env q p := by
  rcases h with ⟨R, hR, hpq⟩
  exact ⟨R, hR, hR.1 p q hpq⟩

theorem Bisimilar.trans (env : RecEnv schema) {p q r : DyNetKAT schema}
    (hpq : Bisimilar env p q) (hqr : Bisimilar env q r) : Bisimilar env p r := by
  rcases hpq with ⟨R, hR, hpq⟩
  rcases hqr with ⟨S, hS, hqr⟩
  let T : DyNetKAT schema → DyNetKAT schema → Prop := fun x z =>
    (∃ y, R x y ∧ S y z) ∨ (∃ y, R z y ∧ S y x)
  refine ⟨T, ?_, Or.inl ⟨q, hpq, hqr⟩⟩
  constructor
  · intro x z h
    rcases h with ⟨y, hxy, hyz⟩ | ⟨y, hzy, hyx⟩
    · exact Or.inr ⟨y, hxy, hyz⟩
    · exact Or.inl ⟨y, hzy, hyx⟩
  · intro x z h pending handled action x' pending' handled' step
    rcases h with ⟨y, hxy, hyz⟩ | ⟨y, hzy, hyx⟩
    · rcases hR.2 x y hxy pending handled action x' pending' handled' step with
        ⟨y', step', hxy'⟩
      rcases hS.2 y z hyz pending handled action y' pending' handled' step' with
        ⟨z', step'', hyz'⟩
      exact ⟨z', step'', Or.inl ⟨y', hxy', hyz'⟩⟩
    · rcases hS.2 x y (hS.1 y x hyx) pending handled action x' pending' handled' step with
        ⟨y', step', hyx'⟩
      rcases hR.2 y z (hR.1 z y hzy) pending handled action y' pending' handled' step' with
        ⟨z', step'', hzy'⟩
      exact ⟨z', step'', Or.inr ⟨y', hR.1 y' z' hzy', hS.1 x' y' hyx'⟩⟩

theorem Bisimilar.choice_left (env : RecEnv schema) {p q r : DyNetKAT schema}
    (hpq : Bisimilar env p q) :
    Bisimilar env (.choice p r) (.choice q r) := by
  rcases hpq with ⟨R, hR, hpq⟩
  let T : DyNetKAT schema → DyNetKAT schema → Prop := fun x y =>
    (x = .choice p r ∧ y = .choice q r) ∨
    (x = .choice q r ∧ y = .choice p r) ∨
    R x y ∨ x = y
  refine ⟨T, ?_, Or.inl ⟨rfl, rfl⟩⟩
  constructor
  · intro x y h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hxy | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl (hR.1 x y hxy)))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · intro x y h pending handled action x' pending' handled' step
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hxy | ⟨rfl, rfl⟩
    · cases step with
      | cpol_choice_l _ _ _ action pending pending' handled handled' steps =>
          rcases hR.2 p q hpq pending handled action _ pending' handled' steps with
            ⟨q1, steps1, hp1q1⟩
          exact ⟨q1, Step.cpol_choice_l q r q1 action pending pending' handled handled' steps1,
            Or.inr (Or.inr (Or.inl hp1q1))⟩
      | cpol_choice_r _ _ _ action pending pending' handled handled' steps =>
          exact ⟨_, Step.cpol_choice_r q r _ action pending pending' handled handled' steps,
            Or.inr (Or.inr (Or.inr rfl))⟩
    · cases step with
      | cpol_choice_l _ _ _ action pending pending' handled handled' steps =>
          rcases hR.2 q p (hR.1 p q hpq) pending handled action _ pending' handled' steps with
            ⟨p1, steps1, hp1q1⟩
          exact ⟨p1, Step.cpol_choice_l p r p1 action pending pending' handled handled' steps1,
            Or.inr (Or.inr (Or.inl hp1q1))⟩
      | cpol_choice_r _ _ _ action pending pending' handled handled' steps =>
          exact ⟨_, Step.cpol_choice_r p r _ action pending pending' handled handled' steps,
            Or.inr (Or.inr (Or.inr rfl))⟩
    · rcases hR.2 x y hxy pending handled action x' pending' handled' step with
        ⟨y', step', hxy'⟩
      exact ⟨y', step', Or.inr (Or.inr (Or.inl hxy'))⟩
    · exact ⟨x', step, Or.inr (Or.inr (Or.inr rfl))⟩

theorem Bisimilar.choice_right (env : RecEnv schema) {p q r : DyNetKAT schema}
    (hpq : Bisimilar env p q) :
    Bisimilar env (.choice r p) (.choice r q) := by
  rcases hpq with ⟨R, hR, hpq⟩
  let T : DyNetKAT schema → DyNetKAT schema → Prop := fun x y =>
    (x = .choice r p ∧ y = .choice r q) ∨
    (x = .choice r q ∧ y = .choice r p) ∨
    R x y ∨ x = y
  refine ⟨T, ?_, Or.inl ⟨rfl, rfl⟩⟩
  constructor
  · intro x y h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hxy | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl (hR.1 x y hxy)))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · intro x y h pending handled action x' pending' handled' step
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hxy | ⟨rfl, rfl⟩
    · cases step with
      | cpol_choice_l _ _ _ action pending pending' handled handled' steps =>
          exact ⟨_, Step.cpol_choice_l r q _ action pending pending' handled handled' steps,
            Or.inr (Or.inr (Or.inr rfl))⟩
      | cpol_choice_r _ _ _ action pending pending' handled handled' steps =>
          rcases hR.2 p q hpq pending handled action _ pending' handled' steps with
            ⟨q1, steps1, hp1q1⟩
          exact ⟨q1, Step.cpol_choice_r r q q1 action pending pending' handled handled' steps1,
            Or.inr (Or.inr (Or.inl hp1q1))⟩
    · cases step with
      | cpol_choice_l _ _ _ action pending pending' handled handled' steps =>
          exact ⟨_, Step.cpol_choice_l r p _ action pending pending' handled handled' steps,
            Or.inr (Or.inr (Or.inr rfl))⟩
      | cpol_choice_r _ _ _ action pending pending' handled handled' steps =>
          rcases hR.2 q p (hR.1 p q hpq) pending handled action _ pending' handled' steps with
            ⟨p1, steps1, hp1q1⟩
          exact ⟨p1, Step.cpol_choice_r r p p1 action pending pending' handled handled' steps1,
            Or.inr (Or.inr (Or.inl hp1q1))⟩
    · rcases hR.2 x y hxy pending handled action x' pending' handled' step with
        ⟨y', step', hxy'⟩
      exact ⟨y', step', Or.inr (Or.inr (Or.inl hxy'))⟩
    · exact ⟨x', step, Or.inr (Or.inr (Or.inr rfl))⟩

theorem Bisimilar.parallel_right (env : RecEnv schema) {p q r : DyNetKAT schema}
    (hpq : Bisimilar env p q) :
    Bisimilar env (.parallel p r) (.parallel q r) := by
  rcases hpq with ⟨R, hR, hpq⟩
  let T : DyNetKAT schema → DyNetKAT schema → Prop := fun x y =>
    (∃ a b c, R a b ∧ x = .parallel a c ∧ y = .parallel b c) ∨
    (∃ a b c, R a b ∧ x = .parallel b c ∧ y = .parallel a c) ∨
    R x y ∨ x = y
  refine ⟨T, ?_, Or.inl ⟨p, q, r, hpq, rfl, rfl⟩⟩
  constructor
  · intro x y h
    rcases h with ⟨a, b, c, hab, rfl, rfl⟩ | ⟨a, b, c, hab, rfl, rfl⟩ | hab | rfl
    · exact Or.inr (Or.inl ⟨a, b, c, hab, rfl, rfl⟩)
    · exact Or.inl ⟨a, b, c, hab, rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl (hR.1 x y hab)))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · intro x y h pending handled action x' pending' handled' step
    rcases h with ⟨a, b, c, hab, rfl, rfl⟩ | ⟨a, b, c, hab, rfl, rfl⟩ | hab | rfl
    · cases step with
      | cpol_par_l a c a' action pending pending' handled handled' substep =>
          rcases hR.2 a b hab pending handled action _ pending' handled' substep with
            ⟨b', substep', hab'⟩
          exact ⟨_, Step.cpol_par_l b c b' action pending pending' handled handled' substep',
            Or.inl ⟨a', b', c, hab', rfl, rfl⟩⟩
      | cpol_par_r a c c' action pending pending' handled handled' substep =>
          exact ⟨_, Step.cpol_par_r b c _ action pending pending' handled handled' substep,
            Or.inl ⟨a, b, c', hab, rfl, rfl⟩⟩
      | cpol_sync_recv_send x r a c a' c' pending handled recv_step send_step =>
          rcases hR.2 a b hab pending handled (Action.recv x r) _ pending handled recv_step with
            ⟨b', recv_step', hab'⟩
          exact ⟨_, Step.cpol_sync_recv_send x r b c b' c' pending handled recv_step' send_step,
            Or.inl ⟨a', b', c', hab', rfl, rfl⟩⟩
      | cpol_sync_send_recv x r a c a' c' pending handled send_step recv_step =>
          rcases hR.2 a b hab pending handled (Action.send x r) _ pending handled send_step with
            ⟨b', send_step', hab'⟩
          exact ⟨_, Step.cpol_sync_send_recv x r b c b' c' pending handled send_step' recv_step,
            Or.inl ⟨a', b', c', hab', rfl, rfl⟩⟩
    · cases step with
      | cpol_par_l b c b' action pending pending' handled handled' substep =>
          rcases hR.2 b a (hR.1 a b hab) pending handled action _ pending' handled' substep with
            ⟨a', substep', hba'⟩
          have hrel : T (.parallel b' c) (.parallel a' c) :=
            Or.inl ⟨b', a', c, hba', rfl, rfl⟩
          exact ⟨.parallel a' c, Step.cpol_par_l a c a' action pending pending' handled handled' substep', hrel⟩
      | cpol_par_r b c c' action pending pending' handled handled' substep =>
          exact ⟨.parallel a c', Step.cpol_par_r a c c' action pending pending' handled handled' substep,
            Or.inr (Or.inl ⟨a, b, c', hab, rfl, rfl⟩)⟩
      | cpol_sync_recv_send x r b c b' c' pending handled recv_step send_step =>
          rcases hR.2 b a (hR.1 a b hab) pending handled (Action.recv x r) _ pending handled recv_step with
            ⟨a', recv_step', hba'⟩
          have hrel : T (.parallel b' c') (.parallel a' c') :=
            Or.inl ⟨b', a', c', hba', rfl, rfl⟩
          exact ⟨.parallel a' c', Step.cpol_sync_recv_send x r a c a' c' pending handled recv_step' send_step, hrel⟩
      | cpol_sync_send_recv x r b c b' c' pending handled send_step recv_step =>
          rcases hR.2 b a (hR.1 a b hab) pending handled (Action.send x r) _ pending handled send_step with
            ⟨a', send_step', hba'⟩
          have hrel : T (.parallel b' c') (.parallel a' c') :=
            Or.inl ⟨b', a', c', hba', rfl, rfl⟩
          exact ⟨.parallel a' c', Step.cpol_sync_send_recv x r a c a' c' pending handled send_step' recv_step, hrel⟩
    · rcases hR.2 x y hab pending handled action x' pending' handled' step with
        ⟨y', step', hxy'⟩
      exact ⟨y', step', Or.inr (Or.inr (Or.inl hxy'))⟩
    · exact ⟨x', step, Or.inr (Or.inr (Or.inr rfl))⟩

theorem Bisimilar.parallel_left (env : RecEnv schema) {p q r : DyNetKAT schema}
    (hpq : Bisimilar env p q) :
    Bisimilar env (.parallel r p) (.parallel r q) := by
  rcases hpq with ⟨R, hR, hpq⟩
  let T : DyNetKAT schema → DyNetKAT schema → Prop := fun x y =>
    (∃ a b c, R a b ∧ x = .parallel c a ∧ y = .parallel c b) ∨
    (∃ a b c, R a b ∧ x = .parallel c b ∧ y = .parallel c a) ∨
    R x y ∨ x = y
  refine ⟨T, ?_, Or.inl ⟨p, q, r, hpq, rfl, rfl⟩⟩
  constructor
  · intro x y h
    rcases h with ⟨a, b, c, hab, rfl, rfl⟩ | ⟨a, b, c, hab, rfl, rfl⟩ | hab | rfl
    · exact Or.inr (Or.inl ⟨a, b, c, hab, rfl, rfl⟩)
    · exact Or.inl ⟨a, b, c, hab, rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl (hR.1 x y hab)))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · intro x y h pending handled action x' pending' handled' step
    rcases h with ⟨a, b, c, hab, rfl, rfl⟩ | ⟨a, b, c, hab, rfl, rfl⟩ | hab | rfl
    · cases step with
      | cpol_par_l c a c' action pending pending' handled handled' substep =>
          exact ⟨_, Step.cpol_par_l c b c' action pending pending' handled handled' substep,
            Or.inl ⟨a, b, c', hab, rfl, rfl⟩⟩
      | cpol_par_r c a a' action pending pending' handled handled' substep =>
          rcases hR.2 a b hab pending handled action _ pending' handled' substep with
            ⟨b', substep', hab'⟩
          exact ⟨_, Step.cpol_par_r c b b' action pending pending' handled handled' substep',
            Or.inl ⟨a', b', c, hab', rfl, rfl⟩⟩
      | cpol_sync_recv_send x r c a c' a' pending handled recv_step send_step =>
          rcases hR.2 a b hab pending handled (Action.send x r) _ pending handled send_step with
            ⟨b', send_step', hab'⟩
          exact ⟨_, Step.cpol_sync_recv_send x r c b c' b' pending handled recv_step send_step',
            Or.inl ⟨a', b', c', hab', rfl, rfl⟩⟩
      | cpol_sync_send_recv x r c a c' a' pending handled send_step recv_step =>
          rcases hR.2 a b hab pending handled (Action.recv x r) _ pending handled recv_step with
            ⟨b', recv_step', hab'⟩
          exact ⟨_, Step.cpol_sync_send_recv x r c b c' b' pending handled send_step recv_step',
            Or.inl ⟨a', b', c', hab', rfl, rfl⟩⟩
    · cases step with
      | cpol_par_l c b c' action pending pending' handled handled' substep =>
          exact ⟨_, Step.cpol_par_l c a c' action pending pending' handled handled' substep,
            Or.inl ⟨b, a, c', hR.1 a b hab, rfl, rfl⟩⟩
      | cpol_par_r c b b' action pending pending' handled handled' substep =>
          rcases hR.2 b a (hR.1 a b hab) pending handled action _ pending' handled' substep with
            ⟨a', substep', hba'⟩
          have hrel : T (.parallel c b') (.parallel c a') :=
            Or.inl ⟨b', a', c, hba', rfl, rfl⟩
          exact ⟨.parallel c a', Step.cpol_par_r c a a' action pending pending' handled handled' substep', hrel⟩
      | cpol_sync_recv_send x r c b c' b' pending handled recv_step send_step =>
          rcases hR.2 b a (hR.1 a b hab) pending handled (Action.send x r) _ pending handled send_step with
            ⟨a', send_step', hba'⟩
          have hrel : T (.parallel c' b') (.parallel c' a') :=
            Or.inl ⟨b', a', c', hba', rfl, rfl⟩
          exact ⟨.parallel c' a', Step.cpol_sync_recv_send x r c a c' a' pending handled recv_step send_step', hrel⟩
      | cpol_sync_send_recv x r c b c' b' pending handled send_step recv_step =>
          rcases hR.2 b a (hR.1 a b hab) pending handled (Action.recv x r) _ pending handled recv_step with
            ⟨a', recv_step', hba'⟩
          have hrel : T (.parallel c' b') (.parallel c' a') :=
            Or.inl ⟨b', a', c', hba', rfl, rfl⟩
          exact ⟨.parallel c' a', Step.cpol_sync_send_recv x r c a c' a' pending handled send_step recv_step', hrel⟩
    · rcases hR.2 x y hab pending handled action x' pending' handled' step with
        ⟨y', step', hxy'⟩
      exact ⟨y', step', Or.inr (Or.inr (Or.inl hxy'))⟩
    · exact ⟨x', step, Or.inr (Or.inr (Or.inr rfl))⟩

theorem Bisimilar.leftMerge_left (env : RecEnv schema) {p q r : DyNetKAT schema}
    (hpq : Bisimilar env p q) :
    Bisimilar env (.leftMerge p r) (.leftMerge q r) := by
  rcases hpq with ⟨R, hR, hpq⟩
  let T : DyNetKAT schema → DyNetKAT schema → Prop := fun x y =>
    (x = .leftMerge p r ∧ y = .leftMerge q r) ∨
    (x = .leftMerge q r ∧ y = .leftMerge p r) ∨
    Bisimilar env x y
  refine ⟨T, ?_, Or.inl ⟨rfl, rfl⟩⟩
  constructor
  · intro x y h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hxy
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Bisimilar.symm env hxy))
  · intro x y h pending handled action x' pending' handled' step
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hxy
    · cases step with
      | cpol_left_merge _ _ p' action pending pending' handled handled' substep =>
          rcases hR.2 p q hpq pending handled action p' pending' handled' substep with
            ⟨q', substep', hp'q'⟩
          exact ⟨.parallel q' r,
            Step.cpol_left_merge q r q' action pending pending' handled handled' substep',
            Or.inr (Or.inr (Bisimilar.parallel_right env ⟨R, hR, hp'q'⟩))⟩
    · cases step with
      | cpol_left_merge _ _ q' action pending pending' handled handled' substep =>
          rcases hR.2 q p (hR.1 p q hpq) pending handled action q' pending' handled' substep with
            ⟨p', substep', hq'p'⟩
          exact ⟨.parallel p' r,
            Step.cpol_left_merge p r p' action pending pending' handled handled' substep',
            Or.inr (Or.inr (Bisimilar.parallel_right env ⟨R, hR, hq'p'⟩))⟩
    · rcases hxy with ⟨S, hS, hxy⟩
      rcases hS.2 x y hxy pending handled action x' pending' handled' step with
        ⟨y', step', hxy'⟩
      exact ⟨y', step', Or.inr (Or.inr ⟨S, hS, hxy'⟩)⟩

theorem Bisimilar.leftMerge_right (env : RecEnv schema) {p q r : DyNetKAT schema}
     (hpq : Bisimilar env p q) :
     Bisimilar env (.leftMerge r p) (.leftMerge r q) := by
  let T : DyNetKAT schema → DyNetKAT schema → Prop := fun x y =>
    (x = .leftMerge r p ∧ y = .leftMerge r q) ∨
    (x = .leftMerge r q ∧ y = .leftMerge r p) ∨
    Bisimilar env x y
  refine ⟨T, ?_, Or.inl ⟨rfl, rfl⟩⟩
  constructor
  · intro x y h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hxy
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Bisimilar.symm env hxy))
  · intro x y h pending handled action x' pending' handled' step
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hxy
    · cases step with
      | cpol_left_merge _ _ r' action pending pending' handled handled' substep =>
          exact ⟨.parallel r' q,
            Step.cpol_left_merge r q r' action pending pending' handled handled' substep,
            Or.inr (Or.inr (Bisimilar.parallel_left env hpq))⟩
    · cases step with
      | cpol_left_merge _ _ r' action pending pending' handled handled' substep =>
          exact ⟨.parallel r' p,
            Step.cpol_left_merge r p r' action pending pending' handled handled' substep,
            Or.inr (Or.inr (Bisimilar.parallel_left env (Bisimilar.symm env hpq)))⟩
    · rcases hxy with ⟨S, hS, hxy⟩
      rcases hS.2 x y hxy pending handled action x' pending' handled' step with
        ⟨y', step', hxy'⟩
      exact ⟨y', step', Or.inr (Or.inr ⟨S, hS, hxy'⟩)⟩

theorem Bisimilar.commMerge_right (env : RecEnv schema) {p q r : DyNetKAT schema}
    (hpq : Bisimilar env p q) :
    Bisimilar env (.commMerge p r) (.commMerge q r) := by
  rcases hpq with ⟨R, hR, hpq⟩
  let T : DyNetKAT schema → DyNetKAT schema → Prop := fun x y =>
    (x = .commMerge p r ∧ y = .commMerge q r) ∨
    (x = .commMerge q r ∧ y = .commMerge p r) ∨
    Bisimilar env x y
  refine ⟨T, ?_, Or.inl ⟨rfl, rfl⟩⟩
  constructor
  · intro x y h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hxy
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Bisimilar.symm env hxy))
  · intro x y h pending handled action x' pending' handled' step
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hxy
    · cases step with
        | cpol_comm_merge_recv_send chan pol q0 s q1 s1 pending handled recv_step send_step =>
            rcases hR.2 p q hpq pending handled (Action.recv chan pol) q1 pending handled recv_step with
              ⟨q', recv_step', hp'q'⟩
            exact ⟨.parallel q' s1,
              Step.cpol_comm_merge_recv_send chan pol q r q' s1 pending handled recv_step' send_step,
              Or.inr (Or.inr (Bisimilar.parallel_right env ⟨R, hR, hp'q'⟩))⟩
        | cpol_comm_merge_send_recv chan pol q0 s q1 s1 pending handled send_step recv_step =>
            rcases hR.2 p q hpq pending handled (Action.send chan pol) q1 pending handled send_step with
              ⟨q', send_step', hp'q'⟩
            exact ⟨.parallel q' s1,
              Step.cpol_comm_merge_send_recv chan pol q r q' s1 pending handled send_step' recv_step,
              Or.inr (Or.inr (Bisimilar.parallel_right env ⟨R, hR, hp'q'⟩))⟩
    · cases step with
      | cpol_comm_merge_recv_send chan pol _ _ q1 s1 pending handled recv_step send_step =>
          rcases hR.2 q p (hR.1 p q hpq) pending handled (Action.recv chan pol) q1 pending handled recv_step with
            ⟨p', recv_step', hq'p'⟩
          exact ⟨.parallel p' s1,
            Step.cpol_comm_merge_recv_send chan pol p r p' s1 pending handled recv_step' send_step,
            Or.inr (Or.inr (Bisimilar.parallel_right env ⟨R, hR, hq'p'⟩))⟩
      | cpol_comm_merge_send_recv chan pol _ _ q1 s1 pending handled send_step recv_step =>
          rcases hR.2 q p (hR.1 p q hpq) pending handled (Action.send chan pol) q1 pending handled send_step with
            ⟨p', send_step', hq'p'⟩
          exact ⟨.parallel p' s1,
            Step.cpol_comm_merge_send_recv chan pol p r p' s1 pending handled send_step' recv_step,
            Or.inr (Or.inr (Bisimilar.parallel_right env ⟨R, hR, hq'p'⟩))⟩
    · rcases hxy with ⟨S, hS, hxy⟩
      rcases hS.2 x y hxy pending handled action x' pending' handled' step with
        ⟨y', step', hxy'⟩
      exact ⟨y', step', Or.inr (Or.inr ⟨S, hS, hxy'⟩)⟩

theorem Bisimilar.commMerge_left (env : RecEnv schema) {p q r : DyNetKAT schema}
    (hpq : Bisimilar env p q) :
    Bisimilar env (.commMerge r p) (.commMerge r q) := by
  rcases hpq with ⟨R, hR, hpq⟩
  let T : DyNetKAT schema → DyNetKAT schema → Prop := fun x y =>
    (x = .commMerge r p ∧ y = .commMerge r q) ∨
    (x = .commMerge r q ∧ y = .commMerge r p) ∨
    Bisimilar env x y
  refine ⟨T, ?_, Or.inl ⟨rfl, rfl⟩⟩
  constructor
  · intro x y h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hxy
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Bisimilar.symm env hxy))
  · intro x y h pending handled action x' pending' handled' step
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hxy
    · cases step with
      | cpol_comm_merge_recv_send chan pol r0 p0 r' p' pending handled recv_step send_step =>
          rcases hR.2 p q hpq pending handled (Action.send chan pol) p' pending handled send_step with
            ⟨q', send_step', hp'q'⟩
          exact ⟨.parallel r' q',
            Step.cpol_comm_merge_recv_send chan pol r q r' q' pending handled recv_step send_step',
            Or.inr (Or.inr (Bisimilar.parallel_left env ⟨R, hR, hp'q'⟩))⟩
      | cpol_comm_merge_send_recv chan pol r0 p0 r' p' pending handled send_step recv_step =>
          rcases hR.2 p q hpq pending handled (Action.recv chan pol) p' pending handled recv_step with
            ⟨q', recv_step', hp'q'⟩
          exact ⟨.parallel r' q',
            Step.cpol_comm_merge_send_recv chan pol r q r' q' pending handled send_step recv_step',
            Or.inr (Or.inr (Bisimilar.parallel_left env ⟨R, hR, hp'q'⟩))⟩
    · cases step with
      | cpol_comm_merge_recv_send chan pol r0 q0 r' q' pending handled recv_step send_step =>
          rcases hR.2 q p (hR.1 p q hpq) pending handled (Action.send chan pol) q' pending handled send_step with
            ⟨p', send_step', hq'p'⟩
          exact ⟨.parallel r' p',
            Step.cpol_comm_merge_recv_send chan pol r p r' p' pending handled recv_step send_step',
            Or.inr (Or.inr (Bisimilar.parallel_left env ⟨R, hR, hq'p'⟩))⟩
      | cpol_comm_merge_send_recv chan pol r0 q0 r' q' pending handled send_step recv_step =>
          rcases hR.2 q p (hR.1 p q hpq) pending handled (Action.recv chan pol) q' pending handled recv_step with
            ⟨p', recv_step', hq'p'⟩
          exact ⟨.parallel r' p',
            Step.cpol_comm_merge_send_recv chan pol r p r' p' pending handled send_step recv_step',
            Or.inr (Or.inr (Bisimilar.parallel_left env ⟨R, hR, hq'p'⟩))⟩
    · rcases hxy with ⟨S, hS, hxy⟩
      rcases hS.2 x y hxy pending handled action x' pending' handled' step with
        ⟨y', step', hxy'⟩
      exact ⟨y', step', Or.inr (Or.inr ⟨S, hS, hxy'⟩)⟩

theorem Bisimilar.nSeq_left (env : RecEnv schema) {n : NetKAT schema} {p q : DyNetKAT schema}
    (hpq : Bisimilar env p q) :
    Bisimilar env (.nSeq n p) (.nSeq n q) := by
  rcases hpq with ⟨R, hR, hpq⟩
  let T : DyNetKAT schema → DyNetKAT schema → Prop := fun x y =>
    (x = .nSeq n p ∧ y = .nSeq n q) ∨
    (x = .nSeq n q ∧ y = .nSeq n p) ∨
    R x y ∨ x = y
  refine ⟨T, ?_, Or.inl ⟨rfl, rfl⟩⟩
  constructor
  · intro x y h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hxy | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl (hR.1 x y hxy)))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · intro x y h pending handled action x' pending' handled' step
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hxy | ⟨rfl, rfl⟩
    · cases step with
      | cpol_seq_ok _ _ sigma sigma' _ _ evaluates =>
          exact ⟨q, Step.cpol_seq_ok n q sigma sigma' _ _ evaluates,
            Or.inr (Or.inr (Or.inl hpq))⟩
    · cases step with
      | cpol_seq_ok _ _ sigma sigma' _ _ evaluates =>
          exact ⟨p, Step.cpol_seq_ok n p sigma sigma' _ _ evaluates,
            Or.inr (Or.inr (Or.inl (hR.1 p q hpq)))⟩
    · rcases hR.2 x y hxy pending handled action x' pending' handled' step with
        ⟨y', step', hxy'⟩
      exact ⟨y', step', Or.inr (Or.inr (Or.inl hxy'))⟩
    · exact ⟨x', step, Or.inr (Or.inr (Or.inr rfl))⟩

theorem Bisimilar.recv_left (env : RecEnv schema) {x : Channel} {n : NetKAT schema}
    {p q : DyNetKAT schema} (hpq : Bisimilar env p q) :
    Bisimilar env (.recv x n p) (.recv x n q) := by
  rcases hpq with ⟨R, hR, hpq⟩
  let T : DyNetKAT schema → DyNetKAT schema → Prop := fun a b =>
    (a = .recv x n p ∧ b = .recv x n q) ∨
    (a = .recv x n q ∧ b = .recv x n p) ∨
    R a b ∨ a = b
  refine ⟨T, ?_, Or.inl ⟨rfl, rfl⟩⟩
  constructor
  · intro a b h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hab | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl (hR.1 a b hab)))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · intro a b h pending handled action a' pending' handled' step
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hab | ⟨rfl, rfl⟩
    · cases step with
      | cpol_recv _ _ _ pending handled =>
          exact ⟨q, Step.cpol_recv x n q pending handled,
            Or.inr (Or.inr (Or.inl hpq))⟩
    · cases step with
      | cpol_recv _ _ _ pending handled =>
          exact ⟨p, Step.cpol_recv x n p pending handled,
            Or.inr (Or.inr (Or.inl (hR.1 p q hpq)))⟩
    · rcases hR.2 a b hab pending handled action a' pending' handled' step with
        ⟨b', step', hab'⟩
      exact ⟨b', step', Or.inr (Or.inr (Or.inl hab'))⟩
    · exact ⟨a', step, Or.inr (Or.inr (Or.inr rfl))⟩

theorem Bisimilar.send_left (env : RecEnv schema) {x : Channel} {n : NetKAT schema}
    {p q : DyNetKAT schema} (hpq : Bisimilar env p q) :
    Bisimilar env (.send x n p) (.send x n q) := by
  rcases hpq with ⟨R, hR, hpq⟩
  let T : DyNetKAT schema → DyNetKAT schema → Prop := fun a b =>
    (a = .send x n p ∧ b = .send x n q) ∨
    (a = .send x n q ∧ b = .send x n p) ∨
    R a b ∨ a = b
  refine ⟨T, ?_, Or.inl ⟨rfl, rfl⟩⟩
  constructor
  · intro a b h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hab | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl (hR.1 a b hab)))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · intro a b h pending handled action a' pending' handled' step
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hab | ⟨rfl, rfl⟩
    · cases step with
      | cpol_send _ _ _ pending handled =>
          exact ⟨q, Step.cpol_send x n q pending handled,
            Or.inr (Or.inr (Or.inl hpq))⟩
    · cases step with
      | cpol_send _ _ _ pending handled =>
          exact ⟨p, Step.cpol_send x n p pending handled,
            Or.inr (Or.inr (Or.inl (hR.1 p q hpq)))⟩
    · rcases hR.2 a b hab pending handled action a' pending' handled' step with
        ⟨b', step', hab'⟩
      exact ⟨b', step', Or.inr (Or.inr (Or.inl hab'))⟩
    · exact ⟨a', step, Or.inr (Or.inr (Or.inr rfl))⟩

theorem Bisimilar.rcfgPrefix_left (env : RecEnv schema) {x : Channel} {n : NetKAT schema}
    {p q : DyNetKAT schema} (hpq : Bisimilar env p q) :
    Bisimilar env (.rcfgPrefix x n p) (.rcfgPrefix x n q) := by
  rcases hpq with ⟨R, hR, hpq⟩
  let T : DyNetKAT schema → DyNetKAT schema → Prop := fun a b =>
    (a = .rcfgPrefix x n p ∧ b = .rcfgPrefix x n q) ∨
    (a = .rcfgPrefix x n q ∧ b = .rcfgPrefix x n p) ∨
    R a b ∨ a = b
  refine ⟨T, ?_, Or.inl ⟨rfl, rfl⟩⟩
  constructor
  · intro a b h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hab | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl (hR.1 a b hab)))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · intro a b h pending handled action a' pending' handled' step
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hab | ⟨rfl, rfl⟩
    · cases step with
      | cpol_rcfg _ _ _ pending handled =>
          exact ⟨q, Step.cpol_rcfg x n q pending handled,
            Or.inr (Or.inr (Or.inl hpq))⟩
    · cases step with
      | cpol_rcfg _ _ _ pending handled =>
          exact ⟨p, Step.cpol_rcfg x n p pending handled,
            Or.inr (Or.inr (Or.inl (hR.1 p q hpq)))⟩
    · rcases hR.2 a b hab pending handled action a' pending' handled' step with
        ⟨b', step', hab'⟩
      exact ⟨b', step', Or.inr (Or.inr (Or.inl hab'))⟩
    · exact ⟨a', step, Or.inr (Or.inr (Or.inr rfl))⟩

theorem Bisimilar.restrict (env : RecEnv schema) {actions : Set (CommunicationAction schema)}
    {p q : DyNetKAT schema} (hpq : Bisimilar env p q) :
    Bisimilar env (.restrict actions p) (.restrict actions q) := by
  rcases hpq with ⟨R, hR, hpq⟩
  let T : DyNetKAT schema → DyNetKAT schema → Prop := fun a b =>
    (∃ c d, R c d ∧ a = .restrict actions c ∧ b = .restrict actions d) ∨
    (∃ c d, R c d ∧ a = .restrict actions d ∧ b = .restrict actions c) ∨
    R a b ∨ a = b
  refine ⟨T, ?_, Or.inl ⟨p, q, hpq, rfl, rfl⟩⟩
  constructor
  · intro a b h
    rcases h with ⟨c, d, hcd, hac, hbd⟩ | ⟨c, d, hcd, hac, hbd⟩ | hab | hab
    · exact Or.inr (Or.inl ⟨c, d, hcd, hbd, hac⟩)
    · exact Or.inl ⟨c, d, hcd, hbd, hac⟩
    · exact Or.inr (Or.inr (Or.inl (hR.1 a b hab)))
    · exact Or.inr (Or.inr (Or.inr hab.symm))
  · intro a b h pending handled action a' pending' handled' step
    rcases h with ⟨c, d, hcd, hac, hbd⟩ | ⟨c, d, hcd, hac, hbd⟩ | hab | hab
    · have step_c : Step env
          (show (Config schema) from { proc := .restrict actions c, pending := pending, handled := handled })
          action
          (show (Config schema) from { proc := a', pending := pending', handled := handled' }) := by
          simpa [hac] using step
      cases step_c with
      | cpol_restrict _ c c' action pending pending' handled handled' allowed step' =>
          rcases hR.2 c d hcd pending handled action _ pending' handled' step' with
            ⟨q', step'', hp'q'⟩
          subst b
          exact ⟨.restrict actions q', Step.cpol_restrict actions d q' action pending pending'
            handled handled' allowed step'', Or.inl ⟨c', q', hp'q', rfl, rfl⟩⟩
    · have step_d : Step env
          (show (Config schema) from { proc := .restrict actions d, pending := pending, handled := handled })
          action
          (show (Config schema) from { proc := a', pending := pending', handled := handled' }) := by
          simpa [hac] using step
      cases step_d with
      | cpol_restrict _ d d' action pending pending' handled handled' allowed step' =>
          rcases hR.2 d c (hR.1 c d hcd) pending handled action _ pending' handled' step' with
            ⟨p', step'', hq'p'⟩
          subst b
          exact ⟨.restrict actions p', Step.cpol_restrict actions c p' action pending pending'
            handled handled' allowed step'', Or.inl ⟨d', p', hq'p', rfl, rfl⟩⟩
    · rcases hR.2 a b hab pending handled action a' pending' handled' step with
        ⟨b', step', hab'⟩
      exact ⟨b', step', Or.inr (Or.inr (Or.inl hab'))⟩
    · have step_b : Step env
          (show (Config schema) from { proc := b, pending := pending, handled := handled })
          action
          (show (Config schema) from { proc := a', pending := pending', handled := handled' }) := by
          simpa [hab] using step
      exact ⟨a', step_b, Or.inr (Or.inr (Or.inr rfl))⟩

theorem Bisimilar.project (env : RecEnv schema) {n : Nat} {p q : DyNetKAT schema}
    (hpq : Bisimilar env p q) :
    Bisimilar env (.project n p) (.project n q) := by
  cases n with
  | zero =>
      let T : DyNetKAT schema → DyNetKAT schema → Prop := fun a b =>
        (a = .project 0 p ∧ b = .project 0 q) ∨
        (a = .project 0 q ∧ b = .project 0 p) ∨
        a = b
      refine ⟨T, ?_, Or.inl ⟨rfl, rfl⟩⟩
      constructor
      · intro a b h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr (Or.inr rfl)
      · intro a b h pending handled action a' pending' handled' step
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
        · cases step
        · cases step
        · exact ⟨a', step, Or.inr (Or.inr rfl)⟩
  | succ n =>
    rcases hpq with ⟨R, hR, hpq⟩
    let T : DyNetKAT schema → DyNetKAT schema → Prop := fun a b =>
      (∃ k c d, k ≤ n + 1 ∧ R c d ∧ a = .project k c ∧ b = .project k d) ∨
      (∃ k c d, k ≤ n + 1 ∧ R c d ∧ a = .project k d ∧ b = .project k c) ∨
      R a b ∨ a = b
    refine ⟨T, ?_, Or.inl ⟨n + 1, p, q, le_rfl, hpq, rfl, rfl⟩⟩
    constructor
    · intro a b h
      rcases h with ⟨k, c, d, hk, hcd, hac, hbd⟩ |
          ⟨k, c, d, hk, hcd, hac, hbd⟩ | hab | hab
      · exact Or.inr (Or.inl ⟨k, c, d, hk, hcd, hbd, hac⟩)
      · exact Or.inl ⟨k, c, d, hk, hcd, hbd, hac⟩
      · exact Or.inr (Or.inr (Or.inl (hR.1 a b hab)))
      · exact Or.inr (Or.inr (Or.inr hab.symm))
    · intro a b h pending handled action a' pending' handled' step
      rcases h with ⟨k, c, d, hk, hcd, hac, hbd⟩ |
          ⟨k, c, d, hk, hcd, hac, hbd⟩ | hab | hab
      · have step_c : Step env
            (show (Config schema) from { proc := .project k c, pending := pending, handled := handled })
            action
            (show (Config schema) from { proc := a', pending := pending', handled := handled' }) := by
            simpa [hac] using step
        cases step_c with
        | cpol_project m c c' action pending pending' handled handled' step' =>
            rcases hR.2 c d hcd pending handled action _ pending' handled' step' with
              ⟨d', step'', hcd'⟩
            have hm : m ≤ n + 1 := Nat.le_trans (Nat.le_succ m) hk
            subst b
            exact ⟨.project m d', Step.cpol_project m d d' action pending pending'
              handled handled' step'', Or.inl ⟨m, c', d', hm, hcd', rfl, rfl⟩⟩
      · have step_d : Step env
            (show (Config schema) from { proc := .project k d, pending := pending, handled := handled })
            action
            (show (Config schema) from { proc := a', pending := pending', handled := handled' }) := by
            simpa [hac] using step
        cases step_d with
        | cpol_project m d d' action pending pending' handled handled' step' =>
            rcases hR.2 d c (hR.1 c d hcd) pending handled action _ pending' handled' step' with
              ⟨c', step'', hd'c'⟩
            have hm : m ≤ n + 1 := Nat.le_trans (Nat.le_succ m) hk
            subst b
            exact ⟨.project m c', Step.cpol_project m c c' action pending pending'
              handled handled' step'', Or.inl ⟨m, d', c', hm, hd'c', rfl, rfl⟩⟩
      · rcases hR.2 a b hab pending handled action a' pending' handled' step with
          ⟨b', step', hab'⟩
        exact ⟨b', step', Or.inr (Or.inr (Or.inl hab'))⟩
      · have step_b : Step env
            (show (Config schema) from { proc := b, pending := pending, handled := handled })
            action
            (show (Config schema) from { proc := a', pending := pending', handled := handled' }) := by
            simpa [hab] using step
        exact ⟨a', step_b, Or.inr (Or.inr (Or.inr rfl))⟩

/-- ArXiv v4 Lemma 3 for the process operands of Eq. (6).
    Prefix policies and channels, restriction sets, and projection depths stay fixed.
    Deadlock and each declared reference are nullary, covered by `Bisimilar.refl`. -/
theorem paperLemma3 (env : RecEnv schema) {p p' q q' : DyNetKAT schema}
    (hp : Bisimilar env p p') (hq : Bisimilar env q q')
    (n : NetKAT schema) (x : Channel) (actions : Set (CommunicationAction schema))
    (depth : Nat) :
    Bisimilar env (.nSeq n p) (.nSeq n p') ∧
    Bisimilar env (.recv x n p) (.recv x n p') ∧
    Bisimilar env (.send x n p) (.send x n p') ∧
    Bisimilar env (.rcfgPrefix x n p) (.rcfgPrefix x n p') ∧
    Bisimilar env (.restrict actions p) (.restrict actions p') ∧
    Bisimilar env (.project depth p) (.project depth p') ∧
    Bisimilar env (.choice p q) (.choice p' q') ∧
    Bisimilar env (.parallel p q) (.parallel p' q') ∧
    Bisimilar env (.leftMerge p q) (.leftMerge p' q') ∧
    Bisimilar env (.commMerge p q) (.commMerge p' q') :=
  ⟨Bisimilar.nSeq_left env hp,
   Bisimilar.recv_left env hp,
   Bisimilar.send_left env hp,
   Bisimilar.rcfgPrefix_left env hp,
   Bisimilar.restrict env hp,
   Bisimilar.project env hp,
   Bisimilar.trans env (Bisimilar.choice_left env hp) (Bisimilar.choice_right env hq),
   Bisimilar.trans env (Bisimilar.parallel_right env hp) (Bisimilar.parallel_left env hq),
   Bisimilar.trans env (Bisimilar.leftMerge_left env hp) (Bisimilar.leftMerge_right env hq),
   Bisimilar.trans env (Bisimilar.commMerge_right env hp) (Bisimilar.commMerge_left env hq)⟩

end DyNetKAT.DyNetKAT
