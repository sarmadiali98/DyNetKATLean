 ------------------------------------------------------------------------
 -- Core `tail` extraction for the DyNetKAT safety pipeline (S5A)
 --
 -- Per the DyNetKAT paper (arXiv:2102.10035v4, §V "Implementation",
 -- PDF p. 16, Eqs. (29)–(33)):
 --
 --   tail(⊥, R)            = ⊥                                     (29)
 --   tail(N;D, R)          = tail(D, R)                            (30)
 --   tail(D ⊕ Q, R)        = tail(D, R) ⊕ tail(Q, R)               (31)
 --   tail(rcfg_{X,N};D, R) = D ⊕ tail(D, R)  if rcfg_{X,N} ∈ R     (32)
 --   tail(rcfg_{X,N};D, R) = ⊥               if rcfg_{X,N} ∉ R     (33)
 --
 -- Paper intuition (§V, PDF p. 16): "the operator tail(D, R) returns a
 -- DyNetKAT policy which is the sum of DyNetKAT policies inside D that
 -- appear after the reconfiguration events in R", where "R is a set of
 -- terms of shape rcfgX,N".
 --
 -- Notation note on Eq. (32): the paper prints the side condition as
 -- `rcfgX,Z ∈ R`.  `Z` is the paper's (and the original tool's)
 -- metavariable for the NetKAT policy of a reconfiguration event; the
 -- audited Maude implementation of the original DyNetiKAT tool
 -- (dnk.maude:145-149, recorded in docs/DYNETIKAT_REFERENCE_AUDIT.md
 -- §6.4/§11.3) reads
 --
 --   tail(rcfg(X,Z) ; D, RS) = D o+ tail(D, RS)  if rcfg(X,Z) in RS
 --   tail(rcfg(X,Z) ; D, RS) = bot               if rcfg(X,Z) not in RS
 --
 -- i.e. the side condition of Eq. (32) speaks about the *same*
 -- reconfiguration event `rcfg_{X,N}` that heads the sequence.  This
 -- module therefore reads Eq. (32) with the side condition `(x, N) ∈ R`.
 -- Paper and tool agree on all five equations; the tool additionally
 -- assumes the input is a restricted, projected normal form (Def. 6).
 --
 -- The paper states (§V): "we assume the input D to the operators head
 -- and tail do not contain terms of shape x?q and x!q. This can be
 -- ensured by always applying the restriction operator δ on D."  The
 -- tool applies `head(tail(δ_H(π_n(program)), R))` and feeds the
 -- resulting NetKAT policy into the reachability check of Eq. (35):
 -- `in · head(tail(Init, R)) · out ≢ 0` (R = {rcfg_{secConReq,1}} for
 -- the stateful firewall).  `tail`'s output is a DyNetKAT *process*;
 -- the NetKAT policy consumed by the verdict is `head` of that process.
 --
 -- This module implements `tail` on the fragment spanned by the five
 -- equations above, using the actual constructors of
 -- `DyNetKAT/DyNetKAT/AST.lean`: `deadlock`, `nSeq`, `choice`,
 -- `rcfgPrefix`.  Every other constructor (`recv`, `send`, `parallel`,
 -- `leftMerge`, `commMerge`, `restrict`, `project`, `var`) is OUTSIDE
 -- the supported fragment and yields explicit failure (`none`), never a
 -- silently-extracted process:
 --
 --   - `recv`/`send` are communication prefixes, NOT deadlock (⊥): the
 --     paper excludes them from `tail`'s domain via restriction δ.
 --   - `var` is not resolved: recursive variables are unfolded only by
 --     a separate projection/unfolding stage (H6A; not part of S5A).
 --   - `parallel`/`leftMerge`/`commMerge` are not assumed normalized.
 --   - Eq. (33) is faithful to the paper: for `rcfg_{x,N};D` with
 --     `(x,N) ∉ R` the result is `⊥` *without inspecting D* (the
 --     paper's equation puts no condition on the continuation).
 --     Consequently the exact success domain of `tail R` is the
 --     R-dependent `TailDomain R`, which coincides with the
 --     R-independent fragment `TailSupported` precisely on the paper's
 --     intended inputs (restricted normal forms; see
 --     `tailDomain_all_supported`).  `TailSupported` is strictly
 --     stronger than S4A's `HeadSupported`, because Eq. (32) recurses
 --     into the reconfiguration continuation whereas the corresponding
 --     `head` equation discards it.
 --
 -- Scope boundary: this module characterizes the paper's `tail`
 -- equations on the supported syntactic fragment, the step-behaviour of
 -- the extracted process relative to the post-reconfiguration suffixes
 -- of the input, and the packet-level meaning of the pipeline quantity
 -- `head (tail R D)`.  It does NOT implement normalization, restriction
 -- δ, projection π_n, recursive-variable resolution, safety-property
 -- compilation, or verdicts, and it does NOT establish correctness of
 -- the complete DyNetiKAT safety pipeline against arbitrary `Step`
 -- traces.
 ------------------------------------------------------------------------

 import DyNetKATLean.Core.AST
 import NetKATLean.Core.Semantics
 import DyNetKATLean.Core.SafetyHead
 import DyNetKATLean.Core.RestrictionProjection

 set_option linter.dupNamespace false

 namespace DyNetKAT.DyNetKAT

variable {schema : PacketSchema}

 open DyNetKAT.NetKAT

 ------------------------------------------------------------------------
 -- §0 The reconfiguration-event set `R`
 ------------------------------------------------------------------------

 /-- The paper's reconfiguration-event set `R` (§V: "a set of terms of
     shape `rcfgX,N`"), encoded as a finite set of channel/policy pairs:
     `(x, N) ∈ R` means `rcfg_{x,N} ∈ R`.

     `Finset` makes the membership test of Eqs. (32)–(33) decidable and
     the whole extraction executable.  Decidable equality on the pair
     comes from `String` (channels) and the `DecidableEq NetKAT`
     instance registered in `RestrictionProjection.lean`. -/
 abbrev ReconfigSet (schema : PacketSchema := ctxSchema) := Finset (Channel × NetKAT schema)

 ------------------------------------------------------------------------
 -- §1 Core `tail` operator (paper Eqs. (29)–(33))
 ------------------------------------------------------------------------

 /-- Core `tail` operator (paper §V, Eqs. (29)–(33)).

     Extracts the DyNetKAT process that is "the sum of DyNetKAT policies
     inside `D` that appear after the reconfiguration events in `R`".

     Supported fragment (paper equations, using the actual constructors):
     - `tail R deadlock           = some deadlock`                      (29)
     - `tail R (nSeq N D)         = tail R D`                           (30)
     - `tail R (choice D Q)       = some (tail R D ⊕ tail R Q)`         (31)
     - `tail R (rcfgPrefix x N D) = some (D ⊕ tail R D)` if `(x,N) ∈ R` (32)
     - `tail R (rcfgPrefix x N D) = some deadlock`         if `(x,N) ∉ R` (33)

     Unsupported constructors return `none` (explicit failure):
     `recv`, `send` (excluded by the paper's restriction precondition -
     they are NOT deadlock), `parallel`, `leftMerge`, `commMerge`,
     `restrict`, `project`, `var` (variables are not resolved here).

     Failure propagates: if `tail R D` fails inside Eq. (31) or the
     `(x,N) ∈ R` instance of Eq. (32), the whole extraction fails, so an
     unsupported subterm is never silently treated as `⊥`.  Eq. (33) is
     unconditional on `D`, exactly as the paper states it.  Structurally
     recursive and executable. -/
 def tail (R : ReconfigSet schema) : DyNetKAT schema → Option (DyNetKAT schema)
   | .deadlock => some .deadlock
   | .nSeq _ D => tail R D
   | .choice D Q =>
       (tail R D).bind (fun D' => (tail R Q).map (fun Q' => .choice D' Q'))
   | .rcfgPrefix x N D =>
       if (x, N) ∈ R then (tail R D).map (fun D' => .choice D D')
       else some .deadlock
   | .recv _ _ _ => none
   | .send _ _ _ => none
   | .parallel _ _ => none
   | .leftMerge _ _ => none
   | .commMerge _ _ => none
   | .restrict _ _ => none
   | .project _ _ => none
   | .var _ => none

 ------------------------------------------------------------------------
 -- §2 Defining equations (paper Eqs. (29)–(33))
 ------------------------------------------------------------------------

 /-- Eq. (29): `tail(⊥, R) = ⊥`.  Both ⊥'s are the DyNetKAT process
     `.deadlock`; `tail` returns a process, not a NetKAT policy. -/
 theorem tail_deadlock (R : ReconfigSet schema) : tail R .deadlock = some .deadlock := rfl

 /-- Eq. (30): `tail(N;D, R) = tail(D, R)`.  A NetKAT-policy prefix is
     skipped: `tail` looks past packet-processing steps. -/
 theorem tail_nSeq (R : ReconfigSet schema) (N : NetKAT schema) (D : DyNetKAT schema) :
     tail R (.nSeq N D) = tail R D := rfl

 /-- Eq. (31): `tail(D ⊕ Q, R) = tail(D, R) ⊕ tail(Q, R)`, as a bind/map
     over the optional sub-results.  If either side fails, the whole
     extraction fails. -/
 theorem tail_choice (R : ReconfigSet schema) (D Q : DyNetKAT schema) :
     tail R (.choice D Q) =
       (tail R D).bind (fun D' => (tail R Q).map (fun Q' => .choice D' Q')) := rfl

 /-- Eqs. (32)–(33): the reconfiguration-prefix cases, as an `if` on the
     membership of the event `rcfg_{x,N}` in `R`. -/
 theorem tail_rcfgPrefix (R : ReconfigSet schema) (x : Channel) (N : NetKAT schema) (D : DyNetKAT schema) :
     tail R (.rcfgPrefix x N D) =
       if (x, N) ∈ R then (tail R D).map (fun D' => .choice D D')
       else some .deadlock := rfl

 /-- Unsupported constructors fail explicitly. -/
 theorem tail_recv (R : ReconfigSet schema) (x : Channel) (N : NetKAT schema) (D : DyNetKAT schema) :
     tail R (.recv x N D) = none := rfl

 theorem tail_send (R : ReconfigSet schema) (x : Channel) (N : NetKAT schema) (D : DyNetKAT schema) :
     tail R (.send x N D) = none := rfl

 theorem tail_parallel (R : ReconfigSet schema) (D Q : DyNetKAT schema) :
     tail R (.parallel D Q) = none := rfl

 theorem tail_leftMerge (R : ReconfigSet schema) (D Q : DyNetKAT schema) :
     tail R (.leftMerge D Q) = none := rfl

 theorem tail_commMerge (R : ReconfigSet schema) (D Q : DyNetKAT schema) :
     tail R (.commMerge D Q) = none := rfl

 theorem tail_restrict (R : ReconfigSet schema) (L : Set (CommunicationAction schema)) (D : DyNetKAT schema) :
     tail R (.restrict L D) = none := rfl

 theorem tail_project (R : ReconfigSet schema) (n : Nat) (D : DyNetKAT schema) :
     tail R (.project n D) = none := rfl

 theorem tail_var (R : ReconfigSet schema) (name : Var) : tail R (.var name) = none := rfl

 ------------------------------------------------------------------------
 -- §3 Constructor-specific equations and failure propagation
 ------------------------------------------------------------------------

 /-- Eq. (30) propagates failure: if `tail R D` fails, `tail R (N;D)`
     fails. -/
 theorem tail_nSeq_none (R : ReconfigSet schema) (N : NetKAT schema) (D : DyNetKAT schema)
     (h : tail R D = none) : tail R (.nSeq N D) = none := by
   rw [tail_nSeq, h]

 /-- Eq. (31) in the paper's shape: if `tail R D` and `tail R Q` succeed
     with `D'` and `Q'`, then `tail R (D ⊕ Q) = D' ⊕ Q'`. -/
 theorem tail_choice_eq (R : ReconfigSet schema) (D Q D' Q' : DyNetKAT schema)
     (hD : tail R D = some D') (hQ : tail R Q = some Q') :
     tail R (.choice D Q) = some (.choice D' Q') := by
   rw [tail_choice, hD, hQ]
   rfl

 /-- Failure propagation through `D ⊕ Q` from the left branch. -/
 theorem tail_choice_none_left (R : ReconfigSet schema) (D Q : DyNetKAT schema)
     (h : tail R D = none) : tail R (.choice D Q) = none := by
   rw [tail_choice, h]
   rfl

 /-- Failure propagation through `D ⊕ Q` from the right branch.  Both
     possible values of `tail R D` are discharged explicitly. -/
 theorem tail_choice_none_right (R : ReconfigSet schema) (D Q : DyNetKAT schema)
     (h : tail R Q = none) : tail R (.choice D Q) = none := by
   cases hD : tail R D with
   | none => rw [tail_choice, hD]; rfl
   | some D' => rw [tail_choice, hD, h]; rfl

 /-- Inversion for Eq. (31): a successful extraction from `D ⊕ Q`
     determines successful extractions of both branches. -/
 theorem tail_choice_inv (R : ReconfigSet schema) (D Q X : DyNetKAT schema)
     (h : tail R (.choice D Q) = some X) :
     ∃ D' Q', tail R D = some D' ∧ tail R Q = some Q' ∧ X = .choice D' Q' := by
   rw [tail_choice, Option.bind_eq_some] at h
   obtain ⟨D', hD, hmap⟩ := h
   rw [Option.map_eq_some'] at hmap
   obtain ⟨Q', hQ, hX⟩ := hmap
   exact ⟨D', Q', hD, hQ, hX.symm⟩

 /-- Eq. (32) in the paper's shape: if `rcfg_{x,N} ∈ R` and `tail R D`
     succeeds with `D'`, then `tail R (rcfg_{x,N};D) = D ⊕ D'`.  Note
     that the continuation `D` itself enters the result unmodified,
     exactly as Eq. (32) states. -/
 theorem tail_rcfgPrefix_mem (R : ReconfigSet schema) (x : Channel) (N : NetKAT schema) (D D' : DyNetKAT schema)
     (hmem : (x, N) ∈ R) (hD : tail R D = some D') :
     tail R (.rcfgPrefix x N D) = some (.choice D D') := by
   rw [tail_rcfgPrefix, if_pos hmem, hD]
   rfl

 /-- Failure propagation through Eq. (32): if `rcfg_{x,N} ∈ R` but the
     continuation `D` is outside the supported fragment, the whole
     extraction fails - the unsupported continuation is never silently
     embedded. -/
 theorem tail_rcfgPrefix_mem_none (R : ReconfigSet schema) (x : Channel) (N : NetKAT schema) (D : DyNetKAT schema)
     (hmem : (x, N) ∈ R) (hD : tail R D = none) :
     tail R (.rcfgPrefix x N D) = none := by
   rw [tail_rcfgPrefix, if_pos hmem, hD]
   rfl

 /-- Eq. (33): if `rcfg_{x,N} ∉ R` then `tail R (rcfg_{x,N};D) = ⊥`,
     unconditionally on `D` - the paper's equation does not inspect the
     continuation in this case. -/
 theorem tail_rcfgPrefix_not_mem (R : ReconfigSet schema) (x : Channel) (N : NetKAT schema) (D : DyNetKAT schema)
     (hmem : (x, N) ∉ R) : tail R (.rcfgPrefix x N D) = some .deadlock := by
   rw [tail_rcfgPrefix, if_neg hmem]

 /-- Inversion for Eqs. (32)–(33): a successful extraction from a
     reconfiguration prefix either has its event in `R` (and then the
     continuation extraction succeeded and the result is `D ⊕ D'`), or
     its event is outside `R` (and then the result is `⊥`). -/
 theorem tail_rcfgPrefix_inv (R : ReconfigSet schema) (x : Channel) (N : NetKAT schema) (D Q : DyNetKAT schema)
     (h : tail R (.rcfgPrefix x N D) = some Q) :
     ((x, N) ∈ R ∧ ∃ D', tail R D = some D' ∧ Q = .choice D D') ∨
       ((x, N) ∉ R ∧ Q = .deadlock) := by
   rw [tail_rcfgPrefix] at h
   split at h
   · rename_i hmem
     rw [Option.map_eq_some'] at h
     obtain ⟨D', hD, hX⟩ := h
     exact Or.inl ⟨hmem, D', hD, hX.symm⟩
   · rename_i hmem
     exact Or.inr ⟨hmem, (Option.some.inj h).symm⟩

 ------------------------------------------------------------------------
 -- §4 The supported fragment
 ------------------------------------------------------------------------

 /-- Syntactic predicate characterizing the fragment on which `tail`
     performs the paper's Eqs. (29)–(33) with every recursion defined:

     - `deadlock` is supported unconditionally (Eq. 29).
     - `nSeq N D` is supported when the continuation `D` is supported
       (Eq. 30 recurses into `D`).
     - `choice D Q` is supported when both branches are supported
       (Eq. 31 recurses into both).
     - `rcfgPrefix x N D` is supported when the continuation `D` is
       supported: Eq. (32) embeds `D` itself into the result and
       recurses into it, so - unlike S4A's `head` - `tail` cannot
       discard an unsupported continuation.

     Every other constructor is outside the fragment; for such
     expressions `tail` returns `none` (explicit failure), with the one
     faithful exception recorded in `TailDomain`: Eq. (33) never
     inspects the continuation. -/
 inductive TailSupported {schema : PacketSchema} : DyNetKAT schema → Prop
   | deadlock : TailSupported .deadlock
   | nSeq : ∀ (N : NetKAT schema) (D : DyNetKAT schema),
       TailSupported D → TailSupported (.nSeq N D)
   | choice : ∀ (D Q : DyNetKAT schema),
       TailSupported D → TailSupported Q → TailSupported (.choice D Q)
   | rcfgPrefix : ∀ (x : Channel) (N : NetKAT schema) (D : DyNetKAT schema),
       TailSupported D → TailSupported (.rcfgPrefix x N D)

 /-- The supported fragment of `tail` is contained in the supported
     fragment of S4A's `head`: every `tail`-supported process is also
     `head`-supported, so `head` can always consume `tail`'s output on
     this fragment. -/
 theorem TailSupported.headSupported (D : DyNetKAT schema) (h : TailSupported D) : HeadSupported D := by
   induction h with
   | deadlock => exact HeadSupported.deadlock
   | nSeq N D _ ih => exact HeadSupported.nSeq N D ih
   | choice D Q _ _ ihD ihQ => exact HeadSupported.choice D Q ihD ihQ
   | rcfgPrefix x N D _ ih => exact HeadSupported.rcfgPrefix x N D

 /-- The fragment relationship is strict: a reconfiguration prefix with
     an unresolved recursive variable in its continuation is
     `HeadSupported` (S4A discards the continuation) but not
     `TailSupported` (S5A recurses into it). -/
 theorem tailSupported_strictly_stronger :
     HeadSupported (schema := schema) (.rcfgPrefix "c" NetKAT.id (.var "X")) ∧
       ¬ TailSupported (schema := schema) (.rcfgPrefix "c" NetKAT.id (.var "X")) := by
   constructor
   · exact HeadSupported.rcfgPrefix "c" NetKAT.id _
   · intro h
     cases h with
     | rcfgPrefix _ _ _ hD => cases hD

 /-- Every `TailSupported` process satisfies the paper's §V precondition
     for `head`/`tail`: it contains no terms of shape `x?N` or `x!N`
     (`CommFree`, S4B's formulation of the precondition). -/
 theorem TailSupported.commFree (D : DyNetKAT schema) (h : TailSupported D) : CommFree D := by
   induction h with
   | deadlock => exact trivial
   | nSeq N D _ ih => exact ih
   | choice D Q _ _ ihD ihQ => exact ⟨ihD, ihQ⟩
   | rcfgPrefix x N D _ ih => exact ih

 /-- Every `TailSupported` process is variable-free: recursive variables
     are not resolved by `tail` (H6A), so they are excluded from its
     supported domain rather than silently dropped. -/
 theorem TailSupported.varFree (D : DyNetKAT schema) (h : TailSupported D) : recursiveVars D = ∅ := by
   induction h with
   | deadlock => rfl
   | nSeq N D _ ih => exact ih
   | choice D Q _ _ ihD ihQ =>
       have hunion : recursiveVars D ∪ recursiveVars Q = ∅ := by
         rw [ihD, ihQ]
         simp
       simpa only [recursiveVars] using hunion
   | rcfgPrefix x N D _ ih => exact ih

 /-- Every expression in the supported fragment produces a successful
     `tail` result, for every reconfiguration-event set `R`.  This is
     the domain theorem for `tail`: extraction never fails on
     `TailSupported` input. -/
 theorem tail_supported_some (R : ReconfigSet schema) (D : DyNetKAT schema) (h : TailSupported D) :
     ∃ Q, tail R D = some Q := by
   induction h with
   | deadlock => exact ⟨.deadlock, tail_deadlock R⟩
   | nSeq N D _ ih =>
       obtain ⟨Q, hQ⟩ := ih
       exact ⟨Q, by rw [tail_nSeq]; exact hQ⟩
   | choice D Q _ _ ihD ihQ =>
       obtain ⟨D', hD⟩ := ihD
       obtain ⟨Q', hQ⟩ := ihQ
       exact ⟨.choice D' Q', tail_choice_eq R D Q D' Q' hD hQ⟩
   | rcfgPrefix x N D _ ih =>
       by_cases hmem : (x, N) ∈ R
       · obtain ⟨D', hD⟩ := ih
         exact ⟨.choice D D', tail_rcfgPrefix_mem R x N D D' hmem hD⟩
       · exact ⟨.deadlock, tail_rcfgPrefix_not_mem R x N D hmem⟩

 /-- Extraction never succeeds on unsupported input: if `tail R D`
     fails then `D` is outside the supported fragment. -/
 theorem tail_none_not_supported (R : ReconfigSet schema) (D : DyNetKAT schema)
     (h : tail R D = none) : ¬ TailSupported D := by
   intro hsup
   obtain ⟨Q, hQ⟩ := tail_supported_some R D hsup
   rw [h] at hQ
   exact Option.noConfusion hQ

 ------------------------------------------------------------------------
 -- §5 Exact success domain (`TailDomain R`)
 ------------------------------------------------------------------------

 /-- The exact success domain of `tail R`, as an inductive predicate.

     This refines `TailSupported` by the one case where the paper's
     equations succeed without inspecting the continuation: Eq. (33)
     yields `⊥` for `rcfg_{x,N};D` with `(x,N) ∉ R` regardless of `D`.
     On the paper's intended inputs - restricted normal forms, in which
     every continuation is itself in the fragment - `TailDomain R` and
     `TailSupported` coincide (`tailDomain_all_supported`). -/
 inductive TailDomain {schema : PacketSchema} (R : ReconfigSet schema) : DyNetKAT schema → Prop
   | deadlock : TailDomain R .deadlock
   | nSeq : ∀ (N : NetKAT schema) (D : DyNetKAT schema),
       TailDomain R D → TailDomain R (.nSeq N D)
   | choice : ∀ (D Q : DyNetKAT schema),
       TailDomain R D → TailDomain R Q → TailDomain R (.choice D Q)
   | rcfgPrefix_in : ∀ (x : Channel) (N : NetKAT schema) (D : DyNetKAT schema), (x, N) ∈ R →
       TailDomain R D → TailDomain R (.rcfgPrefix x N D)
   | rcfgPrefix_out : ∀ (x : Channel) (N : NetKAT schema) (D : DyNetKAT schema), (x, N) ∉ R →
       TailDomain R (.rcfgPrefix x N D)

 /-- Totality with explicit failure: every DyNetKAT expression either
     lies in the exact success domain of `tail R` or makes `tail` fail
     explicitly with `none`.  No expression is silently mapped to a
     process. -/
 theorem tail_none_or_domain (R : ReconfigSet schema) (D : DyNetKAT schema) :
     tail R D = none ∨ TailDomain R D := by
   induction D with
   | deadlock => exact Or.inr TailDomain.deadlock
   | nSeq N D ih =>
       rcases ih with hnone | hdom
       · exact Or.inl (tail_nSeq_none R N D hnone)
       · exact Or.inr (TailDomain.nSeq N D hdom)
   | choice D Q ihD ihQ =>
       rcases ihD with hnoneD | hdomD
       · exact Or.inl (tail_choice_none_left R D Q hnoneD)
       · rcases ihQ with hnoneQ | hdomQ
         · exact Or.inl (tail_choice_none_right R D Q hnoneQ)
         · exact Or.inr (TailDomain.choice D Q hdomD hdomQ)
   | rcfgPrefix x N D ih =>
       by_cases hmem : (x, N) ∈ R
       · rcases ih with hnone | hdom
         · exact Or.inl (tail_rcfgPrefix_mem_none R x N D hmem hnone)
         · exact Or.inr (TailDomain.rcfgPrefix_in x N D hmem hdom)
       · exact Or.inr (TailDomain.rcfgPrefix_out x N D hmem)
   | recv x N D => exact Or.inl rfl
   | send x N D => exact Or.inl rfl
   | parallel D Q _ _ => exact Or.inl rfl
   | leftMerge D Q _ _ => exact Or.inl rfl
   | commMerge D Q _ _ => exact Or.inl rfl
   | restrict actions D _ => exact Or.inl rfl
   | project n D _ => exact Or.inl rfl
   | var X => exact Or.inl rfl

 /-- A successful extraction implies membership in the exact domain. -/
 theorem tail_domain_of_some (R : ReconfigSet schema) (D : DyNetKAT schema) :
     ∀ Q, tail R D = some Q → TailDomain R D := by
   induction D with
   | deadlock =>
       intro Q h
       rw [tail_deadlock, Option.some.injEq] at h
       subst h
       exact TailDomain.deadlock
   | nSeq N D ih =>
       intro Q h
       rw [tail_nSeq] at h
       exact TailDomain.nSeq N D (ih Q h)
   | choice D Q ihD ihQ =>
       intro X h
       obtain ⟨D', Q', hD, hQ, rfl⟩ := tail_choice_inv R D Q X h
       exact TailDomain.choice D Q (ihD D' hD) (ihQ Q' hQ)
   | rcfgPrefix x N D ih =>
       intro Q h
       rcases tail_rcfgPrefix_inv R x N D Q h with ⟨hmem, D', hD, rfl⟩ |
         ⟨hmem, rfl⟩
       · exact TailDomain.rcfgPrefix_in x N D hmem (ih D' hD)
       · exact TailDomain.rcfgPrefix_out x N D hmem
   | recv x N D _ => intro Q h; rw [tail_recv] at h; exact absurd h (by simp)
   | send x N D _ => intro Q h; rw [tail_send] at h; exact absurd h (by simp)
   | parallel D Q _ _ => intro Q h; rw [tail_parallel] at h; exact absurd h (by simp)
   | leftMerge D Q _ _ => intro Q h; rw [tail_leftMerge] at h; exact absurd h (by simp)
   | commMerge D Q _ _ => intro Q h; rw [tail_commMerge] at h; exact absurd h (by simp)
   | restrict L D _ => intro Q h; rw [tail_restrict] at h; exact absurd h (by simp)
   | project n D _ => intro Q h; rw [tail_project] at h; exact absurd h (by simp)
   | var name => intro Q h; rw [tail_var] at h; exact absurd h (by simp)

 /-- Membership in the exact domain implies a successful extraction. -/
 theorem tail_some_of_domain (R : ReconfigSet schema) (D : DyNetKAT schema) (h : TailDomain R D) :
     ∃ Q, tail R D = some Q := by
   induction h with
   | deadlock => exact ⟨.deadlock, tail_deadlock R⟩
   | nSeq N D _ ih =>
       obtain ⟨Q, hQ⟩ := ih
       exact ⟨Q, by rw [tail_nSeq]; exact hQ⟩
   | choice D Q _ _ ihD ihQ =>
       obtain ⟨D', hD⟩ := ihD
       obtain ⟨Q', hQ⟩ := ihQ
       exact ⟨.choice D' Q', tail_choice_eq R D Q D' Q' hD hQ⟩
   | rcfgPrefix_in x N D hmem _ ih =>
       obtain ⟨D', hD⟩ := ih
       exact ⟨.choice D D', tail_rcfgPrefix_mem R x N D D' hmem hD⟩
   | rcfgPrefix_out x N D hmem =>
       exact ⟨.deadlock, tail_rcfgPrefix_not_mem R x N D hmem⟩

 /-- The success domain of `tail R` is exactly `TailDomain R`. -/
 theorem tail_domain_iff (R : ReconfigSet schema) (D : DyNetKAT schema) :
     (∃ Q, tail R D = some Q) ↔ TailDomain R D := by
   constructor
   · intro h
     obtain ⟨Q, hQ⟩ := h
     exact tail_domain_of_some R D Q hQ
   · exact tail_some_of_domain R D

 /-- The R-independent fragment is contained in every R-dependent exact
     domain. -/
 theorem TailSupported.tailDomain (R : ReconfigSet schema) (D : DyNetKAT schema) (h : TailSupported D) :
     TailDomain R D := by
   induction h with
   | deadlock => exact TailDomain.deadlock
   | nSeq N D _ ih => exact TailDomain.nSeq N D ih
   | choice D Q _ _ ihD ihQ => exact TailDomain.choice D Q ihD ihQ
   | rcfgPrefix x N D _ ih =>
       by_cases hmem : (x, N) ∈ R
       · exact TailDomain.rcfgPrefix_in x N D hmem ih
       · exact TailDomain.rcfgPrefix_out x N D hmem

 /-- Strengthened converse: if `tail R D` succeeds for every `R`
     extending a fixed finite set `S`, then `D` is `TailSupported`.
     The strengthening is needed because Eq. (33) succeeds without
     inspecting the continuation, so a single `R` never constrains the
     continuation of an out-of-`R` reconfiguration prefix. -/
 theorem tailDomain_superset_supported (D : DyNetKAT schema) (S : ReconfigSet schema)
     (h : ∀ R : ReconfigSet schema, S ⊆ R → TailDomain R D) : TailSupported D := by
   induction D generalizing S with
   | deadlock => exact TailSupported.deadlock
   | nSeq N D ih =>
       refine TailSupported.nSeq N D (ih S fun R hR => ?_)
       exact match h R hR with
         | TailDomain.nSeq _ _ hD => hD
   | choice D Q ihD ihQ =>
       refine TailSupported.choice D Q (ihD S fun R hR => ?_)
         (ihQ S fun R hR => ?_)
       · exact match h R hR with
           | TailDomain.choice _ _ hD _ => hD
       · exact match h R hR with
           | TailDomain.choice _ _ _ hQ => hQ
   | rcfgPrefix x N D ih =>
       refine TailSupported.rcfgPrefix x N D (ih (S ∪ {(x, N)}) fun R hR => ?_)
       have hrcfg := h R (fun _ ha => hR (Finset.mem_union_left _ ha))
       cases hrcfg with
       | rcfgPrefix_in _ _ _ _ hD => exact hD
       | rcfgPrefix_out _ _ _ hnotmem =>
           exact absurd (hR (Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl))) hnotmem
   | recv x N D _ => exact absurd (h _ (fun _ ha => ha)) (by intro hd; cases hd)
   | send x N D _ => exact absurd (h _ (fun _ ha => ha)) (by intro hd; cases hd)
   | parallel D Q _ _ => exact absurd (h _ (fun _ ha => ha)) (by intro hd; cases hd)
   | leftMerge D Q _ _ => exact absurd (h _ (fun _ ha => ha)) (by intro hd; cases hd)
   | commMerge D Q _ _ => exact absurd (h _ (fun _ ha => ha)) (by intro hd; cases hd)
   | restrict L D _ => exact absurd (h _ (fun _ ha => ha)) (by intro hd; cases hd)
   | project n D _ => exact absurd (h _ (fun _ ha => ha)) (by intro hd; cases hd)
   | var name => exact absurd (h _ (fun _ ha => ha)) (by intro hd; cases hd)

 /-- Exactness of the R-independent fragment: `tail R D` succeeds for
     every reconfiguration-event set `R` (in particular for every
     single-event set, which is how the pipeline exercises `tail`) if
     and only if `D` is `TailSupported`. -/
 theorem tailDomain_all_supported (D : DyNetKAT schema) :
     (∀ R : ReconfigSet schema, TailDomain R D) ↔ TailSupported D := by
   constructor
   · intro h
     exact tailDomain_superset_supported D ∅ (fun R _ => h R)
   · intro h R
     exact h.tailDomain R D

 ------------------------------------------------------------------------
 -- §6 Independent specification `TailSpec` (the paper equations as a
 --     relation)
 ------------------------------------------------------------------------

 /-- Independent relational specification of `tail` (paper Eqs.
     (29)–(33)).  `TailSpec R D Q` holds exactly when `Q` is the process
     that the paper's equations assign to `tail(D, R)`:

       TailSpec R ⊥ Q          = (Q = ⊥)                            (Eq. 29)
       TailSpec R (N;D) Q      = TailSpec R D Q                     (Eq. 30)
       TailSpec R (D⊕Q) Q'     = ∃ D' Q', TailSpec R D D' ∧
                                   TailSpec R Q Q' ∧ Q' = D'⊕Q'      (Eq. 31)
       TailSpec R (rcfg;D) Q   = (rcfg ∈ R ∧ ∃ D', TailSpec R D D' ∧
                                   Q = D⊕D') ∨
                                 (rcfg ∉ R ∧ Q = ⊥)               (Eqs. 32–33)

     The relation is defined by its own constructors and never mentions
     `tail`; there are no constructors for `recv`, `send`, `parallel`,
     `leftMerge`, `commMerge`, `restrict`, `project`, or `var`, so the
     spec is uninhabited for those shapes. -/
 inductive TailSpec {schema : PacketSchema} (R : ReconfigSet schema) : DyNetKAT schema → DyNetKAT schema → Prop
   | deadlock : TailSpec R .deadlock .deadlock
   | nSeq : ∀ (N : NetKAT schema) (D Q : DyNetKAT schema),
       TailSpec R D Q → TailSpec R (.nSeq N D) Q
   | choice : ∀ (D Q D' Q' : DyNetKAT schema),
       TailSpec R D D' → TailSpec R Q Q' → TailSpec R (.choice D Q) (.choice D' Q')
   | rcfgPrefix_in : ∀ (x : Channel) (N : NetKAT schema) (D D' : DyNetKAT schema), (x, N) ∈ R →
       TailSpec R D D' → TailSpec R (.rcfgPrefix x N D) (.choice D D')
   | rcfgPrefix_out : ∀ (x : Channel) (N : NetKAT schema) (D : DyNetKAT schema), (x, N) ∉ R →
       TailSpec R (.rcfgPrefix x N D) .deadlock

 /-- The extraction meets the specification: every successful `tail`
     result satisfies the paper-equation relation. -/
 theorem tail_spec (R : ReconfigSet schema) (D : DyNetKAT schema) :
     ∀ Q, tail R D = some Q → TailSpec R D Q := by
   induction D with
   | deadlock =>
       intro Q h
       rw [tail_deadlock, Option.some.injEq] at h
       subst h
       exact TailSpec.deadlock
   | nSeq N D ih =>
       intro Q h
       rw [tail_nSeq] at h
       exact TailSpec.nSeq N D Q (ih Q h)
   | choice D Q ihD ihQ =>
       intro X h
       obtain ⟨D', Q', hD, hQ, rfl⟩ := tail_choice_inv R D Q X h
       exact TailSpec.choice D Q D' Q' (ihD D' hD) (ihQ Q' hQ)
   | rcfgPrefix x N D ih =>
       intro Q h
       rcases tail_rcfgPrefix_inv R x N D Q h with ⟨hmem, D', hD, rfl⟩ | ⟨hmem, rfl⟩
       · exact TailSpec.rcfgPrefix_in x N D D' hmem (ih D' hD)
       · exact TailSpec.rcfgPrefix_out x N D hmem
   | recv x N D _ => intro Q h; rw [tail_recv] at h; exact absurd h (by simp)
   | send x N D _ => intro Q h; rw [tail_send] at h; exact absurd h (by simp)
   | parallel D Q _ _ => intro Q h; rw [tail_parallel] at h; exact absurd h (by simp)
   | leftMerge D Q _ _ => intro Q h; rw [tail_leftMerge] at h; exact absurd h (by simp)
   | commMerge D Q _ _ => intro Q h; rw [tail_commMerge] at h; exact absurd h (by simp)
   | restrict L D _ => intro Q h; rw [tail_restrict] at h; exact absurd h (by simp)
   | project n D _ => intro Q h; rw [tail_project] at h; exact absurd h (by simp)
   | var name => intro Q h; rw [tail_var] at h; exact absurd h (by simp)

 /-- The paper equations define a partial function: the specification is
     deterministic. -/
 theorem tailSpec_deterministic (R : ReconfigSet schema) (D : DyNetKAT schema) :
     ∀ Q Q', TailSpec R D Q → TailSpec R D Q' → Q = Q' := by
   intro Q Q' h h'
   induction h generalizing Q' with
   | deadlock =>
       cases h' with
       | deadlock => rfl
   | nSeq N D Q hD ih =>
       cases h' with
       | nSeq _ _ Q' hD' => exact ih Q' hD'
   | choice D Q D' Q' hD hQ ihD ihQ =>
       cases h' with
       | choice _ _ D'' Q'' hD' hQ' =>
           rw [ihD D'' hD', ihQ Q'' hQ']
   | rcfgPrefix_in x N D D' hmem hD ih =>
       cases h' with
       | rcfgPrefix_in _ _ _ D'' _ hD' => rw [ih D'' hD']
       | rcfgPrefix_out _ _ _ hnotmem => exact absurd hmem hnotmem
   | rcfgPrefix_out x N D hnotmem =>
       cases h' with
       | rcfgPrefix_in _ _ _ _ hmem _ => exact absurd hmem hnotmem
       | rcfgPrefix_out _ _ _ _ => rfl

 /-- The specification determines the extraction: every process
     satisfying the paper-equation relation is produced by `tail`. -/
 theorem tailSpec_of_tail (R : ReconfigSet schema) (D Q : DyNetKAT schema) (h : TailSpec R D Q) :
     tail R D = some Q := by
   induction h with
   | deadlock => exact tail_deadlock R
   | nSeq N D Q hD ih => rw [tail_nSeq]; exact ih
   | choice D Q D' Q' hD hQ ihD ihQ => exact tail_choice_eq R D Q D' Q' ihD ihQ
   | rcfgPrefix_in x N D D' hmem hD ih => exact tail_rcfgPrefix_mem R x N D D' hmem ih
   | rcfgPrefix_out x N D hnotmem => exact tail_rcfgPrefix_not_mem R x N D hnotmem

 /-- Full correspondence: `tail R D` succeeds with exactly `Q` iff `Q`
     satisfies the paper-equation specification. -/
 theorem tail_spec_iff (R : ReconfigSet schema) (D Q : DyNetKAT schema) :
     tail R D = some Q ↔ TailSpec R D Q := by
   constructor
   · exact tail_spec R D Q
   · exact tailSpec_of_tail R D Q

 /-- The specification's domain is the exact success domain. -/
 theorem tailSpec_domain (R : ReconfigSet schema) (D Q : DyNetKAT schema) (h : TailSpec R D Q) :
     TailDomain R D := by
   induction h with
   | deadlock => exact TailDomain.deadlock
   | nSeq N D Q _ ih => exact TailDomain.nSeq N D ih
   | choice D Q D' Q' _ _ ihD ihQ => exact TailDomain.choice D Q ihD ihQ
   | rcfgPrefix_in x N D D' hmem _ ih => exact TailDomain.rcfgPrefix_in x N D hmem ih
   | rcfgPrefix_out x N D hnotmem => exact TailDomain.rcfgPrefix_out x N D hnotmem

 ------------------------------------------------------------------------
 -- §7 Post-reconfiguration suffixes and step-level soundness
 ------------------------------------------------------------------------

 /-- `TailSuffix R D S` : `S` is one of the "DyNetKAT policies inside D
     that appear after the reconfiguration events in R" (paper §V) -
     the continuation after an unblocked `R`-reconfiguration prefix
     along some branch of `D`.  Unblocked means: no reconfiguration
     event outside `R` occurs on the branch before the one whose
     continuation is `S` (Eq. (33) cuts such branches off).

     This predicate is defined independently of `tail` and is the
     process-level reading of the paper's intuition for `tail`. -/
 inductive TailSuffix {schema : PacketSchema} (R : ReconfigSet schema) : DyNetKAT schema → DyNetKAT schema → Prop
   | rcfgPrefix_here : ∀ (x : Channel) (N : NetKAT schema) (D : DyNetKAT schema), (x, N) ∈ R →
       TailSuffix R (.rcfgPrefix x N D) D
   | rcfgPrefix_of : ∀ (x : Channel) (N : NetKAT schema) (D S : DyNetKAT schema), (x, N) ∈ R →
       TailSuffix R D S → TailSuffix R (.rcfgPrefix x N D) S
   | nSeq_of : ∀ (N : NetKAT schema) (D S : DyNetKAT schema),
       TailSuffix R D S → TailSuffix R (.nSeq N D) S
   | choice_left : ∀ (D Q S : DyNetKAT schema),
       TailSuffix R D S → TailSuffix R (.choice D Q) S
   | choice_right : ∀ (D Q S : DyNetKAT schema),
       TailSuffix R Q S → TailSuffix R (.choice D Q) S

 /-- Step-level soundness of the extraction (no invented behaviour):
     every transition of the extracted process `tail R D` is a
     transition of one of the post-reconfiguration suffixes of `D`,
     taken from the same configuration.  In particular the extraction
     never introduces a transition that `D`'s own suffixes do not
     justify.

     This is stated for `TailSupported` inputs; on the Eq.-33 case of
     `rcfgPrefix` the extracted process is `⊥`, which affords no
     transitions, so the statement is vacuous there. -/
 theorem tail_step_suffix (env : RecEnv schema) (R : ReconfigSet schema) (D : DyNetKAT schema)
     (hsup : TailSupported D) :
     ∀ Q, tail R D = some Q →
       ∀ (pending handled : List schema.Packet) (action : Action schema) (Q' : DyNetKAT schema)
         (pending' handled' : List schema.Packet),
         Step env
           (show (Config schema) from { proc := Q, pending := pending, handled := handled })
           action
           (show (Config schema) from
             { proc := Q', pending := pending', handled := handled' }) →
         ∃ S, TailSuffix R D S ∧
           Step env
             (show (Config schema) from { proc := S, pending := pending, handled := handled })
             action
             (show (Config schema) from
               { proc := Q', pending := pending', handled := handled' }) := by
   induction hsup with
   | deadlock =>
       intro Q hQ pending handled action Q' pending' handled' hstep
       rw [tail_deadlock, Option.some.injEq] at hQ
       subst hQ
       exact absurd hstep (deadlock_no_step env pending handled action _)
   | nSeq N D _ ih =>
       intro Q hQ pending handled action Q' pending' handled' hstep
       rw [tail_nSeq] at hQ
       obtain ⟨S, hS, hstep⟩ := ih Q hQ pending handled action Q' pending' handled' hstep
       exact ⟨S, TailSuffix.nSeq_of N D S hS, hstep⟩
   | choice D Q _ _ ihD ihQ =>
       intro X hX pending handled action X' pending' handled' hstep
       obtain ⟨D', Q', hD, hQ, rfl⟩ := tail_choice_inv R D Q X hX
       cases hstep with
       | cpol_choice_l _ _ _ _ _ _ _ _ steps =>
           obtain ⟨S, hS, hstep⟩ := ihD D' hD pending handled action _ pending' handled' steps
           exact ⟨S, TailSuffix.choice_left D Q S hS, hstep⟩
       | cpol_choice_r _ _ _ _ _ _ _ _ steps =>
           obtain ⟨S, hS, hstep⟩ := ihQ Q' hQ pending handled action _ pending' handled' steps
           exact ⟨S, TailSuffix.choice_right D Q S hS, hstep⟩
   | rcfgPrefix x N D _ ih =>
       intro Q hQ pending handled action Q' pending' handled' hstep
       rcases tail_rcfgPrefix_inv R x N D Q hQ with ⟨hmem, D', hD, rfl⟩ | ⟨hmem, rfl⟩
       · cases hstep with
         | cpol_choice_l _ _ _ _ _ _ _ _ steps =>
             exact ⟨D, TailSuffix.rcfgPrefix_here x N D hmem, steps⟩
         | cpol_choice_r _ _ _ _ _ _ _ _ steps =>
             obtain ⟨S, hS, hstep⟩ := ih D' hD pending handled action _ pending' handled' steps
             exact ⟨S, TailSuffix.rcfgPrefix_of x N D S hmem hS, hstep⟩
       · exact absurd hstep (deadlock_no_step env pending handled action _)
/-- Step-level completeness of the extraction (no lost behaviour):
    every transition of a post-reconfiguration suffix `S` of `D` is
    afforded by the extracted process `tail R D` from the same
    configuration, with the same target process: under the resolving
    `(cpol⊕)` rules, when the disjunct `S` of the extracted choice tree
    steps to `S'`, the whole extracted process steps to `S'`.

    Together with `tail_step_suffix` this shows that the extracted
    process affords exactly the transitions of the post-reconfiguration
    suffixes of `D`, i.e. the paper's "sum of DyNetKAT policies inside
    D that appear after the reconfiguration events in R" is extracted
    behaviourally without invention or loss. -/
theorem suffix_step_tail (env : RecEnv schema) (R : ReconfigSet schema) (D : DyNetKAT schema)
    (hsup : TailSupported D) :
    ∀ S S', TailSuffix R D S →
      ∀ (pending handled : List schema.Packet) (action : Action schema)
        (pending' handled' : List schema.Packet),
        Step env
          (show (Config schema) from { proc := S, pending := pending, handled := handled })
          action
          (show (Config schema) from
            { proc := S', pending := pending', handled := handled' }) →
        ∀ Q, tail R D = some Q →
          Step env
            (show (Config schema) from { proc := Q, pending := pending, handled := handled })
            action
            (show (Config schema) from
              { proc := S', pending := pending', handled := handled' }) := by
  induction hsup with
  | deadlock =>
      intro S S' hS pending handled action pending' handled' hstep Q hQ
      cases hS
  | nSeq N D _ ih =>
      intro S S' hS pending handled action pending' handled' hstep Q hQ
      cases hS with
      | nSeq_of _ _ _ hD =>
          rw [tail_nSeq] at hQ
          exact ih S S' hD pending handled action pending' handled' hstep Q hQ
  | choice D Qd _ _ ihD ihQ =>
      intro S S' hS pending handled action pending' handled' hstep Q hQ
      obtain ⟨D', Q'', hD, hQd, rfl⟩ := tail_choice_inv R D Qd Q hQ
      cases hS with
      | choice_left _ _ _ hSD =>
          exact Step.cpol_choice_l D' Q'' S' action pending pending' handled handled'
            (ihD S S' hSD pending handled action pending' handled' hstep D' hD)
      | choice_right _ _ _ hSQ =>
          exact Step.cpol_choice_r D' Q'' S' action pending pending' handled handled'
            (ihQ S S' hSQ pending handled action pending' handled' hstep Q'' hQd)
  | rcfgPrefix x N Dc _ ih =>
      intro S S' hS pending handled action pending' handled' hstep Q hQ
      rcases tail_rcfgPrefix_inv R x N Dc Q hQ with ⟨hmemQ, D', hD', rfl⟩ | ⟨hmemQ, rfl⟩
      · cases hS with
        | rcfgPrefix_here _ _ _ hmem =>
            exact Step.cpol_choice_l Dc D' S' action pending pending' handled handled' hstep
        | rcfgPrefix_of _ _ _ _ hmem hD =>
            exact Step.cpol_choice_r Dc D' S' action pending pending' handled handled'
              (ih S S' hD pending handled action pending' handled' hstep D' hD')
      · cases hS with
        | rcfgPrefix_here _ _ _ hmem => exact absurd hmem hmemQ
        | rcfgPrefix_of _ _ _ _ hmem _ => exact absurd hmem hmemQ


 ------------------------------------------------------------------------
 -- §8 Packet-level specification of the pipeline quantity
 --     `head (tail R D)`
 ------------------------------------------------------------------------

 /-- Independent packet-pair specification for the "all-R" positions of
     a process: `AllRSpec R D σ τ` holds exactly when the packet pair
     `(σ, τ)` is contributed by a NetKAT policy that occurs at a branch
     position of `D` in which *every* reconfiguration prefix that
     precedes it carries an event of `R`.  This is the contribution
     relation of the policies that become current immediately after an
     (unblocked) `R`-reconfiguration, and it is the relation that
     `head D` and `head (tail R D)` jointly describe (see
     `allR_head_spec`). -/
 inductive AllRSpec {schema : PacketSchema} (R : ReconfigSet schema) : DyNetKAT schema → schema.Packet → schema.Packet → Prop
   | nSeq_of_sem : ∀ (N : NetKAT schema) (D : DyNetKAT schema) (σ τ : schema.Packet),
       Semantics N σ τ → AllRSpec R (.nSeq N D) σ τ
   | nSeq_of_allR : ∀ (N : NetKAT schema) (D : DyNetKAT schema) (σ τ : schema.Packet),
       AllRSpec R D σ τ → AllRSpec R (.nSeq N D) σ τ
   | choice_left : ∀ (D Q : DyNetKAT schema) (σ τ : schema.Packet),
       AllRSpec R D σ τ → AllRSpec R (.choice D Q) σ τ
   | choice_right : ∀ (D Q : DyNetKAT schema) (σ τ : schema.Packet),
       AllRSpec R Q σ τ → AllRSpec R (.choice D Q) σ τ
   | rcfgPrefix_of : ∀ (x : Channel) (N : NetKAT schema) (D : DyNetKAT schema) (σ τ : schema.Packet),
       (x, N) ∈ R → AllRSpec R D σ τ → AllRSpec R (.rcfgPrefix x N D) σ τ

 /-- Independent packet-pair specification of `head (tail R D)` (paper
     Eqs. (29)–(33) composed with Eqs. (29)–(32) for `head`):
     `TailHeadSpec R D σ τ` holds exactly when `(σ, τ)` is contributed
     by a NetKAT policy that occurs at a branch position of `D` that
     (i) is preceded by at least one reconfiguration prefix and (ii) has
     *all* preceding reconfiguration prefixes carrying events of `R`.
     This formalizes the paper's intuition - the policies that appear
     after the reconfiguration events in `R` - at the level the safety
     pipeline consumes it (Eq. (35): `in · head(tail(Init, R)) · out`). -/
 inductive TailHeadSpec {schema : PacketSchema} (R : ReconfigSet schema) : DyNetKAT schema → schema.Packet → schema.Packet → Prop
   | nSeq_of : ∀ (N : NetKAT schema) (D : DyNetKAT schema) (σ τ : schema.Packet),
       TailHeadSpec R D σ τ → TailHeadSpec R (.nSeq N D) σ τ
   | choice_left : ∀ (D Q : DyNetKAT schema) (σ τ : schema.Packet),
       TailHeadSpec R D σ τ → TailHeadSpec R (.choice D Q) σ τ
   | choice_right : ∀ (D Q : DyNetKAT schema) (σ τ : schema.Packet),
       TailHeadSpec R Q σ τ → TailHeadSpec R (.choice D Q) σ τ
   | rcfgPrefix_of : ∀ (x : Channel) (N : NetKAT schema) (D : DyNetKAT schema) (σ τ : schema.Packet),
       (x, N) ∈ R → AllRSpec R D σ τ → TailHeadSpec R (.rcfgPrefix x N D) σ τ

 /-- Spec clause: the all-R contribution of `N;D` is `⟦N⟧` together with
     the all-R contribution of `D`. -/
 theorem allRSpec_nSeq_iff (R : ReconfigSet schema) (N : NetKAT schema) (D : DyNetKAT schema) (σ τ : schema.Packet) :
     AllRSpec R (.nSeq N D) σ τ ↔ (Semantics N σ τ ∨ AllRSpec R D σ τ) := by
   constructor
   · intro h
     cases h with
     | nSeq_of_sem _ _ _ _ hN => exact Or.inl hN
     | nSeq_of_allR _ _ _ _ hD => exact Or.inr hD
   · intro h
     rcases h with hN | hD
     · exact AllRSpec.nSeq_of_sem N D σ τ hN
     · exact AllRSpec.nSeq_of_allR N D σ τ hD

 /-- Spec clause: the all-R contribution of `D ⊕ Q` is the union of the
     contributions of both branches. -/
 theorem allRSpec_choice_iff (R : ReconfigSet schema) (D Q : DyNetKAT schema) (σ τ : schema.Packet) :
     AllRSpec R (.choice D Q) σ τ ↔ (AllRSpec R D σ τ ∨ AllRSpec R Q σ τ) := by
   constructor
   · intro h
     cases h with
     | choice_left _ _ _ _ h1 => exact Or.inl h1
     | choice_right _ _ _ _ h2 => exact Or.inr h2
   · intro h
     rcases h with h1 | h2
     · exact AllRSpec.choice_left D Q σ τ h1
     · exact AllRSpec.choice_right D Q σ τ h2

 /-- Spec clause: past a reconfiguration prefix the all-R contribution
     continues only when the event itself is in `R` (Eq. 33 cuts the
     branch otherwise). -/
 theorem allRSpec_rcfgPrefix_iff (R : ReconfigSet schema) (x : Channel) (N : NetKAT schema)
     (D : DyNetKAT schema) (σ τ : schema.Packet) :
     AllRSpec R (.rcfgPrefix x N D) σ τ ↔ ((x, N) ∈ R ∧ AllRSpec R D σ τ) := by
   constructor
   · intro h
     cases h with
     | rcfgPrefix_of _ _ _ _ _ hmem hD => exact ⟨hmem, hD⟩
   · intro h
     obtain ⟨hmem, hD⟩ := h
     exact AllRSpec.rcfgPrefix_of x N D σ τ hmem hD

 /-- ⊥ contributes nothing to the all-R relation. -/
 theorem allRSpec_deadlock_false (R : ReconfigSet schema) (σ τ : schema.Packet) :
     ¬ AllRSpec R .deadlock σ τ := by
   intro h
   cases h

 /-- Spec clause: the tail contribution of `N;D` is the tail
     contribution of `D` (the policy `N` at the current position is
     *before* any reconfiguration and does not contribute). -/
 theorem tailHeadSpec_nSeq_iff (R : ReconfigSet schema) (N : NetKAT schema) (D : DyNetKAT schema) (σ τ : schema.Packet) :
     TailHeadSpec R (.nSeq N D) σ τ ↔ TailHeadSpec R D σ τ := by
   constructor
   · intro h
     cases h with
     | nSeq_of _ _ _ _ h => exact h
   · intro h
     exact TailHeadSpec.nSeq_of N D σ τ h

 /-- Spec clause: the tail contribution of `D ⊕ Q` is the union of the
     contributions of both branches. -/
 theorem tailHeadSpec_choice_iff (R : ReconfigSet schema) (D Q : DyNetKAT schema) (σ τ : schema.Packet) :
     TailHeadSpec R (.choice D Q) σ τ ↔ (TailHeadSpec R D σ τ ∨ TailHeadSpec R Q σ τ) := by
   constructor
   · intro h
     cases h with
     | choice_left _ _ _ _ h1 => exact Or.inl h1
     | choice_right _ _ _ _ h2 => exact Or.inr h2
   · intro h
     rcases h with h1 | h2
     · exact TailHeadSpec.choice_left D Q σ τ h1
     · exact TailHeadSpec.choice_right D Q σ τ h2

 /-- Spec clause: the tail contribution of `rcfg_{x,N};D` is the all-R
     contribution of `D` when the event is in `R`, and nothing
     otherwise (Eq. 33). -/
 theorem tailHeadSpec_rcfgPrefix_iff (R : ReconfigSet schema) (x : Channel) (N : NetKAT schema)
     (D : DyNetKAT schema) (σ τ : schema.Packet) :
     TailHeadSpec R (.rcfgPrefix x N D) σ τ ↔ ((x, N) ∈ R ∧ AllRSpec R D σ τ) := by
   constructor
   · intro h
     cases h with
     | rcfgPrefix_of _ _ _ _ _ hmem hD => exact ⟨hmem, hD⟩
   · intro h
     obtain ⟨hmem, hD⟩ := h
     exact TailHeadSpec.rcfgPrefix_of x N D σ τ hmem hD

 /-- ⊥ contributes nothing to the tail relation. -/
 theorem tailHeadSpec_deadlock_false (R : ReconfigSet schema) (σ τ : schema.Packet) :
     ¬ TailHeadSpec R .deadlock σ τ := by
   intro h
   cases h

 /-- Eq. (30) for `head` in map form: definitionally equal to the match
     of `head_nSeq`, but amenable to the standard `Option` inversion
     lemmas. -/
 theorem head_nSeq_map (N : NetKAT schema) (D : DyNetKAT schema) :
     head (.nSeq N D) = (head D).map (fun H' => NetKAT.union N H') := by
   rw [head_nSeq]
   cases hD : head D <;> rfl

 /-- Inversion for S4A's `head` on `N;D`: a successful extraction
     determines a successful extraction of the continuation. -/
 theorem head_nSeq_inv (N : NetKAT schema) (D : DyNetKAT schema) (H : NetKAT schema)
     (h : head (.nSeq N D) = some H) :
     ∃ H', head D = some H' ∧ H = NetKAT.union N H' := by
   rw [head_nSeq_map, Option.map_eq_some'] at h
   obtain ⟨H', hD, hX⟩ := h
   exact ⟨H', hD, hX.symm⟩

 /-- Eq. (31) for `head` in bind/map form: definitionally equal to the
     two-scrutinee match of `head_choice`, but amenable to the standard
     `Option` inversion lemmas. -/
 theorem head_choice_bind (D Q : DyNetKAT schema) :
     head (.choice D Q) =
       (head D).bind (fun H₁ => (head Q).map (fun H₂ => NetKAT.union H₁ H₂)) := by
   rw [head_choice]
   cases hD : head D <;> cases hQ : head Q <;> rfl

 /-- Inversion for S4A's `head` on `D ⊕ Q`: a successful extraction
     determines successful extractions of both branches. -/
 theorem head_choice_inv (D Q : DyNetKAT schema) (H : NetKAT schema)
     (h : head (.choice D Q) = some H) :
     ∃ H₁ H₂ : NetKAT schema, head D = some H₁ ∧ head Q = some H₂ ∧ H = NetKAT.union H₁ H₂ := by
   rw [head_choice_bind, Option.bind_eq_some] at h
   obtain ⟨H₁, hD, hmap⟩ := h
   rw [Option.map_eq_some'] at hmap
   obtain ⟨H₂, hQ, hX⟩ := hmap
   exact ⟨H₁, H₂, hD, hQ, hX.symm⟩

 ------------------------------------------------------------------------
 -- §9 Semantic characterization of `head (tail R D)`
 ------------------------------------------------------------------------

 /-- Main semantic theorem (proved by a simultaneous induction on the
     `TailSupported` derivation, establishing both the tail-level and
     the head-level correspondence):

     (a) For supported `D`, the NetKAT policy `H` extracted by the
         pipeline quantity `head (tail R D)` denotes exactly the
         `TailHeadSpec R D` packet-pair relation: the pairs contributed
         by the NetKAT policies that occur in `D` after at least one
         reconfiguration prefix, all of whose preceding reconfiguration
         prefixes carry events of `R`.

     (b) Decomposition identity: the "all-R" contribution of `D` is
         exactly the contribution of `head D` (the policies before the
         first reconfiguration on each branch - any event set) together
         with the tail contribution `TailHeadSpec R D`.  For `R = ∅`
         this degenerates to `AllRSpec ∅ D ↔ ⟦head D⟧`, since
         `TailHeadSpec ∅` is empty.

     The theorem is stated only on `TailSupported` inputs; the empty
     spec on unsupported shapes is never used to claim anything about
     them. -/
 theorem tail_head_spec_aux (R : ReconfigSet schema) (D : DyNetKAT schema) (hsup : TailSupported D) :
     (∀ (Q : DyNetKAT schema) (H : NetKAT schema), tail R D = some Q → head Q = some H →
         ∀ σ τ : schema.Packet, Semantics H σ τ ↔ TailHeadSpec R D σ τ) ∧
     (∀ (H : NetKAT schema), head D = some H →
         ∀ σ τ : schema.Packet, AllRSpec R D σ τ ↔ (Semantics H σ τ ∨ TailHeadSpec R D σ τ)) := by
   induction hsup with
   | deadlock =>
       constructor
       · intro Q H hQ hH σ τ
         rw [tail_deadlock, Option.some.injEq] at hQ
         subst hQ
         rw [head_deadlock, Option.some.injEq] at hH
         subst hH
         constructor
         · intro hsem; exact absurd hsem (sem_drop_empty σ τ)
         · intro hspec; exact absurd hspec (tailHeadSpec_deadlock_false R σ τ)
       · intro H hH σ τ
         rw [head_deadlock, Option.some.injEq] at hH
         subst hH
         constructor
         · intro h; exact absurd h (allRSpec_deadlock_false R σ τ)
         · intro h
           rcases h with h | h
           · exact absurd h (sem_drop_empty σ τ)
           · exact absurd h (tailHeadSpec_deadlock_false R σ τ)
   | nSeq N D _ ihD =>
       constructor
       · intro Q H hQ hH σ τ
         rw [tail_nSeq] at hQ
         exact (ihD.1 Q H hQ hH σ τ).trans (tailHeadSpec_nSeq_iff R N D σ τ).symm
       · intro H hH σ τ
         obtain ⟨H', hHD, rfl⟩ := head_nSeq_inv N D H hH
         constructor
         · intro h
           rcases (allRSpec_nSeq_iff R N D σ τ).mp h with hN | hD
           · exact Or.inl ((union_sem N H' σ τ).mpr (Or.inl hN))
           · rcases (ihD.2 H' hHD σ τ).mp hD with h | h
             · exact Or.inl ((union_sem N H' σ τ).mpr (Or.inr h))
             · exact Or.inr ((tailHeadSpec_nSeq_iff R N D σ τ).mpr h)
         · intro h
           rcases h with h | h
           · rcases (union_sem N H' σ τ).mp h with hN | hH'
             · exact (allRSpec_nSeq_iff R N D σ τ).mpr (Or.inl hN)
             · exact (allRSpec_nSeq_iff R N D σ τ).mpr
                 (Or.inr ((ihD.2 H' hHD σ τ).mpr (Or.inl hH')))
           · exact (allRSpec_nSeq_iff R N D σ τ).mpr
               (Or.inr ((ihD.2 H' hHD σ τ).mpr (Or.inr
                 ((tailHeadSpec_nSeq_iff R N D σ τ).mp h))))
   | choice D Q _ _ ihD ihQ =>
       constructor
       · intro X H hX hH σ τ
         obtain ⟨D', Q', hD, hQ, rfl⟩ := tail_choice_inv R D Q X hX
         obtain ⟨H₁, H₂, hHD, hHQ, rfl⟩ := head_choice_inv D' Q' H hH
         constructor
         · intro hsem
           rcases (union_sem H₁ H₂ σ τ).mp hsem with h | h
           · exact (tailHeadSpec_choice_iff R D Q σ τ).mpr
               (Or.inl ((ihD.1 D' H₁ hD hHD σ τ).mp h))
           · exact (tailHeadSpec_choice_iff R D Q σ τ).mpr
               (Or.inr ((ihQ.1 Q' H₂ hQ hHQ σ τ).mp h))
         · intro hspec
           rcases (tailHeadSpec_choice_iff R D Q σ τ).mp hspec with h | h
           · exact (union_sem H₁ H₂ σ τ).mpr (Or.inl ((ihD.1 D' H₁ hD hHD σ τ).mpr h))
           · exact (union_sem H₁ H₂ σ τ).mpr (Or.inr ((ihQ.1 Q' H₂ hQ hHQ σ τ).mpr h))
       · intro H hH σ τ
         obtain ⟨H₁, H₂, hHD, hHQ, rfl⟩ := head_choice_inv D Q H hH
         constructor
         · intro h
           rcases (allRSpec_choice_iff R D Q σ τ).mp h with h | h
           · rcases (ihD.2 H₁ hHD σ τ).mp h with h1 | h2
             · exact Or.inl ((union_sem H₁ H₂ σ τ).mpr (Or.inl h1))
             · exact Or.inr ((tailHeadSpec_choice_iff R D Q σ τ).mpr (Or.inl h2))
           · rcases (ihQ.2 H₂ hHQ σ τ).mp h with h1 | h2
             · exact Or.inl ((union_sem H₁ H₂ σ τ).mpr (Or.inr h1))
             · exact Or.inr ((tailHeadSpec_choice_iff R D Q σ τ).mpr (Or.inr h2))
         · intro h
           rcases h with h | h
           · rcases (union_sem H₁ H₂ σ τ).mp h with h1 | h2
             · exact (allRSpec_choice_iff R D Q σ τ).mpr
                 (Or.inl ((ihD.2 H₁ hHD σ τ).mpr (Or.inl h1)))
             · exact (allRSpec_choice_iff R D Q σ τ).mpr
                 (Or.inr ((ihQ.2 H₂ hHQ σ τ).mpr (Or.inl h2)))
           · rcases (tailHeadSpec_choice_iff R D Q σ τ).mp h with h1 | h2
             · exact (allRSpec_choice_iff R D Q σ τ).mpr
                 (Or.inl ((ihD.2 H₁ hHD σ τ).mpr (Or.inr h1)))
             · exact (allRSpec_choice_iff R D Q σ τ).mpr
                 (Or.inr ((ihQ.2 H₂ hHQ σ τ).mpr (Or.inr h2)))
   | rcfgPrefix x N D hDsup ihD =>
       constructor
       · intro Q H hQ hH σ τ
         rcases tail_rcfgPrefix_inv R x N D Q hQ with ⟨hmem, D', hD, rfl⟩ | ⟨hnotmem, rfl⟩
         · obtain ⟨H₁, H₂, hHD, hHD', rfl⟩ := head_choice_inv D D' H hH
           constructor
           · intro hsem
             refine (tailHeadSpec_rcfgPrefix_iff R x N D σ τ).mpr ⟨hmem, ?_⟩
             rcases (union_sem H₁ H₂ σ τ).mp hsem with h | h
             · exact (ihD.2 H₁ hHD σ τ).mpr (Or.inl h)
             · exact (ihD.2 H₁ hHD σ τ).mpr (Or.inr ((ihD.1 D' H₂ hD hHD' σ τ).mp h))
           · intro hspec
             obtain ⟨_, hallR⟩ := (tailHeadSpec_rcfgPrefix_iff R x N D σ τ).mp hspec
             rcases (ihD.2 H₁ hHD σ τ).mp hallR with h | h
             · exact (union_sem H₁ H₂ σ τ).mpr (Or.inl h)
             · exact (union_sem H₁ H₂ σ τ).mpr (Or.inr ((ihD.1 D' H₂ hD hHD' σ τ).mpr h))
         · rw [head_deadlock, Option.some.injEq] at hH
           subst hH
           constructor
           · intro hsem; exact absurd hsem (sem_drop_empty σ τ)
           · intro hspec
             obtain ⟨hmem, _⟩ := (tailHeadSpec_rcfgPrefix_iff R x N D σ τ).mp hspec
             exact absurd hmem hnotmem
       · intro H hH σ τ
         rw [head_rcfgPrefix, Option.some.injEq] at hH
         subst hH
         constructor
         · intro h
           obtain ⟨hmem, hallR⟩ := (allRSpec_rcfgPrefix_iff R x N D σ τ).mp h
           exact Or.inr ((tailHeadSpec_rcfgPrefix_iff R x N D σ τ).mpr ⟨hmem, hallR⟩)
         · intro h
           rcases h with h | h
           · exact absurd h (sem_drop_empty σ τ)
           · exact (allRSpec_rcfgPrefix_iff R x N D σ τ).mpr
               ((tailHeadSpec_rcfgPrefix_iff R x N D σ τ).mp h)

 /-- Semantic characterization of the pipeline quantity `head (tail R D)`
     on the supported fragment: the extracted NetKAT policy `H` denotes
     exactly the packet pairs contributed by the NetKAT policies that
     occur in `D` after at least one reconfiguration prefix, all of
     whose preceding reconfiguration prefixes carry events of `R`
     (paper §V: "the sum of DyNetKAT policies inside D that appear
     after the reconfiguration events in R", consumed as in Eq. (35)). -/
 theorem tail_head_spec (R : ReconfigSet schema) (D : DyNetKAT schema) (hsup : TailSupported D)
     (Q : DyNetKAT schema) (H : NetKAT schema) (hQ : tail R D = some Q) (hH : head Q = some H)
     (σ τ : schema.Packet) :
     Semantics H σ τ ↔ TailHeadSpec R D σ τ :=
   (tail_head_spec_aux R D hsup).1 Q H hQ hH σ τ

 /-- Decomposition identity: the all-R contribution of a supported `D`
     is the contribution of S4A's `head D` (policies before the first
     reconfiguration on each branch) together with the tail
     contribution.  For `R = ∅` the tail contribution is empty and the
     identity reduces to `AllRSpec ∅ D ↔ ⟦head D⟧`. -/
 theorem allR_head_spec (R : ReconfigSet schema) (D : DyNetKAT schema) (hsup : TailSupported D)
     (H : NetKAT schema) (hH : head D = some H) (σ τ : schema.Packet) :
     AllRSpec R D σ τ ↔ (Semantics H σ τ ∨ TailHeadSpec R D σ τ) :=
   (tail_head_spec_aux R D hsup).2 H hH σ τ

 /-- The output of `tail` on supported input is again `HeadSupported`,
     so S4A's `head` can always consume it - the composition
     `head (tail R D)` is defined on the whole supported fragment. -/
 theorem tail_headSupported (R : ReconfigSet schema) (D : DyNetKAT schema) (hsup : TailSupported D) :
     ∀ Q, tail R D = some Q → HeadSupported Q := by
   induction hsup with
   | deadlock =>
       intro Q hQ
       rw [tail_deadlock, Option.some.injEq] at hQ
       subst hQ
       exact HeadSupported.deadlock
   | nSeq N D _ ih =>
       intro Q hQ
       rw [tail_nSeq] at hQ
       exact ih Q hQ
   | choice D Qd _ _ ihD ihQ =>
       intro Q hQ
       obtain ⟨D', Q'', hD, hQd, rfl⟩ := tail_choice_inv R D Qd Q hQ
       exact HeadSupported.choice D' Q'' (ihD D' hD) (ihQ Q'' hQd)
   | rcfgPrefix x N D hDsup ih =>
       intro Q hQ
       rcases tail_rcfgPrefix_inv R x N D Q hQ with ⟨hmem, D', hD, rfl⟩ | ⟨hmem, rfl⟩
       · exact HeadSupported.choice D D' (TailSupported.headSupported D hDsup) (ih D' hD)
       · exact HeadSupported.deadlock

 /-- The full extraction `head (tail R D)` succeeds on the whole
     supported fragment. -/
 theorem tail_head_some (R : ReconfigSet schema) (D : DyNetKAT schema) (hsup : TailSupported D) :
     ∃ Q H, tail R D = some Q ∧ head Q = some H := by
   obtain ⟨Q, hQ⟩ := tail_supported_some R D hsup
   obtain ⟨H, hH⟩ := head_supported_some Q (tail_headSupported R D hsup Q hQ)
   exact ⟨Q, H, hQ, hH⟩

 ------------------------------------------------------------------------
 -- §10 Integration with S4B preprocessing and S4A `head`
 ------------------------------------------------------------------------

 /-- S4B's `restrictElim` produces `TailSupported` output whenever it
     succeeds on a process whose communication actions are all blocked
     by `L` (the same hypothesis under which S4B proves
     `CommFree ∧ HeadSupported`).  The reconfiguration case is where
     the stronger fragment matters: Eq. (32) recurses into the
     continuation, and the induction hypothesis provides exactly the
     required `TailSupported D'`. -/
 theorem restrictElim_tailSupported (L : Finset (CommunicationAction schema)) (p : DyNetKAT schema) :
     (∀ a ∈ commActions p, a ∈ L) →
       ∀ q, restrictElim L p = some q → CommFree q ∧ TailSupported q := by
   induction p with
   | deadlock =>
       intro hsub q h
       rw [restrictElim_deadlock, Option.some.injEq] at h
       subst h
       exact ⟨trivial, TailSupported.deadlock⟩
   | nSeq N D ih =>
       intro hsub q h
       rw [restrictElim_nSeq, Option.map_eq_some'] at h
       obtain ⟨D', hD', rfl⟩ := h
       obtain ⟨hcf, hts⟩ := ih (fun a ha => hsub a ha) D' hD'
       exact ⟨hcf, TailSupported.nSeq N D' hts⟩
   | recv x N D ih =>
       intro hsub q h
       rw [restrictElim_recv] at h
       split at h
       · rename_i hmem
         have hq : .deadlock = q := Option.some.inj h
         subst hq
         exact ⟨trivial, TailSupported.deadlock⟩
       · rename_i hmem
         exact absurd (hsub _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr rfl))) hmem
   | send x N D ih =>
       intro hsub q h
       rw [restrictElim_send] at h
       split at h
       · rename_i hmem
         have hq : .deadlock = q := Option.some.inj h
         subst hq
         exact ⟨trivial, TailSupported.deadlock⟩
       · rename_i hmem
         exact absurd (hsub _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr rfl))) hmem
   | rcfgPrefix x N D ih =>
       intro hsub q h
       rw [restrictElim_rcfgPrefix, Option.map_eq_some'] at h
       obtain ⟨D', hD', rfl⟩ := h
       obtain ⟨hcf, hts⟩ := ih (fun a ha => hsub a ha) D' hD'
       exact ⟨hcf, TailSupported.rcfgPrefix x N D' hts⟩
   | choice D Q ihD ihQ =>
       intro hsub q h
       rw [restrictElim_choice] at h
       simp only [Option.bind_eq_some, Option.map_eq_some'] at h
       obtain ⟨D', hD, Q', hQ, rfl⟩ := h
       obtain ⟨hcfD, htsD⟩ := ihD (fun a ha => hsub a (Finset.subset_union_left ha)) D' hD
       obtain ⟨hcfQ, htsQ⟩ := ihQ (fun a ha => hsub a (Finset.subset_union_right ha)) Q' hQ
       exact ⟨⟨hcfD, hcfQ⟩, TailSupported.choice D' Q' htsD htsQ⟩
   | parallel D Q _ _ => intro hsub q h; rw [restrictElim_parallel] at h; exact absurd h (by simp)
   | leftMerge D Q _ _ => intro hsub q h; rw [restrictElim_leftMerge] at h; exact absurd h (by simp)
   | commMerge D Q _ _ => intro hsub q h; rw [restrictElim_commMerge] at h; exact absurd h (by simp)
   | restrict M D _ => intro hsub q h; rw [restrictElim_restrict] at h; exact absurd h (by simp)
   | project n D _ => intro hsub q h; rw [restrictElim_project] at h; exact absurd h (by simp)
   | var name => intro hsub q h; rw [restrictElim_var] at h; exact absurd h (by simp)

 /-- Whenever S4B's `preprocess` succeeds, its result satisfies the
     paper's §V precondition (`CommFree`) *and* lies in the S5A
     `TailSupported` fragment - no additional conditions beyond S4B's
     are needed for `tail`. -/
 theorem preprocess_tail_supported (env : RecEnv schema) (p : DyNetKAT schema) (q : DyNetKAT schema)
     (hq : preprocess env p = some q) : CommFree q ∧ TailSupported q := by
   simp only [preprocess] at hq
   exact restrictElim_tailSupported (commActions p) p (fun _ ha => ha) q hq

 /-- Full S4B + S5A + S4A pipeline: under S4B's preprocessing
     conditions, `preprocess` succeeds and both extractions succeed on
     its result - the preprocessed process feeds `head` and `tail`
     simultaneously, as in the paper's Eqs. (34)–(35). -/
 theorem preprocess_head_tail_some (env : RecEnv schema) (p : DyNetKAT schema) (R : ReconfigSet schema)
     (h : PreprocessingConditions env p) :
     ∃ q Q H, preprocess env p = some q ∧ HeadSupported q ∧ TailSupported q ∧
       tail R q = some Q ∧ head Q = some H := by
   obtain ⟨q, hq, hsup⟩ := preprocess_head_supported env p h
   obtain ⟨_, hts⟩ := preprocess_tail_supported env p q hq
   obtain ⟨Q, hQ⟩ := tail_supported_some R q hts
   obtain ⟨H, hH⟩ := head_supported_some Q (tail_headSupported R q hts Q hQ)
   exact ⟨q, Q, H, hq, hsup, hts, hQ, hH⟩

 /-- Semantic characterization of the pipeline quantity on preprocessed
     input: for `q` produced by S4B's `preprocess`, the NetKAT policy
     extracted by `head (tail R q)` denotes exactly the `TailHeadSpec`
     relation of `q`. -/
 theorem preprocess_tail_head_spec (env : RecEnv schema) (p : DyNetKAT schema) (R : ReconfigSet schema)
     (q : DyNetKAT schema) (hq : preprocess env p = some q) (Q : DyNetKAT schema) (H : NetKAT schema)
     (hQ : tail R q = some Q) (hH : head Q = some H) (σ τ : schema.Packet) :
     Semantics H σ τ ↔ TailHeadSpec R q σ τ :=
   tail_head_spec R q (preprocess_tail_supported env p q hq).2 Q H hQ hH σ τ

 end DyNetKAT.DyNetKAT
