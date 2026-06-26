/-
M7 proof frontier for the generated Ben-Or model.

This module imports the real Step B output copied into `BenOr.Defs`. The predicates
below mirror the auxiliary invariant structure from
`Ben_or83_inductive.tla`, using the faster cardinality-based variants where the
TLA+ development introduced them.

The source checker and the corrected lowering both allow `step3` to create a
decision. Agreement therefore cannot be proved by treating `step3` as
impossible. The proved bridge below shows that the strengthened auxiliary
invariant implies `agreement_inv`; the remaining frontier is to prove that this
invariant is initialized and preserved.
-/
import BenOr.Defs

namespace ben_or

def values : Finset Int :=
  insert 0 (insert 1 (∅ : Finset Int))

def allReplicas (s : State) : Finset Int :=
  s.CORRECT ∪ s.FAULTY

def senders1 (s : State) (msgs : Finset Msg1) : Finset Int :=
  Finset.filter (fun rid => ∃ m ∈ msgs, rid = Msg1.src m) (allReplicas s)

def senders2 (s : State) (msgs : Finset Msg2) : Finset Int :=
  Finset.filter (fun rid => ∃ m ∈ msgs, rid = Msg2.src m) (allReplicas s)

def d2MsgsFor (v : Int) (msgs : Finset Msg2) : Finset Msg2 :=
  Finset.filter (fun m => Msg2.kind m = Msg2Kind.D2 ∧ Msg2.value m = v) msgs

def q2Msgs (msgs : Finset Msg2) : Finset Msg2 :=
  Finset.filter (fun m => Msg2.kind m = Msg2Kind.Q2) msgs

def existsQuorum1 (s : State) (r v : Int) : Prop :=
  2 * Finset.card (senders1 s (Finset.filter (fun m => Msg1.value m = v) (Finmap.lookupD r s.msgs1))) >
    s.N + s.T

def existsQuorum2LessRam (s : State) (r v : Int) : Prop :=
  let msgs := Finmap.lookupD r s.msgs2
  let nv := Finset.card (d2MsgsFor v msgs)
  let n := Finset.card msgs
  n ≥ s.N - s.T ∧ nv ≥ s.T + 1 ∧ 2 * nv > s.N + s.T

def supportedValues (s : State) (r : Int) : Finset Int :=
  Finset.filter
    (fun v =>
      let msgs := Finmap.lookupD r s.msgs2
      let sv := senders2 s (d2MsgsFor v msgs)
      let others :=
        senders2 s
          (Finset.filter
            (fun m => Msg2.kind m = Msg2Kind.Q2 ∨ Msg2.value m ≠ v)
            msgs)
      Finset.card (senders2 s msgs) ≥ s.N - s.T ∧
        Finset.card sv ≥ s.T + 1 ∧
          Finset.card others < s.N - 2 * s.T)
    values

def decision_requires_last_quorum_less_ram (s : State) : Prop :=
  ∀ id ∈ s.CORRECT,
    Finmap.lookupD id s.decision = -1 ∨
      Finmap.lookupD id s.round > 1 ∧
        existsQuorum2LessRam s (Finmap.lookupD id s.round - 1) (Finmap.lookupD id s.decision)

def no_equivocation1_by_correct (s : State) : Prop :=
  ∀ r ∈ s.ROUNDS,
    ∀ m1 ∈ Finmap.lookupD r s.msgs1,
      ∀ m2 ∈ Finmap.lookupD r s.msgs1,
        m1.src ∈ s.CORRECT ∧ m1.src = m2.src → m1.value = m2.value

def no_equivocation2_by_correct (s : State) : Prop :=
  ∀ r ∈ s.ROUNDS,
    ∀ m1 ∈ Finmap.lookupD r s.msgs2,
      ∀ m2 ∈ Finmap.lookupD r s.msgs2,
        (m1.kind = Msg2Kind.D2 ∧ m2.kind = Msg2Kind.D2 ∧ m1.src = m2.src →
            m1.src ∈ s.CORRECT → m1.value = m2.value) ∧
          (m1.kind = Msg2Kind.Q2 ∧ m2.kind = Msg2Kind.D2 ∧ m1.src = m2.src →
            m1.src ∈ s.FAULTY)

def messages_not_from_future (s : State) : Prop :=
  ∀ r ∈ s.ROUNDS,
    (∀ m ∈ Finmap.lookupD r s.msgs1,
        m.src ∈ s.CORRECT →
          (Finmap.lookupD m.src s.step ≠ Step.S1 → m.round ≤ Finmap.lookupD m.src s.round) ∧
            (Finmap.lookupD m.src s.step = Step.S1 → m.round < Finmap.lookupD m.src s.round)) ∧
      (∀ m ∈ Finmap.lookupD r s.msgs2,
        m.src ∈ s.CORRECT →
          (Finmap.lookupD m.src s.step = Step.S3 → m.round ≤ Finmap.lookupD m.src s.round) ∧
            (Finmap.lookupD m.src s.step ≠ Step.S3 → m.round < Finmap.lookupD m.src s.round))

def round_needs_sent_messages (s : State) : Prop :=
  ∀ id ∈ s.CORRECT,
    ∀ r ∈ s.ROUNDS,
      (r < Finmap.lookupD id s.round ∨
          (r = Finmap.lookupD id s.round ∧ Finmap.lookupD id s.step ≠ Step.S1) →
        ∃ m ∈ Finmap.lookupD r s.msgs1, m.src = id) ∧
        (r < Finmap.lookupD id s.round →
          ∃ m ∈ Finmap.lookupD r s.msgs2, m.src = id) ∧
          (r = Finmap.lookupD id s.round ∧ Finmap.lookupD id s.step = Step.S3 →
            ∃ m ∈ Finmap.lookupD r s.msgs2, m.src = id)

def decision_defines_value (s : State) : Prop :=
  ∀ id ∈ s.CORRECT,
    Finmap.lookupD id s.decision ≠ -1 →
      Finmap.lookupD id s.value = Finmap.lookupD id s.decision

def d2_requires_quorum (s : State) : Prop :=
  ∀ r ∈ s.ROUNDS,
    ∀ v ∈ values,
      (∃ m ∈ Finmap.lookupD r s.msgs2,
          m.kind = Msg2Kind.D2 ∧ m.value = v ∧ m.src ∈ s.CORRECT) →
        existsQuorum1 s r v

def q2_requires_no_quorum_faster (s : State) : Prop :=
  ∀ r ∈ s.ROUNDS,
    (∃ m ∈ Finmap.lookupD r s.msgs2, m.kind = Msg2Kind.Q2 ∧ m.src ∈ s.CORRECT) →
      let n0 :=
        Finset.card
          (Finset.filter (fun id => Msg1.mk r id 0 ∈ Finmap.lookupD r s.msgs1) s.CORRECT)
      let n1 :=
        Finset.card
          (Finset.filter (fun id => Msg1.mk r id 1 ∈ Finmap.lookupD r s.msgs1) s.CORRECT)
      let nf :=
        Finset.card
          (Finset.filter
            (fun id => id ∈ senders1 s (Finmap.lookupD r s.msgs1))
            s.FAULTY)
      ∃ x0 ∈ Finset.Icc 0 s.N,
        ∃ x1 ∈ Finset.Icc 0 s.N,
          x0 ≤ n0 ∧ x1 ≤ n1 ∧ x0 + x1 + nf ≥ s.N - s.T ∧
            2 * x0 ≤ s.N + s.T ∧ 2 * x1 ≤ s.N + s.T

def rounds_connection (s : State) : Prop :=
  ∀ r ∈ s.ROUNDS,
    r + 1 ∈ s.ROUNDS →
      supportedValues s r = ∅ ∨
        ∃ v ∈ supportedValues s r,
          ∀ m ∈ Finmap.lookupD (r + 1) s.msgs1,
            m.src ∈ s.CORRECT → m.value = v

def m1_requires_quorum (s : State) : Prop :=
  ∀ r ∈ s.ROUNDS,
    r ≠ 1 →
      (∃ m ∈ Finmap.lookupD r s.msgs1, m.src ∈ s.CORRECT) →
        Finset.card (senders2 s (Finmap.lookupD (r - 1) s.msgs2)) ≥ s.N - s.T

def value_on_quorum_less_ram (s : State) : Prop :=
  ∀ id ∈ s.CORRECT,
    let r := Finmap.lookupD id s.round
    r > 1 →
      let prevMsgs := Finmap.lookupD (r - 1) s.msgs2
      (2 * Finset.card (senders2 s (d2MsgsFor (Finmap.lookupD id s.value) prevMsgs)) >
          s.N + s.T) ∨
        (let n0 := Finset.card (d2MsgsFor 0 prevMsgs)
         let n1 := Finset.card (d2MsgsFor 1 prevMsgs)
         let nq := Finset.card (q2Msgs prevMsgs)
         ∃ x0 ∈ Finset.Icc 0 s.N,
           ∃ x1 ∈ Finset.Icc 0 s.N,
             x0 ≤ n0 ∧ x1 ≤ n1 ∧ x0 + x1 + nq ≥ s.N - s.T ∧
               2 * x0 ≤ s.N + s.T ∧ 2 * x1 ≤ s.N + s.T)

def cannot_jump_rounds_without_quorum (s : State) : Prop :=
  ∀ r ∈ s.ROUNDS,
    r + 1 ∈ s.ROUNDS →
      (∃ id ∈ s.CORRECT,
          Finmap.lookupD id s.round = r + 1 ∧ Finmap.lookupD id s.step = Step.S1) →
        Finset.card (senders2 s (Finmap.lookupD r s.msgs2)) ≥ s.N - s.T

def value_lock (s : State) : Prop :=
  ∀ id ∈ s.CORRECT,
    ∀ v ∈ values,
      Finmap.lookupD id s.round = 1 ∨
        Finmap.lookupD id s.round > 1 ∧
          (supportedValues s (Finmap.lookupD id s.round - 1) = ∅ ∨
            Finmap.lookupD id s.value ∈ supportedValues s (Finmap.lookupD id s.round - 1))

/-- Lean-local bridge: all non-bottom decisions made by correct processes agree.
This is weaker than the false current-value lock and matches the generated
agreement property's non-bottom branch. -/
def step3_local_decision_bottom (s : State) : Prop :=
  ∀ rid ∈ s.CORRECT,
    Finmap.lookupD rid s.step = Step.S3 →
      ∀ received ∈ Finset.powerset (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2),
        Finset.card
            (Finset.filter (fun id => ∃ m ∈ received, id = Msg2.src m)
              (s.CORRECT ∪ s.FAULTY)) =
          s.N - s.T →
          ((∀ v ∈ values,
              Finset.card
                  (Finset.filter
                    (fun id =>
                      ∃ m ∈
                          Finset.filter
                            (fun m => Msg2.kind m = Msg2Kind.D2 ∧ v = Msg2.value m)
                            received,
                        id = Msg2.src m)
                    (s.CORRECT ∪ s.FAULTY)) <
                s.T + 1) →
            Finmap.lookupD rid s.decision = -1) ∧
            (∀ v ∈ values,
              Finset.card
                  (Finset.filter
                    (fun id =>
                      ∃ m ∈
                          Finset.filter
                            (fun m => Msg2.kind m = Msg2Kind.D2 ∧ v = Msg2.value m)
                            received,
                        id = Msg2.src m)
                    (s.CORRECT ∪ s.FAULTY)) ≥
                s.T + 1 →
                ¬ 2 *
                    Finset.card
                      (Finset.filter
                        (fun id =>
                          ∃ m ∈
                              Finset.filter
                                (fun m => Msg2.kind m = Msg2Kind.D2 ∧ v = Msg2.value m)
                                received,
                            id = Msg2.src m)
                        (s.CORRECT ∪ s.FAULTY)) >
                  s.N + s.T →
                  Finmap.lookupD rid s.decision = -1)

/-- The 13 Apalache-verified core lemmas — the single inductive invariant.

Agreement (`agreement_inv`) is *not* a conjunct: it is a single-state consequence
of these 13 (see `agreement_inv_of_ind_inv_13`), so it need never be carried or
preserved. -/
def ind_inv_13 (s : State) : Prop :=
  no_equivocation1_by_correct s ∧
    no_equivocation2_by_correct s ∧
      messages_not_from_future s ∧
        round_needs_sent_messages s ∧
          decision_defines_value s ∧
            d2_requires_quorum s ∧
              q2_requires_no_quorum_faster s ∧
                rounds_connection s ∧
                  m1_requires_quorum s ∧
                    value_on_quorum_less_ram s ∧
                      cannot_jump_rounds_without_quorum s ∧
                        value_lock s ∧
          decision_requires_last_quorum_less_ram s

lemma correct_round_mem_of_type_ok {s : State}
    (htype : type_ok s) :
    ∀ id ∈ s.CORRECT, Finmap.lookupD id s.round ∈ s.ROUNDS := by
  intro id hid
  unfold type_ok at htype
  exact htype.2.2.1.2 id hid

def model_assumptions (s : State) : Prop :=
  assumptions_hold s ∧
    s.CORRECT ∩ s.FAULTY = ∅ ∧
      (∀ r ∈ s.ROUNDS, 1 ≤ r) ∧
        (∀ r ∈ s.ROUNDS, r ≠ 1 → r - 1 ∈ s.ROUNDS) ∧
          s.F ≤ s.T

def model_base_assumptions (s : State) : Prop :=
  assumptions_hold s ∧
    s.CORRECT ∩ s.FAULTY = ∅ ∧
      (∀ r ∈ s.ROUNDS, 1 ≤ r) ∧
        (∀ r ∈ s.ROUNDS, r ≠ 1 → r - 1 ∈ s.ROUNDS) ∧
          s.F ≤ s.T

lemma model_base_of_model
    {s : State}
    (hmodel : model_assumptions s) :
    model_base_assumptions s := by
  unfold model_assumptions at hmodel
  unfold model_base_assumptions
  rcases hmodel with ⟨hassumptions, hdisj, hround_pos, hround_pred, hFleT⟩
  exact ⟨hassumptions, hdisj, hround_pos, hround_pred, hFleT⟩

/-- The model's resilience bound `N > 5·T`, recovered from `assumptions_hold`. -/
lemma assumptions_N5T {s : State} (h : assumptions_hold s) : s.N > 5 * s.T := by
  unfold assumptions_hold at h; exact h.1

lemma model_N5T {s : State} (h : model_assumptions s) : s.N > 5 * s.T := by
  unfold model_assumptions at h; exact assumptions_N5T h.1

lemma senders1_mono {s : State} {msgs msgs' : Finset Msg1}
    (hsub : msgs ⊆ msgs') :
    senders1 s msgs ⊆ senders1 s msgs' := by
  intro rid hrid
  unfold senders1 at hrid ⊢
  simp only [Finset.mem_filter] at hrid ⊢
  rcases hrid with ⟨hall, m, hm, hsrc⟩
  exact ⟨hall, m, hsub hm, hsrc⟩

lemma senders1_mono_frame {s s' : State} {msgs msgs' : Finset Msg1}
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hsub : msgs ⊆ msgs') :
    senders1 s msgs ⊆ senders1 s' msgs' := by
  intro rid hrid
  unfold senders1 allReplicas at hrid ⊢
  rw [hcorrect, hfaulty]
  rcases Finset.mem_filter.mp hrid with ⟨hall, m, hm, hsrc⟩
  exact Finset.mem_filter.mpr ⟨hall, m, hsub hm, hsrc⟩

@[simp] lemma lookupD_insert_self {α β : Type} [DecidableEq α] [Inhabited β]
    (a : α) (b : β) (m : Finmap (fun _ : α => β)) :
    Finmap.lookupD a (Finmap.insert a b m) = b := by
  unfold Finmap.lookupD
  rw [Finmap.lookup_insert]
  simp

@[simp] lemma lookupD_insert_of_ne {α β : Type} [DecidableEq α] [Inhabited β]
    {a k : α} (h : a ≠ k) (b : β) (m : Finmap (fun _ : α => β)) :
    Finmap.lookupD a (Finmap.insert k b m) = Finmap.lookupD a m := by
  unfold Finmap.lookupD
  rw [Finmap.lookup_insert_of_ne]
  exact h

lemma msg1_round_eq_of_type_ok {s : State} {r : Int} {m : Msg1}
    (htype : type_ok s) (hr : r ∈ s.ROUNDS)
    (hm : m ∈ Finmap.lookupD r s.msgs1) :
    r = m.round := by
  unfold type_ok at htype
  rcases htype with ⟨_, _, _, _, hmsgs1, _⟩
  exact (hmsgs1 r hr m hm).2.1

lemma msg2_round_eq_of_type_ok {s : State} {r : Int} {m : Msg2}
    (htype : type_ok s) (hr : r ∈ s.ROUNDS)
    (hm : m ∈ Finmap.lookupD r s.msgs2) :
    r = m.round := by
  unfold type_ok at htype
  rcases htype with ⟨_, _, _, _, _, hmsgs2⟩
  exact (hmsgs2 r hr m hm).2.1

lemma step1_old_msg_from_sender_impossible
    {s : State} {rid : Int} {m : Msg1}
    (htype : type_ok s) (hfuture : messages_not_from_future s)
    (hrid : rid ∈ s.CORRECT)
    (hstep : Finmap.lookupD rid s.step = Step.S1)
    (hm : m ∈ Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs1)
    (hsrc : m.src = rid) :
    False := by
  have hround_mem : Finmap.lookupD rid s.round ∈ s.ROUNDS := by
    unfold type_ok at htype
    exact htype.2.2.1.2 rid hrid
  have hround_eq :=
    msg1_round_eq_of_type_ok (s := s) (r := Finmap.lookupD rid s.round)
      (m := m) htype hround_mem hm
  have hcorrect : m.src ∈ s.CORRECT := by
    rw [hsrc]
    exact hrid
  have hstep_m : Finmap.lookupD m.src s.step = Step.S1 := by
    rw [hsrc]
    exact hstep
  have hlt := ((hfuture (Finmap.lookupD rid s.round) hround_mem).1 m hm hcorrect).2 hstep_m
  rw [hsrc] at hlt
  omega

lemma step2_old_msg_from_sender_impossible
    {s : State} {rid : Int} {m : Msg2}
    (htype : type_ok s) (hfuture : messages_not_from_future s)
    (hrid : rid ∈ s.CORRECT)
    (hstep : Finmap.lookupD rid s.step = Step.S2)
    (hm : m ∈ Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2)
    (hsrc : m.src = rid) :
    False := by
  have hround_mem : Finmap.lookupD rid s.round ∈ s.ROUNDS := by
    unfold type_ok at htype
    exact htype.2.2.1.2 rid hrid
  have hround_eq :=
    msg2_round_eq_of_type_ok (s := s) (r := Finmap.lookupD rid s.round)
      (m := m) htype hround_mem hm
  have hcorrect : m.src ∈ s.CORRECT := by
    rw [hsrc]
    exact hrid
  have hstep_m : Finmap.lookupD m.src s.step ≠ Step.S3 := by
    rw [hsrc, hstep]
    decide
  have hlt := ((hfuture (Finmap.lookupD rid s.round) hround_mem).2 m hm hcorrect).2 hstep_m
  rw [hsrc] at hlt
  omega

lemma step1_preserves_no_equivocation1
    {s s' : State} {rid : Int}
    (htype : type_ok s)
    (hnoeq : no_equivocation1_by_correct s)
    (hfuture : messages_not_from_future s)
    (hrid : rid ∈ s.CORRECT)
    (hstep : Finmap.lookupD rid s.step = Step.S1)
    (hmsgs1 :
      s'.msgs1 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs1 ∪
            insert { round := Finmap.lookupD rid s.round, src := rid, value := Finmap.lookupD rid s.value }
              (∅ : Finset Msg1))
          s.msgs1)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hrounds : s'.ROUNDS = s.ROUNDS) :
    no_equivocation1_by_correct s' := by
  classical
  unfold no_equivocation1_by_correct
  intro r hr m1 hm1 m2 hm2 hsrc
  rw [hcorrect] at hsrc
  rw [hrounds] at hr
  rw [hmsgs1] at hm1 hm2
  by_cases hrid_round : r = Finmap.lookupD rid s.round
  · subst r
    simp [lookupD_insert_self] at hm1 hm2
    rcases hm1 with hm1old | hm1new
    · rcases hm2 with hm2old | hm2new
      · rw [hm1old, hm2old]
      · rw [hm1old] at hsrc
        exact False.elim
          (step1_old_msg_from_sender_impossible (s := s) (rid := rid) (m := m2)
            htype hfuture hrid hstep hm2new hsrc.2.symm)
    · rcases hm2 with hm2old | hm2new
      · rw [hm2old] at hsrc
        exact False.elim
          (step1_old_msg_from_sender_impossible (s := s) (rid := rid) (m := m1)
            htype hfuture hrid hstep hm1new hsrc.2)
      · exact hnoeq (Finmap.lookupD rid s.round) hr m1 hm1new m2 hm2new hsrc
  · rw [lookupD_insert_of_ne hrid_round] at hm1 hm2
    exact hnoeq r hr m1 hm1 m2 hm2 hsrc

lemma frame_no_equivocation1
    {s s' : State}
    (hnoeq : no_equivocation1_by_correct s)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1 : s'.msgs1 = s.msgs1) :
    no_equivocation1_by_correct s' := by
  unfold no_equivocation1_by_correct at hnoeq ⊢
  intro r hr m1 hm1 m2 hm2 hsrc
  rw [hcorrect] at hsrc
  rw [hrounds] at hr
  rw [hmsgs1] at hm1 hm2
  exact hnoeq r hr m1 hm1 m2 hm2 hsrc

lemma msg1_src_faulty_of_mem_faulty_step
    {s : State} {r : Int} {f : Finset Msg1} {m : Msg1}
    (hf :
      f ∈
        Finset.powerset
          (Finset.image (fun x => Msg1.mk r (x).1 (x).2)
            (Finset.product s.FAULTY (insert 0 (insert 1 (∅ : Finset Int))))))
    (hm : m ∈ f) :
    m.src ∈ s.FAULTY := by
  have hsubset := (Finset.mem_powerset.mp hf) hm
  rcases Finset.mem_image.mp hsubset with ⟨x, hx, rfl⟩
  exact (Finset.mem_product.mp hx).1

lemma msg1_src_not_correct_of_mem_faulty_step
    {s : State} {r : Int} {f : Finset Msg1} {m : Msg1}
    (hdisj : s.CORRECT ∩ s.FAULTY = ∅)
    (hf :
      f ∈
        Finset.powerset
          (Finset.image (fun x => Msg1.mk r (x).1 (x).2)
            (Finset.product s.FAULTY (insert 0 (insert 1 (∅ : Finset Int))))))
    (hm : m ∈ f) :
    m.src ∉ s.CORRECT := by
  intro hc
  have hfaulty := msg1_src_faulty_of_mem_faulty_step (s := s) hf hm
  have : m.src ∈ s.CORRECT ∩ s.FAULTY := Finset.mem_inter.mpr ⟨hc, hfaulty⟩
  simp [hdisj] at this

lemma msg2_d2_src_faulty_of_mem_faulty_step
    {s : State} {r : Int} {f : Finset Msg2} {m : Msg2}
    (hf :
      f ∈
        Finset.powerset
          (Finset.image (fun x => Msg2.mk Msg2Kind.D2 r (x).1 (x).2)
            (Finset.product s.FAULTY (insert 0 (insert 1 (∅ : Finset Int))))))
    (hm : m ∈ f) :
    m.src ∈ s.FAULTY := by
  have hsubset := (Finset.mem_powerset.mp hf) hm
  rcases Finset.mem_image.mp hsubset with ⟨x, hx, rfl⟩
  exact (Finset.mem_product.mp hx).1

lemma msg2_q2_src_faulty_of_mem_faulty_step
    {s : State} {r : Int} {f : Finset Msg2} {m : Msg2}
    (hf :
      f ∈
        Finset.powerset
          (Finset.image (fun src => Msg2.mk Msg2Kind.Q2 r src (-2)) s.FAULTY))
    (hm : m ∈ f) :
    m.src ∈ s.FAULTY := by
  have hsubset := (Finset.mem_powerset.mp hf) hm
  rcases Finset.mem_image.mp hsubset with ⟨src, hsrc, rfl⟩
  exact hsrc

lemma msg2_d2_src_not_correct_of_mem_faulty_step
    {s : State} {r : Int} {f : Finset Msg2} {m : Msg2}
    (hdisj : s.CORRECT ∩ s.FAULTY = ∅)
    (hf :
      f ∈
        Finset.powerset
          (Finset.image (fun x => Msg2.mk Msg2Kind.D2 r (x).1 (x).2)
            (Finset.product s.FAULTY (insert 0 (insert 1 (∅ : Finset Int))))))
    (hm : m ∈ f) :
    m.src ∉ s.CORRECT := by
  intro hc
  have hfaulty := msg2_d2_src_faulty_of_mem_faulty_step (s := s) hf hm
  have : m.src ∈ s.CORRECT ∩ s.FAULTY := Finset.mem_inter.mpr ⟨hc, hfaulty⟩
  simp [hdisj] at this

lemma msg2_q2_src_not_correct_of_mem_faulty_step
    {s : State} {r : Int} {f : Finset Msg2} {m : Msg2}
    (hdisj : s.CORRECT ∩ s.FAULTY = ∅)
    (hf :
      f ∈
        Finset.powerset
          (Finset.image (fun src => Msg2.mk Msg2Kind.Q2 r src (-2)) s.FAULTY))
    (hm : m ∈ f) :
    m.src ∉ s.CORRECT := by
  intro hc
  have hfaulty := msg2_q2_src_faulty_of_mem_faulty_step (s := s) hf hm
  have : m.src ∈ s.CORRECT ∩ s.FAULTY := Finset.mem_inter.mpr ⟨hc, hfaulty⟩
  simp [hdisj] at this

lemma faulty_step_preserves_no_equivocation1
    {s s' : State} {r : Int} {f1 : Finset Msg1}
    (hdisj : s.CORRECT ∩ s.FAULTY = ∅)
    (hnoeq : no_equivocation1_by_correct s)
    (hf1 :
      f1 ∈
        Finset.powerset
          (Finset.image (fun x => Msg1.mk r (x).1 (x).2)
            (Finset.product s.FAULTY (insert 0 (insert 1 (∅ : Finset Int))))))
    (hmsgs1 : s'.msgs1 = Finmap.insert r (Finmap.lookupD r s.msgs1 ∪ f1) s.msgs1)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hrounds : s'.ROUNDS = s.ROUNDS) :
    no_equivocation1_by_correct s' := by
  classical
  unfold no_equivocation1_by_correct at hnoeq ⊢
  intro r0 hr0 m1 hm1 m2 hm2 hsrc
  rw [hcorrect] at hsrc
  rw [hrounds] at hr0
  rw [hmsgs1] at hm1 hm2
  by_cases hr : r0 = r
  · subst r0
    simp [lookupD_insert_self] at hm1 hm2
    rcases hm1 with hm1old | hm1faulty
    · rcases hm2 with hm2old | hm2faulty
      · exact hnoeq r hr0 m1 hm1old m2 hm2old hsrc
      · have hnot2 := msg1_src_not_correct_of_mem_faulty_step (s := s) hdisj hf1 hm2faulty
        have hnot1 : m1.src ∉ s.CORRECT := by
          intro hc
          apply hnot2
          rw [← hsrc.2]
          exact hc
        exact False.elim (hnot1 hsrc.1)
    · have hnot1 := msg1_src_not_correct_of_mem_faulty_step (s := s) hdisj hf1 hm1faulty
      exact False.elim (hnot1 hsrc.1)
  · rw [lookupD_insert_of_ne hr] at hm1 hm2
    exact hnoeq r0 hr0 m1 hm1 m2 hm2 hsrc

lemma frame_no_equivocation2
    {s s' : State}
    (hnoeq : no_equivocation2_by_correct s)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    no_equivocation2_by_correct s' := by
  unfold no_equivocation2_by_correct at hnoeq ⊢
  intro r hr m1 hm1 m2 hm2
  rw [hcorrect, hfaulty]
  rw [hrounds] at hr
  rw [hmsgs2] at hm1 hm2
  exact hnoeq r hr m1 hm1 m2 hm2

lemma faulty_step_preserves_no_equivocation2
    {s s' : State} {r : Int} {f2d f2q : Finset Msg2}
    (hdisj : s.CORRECT ∩ s.FAULTY = ∅)
    (hnoeq : no_equivocation2_by_correct s)
    (hf2d :
      f2d ∈
        Finset.powerset
          (Finset.image (fun x => Msg2.mk Msg2Kind.D2 r (x).1 (x).2)
            (Finset.product s.FAULTY (insert 0 (insert 1 (∅ : Finset Int))))))
    (hf2q :
      f2q ∈
        Finset.powerset
          (Finset.image (fun src => Msg2.mk Msg2Kind.Q2 r src (-2)) s.FAULTY))
    (hmsgs2 : s'.msgs2 = Finmap.insert r (Finmap.lookupD r s.msgs2 ∪ (f2d ∪ f2q)) s.msgs2)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS) :
    no_equivocation2_by_correct s' := by
  classical
  unfold no_equivocation2_by_correct at hnoeq ⊢
  intro r0 hr0 m1 hm1 m2 hm2
  rw [hcorrect, hfaulty]
  rw [hrounds] at hr0
  rw [hmsgs2] at hm1 hm2
  by_cases hr : r0 = r
  · subst r0
    simp [lookupD_insert_self] at hm1 hm2
    constructor
    · intro hD hc
      rcases hm1 with hm1old | hm1new
      · rcases hm2 with hm2old | hm2new
        · exact (hnoeq r hr0 m1 hm1old m2 hm2old).1 hD hc
        · rcases hm2new with hm2d | hm2q
          · have hnot2 := msg2_d2_src_not_correct_of_mem_faulty_step (s := s) hdisj hf2d hm2d
            have hnot1 : m1.src ∉ s.CORRECT := by
              intro hc1
              apply hnot2
              rw [← hD.2.2]
              exact hc1
            exact False.elim (hnot1 hc)
          · have hnot2 := msg2_q2_src_not_correct_of_mem_faulty_step (s := s) hdisj hf2q hm2q
            have hnot1 : m1.src ∉ s.CORRECT := by
              intro hc1
              apply hnot2
              rw [← hD.2.2]
              exact hc1
            exact False.elim (hnot1 hc)
      · rcases hm1new with hm1d | hm1q
        · have hnot1 := msg2_d2_src_not_correct_of_mem_faulty_step (s := s) hdisj hf2d hm1d
          exact False.elim (hnot1 hc)
        · have hnot1 := msg2_q2_src_not_correct_of_mem_faulty_step (s := s) hdisj hf2q hm1q
          exact False.elim (hnot1 hc)
    · intro hQ
      rcases hm1 with hm1old | hm1new
      · rcases hm2 with hm2old | hm2new
        · exact (hnoeq r hr0 m1 hm1old m2 hm2old).2 hQ
        · rcases hm2new with hm2d | hm2q
          · have hfaulty2 := msg2_d2_src_faulty_of_mem_faulty_step (s := s) hf2d hm2d
            rw [hQ.2.2]
            exact hfaulty2
          · have hfaulty2 := msg2_q2_src_faulty_of_mem_faulty_step (s := s) hf2q hm2q
            rw [hQ.2.2]
            exact hfaulty2
      · rcases hm1new with hm1d | hm1q
        · have hfaulty1 := msg2_d2_src_faulty_of_mem_faulty_step (s := s) hf2d hm1d
          exact hfaulty1
        · have hfaulty1 := msg2_q2_src_faulty_of_mem_faulty_step (s := s) hf2q hm1q
          exact hfaulty1
  · rw [lookupD_insert_of_ne hr] at hm1 hm2
    exact hnoeq r0 hr0 m1 hm1 m2 hm2

lemma step2_d2_preserves_no_equivocation2
    {s s' : State} {rid v : Int}
    (htype : type_ok s)
    (hnoeq : no_equivocation2_by_correct s)
    (hfuture : messages_not_from_future s)
    (hrid : rid ∈ s.CORRECT)
    (hstep : Finmap.lookupD rid s.step = Step.S2)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 ∪
            insert { kind := Msg2Kind.D2, round := Finmap.lookupD rid s.round, src := rid, value := v }
              (∅ : Finset Msg2))
          s.msgs2)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS) :
    no_equivocation2_by_correct s' := by
  classical
  unfold no_equivocation2_by_correct at hnoeq ⊢
  intro r hr m1 hm1 m2 hm2
  rw [hcorrect, hfaulty]
  rw [hrounds] at hr
  rw [hmsgs2] at hm1 hm2
  by_cases hrid_round : r = Finmap.lookupD rid s.round
  · subst r
    simp [lookupD_insert_self] at hm1 hm2
    constructor
    · intro hD hc
      rcases hm1 with hm1new | hm1old
      · rcases hm2 with hm2new | hm2old
        · rw [hm1new, hm2new]
        · rw [hm1new] at hD
          exact False.elim
            (step2_old_msg_from_sender_impossible (s := s) (rid := rid) (m := m2)
              htype hfuture hrid hstep hm2old hD.2.2.symm)
      · rcases hm2 with hm2new | hm2old
        · rw [hm2new] at hD
          exact False.elim
            (step2_old_msg_from_sender_impossible (s := s) (rid := rid) (m := m1)
              htype hfuture hrid hstep hm1old hD.2.2)
        · exact (hnoeq (Finmap.lookupD rid s.round) hr m1 hm1old m2 hm2old).1 hD hc
    · intro hQ
      rcases hm1 with hm1new | hm1old
      · rw [hm1new] at hQ
        simp at hQ
      · rcases hm2 with hm2new | hm2old
        · rw [hm2new] at hQ
          exact False.elim
            (step2_old_msg_from_sender_impossible (s := s) (rid := rid) (m := m1)
              htype hfuture hrid hstep hm1old hQ.2.2)
        · exact (hnoeq (Finmap.lookupD rid s.round) hr m1 hm1old m2 hm2old).2 hQ
  · rw [lookupD_insert_of_ne hrid_round] at hm1 hm2
    exact hnoeq r hr m1 hm1 m2 hm2

lemma step2_q2_preserves_no_equivocation2
    {s s' : State} {rid : Int}
    (htype : type_ok s)
    (hnoeq : no_equivocation2_by_correct s)
    (hfuture : messages_not_from_future s)
    (hrid : rid ∈ s.CORRECT)
    (hstep : Finmap.lookupD rid s.step = Step.S2)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 ∪
            insert { kind := Msg2Kind.Q2, round := Finmap.lookupD rid s.round, src := rid, value := -2 }
              (∅ : Finset Msg2))
          s.msgs2)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS) :
    no_equivocation2_by_correct s' := by
  classical
  unfold no_equivocation2_by_correct at hnoeq ⊢
  intro r hr m1 hm1 m2 hm2
  rw [hcorrect, hfaulty]
  rw [hrounds] at hr
  rw [hmsgs2] at hm1 hm2
  by_cases hrid_round : r = Finmap.lookupD rid s.round
  · subst r
    simp [lookupD_insert_self] at hm1 hm2
    constructor
    · intro hD hc
      rcases hm1 with hm1new | hm1old
      · rw [hm1new] at hD
        simp at hD
      · rcases hm2 with hm2new | hm2old
        · rw [hm2new] at hD
          simp at hD
        · exact (hnoeq (Finmap.lookupD rid s.round) hr m1 hm1old m2 hm2old).1 hD hc
    · intro hQ
      rcases hm1 with hm1new | hm1old
      · rcases hm2 with hm2new | hm2old
        · rw [hm2new] at hQ
          simp at hQ
        · rw [hm1new] at hQ
          exact False.elim
            (step2_old_msg_from_sender_impossible (s := s) (rid := rid) (m := m2)
              htype hfuture hrid hstep hm2old hQ.2.2.symm)
      · rcases hm2 with hm2new | hm2old
        · rw [hm2new] at hQ
          simp at hQ
        · exact (hnoeq (Finmap.lookupD rid s.round) hr m1 hm1old m2 hm2old).2 hQ
  · rw [lookupD_insert_of_ne hrid_round] at hm1 hm2
    exact hnoeq r hr m1 hm1 m2 hm2

lemma step1_preserves_messages_not_from_future
    {s s' : State} {rid : Int}
    (hfuture : messages_not_from_future s)
    (hstep_old : Finmap.lookupD rid s.step = Step.S1)
    (hmsgs1 :
      s'.msgs1 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs1 ∪
            insert { round := Finmap.lookupD rid s.round, src := rid, value := Finmap.lookupD rid s.value }
              (∅ : Finset Msg1))
          s.msgs1)
    (hstep : s'.step = Finmap.insert rid Step.S2 s.step)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hround : s'.round = s.round)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    messages_not_from_future s' := by
  classical
  unfold messages_not_from_future at hfuture ⊢
  intro r hr
  rw [hrounds] at hr
  constructor
  · intro m hm hc
    rw [hcorrect] at hc
    rw [hmsgs1] at hm
    by_cases hrid_round : r = Finmap.lookupD rid s.round
    · subst r
      simp [lookupD_insert_self] at hm
      rcases hm with hmnew | hmold
      · rw [hmnew]
        constructor
        · intro _
          rw [hround]
        · intro hs1
          rw [hstep] at hs1
          simp at hs1
      · by_cases hsrc : m.src = rid
        · have hold := ((hfuture (Finmap.lookupD rid s.round) hr).1 m hmold hc).2
          have hlt := hold (by rw [hsrc, hstep_old])
          constructor
          · intro _
            rw [hround]
            omega
          · intro hs1
            rw [hstep, hsrc] at hs1
            simp at hs1
        · have hold := (hfuture (Finmap.lookupD rid s.round) hr).1 m hmold hc
          constructor
          · intro hne
            have hne_old : Finmap.lookupD m.src s.step ≠ Step.S1 := by
              rw [hstep] at hne
              rw [lookupD_insert_of_ne hsrc] at hne
              exact hne
            rw [hround]
            exact hold.1 hne_old
          · intro hs1
            have hs1_old : Finmap.lookupD m.src s.step = Step.S1 := by
              rw [hstep] at hs1
              rw [lookupD_insert_of_ne hsrc] at hs1
              exact hs1
            rw [hround]
            exact hold.2 hs1_old
    · rw [lookupD_insert_of_ne hrid_round] at hm
      by_cases hsrc : m.src = rid
      · have hold := ((hfuture r hr).1 m hm hc).2
        have hlt := hold (by rw [hsrc, hstep_old])
        constructor
        · intro _
          rw [hround]
          omega
        · intro hs1
          rw [hstep, hsrc] at hs1
          simp at hs1
      · have hold := (hfuture r hr).1 m hm hc
        constructor
        · intro hne
          have hne_old : Finmap.lookupD m.src s.step ≠ Step.S1 := by
            rw [hstep] at hne
            rw [lookupD_insert_of_ne hsrc] at hne
            exact hne
          rw [hround]
          exact hold.1 hne_old
        · intro hs1
          have hs1_old : Finmap.lookupD m.src s.step = Step.S1 := by
            rw [hstep] at hs1
            rw [lookupD_insert_of_ne hsrc] at hs1
            exact hs1
          rw [hround]
          exact hold.2 hs1_old
  · intro m hm hc
    rw [hcorrect] at hc
    rw [hmsgs2] at hm
    by_cases hsrc : m.src = rid
    · have hold := ((hfuture r hr).2 m hm hc).2
      have hlt := hold (by rw [hsrc, hstep_old]; decide)
      constructor
      · intro hs3
        rw [hstep, hsrc] at hs3
        simp at hs3
      · intro _
        rw [hround]
        omega
    · have hold := (hfuture r hr).2 m hm hc
      constructor
      · intro hs3
        have hs3_old : Finmap.lookupD m.src s.step = Step.S3 := by
          rw [hstep] at hs3
          rw [lookupD_insert_of_ne hsrc] at hs3
          exact hs3
        rw [hround]
        exact hold.1 hs3_old
      · intro hne
        have hne_old : Finmap.lookupD m.src s.step ≠ Step.S3 := by
          rw [hstep] at hne
          rw [lookupD_insert_of_ne hsrc] at hne
          exact hne
        rw [hround]
        exact hold.2 hne_old

lemma step2_preserves_messages_not_from_future
    {s s' : State} {rid : Int} {newMsg : Msg2}
    (hfuture : messages_not_from_future s)
    (hstep_old : Finmap.lookupD rid s.step = Step.S2)
    (hnew_src : newMsg.src = rid)
    (hnew_round : newMsg.round = Finmap.lookupD rid s.round)
    (hmsgs1 : s'.msgs1 = s.msgs1)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 ∪
            insert newMsg (∅ : Finset Msg2))
          s.msgs2)
    (hstep : s'.step = Finmap.insert rid Step.S3 s.step)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hround : s'.round = s.round) :
    messages_not_from_future s' := by
  classical
  unfold messages_not_from_future at hfuture ⊢
  intro r hr
  rw [hrounds] at hr
  constructor
  · intro m hm hc
    rw [hcorrect] at hc
    rw [hmsgs1] at hm
    by_cases hsrc : m.src = rid
    · have hold := ((hfuture r hr).1 m hm hc).1
      have hle := hold (by rw [hsrc, hstep_old]; decide)
      constructor
      · intro _
        rw [hround]
        exact hle
      · intro hs1
        rw [hstep, hsrc] at hs1
        simp at hs1
    · have hold := (hfuture r hr).1 m hm hc
      constructor
      · intro hne
        have hne_old : Finmap.lookupD m.src s.step ≠ Step.S1 := by
          rw [hstep] at hne
          rw [lookupD_insert_of_ne hsrc] at hne
          exact hne
        rw [hround]
        exact hold.1 hne_old
      · intro hs1
        have hs1_old : Finmap.lookupD m.src s.step = Step.S1 := by
          rw [hstep] at hs1
          rw [lookupD_insert_of_ne hsrc] at hs1
          exact hs1
        rw [hround]
        exact hold.2 hs1_old
  · intro m hm hc
    rw [hcorrect] at hc
    rw [hmsgs2] at hm
    by_cases hrid_round : r = Finmap.lookupD rid s.round
    · subst r
      simp [lookupD_insert_self] at hm
      rcases hm with hmnew | hmold
      · rw [hmnew, hnew_src, hnew_round]
        constructor
        · intro _
          rw [hround]
        · intro hne
          rw [hstep] at hne
          simp at hne
      · by_cases hsrc : m.src = rid
        · have hold := ((hfuture (Finmap.lookupD rid s.round) hr).2 m hmold hc).2
          have hlt := hold (by rw [hsrc, hstep_old]; decide)
          constructor
          · intro _
            rw [hround]
            omega
          · intro hne
            rw [hstep, hsrc] at hne
            simp at hne
        · have hold := (hfuture (Finmap.lookupD rid s.round) hr).2 m hmold hc
          constructor
          · intro hs3
            have hs3_old : Finmap.lookupD m.src s.step = Step.S3 := by
              rw [hstep] at hs3
              rw [lookupD_insert_of_ne hsrc] at hs3
              exact hs3
            rw [hround]
            exact hold.1 hs3_old
          · intro hne
            have hne_old : Finmap.lookupD m.src s.step ≠ Step.S3 := by
              rw [hstep] at hne
              rw [lookupD_insert_of_ne hsrc] at hne
              exact hne
            rw [hround]
            exact hold.2 hne_old
    · rw [lookupD_insert_of_ne hrid_round] at hm
      by_cases hsrc : m.src = rid
      · have hold := ((hfuture r hr).2 m hm hc).2
        have hlt := hold (by rw [hsrc, hstep_old]; decide)
        constructor
        · intro _
          rw [hround]
          omega
        · intro hne
          rw [hstep, hsrc] at hne
          simp at hne
      · have hold := (hfuture r hr).2 m hm hc
        constructor
        · intro hs3
          have hs3_old : Finmap.lookupD m.src s.step = Step.S3 := by
            rw [hstep] at hs3
            rw [lookupD_insert_of_ne hsrc] at hs3
            exact hs3
          rw [hround]
          exact hold.1 hs3_old
        · intro hne
          have hne_old : Finmap.lookupD m.src s.step ≠ Step.S3 := by
            rw [hstep] at hne
            rw [lookupD_insert_of_ne hsrc] at hne
            exact hne
          rw [hround]
          exact hold.2 hne_old

lemma step2_d2_preserves_messages_not_from_future
    {s s' : State} {rid v : Int}
    (hfuture : messages_not_from_future s)
    (hstep_old : Finmap.lookupD rid s.step = Step.S2)
    (hmsgs1 : s'.msgs1 = s.msgs1)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 ∪
            insert { kind := Msg2Kind.D2, round := Finmap.lookupD rid s.round, src := rid, value := v }
              (∅ : Finset Msg2))
          s.msgs2)
    (hstep : s'.step = Finmap.insert rid Step.S3 s.step)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hround : s'.round = s.round) :
    messages_not_from_future s' := by
  exact step2_preserves_messages_not_from_future
    (s := s) (s' := s') (rid := rid)
    (newMsg := { kind := Msg2Kind.D2, round := Finmap.lookupD rid s.round, src := rid, value := v })
    hfuture hstep_old rfl rfl hmsgs1 hmsgs2 hstep hcorrect hrounds hround

lemma step2_q2_preserves_messages_not_from_future
    {s s' : State} {rid : Int}
    (hfuture : messages_not_from_future s)
    (hstep_old : Finmap.lookupD rid s.step = Step.S2)
    (hmsgs1 : s'.msgs1 = s.msgs1)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 ∪
            insert { kind := Msg2Kind.Q2, round := Finmap.lookupD rid s.round, src := rid, value := -2 }
              (∅ : Finset Msg2))
          s.msgs2)
    (hstep : s'.step = Finmap.insert rid Step.S3 s.step)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hround : s'.round = s.round) :
    messages_not_from_future s' := by
  exact step2_preserves_messages_not_from_future
    (s := s) (s' := s') (rid := rid)
    (newMsg := { kind := Msg2Kind.Q2, round := Finmap.lookupD rid s.round, src := rid, value := -2 })
    hfuture hstep_old rfl rfl hmsgs1 hmsgs2 hstep hcorrect hrounds hround

lemma step3_preserves_messages_not_from_future
    {s s' : State} {rid : Int}
    (hfuture : messages_not_from_future s)
    (hstep_old : Finmap.lookupD rid s.step = Step.S3)
    (hmsgs1 : s'.msgs1 = s.msgs1)
    (hmsgs2 : s'.msgs2 = s.msgs2)
    (hstep : s'.step = Finmap.insert rid Step.S1 s.step)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hround : s'.round = Finmap.insert rid (Finmap.lookupD rid s.round + 1) s.round) :
    messages_not_from_future s' := by
  classical
  unfold messages_not_from_future at hfuture ⊢
  intro r hr
  rw [hrounds] at hr
  constructor
  · intro m hm hc
    rw [hcorrect] at hc
    rw [hmsgs1] at hm
    by_cases hsrc : m.src = rid
    · have hold := ((hfuture r hr).1 m hm hc).1
      have hle := hold (by rw [hsrc, hstep_old]; decide)
      rw [hsrc] at hle
      constructor
      · intro hne
        rw [hstep, hsrc] at hne
        simp at hne
      · intro _
        rw [hround, hsrc]
        simp [lookupD_insert_self]
        omega
    · have hold := (hfuture r hr).1 m hm hc
      constructor
      · intro hne
        have hne_old : Finmap.lookupD m.src s.step ≠ Step.S1 := by
          rw [hstep] at hne
          rw [lookupD_insert_of_ne hsrc] at hne
          exact hne
        rw [hround, lookupD_insert_of_ne hsrc]
        exact hold.1 hne_old
      · intro hs1
        have hs1_old : Finmap.lookupD m.src s.step = Step.S1 := by
          rw [hstep] at hs1
          rw [lookupD_insert_of_ne hsrc] at hs1
          exact hs1
        rw [hround, lookupD_insert_of_ne hsrc]
        exact hold.2 hs1_old
  · intro m hm hc
    rw [hcorrect] at hc
    rw [hmsgs2] at hm
    by_cases hsrc : m.src = rid
    · have hold := ((hfuture r hr).2 m hm hc).1
      have hle := hold (by rw [hsrc, hstep_old])
      rw [hsrc] at hle
      constructor
      · intro hs3
        rw [hstep, hsrc] at hs3
        simp at hs3
      · intro _
        rw [hround, hsrc]
        simp [lookupD_insert_self]
        omega
    · have hold := (hfuture r hr).2 m hm hc
      constructor
      · intro hs3
        have hs3_old : Finmap.lookupD m.src s.step = Step.S3 := by
          rw [hstep] at hs3
          rw [lookupD_insert_of_ne hsrc] at hs3
          exact hs3
        rw [hround, lookupD_insert_of_ne hsrc]
        exact hold.1 hs3_old
      · intro hne
        have hne_old : Finmap.lookupD m.src s.step ≠ Step.S3 := by
          rw [hstep] at hne
          rw [lookupD_insert_of_ne hsrc] at hne
          exact hne
        rw [hround, lookupD_insert_of_ne hsrc]
        exact hold.2 hne_old

lemma faulty_step_preserves_messages_not_from_future
    {s s' : State} {r : Int} {f1 : Finset Msg1} {f2d f2q : Finset Msg2}
    (hdisj : s.CORRECT ∩ s.FAULTY = ∅)
    (hfuture : messages_not_from_future s)
    (hf1 :
      f1 ∈
        Finset.powerset
          (Finset.image (fun x => Msg1.mk r (x).1 (x).2)
            (Finset.product s.FAULTY (insert 0 (insert 1 (∅ : Finset Int))))))
    (hf2d :
      f2d ∈
        Finset.powerset
          (Finset.image (fun x => Msg2.mk Msg2Kind.D2 r (x).1 (x).2)
            (Finset.product s.FAULTY (insert 0 (insert 1 (∅ : Finset Int))))))
    (hf2q :
      f2q ∈
        Finset.powerset
          (Finset.image (fun src => Msg2.mk Msg2Kind.Q2 r src (-2)) s.FAULTY))
    (hmsgs1 : s'.msgs1 = Finmap.insert r (Finmap.lookupD r s.msgs1 ∪ f1) s.msgs1)
    (hmsgs2 : s'.msgs2 = Finmap.insert r (Finmap.lookupD r s.msgs2 ∪ (f2d ∪ f2q)) s.msgs2)
    (hstep : s'.step = s.step)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hround : s'.round = s.round) :
    messages_not_from_future s' := by
  classical
  unfold messages_not_from_future at hfuture ⊢
  intro r0 hr0
  rw [hrounds] at hr0
  constructor
  · intro m hm hc
    rw [hcorrect] at hc
    rw [hmsgs1] at hm
    by_cases hr : r0 = r
    · subst r0
      simp [lookupD_insert_self] at hm
      rcases hm with hmold | hmfaulty
      · have hold := (hfuture r hr0).1 m hmold hc
        constructor
        · intro hne
          rw [hstep] at hne
          rw [hround]
          exact hold.1 hne
        · intro hs1
          rw [hstep] at hs1
          rw [hround]
          exact hold.2 hs1
      · have hnot := msg1_src_not_correct_of_mem_faulty_step (s := s) hdisj hf1 hmfaulty
        exact False.elim (hnot hc)
    · rw [lookupD_insert_of_ne hr] at hm
      have hold := (hfuture r0 hr0).1 m hm hc
      constructor
      · intro hne
        rw [hstep] at hne
        rw [hround]
        exact hold.1 hne
      · intro hs1
        rw [hstep] at hs1
        rw [hround]
        exact hold.2 hs1
  · intro m hm hc
    rw [hcorrect] at hc
    rw [hmsgs2] at hm
    by_cases hr : r0 = r
    · subst r0
      simp [lookupD_insert_self] at hm
      rcases hm with hmold | hmnew
      · have hold := (hfuture r hr0).2 m hmold hc
        constructor
        · intro hs3
          rw [hstep] at hs3
          rw [hround]
          exact hold.1 hs3
        · intro hne
          rw [hstep] at hne
          rw [hround]
          exact hold.2 hne
      · rcases hmnew with hmd | hmq
        · have hnot := msg2_d2_src_not_correct_of_mem_faulty_step (s := s) hdisj hf2d hmd
          exact False.elim (hnot hc)
        · have hnot := msg2_q2_src_not_correct_of_mem_faulty_step (s := s) hdisj hf2q hmq
          exact False.elim (hnot hc)
    · rw [lookupD_insert_of_ne hr] at hm
      have hold := (hfuture r0 hr0).2 m hm hc
      constructor
      · intro hs3
        rw [hstep] at hs3
        rw [hround]
        exact hold.1 hs3
      · intro hne
        rw [hstep] at hne
        rw [hround]
        exact hold.2 hne

lemma step1_preserves_round_needs_sent_messages
    {s s' : State} {rid : Int}
    (hroundNeeds : round_needs_sent_messages s)
    (hmsgs1 :
      s'.msgs1 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs1 ∪
            insert { round := Finmap.lookupD rid s.round, src := rid, value := Finmap.lookupD rid s.value }
              (∅ : Finset Msg1))
          s.msgs1)
    (hmsgs2 : s'.msgs2 = s.msgs2)
    (hstep : s'.step = Finmap.insert rid Step.S2 s.step)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hround : s'.round = s.round) :
    round_needs_sent_messages s' := by
  classical
  unfold round_needs_sent_messages at hroundNeeds ⊢
  intro id hid r hr
  rw [hcorrect] at hid
  rw [hrounds] at hr
  constructor
  · intro hprem
    rw [hround] at hprem
    by_cases hsrc : id = rid
    · subst id
      rw [hmsgs1]
      by_cases hrid_round : r = Finmap.lookupD rid s.round
      · subst r
        refine ⟨{ round := Finmap.lookupD rid s.round, src := rid, value := Finmap.lookupD rid s.value }, ?_, rfl⟩
        simp [lookupD_insert_self]
      · have oldPrem :
            r < Finmap.lookupD rid s.round ∨
              (r = Finmap.lookupD rid s.round ∧ Finmap.lookupD rid s.step ≠ Step.S1) := by
          rcases hprem with hlt | heq
          · exact Or.inl hlt
          · exact False.elim (hrid_round heq.1)
        rcases (hroundNeeds rid hid r hr).1 oldPrem with ⟨m, hm, hmsrc⟩
        refine ⟨m, ?_, hmsrc⟩
        rw [lookupD_insert_of_ne hrid_round]
        exact hm
    · have hsrc_ne : id ≠ rid := hsrc
      have oldPrem :
          r < Finmap.lookupD id s.round ∨
            (r = Finmap.lookupD id s.round ∧ Finmap.lookupD id s.step ≠ Step.S1) := by
        rw [hstep] at hprem
        rw [lookupD_insert_of_ne hsrc_ne] at hprem
        exact hprem
      rcases (hroundNeeds id hid r hr).1 oldPrem with ⟨m, hm, hmsrc⟩
      refine ⟨m, ?_, hmsrc⟩
      rw [hmsgs1]
      by_cases hrid_round : r = Finmap.lookupD rid s.round
      · subst r
        simp [lookupD_insert_self, hm]
      · rw [lookupD_insert_of_ne hrid_round]
        exact hm
  · constructor
    · intro hlt
      rw [hround] at hlt
      rcases (hroundNeeds id hid r hr).2.1 hlt with ⟨m, hm, hmsrc⟩
      refine ⟨m, ?_, hmsrc⟩
      rw [hmsgs2]
      exact hm
    · intro hprem
      rw [hround] at hprem
      by_cases hsrc : id = rid
      · subst id
        rw [hstep] at hprem
        simp [lookupD_insert_self] at hprem
      · have hsrc_ne : id ≠ rid := hsrc
        have oldPrem :
            r = Finmap.lookupD id s.round ∧ Finmap.lookupD id s.step = Step.S3 := by
          rw [hstep] at hprem
          rw [lookupD_insert_of_ne hsrc_ne] at hprem
          exact hprem
        rcases (hroundNeeds id hid r hr).2.2 oldPrem with ⟨m, hm, hmsrc⟩
        refine ⟨m, ?_, hmsrc⟩
        rw [hmsgs2]
        exact hm

lemma step2_preserves_round_needs_sent_messages
    {s s' : State} {rid : Int} {newMsg : Msg2}
    (hroundNeeds : round_needs_sent_messages s)
    (hstep_old : Finmap.lookupD rid s.step = Step.S2)
    (hnew_src : newMsg.src = rid)
    (hmsgs1 : s'.msgs1 = s.msgs1)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 ∪
            insert newMsg (∅ : Finset Msg2))
          s.msgs2)
    (hstep : s'.step = Finmap.insert rid Step.S3 s.step)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hround : s'.round = s.round) :
    round_needs_sent_messages s' := by
  classical
  unfold round_needs_sent_messages at hroundNeeds ⊢
  intro id hid r hr
  rw [hcorrect] at hid
  rw [hrounds] at hr
  constructor
  · intro hprem
    rw [hround] at hprem
    have oldPrem :
        r < Finmap.lookupD id s.round ∨
          (r = Finmap.lookupD id s.round ∧ Finmap.lookupD id s.step ≠ Step.S1) := by
      by_cases hsrc : id = rid
      · subst id
        rcases hprem with hlt | heq
        · exact Or.inl hlt
        · exact Or.inr ⟨heq.1, by rw [hstep_old]; decide⟩
      · rw [hstep] at hprem
        rw [lookupD_insert_of_ne hsrc] at hprem
        exact hprem
    rcases (hroundNeeds id hid r hr).1 oldPrem with ⟨m, hm, hmsrc⟩
    refine ⟨m, ?_, hmsrc⟩
    rw [hmsgs1]
    exact hm
  · constructor
    · intro hlt
      rw [hround] at hlt
      rcases (hroundNeeds id hid r hr).2.1 hlt with ⟨m, hm, hmsrc⟩
      refine ⟨m, ?_, hmsrc⟩
      rw [hmsgs2]
      by_cases hrid_round : r = Finmap.lookupD rid s.round
      · subst r
        simp [lookupD_insert_self, hm]
      · rw [lookupD_insert_of_ne hrid_round]
        exact hm
    · intro hprem
      rw [hround] at hprem
      by_cases hsrc : id = rid
      · subst id
        rw [hstep] at hprem
        have hround_eq : r = Finmap.lookupD rid s.round := hprem.1
        subst r
        refine ⟨newMsg, ?_, hnew_src⟩
        rw [hmsgs2]
        simp [lookupD_insert_self]
      · have hsrc_ne : id ≠ rid := hsrc
        have oldPrem :
            r = Finmap.lookupD id s.round ∧ Finmap.lookupD id s.step = Step.S3 := by
          rw [hstep] at hprem
          rw [lookupD_insert_of_ne hsrc_ne] at hprem
          exact hprem
        rcases (hroundNeeds id hid r hr).2.2 oldPrem with ⟨m, hm, hmsrc⟩
        refine ⟨m, ?_, hmsrc⟩
        rw [hmsgs2]
        by_cases hrid_round : r = Finmap.lookupD rid s.round
        · subst r
          simp [lookupD_insert_self, hm]
        · rw [lookupD_insert_of_ne hrid_round]
          exact hm

lemma step2_d2_preserves_round_needs_sent_messages
    {s s' : State} {rid v : Int}
    (hroundNeeds : round_needs_sent_messages s)
    (hstep_old : Finmap.lookupD rid s.step = Step.S2)
    (hmsgs1 : s'.msgs1 = s.msgs1)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 ∪
            insert { kind := Msg2Kind.D2, round := Finmap.lookupD rid s.round, src := rid, value := v }
              (∅ : Finset Msg2))
          s.msgs2)
    (hstep : s'.step = Finmap.insert rid Step.S3 s.step)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hround : s'.round = s.round) :
    round_needs_sent_messages s' := by
  exact step2_preserves_round_needs_sent_messages
    (s := s) (s' := s') (rid := rid)
    (newMsg := { kind := Msg2Kind.D2, round := Finmap.lookupD rid s.round, src := rid, value := v })
    hroundNeeds hstep_old rfl hmsgs1 hmsgs2 hstep hcorrect hrounds hround

lemma step2_q2_preserves_round_needs_sent_messages
    {s s' : State} {rid : Int}
    (hroundNeeds : round_needs_sent_messages s)
    (hstep_old : Finmap.lookupD rid s.step = Step.S2)
    (hmsgs1 : s'.msgs1 = s.msgs1)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 ∪
            insert { kind := Msg2Kind.Q2, round := Finmap.lookupD rid s.round, src := rid, value := -2 }
              (∅ : Finset Msg2))
          s.msgs2)
    (hstep : s'.step = Finmap.insert rid Step.S3 s.step)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hround : s'.round = s.round) :
    round_needs_sent_messages s' := by
  exact step2_preserves_round_needs_sent_messages
    (s := s) (s' := s') (rid := rid)
    (newMsg := { kind := Msg2Kind.Q2, round := Finmap.lookupD rid s.round, src := rid, value := -2 })
    hroundNeeds hstep_old rfl hmsgs1 hmsgs2 hstep hcorrect hrounds hround

lemma step3_preserves_round_needs_sent_messages
    {s s' : State} {rid : Int}
    (hroundNeeds : round_needs_sent_messages s)
    (hstep_old : Finmap.lookupD rid s.step = Step.S3)
    (hmsgs1 : s'.msgs1 = s.msgs1)
    (hmsgs2 : s'.msgs2 = s.msgs2)
    (hstep : s'.step = Finmap.insert rid Step.S1 s.step)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hround : s'.round = Finmap.insert rid (Finmap.lookupD rid s.round + 1) s.round) :
    round_needs_sent_messages s' := by
  classical
  unfold round_needs_sent_messages at hroundNeeds ⊢
  intro id hid r hr
  rw [hcorrect] at hid
  rw [hrounds] at hr
  constructor
  · intro hprem
    by_cases hsrc : id = rid
    · subst id
      rw [hround, lookupD_insert_self] at hprem
      have hle_old : r ≤ Finmap.lookupD rid s.round := by
        rcases hprem with hlt | heq
        · omega
        · rw [hstep] at heq
          simp [lookupD_insert_self] at heq
      by_cases hr_eq : r = Finmap.lookupD rid s.round
      · rcases (hroundNeeds rid hid r hr).1 (Or.inr ⟨hr_eq, by rw [hstep_old]; decide⟩)
            with ⟨m, hm, hmsrc⟩
        refine ⟨m, ?_, hmsrc⟩
        rw [hmsgs1]
        exact hm
      · have hlt_old : r < Finmap.lookupD rid s.round := by omega
        rcases (hroundNeeds rid hid r hr).1 (Or.inl hlt_old) with ⟨m, hm, hmsrc⟩
        refine ⟨m, ?_, hmsrc⟩
        rw [hmsgs1]
        exact hm
    · have hsrc_ne : id ≠ rid := hsrc
      have oldPrem :
          r < Finmap.lookupD id s.round ∨
            (r = Finmap.lookupD id s.round ∧ Finmap.lookupD id s.step ≠ Step.S1) := by
        rw [hround, lookupD_insert_of_ne hsrc_ne] at hprem
        rw [hstep] at hprem
        rw [lookupD_insert_of_ne hsrc_ne] at hprem
        exact hprem
      rcases (hroundNeeds id hid r hr).1 oldPrem with ⟨m, hm, hmsrc⟩
      refine ⟨m, ?_, hmsrc⟩
      rw [hmsgs1]
      exact hm
  · constructor
    · intro hlt
      by_cases hsrc : id = rid
      · subst id
        rw [hround, lookupD_insert_self] at hlt
        have hle_old : r ≤ Finmap.lookupD rid s.round := by omega
        by_cases hr_eq : r = Finmap.lookupD rid s.round
        · rcases (hroundNeeds rid hid r hr).2.2 ⟨hr_eq, hstep_old⟩ with ⟨m, hm, hmsrc⟩
          refine ⟨m, ?_, hmsrc⟩
          rw [hmsgs2]
          exact hm
        · have hlt_old : r < Finmap.lookupD rid s.round := by omega
          rcases (hroundNeeds rid hid r hr).2.1 hlt_old with ⟨m, hm, hmsrc⟩
          refine ⟨m, ?_, hmsrc⟩
          rw [hmsgs2]
          exact hm
      · have hsrc_ne : id ≠ rid := hsrc
        have hlt_old : r < Finmap.lookupD id s.round := by
          rw [hround, lookupD_insert_of_ne hsrc_ne] at hlt
          exact hlt
        rcases (hroundNeeds id hid r hr).2.1 hlt_old with ⟨m, hm, hmsrc⟩
        refine ⟨m, ?_, hmsrc⟩
        rw [hmsgs2]
        exact hm
    · intro hprem
      by_cases hsrc : id = rid
      · subst id
        rw [hstep] at hprem
        simp [lookupD_insert_self] at hprem
      · have hsrc_ne : id ≠ rid := hsrc
        have oldPrem :
            r = Finmap.lookupD id s.round ∧ Finmap.lookupD id s.step = Step.S3 := by
          rw [hround, lookupD_insert_of_ne hsrc_ne] at hprem
          rw [hstep] at hprem
          rw [lookupD_insert_of_ne hsrc_ne] at hprem
          exact hprem
        rcases (hroundNeeds id hid r hr).2.2 oldPrem with ⟨m, hm, hmsrc⟩
        refine ⟨m, ?_, hmsrc⟩
        rw [hmsgs2]
        exact hm

lemma faulty_step_preserves_round_needs_sent_messages
    {s s' : State} {r_faulty : Int} {f1 : Finset Msg1} {f2d f2q : Finset Msg2}
    (hroundNeeds : round_needs_sent_messages s)
    (hmsgs1 : s'.msgs1 = Finmap.insert r_faulty (Finmap.lookupD r_faulty s.msgs1 ∪ f1) s.msgs1)
    (hmsgs2 : s'.msgs2 = Finmap.insert r_faulty (Finmap.lookupD r_faulty s.msgs2 ∪ (f2d ∪ f2q)) s.msgs2)
    (hstep : s'.step = s.step)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hround : s'.round = s.round) :
    round_needs_sent_messages s' := by
  classical
  unfold round_needs_sent_messages at hroundNeeds ⊢
  intro id hid r hr
  rw [hcorrect] at hid
  rw [hrounds] at hr
  constructor
  · intro hprem
    rw [hround, hstep] at hprem
    rcases (hroundNeeds id hid r hr).1 hprem with ⟨m, hm, hmsrc⟩
    refine ⟨m, ?_, hmsrc⟩
    rw [hmsgs1]
    by_cases hr_faulty : r = r_faulty
    · subst r
      simp [lookupD_insert_self, hm]
    · rw [lookupD_insert_of_ne hr_faulty]
      exact hm
  · constructor
    · intro hlt
      rw [hround] at hlt
      rcases (hroundNeeds id hid r hr).2.1 hlt with ⟨m, hm, hmsrc⟩
      refine ⟨m, ?_, hmsrc⟩
      rw [hmsgs2]
      by_cases hr_faulty : r = r_faulty
      · subst r
        simp [lookupD_insert_self, hm]
      · rw [lookupD_insert_of_ne hr_faulty]
        exact hm
    · intro hprem
      rw [hround, hstep] at hprem
      rcases (hroundNeeds id hid r hr).2.2 hprem with ⟨m, hm, hmsrc⟩
      refine ⟨m, ?_, hmsrc⟩
      rw [hmsgs2]
      by_cases hr_faulty : r = r_faulty
      · subst r
        simp [lookupD_insert_self, hm]
      · rw [lookupD_insert_of_ne hr_faulty]
        exact hm

lemma frame_decision_defines_value
    {s s' : State}
    (hdecval : decision_defines_value s)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hvalue : s'.value = s.value)
    (hdecision : s'.decision = s.decision) :
    decision_defines_value s' := by
  unfold decision_defines_value at hdecval ⊢
  intro id hid hne
  rw [hcorrect] at hid
  rw [hdecision] at hne
  rw [hvalue, hdecision]
  exact hdecval id hid hne

lemma step3_decide_preserves_decision_defines_value
    {s s' : State} {rid v : Int}
    (hdecval : decision_defines_value s)
    (hvalue : s'.value = Finmap.insert rid v s.value)
    (hdecision : s'.decision = Finmap.insert rid v s.decision)
    (hcorrect : s'.CORRECT = s.CORRECT) :
    decision_defines_value s' := by
  unfold decision_defines_value at hdecval ⊢
  intro id hid hne
  rw [hcorrect] at hid
  by_cases hsrc : id = rid
  · subst id
    simp [hvalue, hdecision, lookupD_insert_self]
  · rw [hdecision, lookupD_insert_of_ne hsrc] at hne
    rw [hvalue, hdecision, lookupD_insert_of_ne hsrc, lookupD_insert_of_ne hsrc]
    exact hdecval id hid hne

lemma value_update_preserves_decision_defines_value_if
    {s s' : State} {rid v : Int}
    (hdecval : decision_defines_value s)
    (hrid : Finmap.lookupD rid s.decision = -1 ∨ v = Finmap.lookupD rid s.decision)
    (hvalue : s'.value = Finmap.insert rid v s.value)
    (hdecision : s'.decision = s.decision)
    (hcorrect : s'.CORRECT = s.CORRECT) :
    decision_defines_value s' := by
  unfold decision_defines_value at hdecval ⊢
  intro id hid hne
  rw [hcorrect] at hid
  rw [hdecision] at hne
  by_cases hsrc : id = rid
  · subst id
    rcases hrid with hbottom | hsame
    · exact False.elim (hne hbottom)
    · rw [hvalue, hdecision, lookupD_insert_self]
      exact hsame
  · rw [hvalue, hdecision, lookupD_insert_of_ne hsrc]
    exact hdecval id hid hne

lemma step1_preserves_decision_defines_value
    {s s' : State}
    (hdecval : decision_defines_value s)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hvalue : s'.value = s.value)
    (hdecision : s'.decision = s.decision) :
    decision_defines_value s' :=
  frame_decision_defines_value hdecval hcorrect hvalue hdecision

lemma step2_preserves_decision_defines_value
    {s s' : State}
    (hdecval : decision_defines_value s)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hvalue : s'.value = s.value)
    (hdecision : s'.decision = s.decision) :
    decision_defines_value s' :=
  frame_decision_defines_value hdecval hcorrect hvalue hdecision

lemma faulty_step_preserves_decision_defines_value
    {s s' : State}
    (hdecval : decision_defines_value s)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hvalue : s'.value = s.value)
    (hdecision : s'.decision = s.decision) :
    decision_defines_value s' :=
  frame_decision_defines_value hdecval hcorrect hvalue hdecision

lemma step3_value_update_preserves_decision_defines_value_if
    {s s' : State} {rid v : Int}
    (hdecval : decision_defines_value s)
    (hrid : Finmap.lookupD rid s.decision = -1 ∨ v = Finmap.lookupD rid s.decision)
    (hvalue : s'.value = Finmap.insert rid v s.value)
    (hdecision : s'.decision = s.decision)
    (hcorrect : s'.CORRECT = s.CORRECT) :
    decision_defines_value s' :=
  value_update_preserves_decision_defines_value_if hdecval hrid hvalue hdecision hcorrect

lemma d2MsgsFor_mono {v : Int} {msgs msgs' : Finset Msg2}
    (hsub : msgs ⊆ msgs') :
    d2MsgsFor v msgs ⊆ d2MsgsFor v msgs' := by
  intro m hm
  exact Finset.mem_filter.mpr
    ⟨hsub (Finset.mem_filter.mp hm).1, (Finset.mem_filter.mp hm).2⟩

lemma q2Msgs_mono {msgs msgs' : Finset Msg2}
    (hsub : msgs ⊆ msgs') :
    q2Msgs msgs ⊆ q2Msgs msgs' := by
  intro m hm
  exact Finset.mem_filter.mpr
    ⟨hsub (Finset.mem_filter.mp hm).1, (Finset.mem_filter.mp hm).2⟩

lemma senders2_mono_frame {s s' : State} {msgs msgs' : Finset Msg2}
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hsub : msgs ⊆ msgs') :
    senders2 s msgs ⊆ senders2 s' msgs' := by
  intro rid hrid
  unfold senders2 allReplicas at hrid ⊢
  rw [hcorrect, hfaulty]
  rcases Finset.mem_filter.mp hrid with ⟨hall, m, hm, hsrc⟩
  exact Finset.mem_filter.mpr ⟨hall, m, hsub hm, hsrc⟩

lemma senders2_subset_image_src {s : State} {msgs : Finset Msg2} :
    senders2 s msgs ⊆ Finset.image Msg2.src msgs := by
  intro rid hrid
  unfold senders2 at hrid
  rcases Finset.mem_filter.mp hrid with ⟨_, m, hm, hsrc⟩
  exact Finset.mem_image.mpr ⟨m, hm, hsrc.symm⟩

lemma card_senders2_le_card_msgs (s : State) (msgs : Finset Msg2) :
    Finset.card (senders2 s msgs) ≤ Finset.card msgs := by
  exact (Finset.card_le_card (senders2_subset_image_src (s := s) (msgs := msgs))).trans
    (Finset.card_image_le (s := msgs) (f := Msg2.src))

lemma existsQuorum2LessRam_mono_msgs
    {s s' : State} {r v : Int}
    (hquorum : existsQuorum2LessRam s r v)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hsub : Finmap.lookupD r s.msgs2 ⊆ Finmap.lookupD r s'.msgs2) :
    existsQuorum2LessRam s' r v := by
  unfold existsQuorum2LessRam at hquorum ⊢
  have hcard_msgs :=
    Finset.card_le_card hsub
  have hcard_d2 :=
    Finset.card_le_card (d2MsgsFor_mono (v := v) hsub)
  rw [hN, hT]
  omega

lemma existsQuorum2LessRam_of_received_subset
    {s : State} {r v : Int} {received : Finset Msg2}
    (hreceived : received ⊆ Finmap.lookupD r s.msgs2)
    (hcard_received : Finset.card (senders2 s received) = s.N - s.T)
    (hd2_received :
      Finset.card (senders2 s (d2MsgsFor v received)) ≥ s.T + 1)
    (hd2_weight :
      2 * Finset.card (senders2 s (d2MsgsFor v received)) > s.N + s.T) :
    existsQuorum2LessRam s r v := by
  unfold existsQuorum2LessRam
  have hcard_senders_le_received := card_senders2_le_card_msgs s received
  have hreceived_card_le_full := Finset.card_le_card hreceived
  have hd2_senders_le_received :=
    card_senders2_le_card_msgs s (d2MsgsFor v received)
  have hd2_received_le_full :=
    Finset.card_le_card (d2MsgsFor_mono (v := v) hreceived)
  omega

lemma senders2_eq_generated
    {s : State} {msgs : Finset Msg2} :
    senders2 s msgs =
      Finset.filter (fun rid => ∃ m ∈ msgs, rid = Msg2.src m) (s.CORRECT ∪ s.FAULTY) := by
  rfl

lemma senders2_d2_value_eq_generated
    {s : State} {received : Finset Msg2} {v : Int} :
    senders2 s (d2MsgsFor v received) =
      Finset.filter
        (fun rid =>
          ∃ m ∈ Finset.filter (fun m => Msg2.kind m = Msg2Kind.D2 ∧ v = Msg2.value m) received,
            rid = Msg2.src m)
        (s.CORRECT ∪ s.FAULTY) := by
  classical
  unfold senders2 d2MsgsFor allReplicas
  apply Finset.ext
  intro rid
  simp only [Finset.mem_filter]
  constructor
  · intro h
    rcases h with ⟨hall, m, hm, hsrc⟩
    exact ⟨hall, m, ⟨hm.1, hm.2.1, hm.2.2.symm⟩, hsrc⟩
  · intro h
    rcases h with ⟨hall, m, hm, hsrc⟩
    exact ⟨hall, m, ⟨hm.1, hm.2.1, hm.2.2.symm⟩, hsrc⟩

lemma generated_step3_fast_of_all_correct_received_d2
    {s : State} {received : Finset Msg2} {v : Int}
    (hassumptions : assumptions_hold s)
    (hFleT : s.F ≤ s.T)
    (hN5T : s.N > 5 * s.T)
    (hreceived_card :
      Finset.card
          (Finset.filter (fun id => ∃ m ∈ received, id = Msg2.src m) (s.CORRECT ∪ s.FAULTY)) =
        s.N - s.T)
    (hall_correct :
      ∀ m ∈ received,
        m.src ∈ s.CORRECT →
          m.kind = Msg2Kind.D2 ∧ m.value = v) :
    2 *
          Finset.card
            (Finset.filter
              (fun id =>
                ∃ m ∈ Finset.filter (fun m => Msg2.kind m = Msg2Kind.D2 ∧ v = Msg2.value m) received,
                  id = Msg2.src m)
              (s.CORRECT ∪ s.FAULTY)) >
        s.N + s.T := by
  classical
  let allSenders := senders2 s received
  let dSenders := senders2 s (d2MsgsFor v received)
  have hsub : allSenders ⊆ dSenders ∪ s.FAULTY := by
    intro id hid
    unfold allSenders senders2 at hid
    rcases Finset.mem_filter.mp hid with ⟨hall, m, hm, hsrc⟩
    unfold allReplicas at hall
    rcases Finset.mem_union.mp hall with hcorrect_id | hfaulty_id
    · apply Finset.mem_union.mpr
      left
      have hcorrect_m : m.src ∈ s.CORRECT := by
        rw [← hsrc]
        exact hcorrect_id
      have hmv := hall_correct m hm hcorrect_m
      unfold dSenders senders2 d2MsgsFor
      refine Finset.mem_filter.mpr ⟨?_, m, ?_, hsrc⟩
      · unfold allReplicas
        exact Finset.mem_union.mpr (Or.inl hcorrect_id)
      · exact Finset.mem_filter.mpr ⟨hm, hmv.1, hmv.2⟩
    · exact Finset.mem_union.mpr (Or.inr hfaulty_id)
  have hcard_sub := Finset.card_le_card hsub
  have hcard_union : Finset.card (dSenders ∪ s.FAULTY) ≤ Finset.card dSenders + Finset.card s.FAULTY :=
    Finset.card_union_le _ _
  have hall_card : (Finset.card allSenders : Int) = s.N - s.T := by
    unfold allSenders
    rw [senders2_eq_generated]
    exact hreceived_card
  unfold assumptions_hold at hassumptions
  rcases hassumptions with ⟨_, _, hfaulty_card, _, _⟩
  have hd_lower : (Finset.card dSenders : Int) ≥ s.N - s.T - s.F := by
    omega
  have hfast : 2 * (Finset.card dSenders : Int) > s.N + s.T := by
    omega
  rw [← senders2_d2_value_eq_generated]
  exact hfast

lemma existsQuorum2LessRam_of_generated_step3_decision
    {s : State} {r v : Int} {received : Finset Msg2}
    (hreceived : received ∈ Finset.powerset (Finmap.lookupD r s.msgs2))
    (hcard_received :
      Finset.card
          (Finset.filter (fun rid => ∃ m ∈ received, rid = Msg2.src m) (s.CORRECT ∪ s.FAULTY)) =
        s.N - s.T)
    (hd2_received :
      Finset.card
          (Finset.filter
            (fun rid =>
              ∃ m ∈ Finset.filter (fun m => Msg2.kind m = Msg2Kind.D2 ∧ v = Msg2.value m) received,
                rid = Msg2.src m)
            (s.CORRECT ∪ s.FAULTY)) ≥
        s.T + 1)
    (hd2_weight :
      2 *
            Finset.card
              (Finset.filter
                (fun rid =>
                  ∃ m ∈ Finset.filter (fun m => Msg2.kind m = Msg2Kind.D2 ∧ v = Msg2.value m) received,
                    rid = Msg2.src m)
                (s.CORRECT ∪ s.FAULTY)) >
          s.N + s.T) :
    existsQuorum2LessRam s r v := by
  apply existsQuorum2LessRam_of_received_subset
    (s := s) (r := r) (v := v) (received := received)
    (Finset.mem_powerset.mp hreceived)
  · rw [senders2_eq_generated]
    exact hcard_received
  · rw [senders2_d2_value_eq_generated]
    exact hd2_received
  · rw [senders2_d2_value_eq_generated]
    exact hd2_weight

lemma frame_existsQuorum2LessRam
    {s s' : State} {r v : Int}
    (hquorum : existsQuorum2LessRam s r v)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    existsQuorum2LessRam s' r v := by
  apply existsQuorum2LessRam_mono_msgs hquorum hN hT
  rw [hmsgs2]

lemma existsQuorum2LessRam_step2_msg
    {s s' : State} {r v rid : Int} {newMsg : Msg2}
    (hquorum : existsQuorum2LessRam s r v)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 ∪
            insert newMsg (∅ : Finset Msg2))
          s.msgs2) :
    existsQuorum2LessRam s' r v := by
  classical
  apply existsQuorum2LessRam_mono_msgs hquorum hN hT
  rw [hmsgs2]
  by_cases hr : r = Finmap.lookupD rid s.round
  · subst r
    intro m hm
    simp [lookupD_insert_self, hm]
  · intro m hm
    rw [lookupD_insert_of_ne hr]
    exact hm

lemma existsQuorum2LessRam_faulty_step
    {s s' : State} {r v r_faulty : Int} {f2d f2q : Finset Msg2}
    (hquorum : existsQuorum2LessRam s r v)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert r_faulty (Finmap.lookupD r_faulty s.msgs2 ∪ (f2d ∪ f2q)) s.msgs2) :
    existsQuorum2LessRam s' r v := by
  classical
  apply existsQuorum2LessRam_mono_msgs hquorum hN hT
  rw [hmsgs2]
  by_cases hr : r = r_faulty
  · subst r
    intro m hm
    simp [lookupD_insert_self, hm]
  · intro m hm
    rw [lookupD_insert_of_ne hr]
    exact hm

lemma frame_decision_requires_last_quorum_less_ram
    {s s' : State}
    (hdecision_req : decision_requires_last_quorum_less_ram s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hdecision : s'.decision = s.decision)
    (hround : s'.round = s.round)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    decision_requires_last_quorum_less_ram s' := by
  unfold decision_requires_last_quorum_less_ram at hdecision_req ⊢
  intro id hid
  rw [hcorrect] at hid
  rw [hdecision, hround]
  rcases hdecision_req id hid with hbottom | hquorum
  · exact Or.inl hbottom
  · exact Or.inr ⟨hquorum.1,
      frame_existsQuorum2LessRam hquorum.2 hN hT hmsgs2⟩

lemma step1_preserves_decision_requires_last_quorum_less_ram
    {s s' : State}
    (hdecision_req : decision_requires_last_quorum_less_ram s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hdecision : s'.decision = s.decision)
    (hround : s'.round = s.round)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    decision_requires_last_quorum_less_ram s' :=
  frame_decision_requires_last_quorum_less_ram
    hdecision_req hN hT hcorrect hdecision hround hmsgs2

lemma step2_preserves_decision_requires_last_quorum_less_ram
    {s s' : State} {rid : Int} {newMsg : Msg2}
    (hdecision_req : decision_requires_last_quorum_less_ram s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hdecision : s'.decision = s.decision)
    (hround : s'.round = s.round)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 ∪
            insert newMsg (∅ : Finset Msg2))
          s.msgs2) :
    decision_requires_last_quorum_less_ram s' := by
  unfold decision_requires_last_quorum_less_ram at hdecision_req ⊢
  intro id hid
  rw [hcorrect] at hid
  rw [hdecision, hround]
  rcases hdecision_req id hid with hbottom | hquorum
  · exact Or.inl hbottom
  · exact Or.inr ⟨hquorum.1,
      existsQuorum2LessRam_step2_msg
        (s := s) (s' := s') (rid := rid) (newMsg := newMsg)
        hquorum.2 hN hT hmsgs2⟩

lemma step2_d2_preserves_decision_requires_last_quorum_less_ram
    {s s' : State} {rid v : Int}
    (hdecision_req : decision_requires_last_quorum_less_ram s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hdecision : s'.decision = s.decision)
    (hround : s'.round = s.round)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 ∪
            insert { kind := Msg2Kind.D2, round := Finmap.lookupD rid s.round, src := rid, value := v }
              (∅ : Finset Msg2))
          s.msgs2) :
    decision_requires_last_quorum_less_ram s' :=
  step2_preserves_decision_requires_last_quorum_less_ram
    (s := s) (s' := s') (rid := rid)
    (newMsg := { kind := Msg2Kind.D2, round := Finmap.lookupD rid s.round, src := rid, value := v })
    hdecision_req hN hT hcorrect hdecision hround hmsgs2

lemma step2_q2_preserves_decision_requires_last_quorum_less_ram
    {s s' : State} {rid : Int}
    (hdecision_req : decision_requires_last_quorum_less_ram s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hdecision : s'.decision = s.decision)
    (hround : s'.round = s.round)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 ∪
            insert { kind := Msg2Kind.Q2, round := Finmap.lookupD rid s.round, src := rid, value := -2 }
              (∅ : Finset Msg2))
          s.msgs2) :
    decision_requires_last_quorum_less_ram s' :=
  step2_preserves_decision_requires_last_quorum_less_ram
    (s := s) (s' := s') (rid := rid)
    (newMsg := { kind := Msg2Kind.Q2, round := Finmap.lookupD rid s.round, src := rid, value := -2 })
    hdecision_req hN hT hcorrect hdecision hround hmsgs2

lemma faulty_step_preserves_decision_requires_last_quorum_less_ram
    {s s' : State} {r_faulty : Int} {f2d f2q : Finset Msg2}
    (hdecision_req : decision_requires_last_quorum_less_ram s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hdecision : s'.decision = s.decision)
    (hround : s'.round = s.round)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert r_faulty (Finmap.lookupD r_faulty s.msgs2 ∪ (f2d ∪ f2q)) s.msgs2) :
    decision_requires_last_quorum_less_ram s' := by
  unfold decision_requires_last_quorum_less_ram at hdecision_req ⊢
  intro id hid
  rw [hcorrect] at hid
  rw [hdecision, hround]
  rcases hdecision_req id hid with hbottom | hquorum
  · exact Or.inl hbottom
  · exact Or.inr ⟨hquorum.1,
      existsQuorum2LessRam_faulty_step
        (s := s) (s' := s') (r_faulty := r_faulty) (f2d := f2d) (f2q := f2q)
        hquorum.2 hN hT hmsgs2⟩

lemma step3_decide_preserves_decision_requires_last_quorum_less_ram
    {s s' : State} {rid v : Int}
    (hdecision_req : decision_requires_last_quorum_less_ram s)
    (hround_old_pos : 1 ≤ Finmap.lookupD rid s.round)
    (hnew_quorum : existsQuorum2LessRam s (Finmap.lookupD rid s.round) v)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hdecision : s'.decision = Finmap.insert rid v s.decision)
    (hround : s'.round = Finmap.insert rid (Finmap.lookupD rid s.round + 1) s.round)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    decision_requires_last_quorum_less_ram s' := by
  classical
  unfold decision_requires_last_quorum_less_ram at hdecision_req ⊢
  intro id hid
  rw [hcorrect] at hid
  by_cases hsrc : id = rid
  · subst id
    right
    constructor
    · rw [hround, lookupD_insert_self]
      omega
    · rw [hround, hdecision, lookupD_insert_self, lookupD_insert_self]
      have hprev : Finmap.lookupD rid s.round + 1 - 1 = Finmap.lookupD rid s.round := by
        omega
      rw [hprev]
      exact frame_existsQuorum2LessRam hnew_quorum hN hT hmsgs2
  · have hsrc_ne : id ≠ rid := hsrc
    rw [hdecision, hround, lookupD_insert_of_ne hsrc_ne, lookupD_insert_of_ne hsrc_ne]
    rcases hdecision_req id hid with hbottom | hquorum
    · exact Or.inl hbottom
    · exact Or.inr ⟨hquorum.1,
        frame_existsQuorum2LessRam hquorum.2 hN hT hmsgs2⟩

lemma step3_decide_preserves_decision_requires_last_quorum_less_ram_of_generated
    {s s' : State} {rid v : Int} {received : Finset Msg2}
    (hdecision_req : decision_requires_last_quorum_less_ram s)
    (hround_old_pos : 1 ≤ Finmap.lookupD rid s.round)
    (hreceived : received ∈ Finset.powerset (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2))
    (hcard_received :
      Finset.card
          (Finset.filter (fun id => ∃ m ∈ received, id = Msg2.src m) (s.CORRECT ∪ s.FAULTY)) =
        s.N - s.T)
    (hd2_received :
      Finset.card
          (Finset.filter
            (fun id =>
              ∃ m ∈ Finset.filter (fun m => Msg2.kind m = Msg2Kind.D2 ∧ v = Msg2.value m) received,
                id = Msg2.src m)
            (s.CORRECT ∪ s.FAULTY)) ≥
        s.T + 1)
    (hd2_weight :
      2 *
            Finset.card
              (Finset.filter
                (fun id =>
                  ∃ m ∈ Finset.filter (fun m => Msg2.kind m = Msg2Kind.D2 ∧ v = Msg2.value m) received,
                    id = Msg2.src m)
                (s.CORRECT ∪ s.FAULTY)) >
          s.N + s.T)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hdecision : s'.decision = Finmap.insert rid v s.decision)
    (hround : s'.round = Finmap.insert rid (Finmap.lookupD rid s.round + 1) s.round)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    decision_requires_last_quorum_less_ram s' := by
  exact step3_decide_preserves_decision_requires_last_quorum_less_ram
    (s := s) (s' := s') (rid := rid) (v := v)
    hdecision_req hround_old_pos
    (existsQuorum2LessRam_of_generated_step3_decision
      (s := s) (r := Finmap.lookupD rid s.round) (v := v)
      (received := received) hreceived hcard_received hd2_received hd2_weight)
    hN hT hcorrect hdecision hround hmsgs2

lemma step3_no_decision_preserves_decision_requires_last_quorum_less_ram
    {s s' : State} {rid : Int}
    (hdecision_req : decision_requires_last_quorum_less_ram s)
    (hround_old_pos : 1 ≤ Finmap.lookupD rid s.round)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hdecision : s'.decision = s.decision)
    (hround : s'.round = Finmap.insert rid (Finmap.lookupD rid s.round + 1) s.round)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    (Finmap.lookupD rid s.decision = -1 ∨
      existsQuorum2LessRam s (Finmap.lookupD rid s.round) (Finmap.lookupD rid s.decision)) →
      decision_requires_last_quorum_less_ram s' := by
  classical
  intro hrid_ok
  unfold decision_requires_last_quorum_less_ram at hdecision_req ⊢
  intro id hid
  rw [hcorrect] at hid
  by_cases hsrc : id = rid
  · subst id
    rw [hdecision]
    rcases hrid_ok with hbottom | hnew_quorum
    · rw [hbottom]
      exact Or.inl rfl
    · right
      rw [hround, lookupD_insert_self]
      constructor
      · omega
      · have hprev : Finmap.lookupD rid s.round + 1 - 1 = Finmap.lookupD rid s.round := by
          omega
        rw [hprev]
        exact frame_existsQuorum2LessRam hnew_quorum hN hT hmsgs2
  · have hsrc_ne : id ≠ rid := hsrc
    rw [hdecision, hround, lookupD_insert_of_ne hsrc_ne]
    rcases hdecision_req id hid with hbottom | hquorum
    · exact Or.inl hbottom
    · exact Or.inr ⟨hquorum.1,
        frame_existsQuorum2LessRam hquorum.2 hN hT hmsgs2⟩

lemma frame_supportedValues
    {s s' : State} {r : Int}
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    supportedValues s' r = supportedValues s r := by
  unfold supportedValues
  apply Finset.ext
  intro v
  simp only [Finset.mem_filter]
  constructor
  · intro h
    simpa [senders2, allReplicas, hN, hT, hcorrect, hfaulty, hmsgs2] using h
  · intro h
    simpa [senders2, allReplicas, hN, hT, hcorrect, hfaulty, hmsgs2] using h

lemma supportedValues_of_mono_msgs2_and_old_quorum
    {s s' : State} {r v : Int}
    (htype : type_ok s)
    (hr : r ∈ s.ROUNDS)
    (hN5T : s.N > 5 * s.T)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hmsgs2_sub : Finmap.lookupD r s.msgs2 ⊆ Finmap.lookupD r s'.msgs2)
    (hold_total :
      (Finset.card (senders2 s (Finmap.lookupD r s.msgs2)) : Int) ≥ s.N - s.T)
    (hsup : v ∈ supportedValues s' r) :
    v ∈ supportedValues s r := by
  classical
  let oldMsgs := Finmap.lookupD r s.msgs2
  let newMsgs := Finmap.lookupD r s'.msgs2
  let oldAll := senders2 s oldMsgs
  let oldD := senders2 s (d2MsgsFor v oldMsgs)
  let oldOthers :=
    senders2 s
      (Finset.filter
        (fun m => Msg2.kind m = Msg2Kind.Q2 ∨ Msg2.value m ≠ v)
        oldMsgs)
  let newOthers :=
    senders2 s'
      (Finset.filter
        (fun m => Msg2.kind m = Msg2Kind.Q2 ∨ Msg2.value m ≠ v)
        newMsgs)
  unfold supportedValues at hsup ⊢
  rcases Finset.mem_filter.mp hsup with ⟨hv_values, hnew_total, hnew_d, hnew_others⟩
  refine Finset.mem_filter.mpr ⟨hv_values, hold_total, ?_, ?_⟩
  · by_contra hnot_ge
    have hold_d_le : (Finset.card oldD : Int) ≤ s.T := by
      change ¬ (Finset.card oldD : Int) ≥ s.T + 1 at hnot_ge
      omega
    have hcover : oldAll ⊆ oldD ∪ newOthers := by
      intro id hid
      unfold oldAll senders2 at hid
      rcases Finset.mem_filter.mp hid with ⟨hall, m, hm_old, hsrc⟩
      by_cases hD : m.kind = Msg2Kind.D2 ∧ m.value = v
      · apply Finset.mem_union.mpr
        left
        unfold oldD senders2 d2MsgsFor
        refine Finset.mem_filter.mpr ⟨hall, m, ?_, hsrc⟩
        exact Finset.mem_filter.mpr ⟨hm_old, hD.1, hD.2⟩
      · apply Finset.mem_union.mpr
        right
        have hm_full : m ∈ Finmap.lookupD r s.msgs2 := by
          simpa [oldMsgs] using hm_old
        have hkind_mem := (htype.2.2.2.2.2 r hr m hm_full).2.2.1
        have hother : m.kind = Msg2Kind.Q2 ∨ m.value ≠ v := by
          simp at hkind_mem
          rcases hkind_mem with hkindD | hkindQ
          · right
            intro hvalue
            exact hD ⟨hkindD, hvalue⟩
          · exact Or.inl hkindQ
        unfold newOthers senders2
        refine Finset.mem_filter.mpr ⟨?_, m, ?_, hsrc⟩
        · unfold allReplicas at hall ⊢
          rwa [hcorrect, hfaulty]
        · exact Finset.mem_filter.mpr ⟨hmsgs2_sub hm_full, hother⟩
    have hcard_cover := Finset.card_le_card hcover
    have hcard_union : Finset.card (oldD ∪ newOthers) ≤ Finset.card oldD + Finset.card newOthers :=
      Finset.card_union_le _ _
    have hnew_others_old :
        (Finset.card newOthers : Int) < s.N - 2 * s.T := by
      change (Finset.card newOthers : Int) < s'.N - 2 * s'.T at hnew_others
      rw [hN, hT] at hnew_others
      exact hnew_others
    change (Finset.card oldAll : Int) ≥ s.N - s.T at hold_total
    omega
  · have hsub_others : oldOthers ⊆ newOthers := by
      intro id hid
      unfold oldOthers senders2 at hid
      rcases Finset.mem_filter.mp hid with ⟨hall, m, hm, hsrc⟩
      rcases Finset.mem_filter.mp hm with ⟨hm_old, hother⟩
      unfold newOthers senders2
      refine Finset.mem_filter.mpr ⟨?_, m, ?_, hsrc⟩
      · unfold allReplicas at hall ⊢
        rwa [hcorrect, hfaulty]
      · exact Finset.mem_filter.mpr ⟨hmsgs2_sub hm_old, hother⟩
    have hcard := Finset.card_le_card hsub_others
    change (Finset.card oldOthers : Int) < s.N - 2 * s.T
    change (Finset.card newOthers : Int) < s'.N - 2 * s'.T at hnew_others
    rw [hN, hT] at hnew_others
    omega

lemma frame_rounds_connection
    {s s' : State}
    (hrounds_conn : rounds_connection s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1 : s'.msgs1 = s.msgs1)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    rounds_connection s' := by
  unfold rounds_connection at hrounds_conn ⊢
  intro r hr hnext
  rw [hrounds] at hr hnext
  have hsup := frame_supportedValues
    (s := s) (s' := s') (r := r) hN hT hcorrect hfaulty hmsgs2
  rcases hrounds_conn r hr hnext with hempty | hwit
  · left
    rw [hsup, hempty]
  · right
    rcases hwit with ⟨v, hv, hmsgs⟩
    refine ⟨v, ?_, ?_⟩
    · rw [hsup]
      exact hv
    · intro m hm hc
      rw [hmsgs1] at hm
      rw [hcorrect] at hc
      exact hmsgs m hm hc

lemma step3_preserves_rounds_connection
    {s s' : State}
    (hrounds_conn : rounds_connection s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1 : s'.msgs1 = s.msgs1)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    rounds_connection s' :=
  frame_rounds_connection hrounds_conn hN hT hcorrect hfaulty hrounds hmsgs1 hmsgs2

lemma step1_preserves_rounds_connection_if
    {s s' : State} {rid : Int}
    (hrounds_conn : rounds_connection s)
    (hcompat :
      ∀ r ∈ s.ROUNDS,
        r + 1 = Finmap.lookupD rid s.round →
          supportedValues s r = ∅ ∨
            ∃ v ∈ supportedValues s r,
              Finmap.lookupD rid s.value = v ∧
                ∀ m ∈ Finmap.lookupD (r + 1) s.msgs1,
                  m.src ∈ s.CORRECT → m.value = v)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1 :
      s'.msgs1 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs1 ∪
            insert { round := Finmap.lookupD rid s.round, src := rid, value := Finmap.lookupD rid s.value }
              (∅ : Finset Msg1))
          s.msgs1)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    rounds_connection s' := by
  classical
  unfold rounds_connection at hrounds_conn ⊢
  intro r hr hnext
  rw [hrounds] at hr hnext
  have hsup := frame_supportedValues
    (s := s) (s' := s') (r := r) hN hT hcorrect hfaulty hmsgs2
  by_cases hnew_round : r + 1 = Finmap.lookupD rid s.round
  · rcases hcompat r hr hnew_round with hempty | hwit
    · left
      rw [hsup, hempty]
    · right
      rcases hwit with ⟨v, hv, hvalue_rid, hold_msgs⟩
      refine ⟨v, ?_, ?_⟩
      · rw [hsup]
        exact hv
      · intro m hm hc
        rw [hcorrect] at hc
        rw [hmsgs1, ← hnew_round] at hm
        simp [lookupD_insert_self] at hm
        rcases hm with hmnew | hmold
        · rw [hmnew]
          exact hvalue_rid
        · exact hold_msgs m hmold hc
  · rcases hrounds_conn r hr hnext with hempty | hwit
    · left
      rw [hsup, hempty]
    · right
      rcases hwit with ⟨v, hv, hmsgs_old⟩
      refine ⟨v, ?_, ?_⟩
      · rw [hsup]
        exact hv
      · intro m hm hc
        rw [hcorrect] at hc
        rw [hmsgs1] at hm
        rw [lookupD_insert_of_ne hnew_round] at hm
        exact hmsgs_old m hm hc

lemma step1_rounds_connection_compat_of_unique_supported
    {s : State} {rid : Int}
    (htype : type_ok s)
    (hrounds_conn : rounds_connection s)
    (hvalue_lock : value_lock s)
    (hrid : rid ∈ s.CORRECT)
    (hround_pos : ∀ r ∈ s.ROUNDS, 1 ≤ r)
    (hsupported_unique :
      ∀ r ∈ s.ROUNDS, ∀ v ∈ supportedValues s r, ∀ w ∈ supportedValues s r, v = w) :
    ∀ r ∈ s.ROUNDS,
      r + 1 = Finmap.lookupD rid s.round →
        supportedValues s r = ∅ ∨
          ∃ v ∈ supportedValues s r,
            Finmap.lookupD rid s.value = v ∧
              ∀ m ∈ Finmap.lookupD (r + 1) s.msgs1,
                m.src ∈ s.CORRECT → m.value = v := by
  intro r hr hround_eq
  have hround_rid_mem : Finmap.lookupD rid s.round ∈ s.ROUNDS := by
    unfold type_ok at htype
    exact htype.2.2.1.2 rid hrid
  have hnext : r + 1 ∈ s.ROUNDS := by
    rwa [hround_eq]
  rcases hrounds_conn r hr hnext with hempty | hwit
  · exact Or.inl hempty
  · right
    rcases hwit with ⟨v, hv, hmsgs⟩
    refine ⟨v, hv, ?_, hmsgs⟩
    have hvalue_mem : Finmap.lookupD rid s.value ∈ values := by
      unfold type_ok at htype
      exact htype.1.2 rid hrid
    rcases hvalue_lock rid hrid (Finmap.lookupD rid s.value) hvalue_mem with hfirst | hlocked
    · rw [← hround_eq] at hfirst
      have hr_pos := hround_pos r hr
      omega
    · rcases hlocked with ⟨_, hempty_or_mem⟩
      rw [← hround_eq] at hempty_or_mem
      have hprev : r + 1 - 1 = r := by omega
      rw [hprev] at hempty_or_mem
      rcases hempty_or_mem with hempty' | hmem
      · rw [hempty'] at hv
        simp at hv
      · exact (hsupported_unique r hr v hv (Finmap.lookupD rid s.value) hmem).symm

lemma frame_m1_requires_quorum
    {s s' : State}
    (hm1 : m1_requires_quorum s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1 : s'.msgs1 = s.msgs1)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    m1_requires_quorum s' := by
  unfold m1_requires_quorum at hm1 ⊢
  intro r hr hne hm
  rw [hrounds] at hr
  rcases hm with ⟨m, hm, hcorrect_m⟩
  rw [hmsgs1] at hm
  rw [hcorrect] at hcorrect_m
  have hold := hm1 r hr hne ⟨m, hm, hcorrect_m⟩
  rw [hN, hT, hmsgs2]
  unfold senders2 allReplicas
  rw [hcorrect, hfaulty]
  exact hold

lemma step3_preserves_m1_requires_quorum
    {s s' : State}
    (hm1 : m1_requires_quorum s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1 : s'.msgs1 = s.msgs1)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    m1_requires_quorum s' :=
  frame_m1_requires_quorum hm1 hN hT hcorrect hfaulty hrounds hmsgs1 hmsgs2

lemma step1_preserves_m1_requires_quorum
    {s s' : State} {rid : Int}
    (hm1 : m1_requires_quorum s)
    (hjumps : cannot_jump_rounds_without_quorum s)
    (hround_pred : ∀ r ∈ s.ROUNDS, r ≠ 1 → r - 1 ∈ s.ROUNDS)
    (hrid : rid ∈ s.CORRECT)
    (hstep_old : Finmap.lookupD rid s.step = Step.S1)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1 :
      s'.msgs1 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs1 ∪
            insert { round := Finmap.lookupD rid s.round, src := rid, value := Finmap.lookupD rid s.value }
              (∅ : Finset Msg1))
          s.msgs1)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    m1_requires_quorum s' := by
  classical
  unfold m1_requires_quorum at hm1 ⊢
  intro r hr hne hm
  rw [hrounds] at hr
  rcases hm with ⟨m, hm, hcorrect_m⟩
  rw [hcorrect] at hcorrect_m
  rw [hmsgs1] at hm
  by_cases hrid_round : r = Finmap.lookupD rid s.round
  · subst r
    simp [lookupD_insert_self] at hm
    rcases hm with hmnew | hmold
    · have hprev :
          Finmap.lookupD rid s.round - 1 ∈ s.ROUNDS :=
        hround_pred (Finmap.lookupD rid s.round) hr hne
      have hnext :
          Finmap.lookupD rid s.round - 1 + 1 ∈ s.ROUNDS := by
        have hsum : Finmap.lookupD rid s.round - 1 + 1 = Finmap.lookupD rid s.round := by
          omega
        rwa [hsum]
      have hproc :
          ∃ id ∈ s.CORRECT,
            Finmap.lookupD id s.round = Finmap.lookupD rid s.round - 1 + 1 ∧
              Finmap.lookupD id s.step = Step.S1 := by
        refine ⟨rid, hrid, ?_, hstep_old⟩
        omega
      have hold := hjumps (Finmap.lookupD rid s.round - 1) hprev hnext hproc
      rw [hN, hT, hmsgs2]
      unfold senders2 allReplicas
      rw [hcorrect, hfaulty]
      exact hold
    · have hold :=
        hm1 (Finmap.lookupD rid s.round) hr hne ⟨m, hmold, hcorrect_m⟩
      rw [hN, hT, hmsgs2]
      unfold senders2 allReplicas
      rw [hcorrect, hfaulty]
      exact hold
  · rw [lookupD_insert_of_ne hrid_round] at hm
    have hold := hm1 r hr hne ⟨m, hm, hcorrect_m⟩
    rw [hN, hT, hmsgs2]
    unfold senders2 allReplicas
    rw [hcorrect, hfaulty]
    exact hold

lemma frame_value_lock
    {s s' : State}
    (hlock : value_lock s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hvalue : s'.value = s.value)
    (hround : s'.round = s.round)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    value_lock s' := by
  unfold value_lock at hlock ⊢
  intro id hid v hv
  rw [hcorrect] at hid
  rw [hround]
  rcases hlock id hid v hv with hfirst | hnext
  · exact Or.inl hfirst
  · right
    rcases hnext with ⟨hgt, hempty | hmem⟩
    · refine ⟨hgt, Or.inl ?_⟩
      rw [frame_supportedValues (s := s) (s' := s')
        (r := Finmap.lookupD id s.round - 1) hN hT hcorrect hfaulty hmsgs2]
      exact hempty
    · refine ⟨hgt, Or.inr ?_⟩
      rw [hvalue]
      rw [frame_supportedValues (s := s) (s' := s')
        (r := Finmap.lookupD id s.round - 1) hN hT hcorrect hfaulty hmsgs2]
      exact hmem

lemma step3_value_update_preserves_value_lock_if
    {s s' : State} {rid newValue : Int}
    (hlock : value_lock s)
    (hsupport :
      supportedValues s (Finmap.lookupD rid s.round) = ∅ ∨
        newValue ∈ supportedValues s (Finmap.lookupD rid s.round))
    (hround_old_pos : 1 ≤ Finmap.lookupD rid s.round)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hvalue : s'.value = Finmap.insert rid newValue s.value)
    (hround : s'.round = Finmap.insert rid (Finmap.lookupD rid s.round + 1) s.round)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    value_lock s' := by
  classical
  unfold value_lock at hlock ⊢
  intro id hid v hv
  rw [hcorrect] at hid
  by_cases hsrc : id = rid
  · subst id
    right
    rw [hround, hvalue, lookupD_insert_self, lookupD_insert_self]
    constructor
    · omega
    · have hprev : Finmap.lookupD rid s.round + 1 - 1 = Finmap.lookupD rid s.round := by
        omega
      rw [hprev]
      rw [frame_supportedValues (s := s) (s' := s')
        (r := Finmap.lookupD rid s.round) hN hT hcorrect hfaulty hmsgs2]
      exact hsupport
  · have hsrc_ne : id ≠ rid := hsrc
    rw [hround, lookupD_insert_of_ne hsrc_ne]
    rcases hlock id hid v hv with hfirst | hnext
    · exact Or.inl hfirst
    · right
      rw [hvalue, lookupD_insert_of_ne hsrc_ne]
      rcases hnext with ⟨hgt, hempty | hmem⟩
      · refine ⟨hgt, Or.inl ?_⟩
        rw [frame_supportedValues (s := s) (s' := s')
          (r := Finmap.lookupD id s.round - 1) hN hT hcorrect hfaulty hmsgs2]
        exact hempty
      · refine ⟨hgt, Or.inr ?_⟩
        rw [frame_supportedValues (s := s) (s' := s')
          (r := Finmap.lookupD id s.round - 1) hN hT hcorrect hfaulty hmsgs2]
        exact hmem

lemma previous_round_has_quorum_for_correct_base
    {s : State} {id : Int}
    (hbase : model_base_assumptions s)
    (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (hid : id ∈ s.CORRECT)
    (hgt : Finmap.lookupD id s.round > 1) :
    Finset.card (senders2 s (Finmap.lookupD (Finmap.lookupD id s.round - 1) s.msgs2)) ≥
      s.N - s.T := by
  classical
  unfold model_base_assumptions at hbase
  rcases hbase with ⟨_, _, _, hround_pred, _⟩
  unfold ind_inv_13 at hinv
  rcases hinv with
    ⟨_, _, _, hroundNeeds, _, _, _, _, hm1, _, hjumps, _, _⟩
  have hround_mem : Finmap.lookupD id s.round ∈ s.ROUNDS := by
    unfold type_ok at htype
    exact htype.2.2.1.2 id hid
  have hprev_mem : Finmap.lookupD id s.round - 1 ∈ s.ROUNDS :=
    hround_pred (Finmap.lookupD id s.round) hround_mem (by omega)
  have hnext_mem : Finmap.lookupD id s.round - 1 + 1 ∈ s.ROUNDS := by
    have hprev_succ : Finmap.lookupD id s.round - 1 + 1 = Finmap.lookupD id s.round := by
      omega
    rwa [hprev_succ]
  by_cases hstep_s1 : Finmap.lookupD id s.step = Step.S1
  · have hproc :
        ∃ pid ∈ s.CORRECT,
          Finmap.lookupD pid s.round = Finmap.lookupD id s.round - 1 + 1 ∧
            Finmap.lookupD pid s.step = Step.S1 := by
      refine ⟨id, hid, ?_, hstep_s1⟩
      omega
    exact hjumps (Finmap.lookupD id s.round - 1) hprev_mem hnext_mem hproc
  · have hmsg :
        ∃ m ∈ Finmap.lookupD (Finmap.lookupD id s.round) s.msgs1, m.src = id := by
      exact (hroundNeeds id hid (Finmap.lookupD id s.round) hround_mem).1
        (Or.inr ⟨rfl, hstep_s1⟩)
    rcases hmsg with ⟨m, hm, hsrc⟩
    have hcorrect_m : m.src ∈ s.CORRECT := by
      rw [hsrc]
      exact hid
    simpa using
      hm1 (Finmap.lookupD id s.round) hround_mem (by omega) ⟨m, hm, hcorrect_m⟩

lemma previous_round_has_quorum_for_correct
    {s : State} {id : Int}
    (hmodel : model_assumptions s)
    (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (hid : id ∈ s.CORRECT)
    (hgt : Finmap.lookupD id s.round > 1) :
    Finset.card (senders2 s (Finmap.lookupD (Finmap.lookupD id s.round - 1) s.msgs2)) ≥
      s.N - s.T :=
  previous_round_has_quorum_for_correct_base (model_base_of_model hmodel) htype hinv hid hgt

lemma m1_requires_quorum_mono_msgs2
    {s s' : State}
    (hm1 : m1_requires_quorum s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1 : s'.msgs1 = s.msgs1)
    (hmsgs2_sub : ∀ r, Finmap.lookupD r s.msgs2 ⊆ Finmap.lookupD r s'.msgs2) :
    m1_requires_quorum s' := by
  unfold m1_requires_quorum at hm1 ⊢
  intro r hr hne hm
  rw [hrounds] at hr
  rcases hm with ⟨m, hm, hcorrect_m⟩
  rw [hmsgs1] at hm
  rw [hcorrect] at hcorrect_m
  have hold := hm1 r hr hne ⟨m, hm, hcorrect_m⟩
  have hsub :=
    senders2_mono_frame (s := s) (s' := s')
      hcorrect hfaulty (hmsgs2_sub (r - 1))
  have hcard := Finset.card_le_card hsub
  rw [hN, hT]
  omega

lemma step2_preserves_m1_requires_quorum
    {s s' : State} {rid : Int} {newMsg : Msg2}
    (hm1 : m1_requires_quorum s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1 : s'.msgs1 = s.msgs1)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 ∪
            insert newMsg (∅ : Finset Msg2))
          s.msgs2) :
    m1_requires_quorum s' := by
  classical
  apply m1_requires_quorum_mono_msgs2 hm1 hN hT hcorrect hfaulty hrounds hmsgs1
  intro r m hm
  rw [hmsgs2]
  by_cases hr : r = Finmap.lookupD rid s.round
  · subst r
    simp [lookupD_insert_self, hm]
  · rw [lookupD_insert_of_ne hr]
    exact hm

lemma step1_preserves_cannot_jump_rounds_without_quorum
    {s s' : State} {rid : Int}
    (hjumps : cannot_jump_rounds_without_quorum s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hround : s'.round = s.round)
    (hstep : s'.step = Finmap.insert rid Step.S2 s.step)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    cannot_jump_rounds_without_quorum s' := by
  unfold cannot_jump_rounds_without_quorum at hjumps ⊢
  intro r hr hnext hproc
  rw [hrounds] at hr hnext
  rcases hproc with ⟨id, hid, hround_id, hstep_id⟩
  rw [hcorrect] at hid
  rw [hround] at hround_id
  by_cases hsrc : id = rid
  · subst id
    rw [hstep, lookupD_insert_self] at hstep_id
    cases hstep_id
  · have hsrc_ne : id ≠ rid := hsrc
    rw [hstep, lookupD_insert_of_ne hsrc_ne] at hstep_id
    have hold := hjumps r hr hnext ⟨id, hid, hround_id, hstep_id⟩
    rw [hN, hT, hmsgs2]
    unfold senders2 allReplicas
    rw [hcorrect, hfaulty]
    exact hold

lemma step2_preserves_cannot_jump_rounds_without_quorum
    {s s' : State} {rid : Int} {newMsg : Msg2}
    (hjumps : cannot_jump_rounds_without_quorum s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hround : s'.round = s.round)
    (hstep : s'.step = Finmap.insert rid Step.S3 s.step)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 ∪
            insert newMsg (∅ : Finset Msg2))
          s.msgs2) :
    cannot_jump_rounds_without_quorum s' := by
  classical
  unfold cannot_jump_rounds_without_quorum at hjumps ⊢
  intro r hr hnext hproc
  rw [hrounds] at hr hnext
  rcases hproc with ⟨id, hid, hround_id, hstep_id⟩
  rw [hcorrect] at hid
  rw [hround] at hround_id
  by_cases hsrc : id = rid
  · subst id
    rw [hstep, lookupD_insert_self] at hstep_id
    cases hstep_id
  · have hsrc_ne : id ≠ rid := hsrc
    rw [hstep, lookupD_insert_of_ne hsrc_ne] at hstep_id
    have hold := hjumps r hr hnext ⟨id, hid, hround_id, hstep_id⟩
    have hsub :
        senders2 s (Finmap.lookupD r s.msgs2) ⊆
          senders2 s' (Finmap.lookupD r s'.msgs2) := by
      apply senders2_mono_frame (s := s) (s' := s') hcorrect hfaulty
      rw [hmsgs2]
      by_cases hrid_round : r = Finmap.lookupD rid s.round
      · subst r
        intro m hm
        simp [lookupD_insert_self, hm]
      · intro m hm
        rw [lookupD_insert_of_ne hrid_round]
        exact hm
    have hcard := Finset.card_le_card hsub
    rw [hN, hT]
    omega

lemma value_on_quorum_less_ram_mono_msgs
    {s s' : State}
    (hvalue_quorum : value_on_quorum_less_ram s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hvalue : s'.value = s.value)
    (hround : s'.round = s.round)
    (hmsgs2_sub : ∀ r, Finmap.lookupD r s.msgs2 ⊆ Finmap.lookupD r s'.msgs2) :
    value_on_quorum_less_ram s' := by
  unfold value_on_quorum_less_ram at hvalue_quorum ⊢
  intro id hid
  rw [hcorrect] at hid
  dsimp
  intro hgt
  rw [hround] at hgt
  have hold := hvalue_quorum id hid hgt
  rw [hN, hT, hvalue, hround]
  dsimp at hold ⊢
  rcases hold with hfast | hslow
  · left
    have hsub :=
      senders2_mono_frame (s := s) (s' := s')
        hcorrect hfaulty
        (d2MsgsFor_mono
          (v := Finmap.lookupD id s.value)
          (hmsgs2_sub (Finmap.lookupD id s.round - 1)))
    have hcard := Finset.card_le_card hsub
    omega
  · right
    rcases hslow with ⟨x0, hx0mem, x1, hx1mem, hx0le, hx1le, hsum, hx0bound, hx1bound⟩
    refine ⟨x0, ?_, x1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [hN] using hx0mem
    · simpa [hN] using hx1mem
    · have hcard :=
        Finset.card_le_card
          (d2MsgsFor_mono (v := 0) (hmsgs2_sub (Finmap.lookupD id s.round - 1)))
      omega
    · have hcard :=
        Finset.card_le_card
          (d2MsgsFor_mono (v := 1) (hmsgs2_sub (Finmap.lookupD id s.round - 1)))
      omega
    · have hcard :=
        Finset.card_le_card
          (q2Msgs_mono (hmsgs2_sub (Finmap.lookupD id s.round - 1)))
      omega
    · omega
    · omega

lemma frame_value_on_quorum_less_ram
    {s s' : State}
    (hvalue_quorum : value_on_quorum_less_ram s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hvalue : s'.value = s.value)
    (hround : s'.round = s.round)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    value_on_quorum_less_ram s' :=
  value_on_quorum_less_ram_mono_msgs
    hvalue_quorum hN hT hcorrect hfaulty hvalue hround
    (by intro r; rw [hmsgs2])

lemma step1_preserves_value_on_quorum_less_ram
    {s s' : State}
    (hvalue_quorum : value_on_quorum_less_ram s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hvalue : s'.value = s.value)
    (hround : s'.round = s.round)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    value_on_quorum_less_ram s' :=
  frame_value_on_quorum_less_ram
    hvalue_quorum hN hT hcorrect hfaulty hvalue hround hmsgs2

lemma step2_preserves_value_on_quorum_less_ram
    {s s' : State} {rid : Int} {newMsg : Msg2}
    (hvalue_quorum : value_on_quorum_less_ram s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hvalue : s'.value = s.value)
    (hround : s'.round = s.round)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 ∪
            insert newMsg (∅ : Finset Msg2))
          s.msgs2) :
    value_on_quorum_less_ram s' := by
  classical
  apply value_on_quorum_less_ram_mono_msgs
    hvalue_quorum hN hT hcorrect hfaulty hvalue hround
  intro r m hm
  rw [hmsgs2]
  by_cases hr : r = Finmap.lookupD rid s.round
  · subst r
    simp [lookupD_insert_self, hm]
  · rw [lookupD_insert_of_ne hr]
    exact hm

lemma faulty_step_preserves_value_on_quorum_less_ram
    {s s' : State} {r_faulty : Int} {f2d f2q : Finset Msg2}
    (hvalue_quorum : value_on_quorum_less_ram s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hvalue : s'.value = s.value)
    (hround : s'.round = s.round)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert r_faulty (Finmap.lookupD r_faulty s.msgs2 ∪ (f2d ∪ f2q)) s.msgs2) :
    value_on_quorum_less_ram s' := by
  classical
  apply value_on_quorum_less_ram_mono_msgs
    hvalue_quorum hN hT hcorrect hfaulty hvalue hround
  intro r m hm
  rw [hmsgs2]
  by_cases hr : r = r_faulty
  · subst r
    simp [lookupD_insert_self, hm]
  · rw [lookupD_insert_of_ne hr]
    exact hm

lemma frame_q2_requires_no_quorum_faster
    {s s' : State}
    (hq2 : q2_requires_no_quorum_faster s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1 : s'.msgs1 = s.msgs1)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    q2_requires_no_quorum_faster s' := by
  unfold q2_requires_no_quorum_faster at hq2 ⊢
  intro r hr hq
  rw [hrounds] at hr
  rcases hq with ⟨m, hm, hkind, hcorrect_m⟩
  rw [hmsgs2] at hm
  rw [hcorrect] at hcorrect_m
  have hold := hq2 r hr ⟨m, hm, hkind, hcorrect_m⟩
  simpa [senders1, allReplicas, hN, hT, hcorrect, hfaulty, hmsgs1] using hold

lemma step3_preserves_q2_requires_no_quorum_faster
    {s s' : State}
    (hq2 : q2_requires_no_quorum_faster s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1 : s'.msgs1 = s.msgs1)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    q2_requires_no_quorum_faster s' :=
  frame_q2_requires_no_quorum_faster hq2 hN hT hcorrect hfaulty hrounds hmsgs1 hmsgs2

lemma q2_requires_no_quorum_faster_mono_msgs1
    {s s' : State}
    (hq2 : q2_requires_no_quorum_faster s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs2 : s'.msgs2 = s.msgs2)
    (hn0_sub :
      ∀ r,
        Finset.filter (fun id => Msg1.mk r id 0 ∈ Finmap.lookupD r s.msgs1) s.CORRECT ⊆
          Finset.filter (fun id => Msg1.mk r id 0 ∈ Finmap.lookupD r s'.msgs1) s'.CORRECT)
    (hn1_sub :
      ∀ r,
        Finset.filter (fun id => Msg1.mk r id 1 ∈ Finmap.lookupD r s.msgs1) s.CORRECT ⊆
          Finset.filter (fun id => Msg1.mk r id 1 ∈ Finmap.lookupD r s'.msgs1) s'.CORRECT)
    (hnf_sub :
      ∀ r,
        Finset.filter (fun id => id ∈ senders1 s (Finmap.lookupD r s.msgs1)) s.FAULTY ⊆
          Finset.filter (fun id => id ∈ senders1 s' (Finmap.lookupD r s'.msgs1)) s'.FAULTY) :
    q2_requires_no_quorum_faster s' := by
  unfold q2_requires_no_quorum_faster at hq2 ⊢
  intro r hr hq
  rw [hrounds] at hr
  rcases hq with ⟨m, hm, hkind, hcorrect_m⟩
  rw [hmsgs2] at hm
  rw [hcorrect] at hcorrect_m
  rcases hq2 r hr ⟨m, hm, hkind, hcorrect_m⟩ with
    ⟨x0, hx0mem, x1, hx1mem, hx0le, hx1le, hsum, hx0bound, hx1bound⟩
  have hn0card := Finset.card_le_card (hn0_sub r)
  have hn1card := Finset.card_le_card (hn1_sub r)
  have hnfcard := Finset.card_le_card (hnf_sub r)
  refine ⟨x0, ?_, x1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hN] using hx0mem
  · simpa [hN] using hx1mem
  · omega
  · omega
  · omega
  · omega
  · omega

lemma step1_preserves_q2_requires_no_quorum_faster
    {s s' : State} {rid : Int}
    (hq2 : q2_requires_no_quorum_faster s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1 :
      s'.msgs1 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs1 ∪
            insert { round := Finmap.lookupD rid s.round, src := rid, value := Finmap.lookupD rid s.value }
              (∅ : Finset Msg1))
          s.msgs1)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    q2_requires_no_quorum_faster s' := by
  classical
  apply q2_requires_no_quorum_faster_mono_msgs1
    hq2 hN hT hcorrect hrounds hmsgs2
  · intro r id hid
    rw [hcorrect]
    rcases Finset.mem_filter.mp hid with ⟨hid_correct, hmsg⟩
    refine Finset.mem_filter.mpr ⟨hid_correct, ?_⟩
    rw [hmsgs1]
    by_cases hr : r = Finmap.lookupD rid s.round
    · subst r
      simp [lookupD_insert_self, hmsg]
    · rw [lookupD_insert_of_ne hr]
      exact hmsg
  · intro r id hid
    rw [hcorrect]
    rcases Finset.mem_filter.mp hid with ⟨hid_correct, hmsg⟩
    refine Finset.mem_filter.mpr ⟨hid_correct, ?_⟩
    rw [hmsgs1]
    by_cases hr : r = Finmap.lookupD rid s.round
    · subst r
      simp [lookupD_insert_self, hmsg]
    · rw [lookupD_insert_of_ne hr]
      exact hmsg
  · intro r id hid
    rcases Finset.mem_filter.mp hid with ⟨hid_faulty, hsender⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [hfaulty]
      exact hid_faulty
    · have hsubmsgs :
          Finmap.lookupD r s.msgs1 ⊆ Finmap.lookupD r s'.msgs1 := by
        rw [hmsgs1]
        by_cases hr : r = Finmap.lookupD rid s.round
        · subst r
          intro m hm
          simp [lookupD_insert_self, hm]
        · intro m hm
          rw [lookupD_insert_of_ne hr]
          exact hm
      exact senders1_mono_frame (s := s) (s' := s') hcorrect hfaulty hsubmsgs hsender

lemma q2_no_quorum_conclusion_mono_msgs1
    {s s' : State} {r : Int}
    (hold :
      let n0 :=
        Finset.card
          (Finset.filter (fun id => Msg1.mk r id 0 ∈ Finmap.lookupD r s.msgs1) s.CORRECT)
      let n1 :=
        Finset.card
          (Finset.filter (fun id => Msg1.mk r id 1 ∈ Finmap.lookupD r s.msgs1) s.CORRECT)
      let nf :=
        Finset.card
          (Finset.filter
            (fun id => id ∈ senders1 s (Finmap.lookupD r s.msgs1))
            s.FAULTY)
      ∃ x0 ∈ Finset.Icc 0 s.N,
        ∃ x1 ∈ Finset.Icc 0 s.N,
          x0 ≤ n0 ∧ x1 ≤ n1 ∧ x0 + x1 + nf ≥ s.N - s.T ∧
            2 * x0 ≤ s.N + s.T ∧ 2 * x1 ≤ s.N + s.T)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hn0_sub :
      Finset.filter (fun id => Msg1.mk r id 0 ∈ Finmap.lookupD r s.msgs1) s.CORRECT ⊆
        Finset.filter (fun id => Msg1.mk r id 0 ∈ Finmap.lookupD r s'.msgs1) s'.CORRECT)
    (hn1_sub :
      Finset.filter (fun id => Msg1.mk r id 1 ∈ Finmap.lookupD r s.msgs1) s.CORRECT ⊆
        Finset.filter (fun id => Msg1.mk r id 1 ∈ Finmap.lookupD r s'.msgs1) s'.CORRECT)
    (hnf_sub :
      Finset.filter (fun id => id ∈ senders1 s (Finmap.lookupD r s.msgs1)) s.FAULTY ⊆
        Finset.filter (fun id => id ∈ senders1 s' (Finmap.lookupD r s'.msgs1)) s'.FAULTY) :
      let n0 :=
        Finset.card
          (Finset.filter (fun id => Msg1.mk r id 0 ∈ Finmap.lookupD r s'.msgs1) s'.CORRECT)
      let n1 :=
        Finset.card
          (Finset.filter (fun id => Msg1.mk r id 1 ∈ Finmap.lookupD r s'.msgs1) s'.CORRECT)
      let nf :=
        Finset.card
          (Finset.filter
            (fun id => id ∈ senders1 s' (Finmap.lookupD r s'.msgs1))
            s'.FAULTY)
      ∃ x0 ∈ Finset.Icc 0 s'.N,
        ∃ x1 ∈ Finset.Icc 0 s'.N,
          x0 ≤ n0 ∧ x1 ≤ n1 ∧ x0 + x1 + nf ≥ s'.N - s'.T ∧
            2 * x0 ≤ s'.N + s'.T ∧ 2 * x1 ≤ s'.N + s'.T := by
  rcases hold with
    ⟨x0, hx0mem, x1, hx1mem, hx0le, hx1le, hsum, hx0bound, hx1bound⟩
  have hn0card := Finset.card_le_card hn0_sub
  have hn1card := Finset.card_le_card hn1_sub
  have hnfcard := Finset.card_le_card hnf_sub
  refine ⟨x0, ?_, x1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hN] using hx0mem
  · simpa [hN] using hx1mem
  · omega
  · omega
  · omega
  · omega
  · omega

lemma step2_d2_preserves_q2_requires_no_quorum_faster
    {s s' : State} {rid v : Int}
    (hq2 : q2_requires_no_quorum_faster s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1 : s'.msgs1 = s.msgs1)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 ∪
            insert { kind := Msg2Kind.D2, round := Finmap.lookupD rid s.round, src := rid, value := v }
              (∅ : Finset Msg2))
          s.msgs2) :
    q2_requires_no_quorum_faster s' := by
  classical
  unfold q2_requires_no_quorum_faster at hq2 ⊢
  intro r hr hq
  rw [hrounds] at hr
  rcases hq with ⟨m, hm, hkind, hcorrect_m⟩
  rw [hcorrect] at hcorrect_m
  rw [hmsgs2] at hm
  by_cases hrid_round : r = Finmap.lookupD rid s.round
  · subst r
    simp [lookupD_insert_self] at hm
    rcases hm with hmnew | hmold
    · rw [hmnew] at hkind
      simp at hkind
    · have hold' := hq2 (Finmap.lookupD rid s.round) hr ⟨m, hmold, hkind, hcorrect_m⟩
      simpa [senders1, allReplicas, hN, hT, hcorrect, hfaulty, hmsgs1] using hold'
  · rw [lookupD_insert_of_ne hrid_round] at hm
    have hold' := hq2 r hr ⟨m, hm, hkind, hcorrect_m⟩
    simpa [senders1, allReplicas, hN, hT, hcorrect, hfaulty, hmsgs1] using hold'

lemma faulty_step_preserves_q2_requires_no_quorum_faster
    {s s' : State} {r_faulty : Int} {f1 : Finset Msg1} {f2d f2q : Finset Msg2}
    (hdisj : s.CORRECT ∩ s.FAULTY = ∅)
    (hq2 : q2_requires_no_quorum_faster s)
    (hf2d :
      f2d ∈
        Finset.powerset
          (Finset.image (fun x => Msg2.mk Msg2Kind.D2 r_faulty (x).1 (x).2)
            (Finset.product s.FAULTY (insert 0 (insert 1 (∅ : Finset Int))))))
    (hf2q :
      f2q ∈
        Finset.powerset
          (Finset.image (fun src => Msg2.mk Msg2Kind.Q2 r_faulty src (-2)) s.FAULTY))
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1 :
      s'.msgs1 = Finmap.insert r_faulty (Finmap.lookupD r_faulty s.msgs1 ∪ f1) s.msgs1)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert r_faulty (Finmap.lookupD r_faulty s.msgs2 ∪ (f2d ∪ f2q)) s.msgs2) :
    q2_requires_no_quorum_faster s' := by
  classical
  unfold q2_requires_no_quorum_faster at hq2 ⊢
  intro r hr hq
  rw [hrounds] at hr
  rcases hq with ⟨m, hm, hkind, hcorrect_m⟩
  rw [hcorrect] at hcorrect_m
  rw [hmsgs2] at hm
  have hmsgs1_sub :
      Finmap.lookupD r s.msgs1 ⊆ Finmap.lookupD r s'.msgs1 := by
    rw [hmsgs1]
    by_cases hr : r = r_faulty
    · subst r
      intro msg hmsg
      simp [lookupD_insert_self, hmsg]
    · intro msg hmsg
      rw [lookupD_insert_of_ne hr]
      exact hmsg
  have hn0_sub :
      Finset.filter (fun id => Msg1.mk r id 0 ∈ Finmap.lookupD r s.msgs1) s.CORRECT ⊆
        Finset.filter (fun id => Msg1.mk r id 0 ∈ Finmap.lookupD r s'.msgs1) s'.CORRECT := by
    intro id hid
    rcases Finset.mem_filter.mp hid with ⟨hid_correct, hmsg⟩
    refine Finset.mem_filter.mpr ⟨?_, hmsgs1_sub hmsg⟩
    rw [hcorrect]
    exact hid_correct
  have hn1_sub :
      Finset.filter (fun id => Msg1.mk r id 1 ∈ Finmap.lookupD r s.msgs1) s.CORRECT ⊆
        Finset.filter (fun id => Msg1.mk r id 1 ∈ Finmap.lookupD r s'.msgs1) s'.CORRECT := by
    intro id hid
    rcases Finset.mem_filter.mp hid with ⟨hid_correct, hmsg⟩
    refine Finset.mem_filter.mpr ⟨?_, hmsgs1_sub hmsg⟩
    rw [hcorrect]
    exact hid_correct
  have hnf_sub :
      Finset.filter (fun id => id ∈ senders1 s (Finmap.lookupD r s.msgs1)) s.FAULTY ⊆
        Finset.filter (fun id => id ∈ senders1 s' (Finmap.lookupD r s'.msgs1)) s'.FAULTY := by
    intro id hid
    rcases Finset.mem_filter.mp hid with ⟨hid_faulty, hsender⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [hfaulty]
      exact hid_faulty
    · exact senders1_mono_frame (s := s) (s' := s') hcorrect hfaulty hmsgs1_sub hsender
  have old_conclusion
      (hmold : m ∈ Finmap.lookupD r s.msgs2) :
      let n0 :=
        Finset.card
          (Finset.filter (fun id => Msg1.mk r id 0 ∈ Finmap.lookupD r s'.msgs1) s'.CORRECT)
      let n1 :=
        Finset.card
          (Finset.filter (fun id => Msg1.mk r id 1 ∈ Finmap.lookupD r s'.msgs1) s'.CORRECT)
      let nf :=
        Finset.card
          (Finset.filter
            (fun id => id ∈ senders1 s' (Finmap.lookupD r s'.msgs1))
            s'.FAULTY)
      ∃ x0 ∈ Finset.Icc 0 s'.N,
        ∃ x1 ∈ Finset.Icc 0 s'.N,
          x0 ≤ n0 ∧ x1 ≤ n1 ∧ x0 + x1 + nf ≥ s'.N - s'.T ∧
            2 * x0 ≤ s'.N + s'.T ∧ 2 * x1 ≤ s'.N + s'.T := by
    exact q2_no_quorum_conclusion_mono_msgs1
      (s := s) (s' := s') (r := r)
      (hq2 r hr ⟨m, hmold, hkind, hcorrect_m⟩)
      hN hT hn0_sub hn1_sub hnf_sub
  by_cases hr_faulty : r = r_faulty
  · subst r
    simp [lookupD_insert_self] at hm
    rcases hm with hmold | hmnew
    · exact old_conclusion hmold
    · rcases hmnew with hmd | hmq
      · have hnot := msg2_d2_src_not_correct_of_mem_faulty_step (s := s) hdisj hf2d hmd
        exact False.elim (hnot hcorrect_m)
      · have hnot := msg2_q2_src_not_correct_of_mem_faulty_step (s := s) hdisj hf2q hmq
        exact False.elim (hnot hcorrect_m)
  · rw [lookupD_insert_of_ne hr_faulty] at hm
    exact old_conclusion hm

lemma frame_existsQuorum1
    {s s' : State} {r v : Int}
    (hquorum : existsQuorum1 s r v)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hmsgs1 : s'.msgs1 = s.msgs1) :
    existsQuorum1 s' r v := by
  unfold existsQuorum1 at hquorum ⊢
  rw [hN, hT, hmsgs1]
  unfold senders1 allReplicas
  rw [hcorrect, hfaulty]
  exact hquorum

lemma existsQuorum1_faulty_step
    {s s' : State} {r v r_faulty : Int} {f1 : Finset Msg1}
    (hquorum : existsQuorum1 s r v)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hmsgs1 :
      s'.msgs1 =
        Finmap.insert r_faulty (Finmap.lookupD r_faulty s.msgs1 ∪ f1) s.msgs1) :
    existsQuorum1 s' r v := by
  classical
  unfold existsQuorum1 at hquorum ⊢
  rw [hN, hT, hmsgs1]
  by_cases hr_faulty : r = r_faulty
  · subst r
    simp [lookupD_insert_self]
    have hsub_msgs :
        Finset.filter (fun m => Msg1.value m = v) (Finmap.lookupD r_faulty s.msgs1) ⊆
          Finset.filter (fun m => Msg1.value m = v) (Finmap.lookupD r_faulty s.msgs1 ∪ f1) := by
      intro m hm
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mp hm).1),
          (Finset.mem_filter.mp hm).2⟩
    have hsub := senders1_mono_frame (s := s) (s' := s') hcorrect hfaulty hsub_msgs
    have hcard := Finset.card_le_card hsub
    omega
  · rw [lookupD_insert_of_ne hr_faulty]
    unfold senders1 allReplicas at hquorum ⊢
    rw [hcorrect, hfaulty]
    exact hquorum

lemma allReplicas_card_eq_N
    {s : State}
    (hassumptions : assumptions_hold s)
    (hdisj : s.CORRECT ∩ s.FAULTY = ∅) :
    (Finset.card (allReplicas s) : Int) = s.N := by
  unfold assumptions_hold at hassumptions
  rcases hassumptions with ⟨_, hcorrect_card, hfaulty_card, _, _⟩
  unfold allReplicas
  have hunion :=
    Finset.card_union_add_card_inter s.CORRECT s.FAULTY
  have hinter : Finset.card (s.CORRECT ∩ s.FAULTY) = 0 := by
    rw [hdisj]
    simp
  rw [hinter] at hunion
  omega

lemma correct_senders1_value_disjoint
    {s : State} {r v w : Int}
    (hnoeq : no_equivocation1_by_correct s)
    (hr : r ∈ s.ROUNDS)
    (hvw : v ≠ w) :
    Disjoint
      (Finset.filter
        (fun id => id ∈ senders1 s (Finset.filter (fun m => Msg1.value m = v) (Finmap.lookupD r s.msgs1)))
        s.CORRECT)
      (Finset.filter
        (fun id => id ∈ senders1 s (Finset.filter (fun m => Msg1.value m = w) (Finmap.lookupD r s.msgs1)))
        s.CORRECT) := by
  rw [Finset.disjoint_left]
  intro id hidv hidw
  rcases Finset.mem_filter.mp hidv with ⟨hid_correct, hsendv⟩
  rcases Finset.mem_filter.mp hidw with ⟨_, hsendw⟩
  unfold senders1 at hsendv hsendw
  rcases Finset.mem_filter.mp hsendv with ⟨_, mv, hmv, hsrcv⟩
  rcases Finset.mem_filter.mp hsendw with ⟨_, mw, hmw, hsrcw⟩
  rcases Finset.mem_filter.mp hmv with ⟨hmv_full, hmv_value⟩
  rcases Finset.mem_filter.mp hmw with ⟨hmw_full, hmw_value⟩
  have heq_value :=
    hnoeq r hr mv hmv_full mw hmw_full
      ⟨by rw [← hsrcv]; exact hid_correct,
        by rw [← hsrcv, ← hsrcw]⟩
  rw [hmv_value, hmw_value] at heq_value
  exact hvw heq_value

lemma correct_senders1_value_inter_subset_faulty
    {s : State} {r v w : Int}
    (hnoeq : no_equivocation1_by_correct s)
    (hr : r ∈ s.ROUNDS)
    (hvw : v ≠ w) :
    (senders1 s (Finset.filter (fun m => Msg1.value m = v) (Finmap.lookupD r s.msgs1)) ∩
        senders1 s (Finset.filter (fun m => Msg1.value m = w) (Finmap.lookupD r s.msgs1))) ⊆
      s.FAULTY := by
  intro id hid
  by_cases hid_correct : id ∈ s.CORRECT
  · have hdisj :=
      correct_senders1_value_disjoint
        (s := s) (r := r) (v := v) (w := w) hnoeq hr hvw
    have hidv :
        id ∈
          Finset.filter
            (fun id => id ∈ senders1 s (Finset.filter (fun m => Msg1.value m = v) (Finmap.lookupD r s.msgs1)))
            s.CORRECT := by
      exact Finset.mem_filter.mpr ⟨hid_correct, (Finset.mem_inter.mp hid).1⟩
    have hidw :
        id ∈
          Finset.filter
            (fun id => id ∈ senders1 s (Finset.filter (fun m => Msg1.value m = w) (Finmap.lookupD r s.msgs1)))
            s.CORRECT := by
      exact Finset.mem_filter.mpr ⟨hid_correct, (Finset.mem_inter.mp hid).2⟩
    exact False.elim (((Finset.disjoint_left.mp hdisj) hidv) hidw)
  · have hall : id ∈ allReplicas s := by
      unfold senders1 at hid
      exact (Finset.mem_filter.mp (Finset.mem_inter.mp hid).1).1
    unfold allReplicas at hall
    rcases Finset.mem_union.mp hall with hidc | hidf
    · exact False.elim (hid_correct hidc)
    · exact hidf

lemma existsQuorum1_distinct_values_impossible
    {s : State} {r v w : Int}
    (hassumptions : assumptions_hold s)
    (hdisj : s.CORRECT ∩ s.FAULTY = ∅)
    (hFleT : s.F ≤ s.T)
    (hnoeq : no_equivocation1_by_correct s)
    (hr : r ∈ s.ROUNDS)
    (hvw : v ≠ w)
    (hqv : existsQuorum1 s r v)
    (hqw : existsQuorum1 s r w) :
    False := by
  classical
  let sv := senders1 s (Finset.filter (fun m => Msg1.value m = v) (Finmap.lookupD r s.msgs1))
  let sw := senders1 s (Finset.filter (fun m => Msg1.value m = w) (Finmap.lookupD r s.msgs1))
  have hcard_all := allReplicas_card_eq_N (s := s) hassumptions hdisj
  have hsub_union : sv ∪ sw ⊆ allReplicas s := by
    intro id hid
    rcases Finset.mem_union.mp hid with hid | hid
    · unfold sv senders1 at hid
      exact (Finset.mem_filter.mp hid).1
    · unfold sw senders1 at hid
      exact (Finset.mem_filter.mp hid).1
  have hcard_union := Finset.card_le_card hsub_union
  have hinter_sub :
      sv ∩ sw ⊆ s.FAULTY := by
    simpa [sv, sw] using
      correct_senders1_value_inter_subset_faulty
        (s := s) (r := r) (v := v) (w := w) hnoeq hr hvw
  have hcard_inter := Finset.card_le_card hinter_sub
  unfold assumptions_hold at hassumptions
  rcases hassumptions with ⟨_, _, hfaulty_card, _, _⟩
  have hcard_sum := Finset.card_union_add_card_inter sv sw
  unfold existsQuorum1 at hqv hqw
  change 2 * (Finset.card sv : Int) > s.N + s.T at hqv
  change 2 * (Finset.card sw : Int) > s.N + s.T at hqw
  omega

lemma existsQuorum1_eq_of_all_correct_msg1
    {s : State} {r v w : Int}
    (hassumptions : assumptions_hold s)
    (hFleT : s.F ≤ s.T)
    (hall :
      ∀ m ∈ Finmap.lookupD r s.msgs1,
        m.src ∈ s.CORRECT → m.value = v)
    (hquorum : existsQuorum1 s r w) :
    w = v := by
  classical
  by_contra hne
  let sw := senders1 s (Finset.filter (fun m => Msg1.value m = w) (Finmap.lookupD r s.msgs1))
  have hsub_faulty : sw ⊆ s.FAULTY := by
    intro id hid
    unfold sw senders1 at hid
    rcases Finset.mem_filter.mp hid with ⟨hall_id, m, hm, hsrc⟩
    by_cases hcorrect_id : id ∈ s.CORRECT
    · rcases Finset.mem_filter.mp hm with ⟨hm_full, hvalue_w⟩
      have hcorrect_m : m.src ∈ s.CORRECT := by
        rw [← hsrc]
        exact hcorrect_id
      have hvalue_v := hall m hm_full hcorrect_m
      have hwv : w = v := hvalue_w.symm.trans hvalue_v
      exact False.elim (hne hwv)
    · unfold allReplicas at hall_id
      rcases Finset.mem_union.mp hall_id with hcorrect | hfaulty
      · exact False.elim (hcorrect_id hcorrect)
      · exact hfaulty
  have hcard_faulty := Finset.card_le_card hsub_faulty
  unfold assumptions_hold at hassumptions
  rcases hassumptions with ⟨hNgt, _, hfaulty_card, _, _⟩
  unfold existsQuorum1 at hquorum
  change 2 * (Finset.card sw : Int) > s.N + s.T at hquorum
  have hcard_le_F : (Finset.card sw : Int) ≤ s.F := by
    rw [hfaulty_card]
    exact_mod_cast hcard_faulty
  omega

lemma existsQuorum1_has_correct_msg1_base
    {s : State} {r v : Int}
    (hbase : model_base_assumptions s)
    (hquorum : existsQuorum1 s r v) :
    ∃ m ∈ Finmap.lookupD r s.msgs1, m.src ∈ s.CORRECT ∧ m.value = v := by
  classical
  have hbase_parts := hbase
  unfold model_base_assumptions at hbase_parts
  rcases hbase_parts with ⟨hassumptions, _, _, _, hFleT⟩
  let sv := senders1 s (Finset.filter (fun m => Msg1.value m = v) (Finmap.lookupD r s.msgs1))
  by_contra hnone
  have hsub_faulty : sv ⊆ s.FAULTY := by
    intro id hid
    unfold sv senders1 at hid
    rcases Finset.mem_filter.mp hid with ⟨hall, m, hm, hsrc⟩
    rcases Finset.mem_filter.mp hm with ⟨hm_msgs, hvalue⟩
    by_cases hid_correct : id ∈ s.CORRECT
    · have hcorrect_m : m.src ∈ s.CORRECT := by
        rw [← hsrc]
        exact hid_correct
      exact False.elim (hnone ⟨m, hm_msgs, hcorrect_m, hvalue⟩)
    · unfold allReplicas at hall
      rcases Finset.mem_union.mp hall with hcorrect | hfaulty
      · exact False.elim (hid_correct hcorrect)
      · exact hfaulty
  have hcard_faulty := Finset.card_le_card hsub_faulty
  unfold assumptions_hold at hassumptions
  rcases hassumptions with ⟨_, _, hfaulty_card, _, _⟩
  unfold existsQuorum1 at hquorum
  change 2 * (Finset.card sv : Int) > s.N + s.T at hquorum
  have hcard_le_F : (Finset.card sv : Int) ≤ s.F := by
    rw [hfaulty_card]
    exact_mod_cast hcard_faulty
  omega

lemma supportedValues_has_correct_d2
    {s : State} {r v : Int}
    (hassumptions : assumptions_hold s)
    (hFleT : s.F ≤ s.T)
    (hsup : v ∈ supportedValues s r) :
    ∃ m ∈ Finmap.lookupD r s.msgs2,
      m.kind = Msg2Kind.D2 ∧ m.value = v ∧ m.src ∈ s.CORRECT := by
  classical
  let msgs := Finmap.lookupD r s.msgs2
  let sv := senders2 s (d2MsgsFor v msgs)
  unfold supportedValues at hsup
  rcases Finset.mem_filter.mp hsup with ⟨_, _, hcard_sv, _⟩
  by_contra hnone
  have hsub_faulty : sv ⊆ s.FAULTY := by
    intro id hid
    unfold sv senders2 at hid
    rcases Finset.mem_filter.mp hid with ⟨hall, m, hm, hsrc⟩
    unfold allReplicas at hall
    rcases Finset.mem_union.mp hall with hid_correct | hid_faulty
    · have hm_full : m ∈ Finmap.lookupD r s.msgs2 := by
        unfold msgs d2MsgsFor at hm
        exact (Finset.mem_filter.mp hm).1
      have hkind : m.kind = Msg2Kind.D2 := by
        unfold msgs d2MsgsFor at hm
        exact (Finset.mem_filter.mp hm).2.1
      have hvalue : m.value = v := by
        unfold msgs d2MsgsFor at hm
        exact (Finset.mem_filter.mp hm).2.2
      have hcorrect_m : m.src ∈ s.CORRECT := by
        rw [← hsrc]
        exact hid_correct
      exact False.elim (hnone ⟨m, hm_full, hkind, hvalue, hcorrect_m⟩)
    · exact hid_faulty
  have hcard_faulty := Finset.card_le_card hsub_faulty
  unfold assumptions_hold at hassumptions
  rcases hassumptions with ⟨_, _, hfaulty_card, _, _⟩
  change (Finset.card sv : Int) ≥ s.T + 1 at hcard_sv
  omega

lemma d2_senders_has_correct
    {s : State} {msgs : Finset Msg2} {v : Int}
    (hassumptions : assumptions_hold s)
    (hFleT : s.F ≤ s.T)
    (hcard :
      (Finset.card (senders2 s (d2MsgsFor v msgs)) : Int) ≥ s.T + 1) :
    ∃ m ∈ msgs, m.kind = Msg2Kind.D2 ∧ m.value = v ∧ m.src ∈ s.CORRECT := by
  classical
  let sv := senders2 s (d2MsgsFor v msgs)
  by_contra hnone
  have hsub_faulty : sv ⊆ s.FAULTY := by
    intro id hid
    unfold sv senders2 at hid
    rcases Finset.mem_filter.mp hid with ⟨hall, m, hm, hsrc⟩
    unfold allReplicas at hall
    rcases Finset.mem_union.mp hall with hid_correct | hid_faulty
    · unfold d2MsgsFor at hm
      rcases Finset.mem_filter.mp hm with ⟨hm_msgs, hkind, hvalue⟩
      have hcorrect_m : m.src ∈ s.CORRECT := by
        rw [← hsrc]
        exact hid_correct
      exact False.elim (hnone ⟨m, hm_msgs, hkind, hvalue, hcorrect_m⟩)
    · exact hid_faulty
  have hcard_faulty := Finset.card_le_card hsub_faulty
  unfold assumptions_hold at hassumptions
  rcases hassumptions with ⟨_, _, hfaulty_card, _, _⟩
  change (Finset.card sv : Int) ≥ s.T + 1 at hcard
  omega

lemma senders2_d2MsgsFor_card_eq
    {s : State} {r v : Int} {msgs : Finset Msg2}
    (htype : type_ok s)
    (hr : r ∈ s.ROUNDS)
    (hsub : msgs ⊆ Finmap.lookupD r s.msgs2) :
    Finset.card (senders2 s (d2MsgsFor v msgs)) =
      Finset.card (d2MsgsFor v msgs) := by
  classical
  have hsenders_image :
      senders2 s (d2MsgsFor v msgs) =
        Finset.image Msg2.src (d2MsgsFor v msgs) := by
    apply Finset.ext
    intro id
    constructor
    · intro hid
      exact senders2_subset_image_src (s := s) (msgs := d2MsgsFor v msgs) hid
    · intro hid
      rcases Finset.mem_image.mp hid with ⟨m, hm, rfl⟩
      have hm_msgs : m ∈ msgs := (Finset.mem_filter.mp hm).1
      have hm_full : m ∈ Finmap.lookupD r s.msgs2 := hsub hm_msgs
      have hsrc_all := (htype.2.2.2.2.2 r hr m hm_full).1
      unfold senders2
      exact Finset.mem_filter.mpr ⟨hsrc_all, m, hm, rfl⟩
  rw [hsenders_image]
  exact Finset.card_image_of_injOn (s := d2MsgsFor v msgs) (f := Msg2.src) (by
    intro m1 hm1 m2 hm2 hsrc
    have hm1_msgs : m1 ∈ msgs := (Finset.mem_filter.mp hm1).1
    have hm2_msgs : m2 ∈ msgs := (Finset.mem_filter.mp hm2).1
    have hm1_full : m1 ∈ Finmap.lookupD r s.msgs2 := hsub hm1_msgs
    have hm2_full : m2 ∈ Finmap.lookupD r s.msgs2 := hsub hm2_msgs
    have hround1 := msg2_round_eq_of_type_ok (s := s) (r := r) (m := m1) htype hr hm1_full
    have hround2 := msg2_round_eq_of_type_ok (s := s) (r := r) (m := m2) htype hr hm2_full
    have hkind1 : m1.kind = Msg2Kind.D2 := (Finset.mem_filter.mp hm1).2.1
    have hkind2 : m2.kind = Msg2Kind.D2 := (Finset.mem_filter.mp hm2).2.1
    have hvalue1 : m1.value = v := (Finset.mem_filter.mp hm1).2.2
    have hvalue2 : m2.value = v := (Finset.mem_filter.mp hm2).2.2
    cases m1
    cases m2
    simp at hsrc hround1 hround2 hkind1 hkind2 hvalue1 hvalue2 ⊢
    exact ⟨hkind1.trans hkind2.symm, hround1.symm.trans hround2, hsrc, hvalue1.trans hvalue2.symm⟩)

lemma existsQuorum2LessRam_supported_of_total_senders
    {s : State} {r v : Int}
    (hbase : model_base_assumptions s)
    (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (hr : r ∈ s.ROUNDS)
    (hv : v ∈ values)
    (hquorum : existsQuorum2LessRam s r v)
    (htotal : (Finset.card (senders2 s (Finmap.lookupD r s.msgs2)) : Int) ≥ s.N - s.T) :
    v ∈ supportedValues s r := by
  classical
  let msgs := Finmap.lookupD r s.msgs2
  let sv := senders2 s (d2MsgsFor v msgs)
  let others :=
    senders2 s
      (Finset.filter
        (fun m => Msg2.kind m = Msg2Kind.Q2 ∨ Msg2.value m ≠ v)
        msgs)
  unfold model_base_assumptions at hbase
  rcases hbase with ⟨hassumptions, hdisj, _, _, hFleT⟩
  unfold ind_inv_13 at hinv
  rcases hinv with ⟨_, hnoeq2, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold existsQuorum2LessRam at hquorum
  rcases hquorum with ⟨_hmsg_total, hd2_ge, hd2_fast⟩
  have hcard_sv_eq :
      Finset.card sv = Finset.card (d2MsgsFor v msgs) := by
    exact senders2_d2MsgsFor_card_eq
      (s := s) (r := r) (v := v) (msgs := msgs)
      htype hr (by intro m hm; exact hm)
  have hsv_ge : (Finset.card sv : Int) ≥ s.T + 1 := by
    rw [hcard_sv_eq]
    exact hd2_ge
  have hsv_fast : 2 * (Finset.card sv : Int) > s.N + s.T := by
    rw [hcard_sv_eq]
    exact hd2_fast
  have hinter_sub : sv ∩ others ⊆ s.FAULTY := by
    intro id hid
    rcases Finset.mem_inter.mp hid with ⟨hid_sv, hid_other⟩
    unfold sv senders2 d2MsgsFor at hid_sv
    unfold others senders2 at hid_other
    rcases Finset.mem_filter.mp hid_sv with ⟨hall_sv, md, hmd, hsrcd⟩
    rcases Finset.mem_filter.mp hmd with ⟨hmd_full, hmd_kind, hmd_value⟩
    rcases Finset.mem_filter.mp hid_other with ⟨_hall_other, mo, hmo, hsrco⟩
    rcases Finset.mem_filter.mp hmo with ⟨hmo_full, hother⟩
    unfold allReplicas at hall_sv
    rcases Finset.mem_union.mp hall_sv with hid_correct | hid_faulty
    · have hmd_correct : md.src ∈ s.CORRECT := by
        rw [← hsrcd]
        exact hid_correct
      rcases hother with hq | hne_value
      · have hfaulty_src :=
          (hnoeq2 r hr mo hmo_full md hmd_full).2
            ⟨hq, hmd_kind, hsrco.symm.trans hsrcd⟩
        rw [hsrco]
        exact hfaulty_src
      · have hkind_mem := (htype.2.2.2.2.2 r hr mo hmo_full).2.2.1
        simp at hkind_mem
        rcases hkind_mem with hD | hQ
        · have hsame :=
            (hnoeq2 r hr md hmd_full mo hmo_full).1
              ⟨hmd_kind, hD, hsrcd.symm.trans hsrco⟩
              hmd_correct
          rw [hmd_value] at hsame
          exact False.elim (hne_value hsame.symm)
        · have hfaulty_src :=
            (hnoeq2 r hr mo hmo_full md hmd_full).2
              ⟨hQ, hmd_kind, hsrco.symm.trans hsrcd⟩
          rw [hsrco]
          exact hfaulty_src
    · exact hid_faulty
  have hcard_all := allReplicas_card_eq_N (s := s) hassumptions hdisj
  have hunion_sub : sv ∪ others ⊆ allReplicas s := by
    intro id hid
    rcases Finset.mem_union.mp hid with hid | hid
    · unfold sv senders2 at hid
      exact (Finset.mem_filter.mp hid).1
    · unfold others senders2 at hid
      exact (Finset.mem_filter.mp hid).1
  have hcard_union_le := Finset.card_le_card hunion_sub
  have hcard_inter_le := Finset.card_le_card hinter_sub
  have hcard_union_inter := Finset.card_union_add_card_inter sv others
  unfold assumptions_hold at hassumptions
  rcases hassumptions with ⟨_, _, hfaulty_card, _, _⟩
  have hothers_lt : (Finset.card others : Int) < s.N - 2 * s.T := by
    omega
  unfold supportedValues
  refine Finset.mem_filter.mpr ⟨hv, ?_, ?_, ?_⟩
  · simpa [msgs, sv] using htotal
  · simpa [msgs, sv] using hsv_ge
  · simpa [msgs, others] using hothers_lt

lemma generated_step3_value_supported_or_empty
    {s : State} {r v : Int} {received : Finset Msg2}
    (hmodel : model_assumptions s)
    (hinv : ind_inv_13 s)
    (hr : r ∈ s.ROUNDS)
    (hv_values : v ∈ values)
    (hreceived : received ∈ Finset.powerset (Finmap.lookupD r s.msgs2))
    (hd2_received :
      Finset.card
          (Finset.filter
            (fun id =>
              ∃ m ∈ Finset.filter (fun m => Msg2.kind m = Msg2Kind.D2 ∧ v = Msg2.value m) received,
                id = Msg2.src m)
            (s.CORRECT ∪ s.FAULTY)) ≥
        s.T + 1) :
    supportedValues s r = ∅ ∨ v ∈ supportedValues s r := by
  classical
  by_cases hempty : supportedValues s r = ∅
  · exact Or.inl hempty
  · right
    have hmodel_parts := hmodel
    unfold model_assumptions at hmodel_parts
    rcases hmodel_parts with ⟨hassumptions, hdisj, _, _, hFleT⟩
    have hinv_parts := hinv
    unfold ind_inv_13 at hinv_parts
    rcases hinv_parts with ⟨hnoeq1, _, _, _, _, hd2, _, _, _, _, _, _, _⟩
    have hnonempty : (supportedValues s r).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨w, hw⟩ := hnonempty
    have hw_values : w ∈ values := by
      unfold supportedValues at hw
      exact (Finset.mem_filter.mp hw).1
    have hcorrect_v :
        ∃ m ∈ Finmap.lookupD r s.msgs2,
          m.kind = Msg2Kind.D2 ∧ m.value = v ∧ m.src ∈ s.CORRECT := by
      have hcard_senders :
          (Finset.card (senders2 s (d2MsgsFor v received)) : Int) ≥ s.T + 1 := by
        rw [senders2_d2_value_eq_generated]
        exact hd2_received
      rcases d2_senders_has_correct
          (s := s) (msgs := received) (v := v)
          hassumptions hFleT hcard_senders with
        ⟨m, hm_received, hkind, hvalue, hcorrect⟩
      exact ⟨m, Finset.mem_powerset.mp hreceived hm_received, hkind, hvalue, hcorrect⟩
    have hcorrect_w :=
      supportedValues_has_correct_d2
        (s := s) (r := r) (v := w) hassumptions hFleT hw
    have hqv := hd2 r hr v hv_values hcorrect_v
    have hqw := hd2 r hr w hw_values hcorrect_w
    by_cases hvw : v = w
    · rwa [hvw]
    · exact False.elim
        (existsQuorum1_distinct_values_impossible
          (s := s) (r := r) (v := v) (w := w)
          hassumptions hdisj hFleT hnoeq1 hr hvw hqv hqw)

lemma received_quorum_contains_supported_value
    {s : State} {r w : Int} {received : Finset Msg2}
    (htype : type_ok s)
    (hr : r ∈ s.ROUNDS)
    (hreceived_sub : received ⊆ Finmap.lookupD r s.msgs2)
    (hreceived_card : (Finset.card (senders2 s received) : Int) = s.N - s.T)
    (hsupport : w ∈ supportedValues s r) :
    (Finset.card (senders2 s (d2MsgsFor w received)) : Int) ≥ s.T + 1 := by
  classical
  let fullMsgs := Finmap.lookupD r s.msgs2
  let receivedSenders := senders2 s received
  let valueSenders := senders2 s (d2MsgsFor w received)
  let others :=
    senders2 s
      (Finset.filter
        (fun m => Msg2.kind m = Msg2Kind.Q2 ∨ Msg2.value m ≠ w)
        fullMsgs)
  unfold supportedValues at hsupport
  rcases Finset.mem_filter.mp hsupport with ⟨_, _, _, hothers⟩
  have hcover : receivedSenders ⊆ valueSenders ∪ others := by
    intro id hid
    unfold receivedSenders senders2 at hid
    rcases Finset.mem_filter.mp hid with ⟨hall, m, hm_received, hsrc⟩
    by_cases hkindD : m.kind = Msg2Kind.D2
    · by_cases hvalue : m.value = w
      · apply Finset.mem_union.mpr
        left
        unfold valueSenders senders2 d2MsgsFor
        refine Finset.mem_filter.mpr ⟨hall, m, ?_, hsrc⟩
        exact Finset.mem_filter.mpr ⟨hm_received, hkindD, hvalue⟩
      · apply Finset.mem_union.mpr
        right
        unfold others senders2
        refine Finset.mem_filter.mpr ⟨hall, m, ?_, hsrc⟩
        exact Finset.mem_filter.mpr
          ⟨hreceived_sub hm_received, Or.inr hvalue⟩
    · apply Finset.mem_union.mpr
      right
      unfold others senders2
      refine Finset.mem_filter.mpr ⟨hall, m, ?_, hsrc⟩
      have hfull := hreceived_sub hm_received
      have hkind_mem := (htype.2.2.2.2.2 r hr m hfull).2.2.1
      have hkindQ : m.kind = Msg2Kind.Q2 := by
        simp at hkind_mem
        rcases hkind_mem with hD | hQ
        · exact False.elim (hkindD hD)
        · exact hQ
      exact Finset.mem_filter.mpr ⟨hfull, Or.inl hkindQ⟩
  have hcard_cover := Finset.card_le_card hcover
  have hcard_union :
      Finset.card (valueSenders ∪ others) ≤ Finset.card valueSenders + Finset.card others :=
    Finset.card_union_le _ _
  have hreceived_card_alias :
      (Finset.card receivedSenders : Int) = s.N - s.T := by
    simpa [receivedSenders] using hreceived_card
  change (Finset.card others : Int) < s.N - 2 * s.T at hothers
  change (Finset.card valueSenders : Int) ≥ s.T + 1
  omega

lemma generated_step3_random_supported_empty
    {s : State} {r : Int} {received : Finset Msg2}
    (htype : type_ok s)
    (hr : r ∈ s.ROUNDS)
    (hreceived : received ∈ Finset.powerset (Finmap.lookupD r s.msgs2))
    (hreceived_card :
      Finset.card
          (Finset.filter (fun id => ∃ m ∈ received, id = Msg2.src m) (s.CORRECT ∪ s.FAULTY)) =
        s.N - s.T)
    (hno_value :
      ∀ v ∈ values,
        Finset.card
            (Finset.filter
              (fun id =>
                ∃ m ∈ Finset.filter (fun m => Msg2.kind m = Msg2Kind.D2 ∧ v = Msg2.value m) received,
                  id = Msg2.src m)
              (s.CORRECT ∪ s.FAULTY)) <
          s.T + 1) :
    supportedValues s r = ∅ := by
  classical
  by_contra hnonempty
  have hne : (supportedValues s r).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hnonempty
  obtain ⟨w, hw⟩ := hne
  have hw_values : w ∈ values := by
    unfold supportedValues at hw
    exact (Finset.mem_filter.mp hw).1
  have hreceived_card_senders :
      (Finset.card (senders2 s received) : Int) = s.N - s.T := by
    rw [senders2_eq_generated]
    exact hreceived_card
  have hge :=
    received_quorum_contains_supported_value
      (s := s) (r := r) (w := w) (received := received)
      htype hr (Finset.mem_powerset.mp hreceived) hreceived_card_senders hw
  have hlt := hno_value w hw_values
  rw [← senders2_d2_value_eq_generated] at hlt
  omega

lemma generated_step3_no_fast_slow_value_quorum
    {s : State} {r : Int} {received : Finset Msg2}
    (htype : type_ok s)
    (hr : r ∈ s.ROUNDS)
    (hreceived : received ∈ Finset.powerset (Finmap.lookupD r s.msgs2))
    (hreceived_card :
      Finset.card
          (Finset.filter (fun id => ∃ m ∈ received, id = Msg2.src m) (s.CORRECT ∪ s.FAULTY)) =
        s.N - s.T)
    (hno_fast :
      ∀ v ∈ values,
        2 *
            Finset.card
              (Finset.filter
                (fun id =>
                  ∃ m ∈ Finset.filter (fun m => Msg2.kind m = Msg2Kind.D2 ∧ v = Msg2.value m) received,
                    id = Msg2.src m)
                (s.CORRECT ∪ s.FAULTY)) ≤
          s.N + s.T)
    (hN5T : s.N > 5 * s.T) :
    let prevMsgs := Finmap.lookupD r s.msgs2
    let n0 := Finset.card (d2MsgsFor 0 prevMsgs)
    let n1 := Finset.card (d2MsgsFor 1 prevMsgs)
    let nq := Finset.card (q2Msgs prevMsgs)
    ∃ x0 ∈ Finset.Icc 0 s.N,
      ∃ x1 ∈ Finset.Icc 0 s.N,
        x0 ≤ n0 ∧ x1 ≤ n1 ∧ x0 + x1 + nq ≥ s.N - s.T ∧
          2 * x0 ≤ s.N + s.T ∧ 2 * x1 ≤ s.N + s.T := by
  classical
  let d0 := senders2 s (d2MsgsFor 0 received)
  let d1 := senders2 s (d2MsgsFor 1 received)
  let qs := senders2 s (q2Msgs received)
  have hreceived_sub : received ⊆ Finmap.lookupD r s.msgs2 :=
    Finset.mem_powerset.mp hreceived
  have hcover :
      senders2 s received ⊆ (d0 ∪ d1) ∪ qs := by
    intro id hid
    unfold senders2 at hid
    rcases Finset.mem_filter.mp hid with ⟨hall, m, hm_received, hsrc⟩
    have hm_full := hreceived_sub hm_received
    have hkind_mem := (htype.2.2.2.2.2 r hr m hm_full).2.2.1
    have hvalue_kind := (htype.2.2.2.2.2 r hr m hm_full).2.2.2
    simp at hkind_mem
    rcases hkind_mem with hD | hQ
    · have hval01 : m.value = 0 ∨ m.value = 1 := by
        rcases hvalue_kind with hDval | hQval
        · rcases hDval with ⟨_, hval⟩
          simp at hval
          exact hval
        · rw [hD] at hQval
          cases hQval.1
      rcases hval01 with hval0 | hval1
      · apply Finset.mem_union.mpr
        left
        apply Finset.mem_union.mpr
        left
        unfold d0 senders2 d2MsgsFor
        refine Finset.mem_filter.mpr ⟨hall, m, ?_, hsrc⟩
        exact Finset.mem_filter.mpr ⟨hm_received, hD, hval0⟩
      · apply Finset.mem_union.mpr
        left
        apply Finset.mem_union.mpr
        right
        unfold d1 senders2 d2MsgsFor
        refine Finset.mem_filter.mpr ⟨hall, m, ?_, hsrc⟩
        exact Finset.mem_filter.mpr ⟨hm_received, hD, hval1⟩
    · apply Finset.mem_union.mpr
      right
      unfold qs senders2 q2Msgs
      refine Finset.mem_filter.mpr ⟨hall, m, ?_, hsrc⟩
      exact Finset.mem_filter.mpr ⟨hm_received, hQ⟩
  have hcover_card := Finset.card_le_card hcover
  have hunion1 : Finset.card ((d0 ∪ d1) ∪ qs) ≤ Finset.card (d0 ∪ d1) + Finset.card qs :=
    Finset.card_union_le _ _
  have hunion0 : Finset.card (d0 ∪ d1) ≤ Finset.card d0 + Finset.card d1 :=
    Finset.card_union_le _ _
  have hreceived_senders :
      (Finset.card (senders2 s received) : Int) = s.N - s.T := by
    rw [senders2_eq_generated]
    exact hreceived_card
  have hsum :
      (Finset.card d0 : Int) + Finset.card d1 + Finset.card qs ≥ s.N - s.T := by
    omega
  have hd0_full :
      (Finset.card d0 : Int) ≤
        Finset.card (d2MsgsFor 0 (Finmap.lookupD r s.msgs2)) := by
    have hsenders := card_senders2_le_card_msgs s (d2MsgsFor 0 received)
    have hmsgs := Finset.card_le_card
      (d2MsgsFor_mono (v := 0) hreceived_sub)
    change (Finset.card (senders2 s (d2MsgsFor 0 received)) : Int) ≤
      Finset.card (d2MsgsFor 0 (Finmap.lookupD r s.msgs2))
    exact_mod_cast le_trans hsenders hmsgs
  have hd1_full :
      (Finset.card d1 : Int) ≤
        Finset.card (d2MsgsFor 1 (Finmap.lookupD r s.msgs2)) := by
    have hsenders := card_senders2_le_card_msgs s (d2MsgsFor 1 received)
    have hmsgs := Finset.card_le_card
      (d2MsgsFor_mono (v := 1) hreceived_sub)
    change (Finset.card (senders2 s (d2MsgsFor 1 received)) : Int) ≤
      Finset.card (d2MsgsFor 1 (Finmap.lookupD r s.msgs2))
    exact_mod_cast le_trans hsenders hmsgs
  have hq_full :
      (Finset.card qs : Int) ≤
        Finset.card (q2Msgs (Finmap.lookupD r s.msgs2)) := by
    have hsenders := card_senders2_le_card_msgs s (q2Msgs received)
    have hmsgs := Finset.card_le_card (q2Msgs_mono hreceived_sub)
    change (Finset.card (senders2 s (q2Msgs received)) : Int) ≤
      Finset.card (q2Msgs (Finmap.lookupD r s.msgs2))
    exact_mod_cast le_trans hsenders hmsgs
  have hd0_bound :
      2 * (Finset.card d0 : Int) ≤ s.N + s.T := by
    have hno := hno_fast 0 (by simp [values])
    rw [← senders2_d2_value_eq_generated] at hno
    exact hno
  have hd1_bound :
      2 * (Finset.card d1 : Int) ≤ s.N + s.T := by
    have hno := hno_fast 1 (by simp [values])
    rw [← senders2_d2_value_eq_generated] at hno
    exact hno
  refine ⟨(Finset.card d0 : Int), ?_, (Finset.card d1 : Int), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Finset.mem_Icc]
    omega
  · simp only [Finset.mem_Icc]
    omega
  · exact hd0_full
  · exact hd1_full
  · omega
  · exact hd0_bound
  · exact hd1_bound

lemma generated_step3_random_slow_value_quorum
    {s : State} {r : Int} {received : Finset Msg2}
    (htype : type_ok s)
    (hr : r ∈ s.ROUNDS)
    (hreceived : received ∈ Finset.powerset (Finmap.lookupD r s.msgs2))
    (hreceived_card :
      Finset.card
          (Finset.filter (fun id => ∃ m ∈ received, id = Msg2.src m) (s.CORRECT ∪ s.FAULTY)) =
        s.N - s.T)
    (hno_value :
      ∀ v ∈ values,
        Finset.card
            (Finset.filter
              (fun id =>
                ∃ m ∈ Finset.filter (fun m => Msg2.kind m = Msg2Kind.D2 ∧ v = Msg2.value m) received,
                  id = Msg2.src m)
              (s.CORRECT ∪ s.FAULTY)) <
          s.T + 1)
    (hN5T : s.N > 5 * s.T) :
    let prevMsgs := Finmap.lookupD r s.msgs2
    let n0 := Finset.card (d2MsgsFor 0 prevMsgs)
    let n1 := Finset.card (d2MsgsFor 1 prevMsgs)
    let nq := Finset.card (q2Msgs prevMsgs)
    ∃ x0 ∈ Finset.Icc 0 s.N,
      ∃ x1 ∈ Finset.Icc 0 s.N,
        x0 ≤ n0 ∧ x1 ≤ n1 ∧ x0 + x1 + nq ≥ s.N - s.T ∧
          2 * x0 ≤ s.N + s.T ∧ 2 * x1 ≤ s.N + s.T := by
  -- A "slow" round (no value reaches `T+1` D2-senders) is the special case of a
  -- "no fast value" round: `card < T+1 ⟹ card ≤ T ⟹ 2·card ≤ 2T ≤ N+T` (since T ≤ N).
  refine generated_step3_no_fast_slow_value_quorum htype hr hreceived hreceived_card ?_ hN5T
  intro v hv
  have hlt := hno_value v hv
  omega

lemma generated_step3_fast_value_quorum
    {s : State} {r v : Int} {received : Finset Msg2}
    (hreceived : received ∈ Finset.powerset (Finmap.lookupD r s.msgs2))
    (hd2_weight :
      2 *
            Finset.card
              (Finset.filter
                (fun id =>
                  ∃ m ∈ Finset.filter (fun m => Msg2.kind m = Msg2Kind.D2 ∧ v = Msg2.value m) received,
                    id = Msg2.src m)
                (s.CORRECT ∪ s.FAULTY)) >
          s.N + s.T) :
    2 * Finset.card (senders2 s (d2MsgsFor v (Finmap.lookupD r s.msgs2))) >
      s.N + s.T := by
  have hreceived_sub : received ⊆ Finmap.lookupD r s.msgs2 :=
    Finset.mem_powerset.mp hreceived
  have hsub :
      senders2 s (d2MsgsFor v received) ⊆
        senders2 s (d2MsgsFor v (Finmap.lookupD r s.msgs2)) :=
    senders2_mono_frame (s := s) (s' := s) rfl rfl
      (d2MsgsFor_mono (v := v) hreceived_sub)
  have hcard := Finset.card_le_card hsub
  have hd2_weight_senders :
      2 * Finset.card (senders2 s (d2MsgsFor v received)) > s.N + s.T := by
    rw [senders2_d2_value_eq_generated]
    exact hd2_weight
  omega

lemma generated_step3_no_other_fast_value
    {s : State} {r v : Int} {received : Finset Msg2}
    (hbase : model_base_assumptions s)
    (hinv : ind_inv_13 s)
    (hr : r ∈ s.ROUNDS)
    (hreceived : received ∈ Finset.powerset (Finmap.lookupD r s.msgs2))
    (hv_values : v ∈ values)
    (hd2_selected :
      Finset.card
          (Finset.filter
            (fun id =>
              ∃ m ∈ Finset.filter (fun m => Msg2.kind m = Msg2Kind.D2 ∧ v = Msg2.value m) received,
                id = Msg2.src m)
            (s.CORRECT ∪ s.FAULTY)) ≥
        s.T + 1)
    (hselected_not_fast :
      ¬ 2 *
          Finset.card
            (Finset.filter
              (fun id =>
                ∃ m ∈ Finset.filter (fun m => Msg2.kind m = Msg2Kind.D2 ∧ v = Msg2.value m) received,
                  id = Msg2.src m)
              (s.CORRECT ∪ s.FAULTY)) >
        s.N + s.T) :
    ∀ w ∈ values,
      2 *
          Finset.card
            (Finset.filter
              (fun id =>
                ∃ m ∈ Finset.filter (fun m => Msg2.kind m = Msg2Kind.D2 ∧ w = Msg2.value m) received,
                  id = Msg2.src m)
              (s.CORRECT ∪ s.FAULTY)) ≤
        s.N + s.T := by
  classical
  intro w hw_values
  by_contra hnot_le
  have hfast_w :
      2 *
          (Finset.card
            (Finset.filter
              (fun id =>
                ∃ m ∈ Finset.filter (fun m => Msg2.kind m = Msg2Kind.D2 ∧ w = Msg2.value m) received,
                  id = Msg2.src m)
              (s.CORRECT ∪ s.FAULTY)) : Int) >
        s.N + s.T := by
    omega
  by_cases hvw : v = w
  · subst w
    exact hselected_not_fast hfast_w
  · unfold model_base_assumptions at hbase
    rcases hbase with ⟨hassumptions, hdisj, _, _, hFleT⟩
    unfold ind_inv_13 at hinv
    rcases hinv with ⟨hnoeq1, _, _, _, _, hd2, _, _, _, _, _, _, _⟩
    have hreceived_sub : received ⊆ Finmap.lookupD r s.msgs2 :=
      Finset.mem_powerset.mp hreceived
    have hselected_senders :
        (Finset.card (senders2 s (d2MsgsFor v received)) : Int) ≥ s.T + 1 := by
      rw [senders2_d2_value_eq_generated]
      exact hd2_selected
    have hcorrect_v_received :=
      d2_senders_has_correct
        (s := s) (msgs := received) (v := v)
        hassumptions hFleT hselected_senders
    rcases hcorrect_v_received with ⟨mv, hmv_received, hmv_kind, hmv_value, hmv_correct⟩
    have hd2_w_ge :
        (Finset.card (senders2 s (d2MsgsFor w received)) : Int) ≥ s.T + 1 := by
      rw [senders2_d2_value_eq_generated]
      omega
    have hcorrect_w_received :=
      d2_senders_has_correct
        (s := s) (msgs := received) (v := w)
        hassumptions hFleT hd2_w_ge
    rcases hcorrect_w_received with ⟨mw, hmw_received, hmw_kind, hmw_value, hmw_correct⟩
    have hqv : existsQuorum1 s r v :=
      hd2 r hr v hv_values
        ⟨mv, hreceived_sub hmv_received, hmv_kind, hmv_value, hmv_correct⟩
    have hqw : existsQuorum1 s r w :=
      hd2 r hr w hw_values
        ⟨mw, hreceived_sub hmw_received, hmw_kind, hmw_value, hmw_correct⟩
    exact existsQuorum1_distinct_values_impossible
      (s := s) (r := r) (v := v) (w := w)
      hassumptions hdisj hFleT hnoeq1 hr hvw hqv hqw

lemma supportedValues_unique_of_ind_inv_base
    {s : State}
    (hbase : model_base_assumptions s)
    (hinv : ind_inv_13 s) :
    ∀ r ∈ s.ROUNDS, ∀ v ∈ supportedValues s r, ∀ w ∈ supportedValues s r, v = w := by
  intro r hr v hsup_v w hsup_w
  by_cases hvw : v = w
  · exact hvw
  · unfold model_base_assumptions at hbase
    rcases hbase with ⟨hassumptions, hdisj, _, _, hFleT⟩
    unfold ind_inv_13 at hinv
    rcases hinv with ⟨hnoeq1, _, _, _, _, hd2, _, _, _, _, _, _, _⟩
    have hv_values : v ∈ values := by
      unfold supportedValues at hsup_v
      exact (Finset.mem_filter.mp hsup_v).1
    have hw_values : w ∈ values := by
      unfold supportedValues at hsup_w
      exact (Finset.mem_filter.mp hsup_w).1
    have hd2_v :=
      supportedValues_has_correct_d2
        (s := s) (r := r) (v := v) hassumptions hFleT hsup_v
    have hd2_w :=
      supportedValues_has_correct_d2
        (s := s) (r := r) (v := w) hassumptions hFleT hsup_w
    have hqv := hd2 r hr v hv_values hd2_v
    have hqw := hd2 r hr w hw_values hd2_w
    exact False.elim
      (existsQuorum1_distinct_values_impossible
        (s := s) (r := r) (v := v) (w := w)
        hassumptions hdisj hFleT hnoeq1 hr hvw hqv hqw)

lemma supportedValues_unique_of_ind_inv
    {s : State}
    (hmodel : model_assumptions s)
    (hinv : ind_inv_13 s) :
    ∀ r ∈ s.ROUNDS, ∀ v ∈ supportedValues s r, ∀ w ∈ supportedValues s r, v = w :=
  supportedValues_unique_of_ind_inv_base (model_base_of_model hmodel) hinv

lemma decision_value_supported_previous_round
    {s : State} {id : Int}
    (hbase : model_base_assumptions s)
    (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (hid : id ∈ s.CORRECT)
    (hdec : Finmap.lookupD id s.decision ≠ -1) :
    Finmap.lookupD id s.decision ∈ supportedValues s (Finmap.lookupD id s.round - 1) := by
  classical
  have hbase_parts := hbase
  unfold model_base_assumptions at hbase_parts
  rcases hbase_parts with ⟨_, _, _, hround_pred, _⟩
  have hinv_parts := hinv
  unfold ind_inv_13 at hinv_parts
  rcases hinv_parts with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hdecReq⟩
  have hround_mem : Finmap.lookupD id s.round ∈ s.ROUNDS := by
    unfold type_ok at htype
    exact htype.2.2.1.2 id hid
  have hdec_value : Finmap.lookupD id s.decision ∈ values := by
    unfold type_ok at htype
    have hmem := htype.2.1.2 id hid
    unfold values
    simp at hmem ⊢
    rcases hmem with hval | hbottoms
    · exact Or.inl hval
    · rcases hbottoms with hval | hbot
      · exact Or.inr hval
      · exact False.elim (hdec hbot)
  rcases hdecReq id hid with hbottom | hquorum_prev
  · exact False.elim (hdec hbottom)
  · rcases hquorum_prev with ⟨hgt, hq2⟩
    have hprev_mem : Finmap.lookupD id s.round - 1 ∈ s.ROUNDS :=
      hround_pred (Finmap.lookupD id s.round) hround_mem (by omega)
    have htotal :=
      previous_round_has_quorum_for_correct_base
        (s := s) (id := id) hbase htype hinv hid hgt
    exact existsQuorum2LessRam_supported_of_total_senders
      (s := s) (r := Finmap.lookupD id s.round - 1)
      (v := Finmap.lookupD id s.decision)
      hbase htype hinv hprev_mem hdec_value hq2 htotal

lemma decision_value_controls_current_msg1
    {s : State} {id : Int}
    (hbase : model_base_assumptions s)
    (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (hid : id ∈ s.CORRECT)
    (hdec : Finmap.lookupD id s.decision ≠ -1) :
    ∀ m ∈ Finmap.lookupD (Finmap.lookupD id s.round) s.msgs1,
      m.src ∈ s.CORRECT → m.value = Finmap.lookupD id s.decision := by
  classical
  have hbase_parts := hbase
  unfold model_base_assumptions at hbase_parts
  rcases hbase_parts with ⟨_, _, _, hround_pred, _⟩
  have hinv_parts := hinv
  unfold ind_inv_13 at hinv_parts
  rcases hinv_parts with ⟨_, _, _, _, _, _, _, hrounds_conn, _, _, _, _, hdecReq⟩
  have hround_mem : Finmap.lookupD id s.round ∈ s.ROUNDS := by
    unfold type_ok at htype
    exact htype.2.2.1.2 id hid
  have hround_gt : Finmap.lookupD id s.round > 1 := by
    rcases hdecReq id hid with hbottom | hq
    · exact False.elim (hdec hbottom)
    · exact hq.1
  have hprev_mem : Finmap.lookupD id s.round - 1 ∈ s.ROUNDS :=
    hround_pred (Finmap.lookupD id s.round) hround_mem (by omega)
  have hprev_succ : Finmap.lookupD id s.round - 1 + 1 = Finmap.lookupD id s.round := by
    omega
  have hsup_prev :=
    decision_value_supported_previous_round hbase htype hinv hid hdec
  rcases hrounds_conn (Finmap.lookupD id s.round - 1) hprev_mem
      (by simpa [hprev_succ] using hround_mem) with hempty | hwit
  · rw [hempty] at hsup_prev
    simp at hsup_prev
  · rcases hwit with ⟨u, hu, hall_msg1⟩
    have hunique := supportedValues_unique_of_ind_inv_base hbase hinv
    have hdec_eq_u :=
      hunique (Finmap.lookupD id s.round - 1) hprev_mem
        (Finmap.lookupD id s.decision) hsup_prev u hu
    intro m hm hcorrect_m
    exact (hall_msg1 m (by simpa [hprev_succ] using hm) hcorrect_m).trans hdec_eq_u.symm

lemma correct_q2_impossible_of_all_correct_msg1_value
    {s : State} {r v : Int} {m : Msg2}
    (hbase : model_base_assumptions s)
    (hinv : ind_inv_13 s)
    (hr : r ∈ s.ROUNDS)
    (hv : v ∈ values)
    (hall_msg1 :
      ∀ m1 ∈ Finmap.lookupD r s.msgs1,
        m1.src ∈ s.CORRECT → m1.value = v)
    (hm : m ∈ Finmap.lookupD r s.msgs2)
    (hcorrect : m.src ∈ s.CORRECT)
    (hkind : m.kind = Msg2Kind.Q2) :
    False := by
  classical
  have hbase_parts := hbase
  unfold model_base_assumptions at hbase_parts
  rcases hbase_parts with ⟨hassumptions, _, _, _, hFleT⟩
  have hinv_parts := hinv
  unfold ind_inv_13 at hinv_parts
  rcases hinv_parts with
    ⟨_, _, _, _, _, _, hq2, _, _, _, _, _, _⟩
  have hq := hq2 r hr ⟨m, hm, hkind, hcorrect⟩
  dsimp at hq
  rcases hq with
    ⟨x0, _hx0mem, x1, _hx1mem, hx0le, hx1le, hsum, hx0bound, hx1bound⟩
  have hN5T : s.N > 5 * s.T := by
    have h := hassumptions
    unfold assumptions_hold at h
    exact h.1
  let nf :=
    Finset.card
      (Finset.filter
        (fun id => id ∈ senders1 s (Finmap.lookupD r s.msgs1))
        s.FAULTY)
  have hnf_le : (nf : Int) ≤ s.F := by
    unfold nf
    have hcard :=
      Finset.card_le_card
        (Finset.filter_subset
          (fun id => id ∈ senders1 s (Finmap.lookupD r s.msgs1))
          s.FAULTY)
    unfold assumptions_hold at hassumptions
    rcases hassumptions with ⟨_, _, hfaulty_card, _, _⟩
    rw [hfaulty_card]
    exact_mod_cast hcard
  have hnf_le_T : (nf : Int) ≤ s.T := by
    omega
  have hvalues : v = 0 ∨ v = 1 := by
    unfold values at hv
    simp at hv
    exact hv
  rcases hvalues with rfl | rfl
  · let n1 :=
      Finset.filter
        (fun id => Msg1.mk r id 1 ∈ Finmap.lookupD r s.msgs1)
        s.CORRECT
    have hn1_empty : n1 = ∅ := by
      apply Finset.ext
      intro id
      constructor
      · intro hid
        rcases Finset.mem_filter.mp hid with ⟨hid_correct, hmsg⟩
        have hval := hall_msg1 (Msg1.mk r id 1) hmsg hid_correct
        simp at hval
      · intro hid
        simp at hid
    have hx1le_zero : x1 ≤ 0 := by
      change x1 ≤ (Finset.card n1 : Int) at hx1le
      rw [hn1_empty] at hx1le
      simpa using hx1le
    change
      x0 + x1 + (nf : Int) ≥ s.N - s.T at hsum
    -- x0 ≥ N−2T (sum, x1≤0, nf≤T) and 2·x0 ≤ N+T force N ≤ 5T, contradicting N>5T.
    omega
  · let n0 :=
      Finset.filter
        (fun id => Msg1.mk r id 0 ∈ Finmap.lookupD r s.msgs1)
        s.CORRECT
    have hn0_empty : n0 = ∅ := by
      apply Finset.ext
      intro id
      constructor
      · intro hid
        rcases Finset.mem_filter.mp hid with ⟨hid_correct, hmsg⟩
        have hval := hall_msg1 (Msg1.mk r id 0) hmsg hid_correct
        simp at hval
      · intro hid
        simp at hid
    have hx0le_zero : x0 ≤ 0 := by
      change x0 ≤ (Finset.card n0 : Int) at hx0le
      rw [hn0_empty] at hx0le
      simpa using hx0le
    change
      x0 + x1 + (nf : Int) ≥ s.N - s.T at hsum
    -- symmetric: x1 ≥ N−2T and 2·x1 ≤ N+T force N ≤ 5T, contradicting N>5T.
    omega

lemma correct_msg2_d2_value_of_all_correct_msg1_value
    {s : State} {r v : Int} {m : Msg2}
    (hbase : model_base_assumptions s)
    (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (hr : r ∈ s.ROUNDS)
    (hv : v ∈ values)
    (hall_msg1 :
      ∀ m1 ∈ Finmap.lookupD r s.msgs1,
        m1.src ∈ s.CORRECT → m1.value = v)
    (hm : m ∈ Finmap.lookupD r s.msgs2)
    (hcorrect : m.src ∈ s.CORRECT) :
    m.kind = Msg2Kind.D2 ∧ m.value = v := by
  classical
  have hbase_parts := hbase
  unfold model_base_assumptions at hbase_parts
  rcases hbase_parts with ⟨hassumptions, _, _, _, hFleT⟩
  have hinv_parts := hinv
  unfold ind_inv_13 at hinv_parts
  rcases hinv_parts with
    ⟨_, _, _, _, _, hd2, _, _, _, _, _, _, _⟩
  have htype_parts := htype
  unfold type_ok at htype_parts
  rcases htype_parts with ⟨_, _, _, _, _, hmsgs2_type⟩
  have hmsg_type := hmsgs2_type r hr m hm
  have hkind_mem : m.kind ∈ insert Msg2Kind.D2 (insert Msg2Kind.Q2 (∅ : Finset Msg2Kind)) :=
    hmsg_type.2.2.1
  have hkind_cases : m.kind = Msg2Kind.D2 ∨ m.kind = Msg2Kind.Q2 := by
    simp at hkind_mem
    exact hkind_mem
  rcases hkind_cases with hkind_d2 | hkind_q2
  · have hvalue_mem : m.value ∈ values := by
      have hbranch := hmsg_type.2.2.2
      rcases hbranch with hdbranch | hqbranch
      · exact hdbranch.2
      · exact False.elim (by
          have hcontra := hqbranch.1
          rw [hkind_d2] at hcontra
          cases hcontra)
    have hquorum :=
      hd2 r hr m.value hvalue_mem
        ⟨m, hm, hkind_d2, rfl, hcorrect⟩
    have hvalue_eq :=
      existsQuorum1_eq_of_all_correct_msg1
        (s := s) (r := r) (v := v) (w := m.value)
        hassumptions hFleT hall_msg1 hquorum
    exact ⟨hkind_d2, hvalue_eq⟩
  · exact False.elim
      (correct_q2_impossible_of_all_correct_msg1_value
        (s := s) (r := r) (v := v) (m := m)
        hbase hinv hr hv hall_msg1 hm hcorrect hkind_q2)

lemma generated_step3_fast_of_all_correct_msg1_value
    {s : State} {r v : Int} {received : Finset Msg2}
    (hbase : model_base_assumptions s)
    (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (hr : r ∈ s.ROUNDS)
    (hv : v ∈ values)
    (hreceived : received ∈ Finset.powerset (Finmap.lookupD r s.msgs2))
    (hreceived_card :
      Finset.card
          (Finset.filter (fun id => ∃ m ∈ received, id = Msg2.src m) (s.CORRECT ∪ s.FAULTY)) =
        s.N - s.T)
    (hall_msg1 :
      ∀ m1 ∈ Finmap.lookupD r s.msgs1,
        m1.src ∈ s.CORRECT → m1.value = v) :
    2 *
          Finset.card
            (Finset.filter
              (fun id =>
                ∃ m ∈ Finset.filter (fun m => Msg2.kind m = Msg2Kind.D2 ∧ v = Msg2.value m) received,
                  id = Msg2.src m)
              (s.CORRECT ∪ s.FAULTY)) >
        s.N + s.T := by
  have hbase_parts := hbase
  unfold model_base_assumptions at hbase_parts
  rcases hbase_parts with ⟨hassumptions, _, _, _, hFleT⟩
  exact generated_step3_fast_of_all_correct_received_d2
    (s := s) (received := received) (v := v)
    hassumptions hFleT (assumptions_N5T hassumptions) hreceived_card
    (by
      intro m hm hcorrect
      exact correct_msg2_d2_value_of_all_correct_msg1_value
        (s := s) (r := r) (v := v) (m := m)
        hbase htype hinv hr hv hall_msg1
        ((Finset.mem_powerset.mp hreceived) hm) hcorrect)

/-- `ind_inv_13` variant of `supported_value_has_quorum`: a supported value
has a round-`r` quorum1.  Uses only `d2_requires_quorum` (`Lemma7`). -/
lemma supported_value_has_quorum_core
    {s : State} {r v : Int}
    (hbase : model_base_assumptions s)
    (hinv : ind_inv_13 s)
    (hr : r ∈ s.ROUNDS)
    (hsup : v ∈ supportedValues s r) :
    existsQuorum1 s r v := by
  unfold model_base_assumptions at hbase
  rcases hbase with ⟨hassumptions, _, _, _, hFleT⟩
  unfold ind_inv_13 at hinv
  rcases hinv with ⟨_, _, _, _, _, hd2, _, _, _, _, _, _, _⟩
  have hv_values : v ∈ values := by
    unfold supportedValues at hsup
    exact (Finset.mem_filter.mp hsup).1
  exact hd2 r hr v hv_values
    (supportedValues_has_correct_d2
      (s := s) (r := r) (v := v) hassumptions hFleT hsup)

/-- `ROUNDS` is downward closed to `1`, hence interval-convex: anything between
`1` and a member is a member. -/
lemma mem_rounds_of_le_core
    {s : State}
    (hbase : model_base_assumptions s)
    {x y : Int} (hx : x ∈ s.ROUNDS) (hy1 : 1 ≤ y) (hyx : y ≤ x) :
    y ∈ s.ROUNDS := by
  classical
  have hbase_parts := hbase
  unfold model_base_assumptions at hbase_parts
  rcases hbase_parts with ⟨_, _, _hpos, hround_pred, _⟩
  have key : ∀ n : ℕ, ∀ z, z ∈ s.ROUNDS → 1 ≤ z - (n : Int) → z - (n : Int) ∈ s.ROUNDS := by
    intro n
    induction n with
    | zero => intro z hz _; simpa using hz
    | succ m ih =>
      intro z hz hle
      have hzm : z - (m : Int) ∈ s.ROUNDS := ih z hz (by omega)
      have hne : z - (m : Int) ≠ 1 := by omega
      have hpred := hround_pred (z - (m : Int)) hzm hne
      have heq : z - (m : Int) - 1 = z - ((m + 1 : ℕ) : Int) := by omega
      rwa [heq] at hpred
  have hsub : x - ((x - y).toNat : Int) = y := by
    have : ((x - y).toNat : Int) = x - y := Int.toNat_of_nonneg (by omega)
    omega
  have := key (x - y).toNat x hx (by rw [hsub]; exact hy1)
  rwa [hsub] at this

/-- Forward-lock membership: on a one-sided round (`AllW(r)`: every correct
`msgs1[r]` carries value `w`) with a round-`r` msgs2 quorum (`senders2 ≥ N-T`),
`w` is the supported value.  Every correct `msgs2` sender is a `D2`-`w` sender
(`correct_msg2_d2_value_of_all_correct_msg1_value`), so the `D2`-`w` senders
number `≥ N-2T ≥ T+1` and the `others` are faulty (`≤ F < N-2T`).  Counting after
`existsQuorum2LessRam_supported_of_total_senders` (6472). -/
lemma supportedValues_of_allW_core
    {s : State} {r w : Int}
    (hbase : model_base_assumptions s)
    (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (hr : r ∈ s.ROUNDS)
    (hw : w ∈ values)
    (hallW : ∀ m ∈ Finmap.lookupD r s.msgs1, m.src ∈ s.CORRECT → m.value = w)
    (hsenders : (Finset.card (senders2 s (Finmap.lookupD r s.msgs2)) : Int) ≥ s.N - s.T) :
    w ∈ supportedValues s r := by
  classical
  let msgs := Finmap.lookupD r s.msgs2
  let total := senders2 s msgs
  let sv := senders2 s (d2MsgsFor w msgs)
  let others :=
    senders2 s
      (Finset.filter (fun m => Msg2.kind m = Msg2Kind.Q2 ∨ Msg2.value m ≠ w) msgs)
  have hbase_parts := hbase
  unfold model_base_assumptions at hbase_parts
  rcases hbase_parts with ⟨hassumptions, _hdisj, _, _, hFleT⟩
  have hassumptions' := hassumptions
  unfold assumptions_hold at hassumptions'
  rcases hassumptions' with ⟨_hNgt, _, hfaulty_card, _, _⟩
  have hcorrect_sub_sv : total ∩ s.CORRECT ⊆ sv := by
    intro id hid
    rcases Finset.mem_inter.mp hid with ⟨hid_total, hid_correct⟩
    have hid_total' : id ∈ senders2 s msgs := hid_total
    unfold senders2 at hid_total'
    rcases Finset.mem_filter.mp hid_total' with ⟨hall, m, hm, hsrc⟩
    have hm_correct : m.src ∈ s.CORRECT := by rw [← hsrc]; exact hid_correct
    have hd2 := correct_msg2_d2_value_of_all_correct_msg1_value
      (s := s) (r := r) (v := w) (m := m) hbase htype hinv hr hw hallW hm hm_correct
    show id ∈ senders2 s (d2MsgsFor w msgs)
    unfold senders2
    refine Finset.mem_filter.mpr ⟨hall, m, ?_, hsrc⟩
    unfold d2MsgsFor
    exact Finset.mem_filter.mpr ⟨hm, hd2.1, hd2.2⟩
  have hothers_sub : others ⊆ s.FAULTY := by
    intro id hid
    have hid' :
        id ∈ senders2 s
          (Finset.filter (fun m => Msg2.kind m = Msg2Kind.Q2 ∨ Msg2.value m ≠ w) msgs) := hid
    unfold senders2 at hid'
    rcases Finset.mem_filter.mp hid' with ⟨hall, m, hm, hsrc⟩
    rcases Finset.mem_filter.mp hm with ⟨hm_msgs, hm_kind⟩
    by_cases hc : id ∈ s.CORRECT
    · exfalso
      have hm_correct : m.src ∈ s.CORRECT := by rw [← hsrc]; exact hc
      have hd2 := correct_msg2_d2_value_of_all_correct_msg1_value
        (s := s) (r := r) (v := w) (m := m) hbase htype hinv hr hw hallW hm_msgs hm_correct
      rcases hm_kind with hq | hne
      · rw [hd2.1] at hq; simp at hq
      · exact hne hd2.2
    · have hmem := hall
      unfold allReplicas at hmem
      rcases Finset.mem_union.mp hmem with hcorr | hf
      · exact absurd hcorr hc
      · exact hf
  have htotal_sub : total ⊆ (total ∩ s.CORRECT) ∪ s.FAULTY := by
    intro id hid
    by_cases hc : id ∈ s.CORRECT
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hid, hc⟩)
    · have hid' : id ∈ senders2 s msgs := hid
      unfold senders2 at hid'
      have hmem := (Finset.mem_filter.mp hid').1
      unfold allReplicas at hmem
      rcases Finset.mem_union.mp hmem with hcorr | hf
      · exact absurd hcorr hc
      · exact Finset.mem_union_right _ hf
  have hsv_ge : (Finset.card sv : Int) ≥ s.T + 1 := by
    have h1 : (Finset.card (total ∩ s.CORRECT) : Int) ≤ Finset.card sv := by
      exact_mod_cast Finset.card_le_card hcorrect_sub_sv
    have h2 : (Finset.card total : Int) ≤ Finset.card (total ∩ s.CORRECT) + Finset.card s.FAULTY := by
      exact_mod_cast le_trans (Finset.card_le_card htotal_sub)
        (Finset.card_union_le (total ∩ s.CORRECT) s.FAULTY)
    have h3 : (Finset.card total : Int) ≥ s.N - s.T := hsenders
    have hFc : (Finset.card s.FAULTY : Int) = s.F := hfaulty_card.symm
    omega
  have hothers_lt : (Finset.card others : Int) < s.N - 2 * s.T := by
    have h4 : (Finset.card others : Int) ≤ Finset.card s.FAULTY := by
      exact_mod_cast Finset.card_le_card hothers_sub
    have hFc : (Finset.card s.FAULTY : Int) = s.F := hfaulty_card.symm
    omega
  unfold supportedValues
  refine Finset.mem_filter.mpr ⟨hw, ?_, ?_, ?_⟩
  · simpa [msgs] using hsenders
  · simpa [msgs, sv] using hsv_ge
  · simpa [msgs, others] using hothers_lt

/-- **Unconditional forward lock.** If round `r` is one-sided for `w` and round
`r+1` has any correct `msgs1`, then `r+1` is one-sided for `w` too.  The `r+1`
activity forces `senders2(r) ≥ N-T` (`m1_requires_quorum`), so
`supportedValues_of_allW_core` re-anchors `w ∈ supportedValues r`, and
`rounds_connection` + uniqueness carry the value to `r+1`.  This re-anchors the
value across rounds where `supportedValues` would otherwise be empty. -/
lemma allW_forward_core
    {s : State} {r w : Int}
    (hbase : model_base_assumptions s)
    (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (hr : r ∈ s.ROUNDS)
    (hrsucc : r + 1 ∈ s.ROUNDS)
    (hw : w ∈ values)
    (hallW : ∀ m ∈ Finmap.lookupD r s.msgs1, m.src ∈ s.CORRECT → m.value = w)
    (hactivity : ∃ m ∈ Finmap.lookupD (r + 1) s.msgs1, m.src ∈ s.CORRECT) :
    ∀ m ∈ Finmap.lookupD (r + 1) s.msgs1, m.src ∈ s.CORRECT → m.value = w := by
  classical
  have hbase_parts := hbase
  unfold model_base_assumptions at hbase_parts
  rcases hbase_parts with ⟨_, _, hpos, _, _⟩
  have hinv_parts := hinv
  unfold ind_inv_13 at hinv_parts
  rcases hinv_parts with ⟨_, _, _, _, _, _, _, hrounds_conn, hm1, _, _, _, _⟩
  have hr1_ne : r + 1 ≠ 1 := by have := hpos r hr; omega
  have hsenders_card := hm1 (r + 1) hrsucc hr1_ne hactivity
  have heq : (r + 1) - 1 = r := by omega
  rw [heq] at hsenders_card
  have hsupp : w ∈ supportedValues s r :=
    supportedValues_of_allW_core hbase htype hinv hr hw hallW hsenders_card
  rcases hrounds_conn r hr hrsucc with hempty | hwit
  · rw [hempty] at hsupp; simp at hsupp
  · rcases hwit with ⟨u, hu, hall_u⟩
    have huniq := supportedValues_unique_of_ind_inv_base hbase hinv
    have hwu : w = u := huniq r hr w hsupp u hu
    intro m hm hcorrect
    rw [hwu]
    exact hall_u m hm hcorrect

/-- Iterate the forward lock over an interval: one-sided at `a` with per-round
correct `msgs1` activity through `a+d` ⇒ one-sided at `a+d`. -/
lemma allW_forward_chain_core
    {s : State} {a w : Int}
    (hbase : model_base_assumptions s)
    (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (hw : w ∈ values)
    (hallW : ∀ m ∈ Finmap.lookupD a s.msgs1, m.src ∈ s.CORRECT → m.value = w) :
    ∀ d : ℕ, (∀ j : ℕ, j ≤ d → a + (j : Int) ∈ s.ROUNDS) →
      (∀ j : ℕ, 1 ≤ j → j ≤ d →
        ∃ m ∈ Finmap.lookupD (a + (j : Int)) s.msgs1, m.src ∈ s.CORRECT) →
      (∀ m ∈ Finmap.lookupD (a + (d : Int)) s.msgs1, m.src ∈ s.CORRECT → m.value = w) := by
  intro d
  induction d with
  | zero => intro _ _; simpa using hallW
  | succ n ih =>
    intro hrounds hactivity
    have hAllWn :=
      ih (fun j hj => hrounds j (by omega)) (fun j hj1 hj => hactivity j hj1 (by omega))
    have hn_round : a + (n : Int) ∈ s.ROUNDS := hrounds n (by omega)
    have hsucc_round : a + (n : Int) + 1 ∈ s.ROUNDS := by
      have h := hrounds (n + 1) (le_refl _)
      have heq : a + ((n + 1 : ℕ) : Int) = a + (n : Int) + 1 := by omega
      rwa [heq] at h
    have hact : ∃ m ∈ Finmap.lookupD (a + (n : Int) + 1) s.msgs1, m.src ∈ s.CORRECT := by
      have h := hactivity (n + 1) (by omega) (le_refl _)
      have heq : a + ((n + 1 : ℕ) : Int) = a + (n : Int) + 1 := by omega
      rwa [heq] at h
    have hstep := allW_forward_core hbase htype hinv hn_round hsucc_round hw hAllWn hact
    have heq : a + ((n + 1 : ℕ) : Int) = a + (n : Int) + 1 := by omega
    rw [heq]; exact hstep

/-- **Decision agreement from core (directed).** Two decided correct replicas with
`round[id1] ≤ round[id2]` decide the same value.  If `round[id1] < round[id2]`,
propagate the one-sidedness of `id1`'s value forward to `round[id2]-1`
(`allW_forward_chain_core`), with per-round activity from `id2`'s own message
history (`round_needs_sent_messages`); then `id2`'s decision value, supported at
`round[id2]-1`, exposes a correct `msgs1` that the forward lock pins to `id1`'s
value.  If the rounds are equal, both decision values are supported at the same
previous round, so they agree by `supportedValues` uniqueness. -/
lemma decision_agreement_core_le
    {s : State} {id1 id2 : Int}
    (hbase : model_base_assumptions s)
    (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (hid1 : id1 ∈ s.CORRECT)
    (hid2 : id2 ∈ s.CORRECT)
    (hdec1 : Finmap.lookupD id1 s.decision ≠ -1)
    (hdec2 : Finmap.lookupD id2 s.decision ≠ -1)
    (hle : Finmap.lookupD id1 s.round ≤ Finmap.lookupD id2 s.round) :
    Finmap.lookupD id1 s.decision = Finmap.lookupD id2 s.decision := by
  classical
  have hr1_mem : Finmap.lookupD id1 s.round ∈ s.ROUNDS :=
    correct_round_mem_of_type_ok htype id1 hid1
  have hr2_mem : Finmap.lookupD id2 s.round ∈ s.ROUNDS :=
    correct_round_mem_of_type_ok htype id2 hid2
  have hbase_parts := hbase
  unfold model_base_assumptions at hbase_parts
  rcases hbase_parts with ⟨_, _, hpos, hpred, _⟩
  have hinv_parts := hinv
  unfold ind_inv_13 at hinv_parts
  rcases hinv_parts with ⟨_, _, _, hroundNeeds, _, _, _, _, _, _, _, _, hdecReq⟩
  have hr2_gt : Finmap.lookupD id2 s.round > 1 := by
    rcases hdecReq id2 hid2 with hb | hq
    · exact absurd hb hdec2
    · exact hq.1
  have hprev2_mem : Finmap.lookupD id2 s.round - 1 ∈ s.ROUNDS :=
    hpred (Finmap.lookupD id2 s.round) hr2_mem (by omega)
  have hw1_val : Finmap.lookupD id1 s.decision ∈ values := by
    unfold type_ok at htype
    have hmem := htype.2.1.2 id1 hid1
    unfold values
    simp at hmem ⊢
    rcases hmem with hval | hbottoms
    · exact Or.inl hval
    · rcases hbottoms with hval | hbot
      · exact Or.inr hval
      · exact False.elim (hdec1 hbot)
  have hAllW1 := decision_value_controls_current_msg1 hbase htype hinv hid1 hdec1
  have hsupp2 := decision_value_supported_previous_round hbase htype hinv hid2 hdec2
  by_cases hlt : Finmap.lookupD id1 s.round < Finmap.lookupD id2 s.round
  · have hr1_pos : 1 ≤ Finmap.lookupD id1 s.round := hpos _ hr1_mem
    set d := (Finmap.lookupD id2 s.round - 1 - Finmap.lookupD id1 s.round).toNat with hd
    have hd_eq : Finmap.lookupD id1 s.round + (d : Int) = Finmap.lookupD id2 s.round - 1 := by
      rw [hd, Int.toNat_of_nonneg (by omega)]; omega
    have hrounds_chain : ∀ j : ℕ, j ≤ d → Finmap.lookupD id1 s.round + (j : Int) ∈ s.ROUNDS := by
      intro j hj
      exact mem_rounds_of_le_core hbase hprev2_mem (by omega) (by omega)
    have hact_chain : ∀ j : ℕ, 1 ≤ j → j ≤ d →
        ∃ m ∈ Finmap.lookupD (Finmap.lookupD id1 s.round + (j : Int)) s.msgs1, m.src ∈ s.CORRECT := by
      intro j hj1 hj
      have hrj_mem := hrounds_chain j hj
      have hrj_lt : Finmap.lookupD id1 s.round + (j : Int) < Finmap.lookupD id2 s.round := by omega
      rcases (hroundNeeds id2 hid2 _ hrj_mem).1 (Or.inl hrj_lt) with ⟨m, hm, hsrc⟩
      exact ⟨m, hm, by rw [hsrc]; exact hid2⟩
    have hAllW_prev2 :=
      allW_forward_chain_core hbase htype hinv hw1_val hAllW1 d hrounds_chain hact_chain
    rw [hd_eq] at hAllW_prev2
    have hquorum2 := supported_value_has_quorum_core hbase hinv hprev2_mem hsupp2
    rcases existsQuorum1_has_correct_msg1_base hbase hquorum2 with ⟨m, hm, hm_correct, hm_value⟩
    have hval := hAllW_prev2 m hm hm_correct
    rw [hm_value] at hval
    exact hval.symm
  · have heq : Finmap.lookupD id1 s.round = Finmap.lookupD id2 s.round := by omega
    have hsupp1 := decision_value_supported_previous_round hbase htype hinv hid1 hdec1
    rw [heq] at hsupp1
    have huniq := supportedValues_unique_of_ind_inv_base hbase hinv
    exact huniq (Finmap.lookupD id2 s.round - 1) hprev2_mem _ hsupp1 _ hsupp2

/-- ## KEY THEOREM 1 of 3 — the safety keystone.

**Agreement (`agreement_inv`) is a single-state consequence of the 13 core
lemmas.**  The proof uses only `ind_inv_13` (via `decision_agreement_core_le`) —
so agreement is never carried as a separate inductive conjunct, and need never be
preserved through the circular `step3_decision_compatibility` route.

This is the mathematical heart: two correct replicas that have both decided must
have decided the same value, proved directly from the Apalache-verified core via
the forward-lock engine (`allW_forward_chain_core`, `supportedValues_of_allW_core`,
Lemma 8 / Lemma 11 coin bounds).  Together with KEY THEOREM 2 it removes the
original circular `∀ i` lock hypotheses entirely.

(`agreement_inv s` is exactly the implication `dec₁ ≠ -1 → dec₂ ≠ -1 → dec₁ = dec₂`
written as the disjunction `(dec₁ = -1 ∨ dec₂ = -1) ∨ dec₁ = dec₂`; this lemma
discharges the two trivial "not yet decided" cases and proves the equality from
core in the remaining case.) -/
theorem agreement_inv_of_ind_inv_13
    {s : State}
    (hbase : model_base_assumptions s) (htype : type_ok s) (hinv : ind_inv_13 s) :
    agreement_inv s := by
  intro id1 hid1 id2 hid2
  by_cases hdec1 : Finmap.lookupD id1 s.decision = -1
  · exact Or.inl (Or.inl hdec1)
  · by_cases hdec2 : Finmap.lookupD id2 s.decision = -1
    · exact Or.inl (Or.inr hdec2)
    · refine Or.inr ?_
      rcases le_total (Finmap.lookupD id1 s.round) (Finmap.lookupD id2 s.round) with hle | hle
      · exact decision_agreement_core_le hbase htype hinv hid1 hid2 hdec1 hdec2 hle
      · exact (decision_agreement_core_le hbase htype hinv hid2 hid1 hdec2 hdec1 hle).symm

lemma step3_local_decision_bottom_of_ind_inv
    {s : State}
    (hbase : model_base_assumptions s)
    (htype : type_ok s)
    (hinv : ind_inv_13 s) :
    step3_local_decision_bottom s := by
  classical
  have hbase_parts := hbase
  unfold model_base_assumptions at hbase_parts
  rcases hbase_parts with ⟨_, _, _, _, _⟩
  unfold step3_local_decision_bottom
  intro rid hrid _hstep3 received hreceived hreceived_card
  have hr : Finmap.lookupD rid s.round ∈ s.ROUNDS := by
    unfold type_ok at htype
    exact htype.2.2.1.2 rid hrid
  constructor
  · intro hno_value
    by_contra hdec_ne
    have hdec_value : Finmap.lookupD rid s.decision ∈ values := by
      unfold type_ok at htype
      have hmem := htype.2.1.2 rid hrid
      unfold values
      simp at hmem ⊢
      rcases hmem with hval | hbottoms
      · exact Or.inl hval
      · rcases hbottoms with hval | hbottom
        · exact Or.inr hval
        · exact False.elim (hdec_ne hbottom)
    have hfast :=
      generated_step3_fast_of_all_correct_msg1_value
        (s := s) (r := Finmap.lookupD rid s.round)
        (v := Finmap.lookupD rid s.decision) (received := received)
        hbase htype hinv hr hdec_value hreceived hreceived_card
        (decision_value_controls_current_msg1
          (s := s) (id := rid) hbase htype hinv hrid hdec_ne)
    have hlt := hno_value (Finmap.lookupD rid s.decision) hdec_value
    omega
  · intro v hv hweight hnot_fast
    by_contra hdec_ne
    have hdec_value : Finmap.lookupD rid s.decision ∈ values := by
      unfold type_ok at htype
      have hmem := htype.2.1.2 rid hrid
      unfold values
      simp at hmem ⊢
      rcases hmem with hval | hbottoms
      · exact Or.inl hval
      · rcases hbottoms with hval | hbottom
        · exact Or.inr hval
        · exact False.elim (hdec_ne hbottom)
    have hfast_dec :=
      generated_step3_fast_of_all_correct_msg1_value
        (s := s) (r := Finmap.lookupD rid s.round)
        (v := Finmap.lookupD rid s.decision) (received := received)
        hbase htype hinv hr hdec_value hreceived hreceived_card
        (decision_value_controls_current_msg1
          (s := s) (id := rid) hbase htype hinv hrid hdec_ne)
    have hnot_fast_dec :=
      generated_step3_no_other_fast_value
        (s := s) (r := Finmap.lookupD rid s.round) (v := v)
        (received := received)
        hbase hinv hr hreceived hv hweight hnot_fast
        (Finmap.lookupD rid s.decision) hdec_value
    omega

lemma value_lock_preserved_of_mono_msgs2
    {s s' : State}
    (hmodel : model_assumptions s)
    (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hvalue : s'.value = s.value)
    (hround : s'.round = s.round)
    (hmsgs2_sub : ∀ r, Finmap.lookupD r s.msgs2 ⊆ Finmap.lookupD r s'.msgs2) :
    value_lock s' := by
  classical
  have hmodel_parts := hmodel
  unfold model_assumptions at hmodel_parts
  rcases hmodel_parts with ⟨_, _, _, hround_pred, _⟩
  have hinv_parts := hinv
  unfold ind_inv_13 at hinv_parts
  rcases hinv_parts with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hvalueLock, _⟩
  have hunique := supportedValues_unique_of_ind_inv hmodel hinv
  unfold value_lock at hvalueLock ⊢
  intro id hid v hv
  rw [hcorrect] at hid
  rw [hround]
  rcases hvalueLock id hid v hv with hfirst | hlocked
  · exact Or.inl hfirst
  · right
    rcases hlocked with ⟨hgt, hold_support⟩
    refine ⟨hgt, ?_⟩
    let prev := Finmap.lookupD id s.round - 1
    by_cases hnew_empty : supportedValues s' prev = ∅
    · exact Or.inl hnew_empty
    · right
      have hprev_mem : prev ∈ s.ROUNDS := by
        exact hround_pred (Finmap.lookupD id s.round)
          (by
            unfold type_ok at htype
            exact htype.2.2.1.2 id hid)
          (by omega)
      have htotal :=
        previous_round_has_quorum_for_correct
          (s := s) (id := id) hmodel htype hinv hid hgt
      have hnonempty : (supportedValues s' prev).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hnew_empty
      rcases hnonempty with ⟨w, hwnew⟩
      have hwold :=
        supportedValues_of_mono_msgs2_and_old_quorum
          (s := s) (s' := s') (r := prev) (v := w)
          htype hprev_mem (model_N5T hmodel) hN hT hcorrect hfaulty
          (hmsgs2_sub prev) htotal hwnew
      rcases hold_support with hold_empty | hvalue_old
      · rw [hold_empty] at hwold
        simp at hwold
      · have heq := hunique prev hprev_mem w hwold (Finmap.lookupD id s.value) hvalue_old
        simpa [hvalue, heq] using hwnew

lemma rounds_connection_preserved_of_mono_msgs2
    {s s' : State}
    (hmodel : model_assumptions s)
    (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1_correct_old :
      ∀ {r : Int}, r ∈ s.ROUNDS →
        ∀ {m : Msg1}, m ∈ Finmap.lookupD r s'.msgs1 →
          m.src ∈ s'.CORRECT → m ∈ Finmap.lookupD r s.msgs1)
    (hmsgs2_sub : ∀ r, Finmap.lookupD r s.msgs2 ⊆ Finmap.lookupD r s'.msgs2) :
    rounds_connection s' := by
  classical
  have hmodel_parts := hmodel
  unfold model_assumptions at hmodel_parts
  rcases hmodel_parts with ⟨_, _, hround_pos, _, _⟩
  have hinv_parts := hinv
  unfold ind_inv_13 at hinv_parts
  rcases hinv_parts with
    ⟨_, _, _, _, _, _, _, hrounds_conn, hm1, _, _, _, _⟩
  have hunique := supportedValues_unique_of_ind_inv hmodel hinv
  unfold rounds_connection at hrounds_conn ⊢
  intro r hr hnext
  rw [hrounds] at hr hnext
  by_cases hnew_empty : supportedValues s' r = ∅
  · exact Or.inl hnew_empty
  · right
    have hnonempty : (supportedValues s' r).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hnew_empty
    rcases hnonempty with ⟨v, hvnew⟩
    refine ⟨v, hvnew, ?_⟩
    intro m hm hcorrect_m'
    have hcorrect_m : m.src ∈ s.CORRECT := by
      rw [← hcorrect]
      exact hcorrect_m'
    have hm_old : m ∈ Finmap.lookupD (r + 1) s.msgs1 :=
      hmsgs1_correct_old hnext hm hcorrect_m'
    have hround_succ_ne : r + 1 ≠ 1 := by
      have hr_pos := hround_pos r hr
      omega
    have htotal :=
      hm1 (r + 1) hnext hround_succ_ne ⟨m, hm_old, hcorrect_m⟩
    have hprev_eq : r + 1 - 1 = r := by
      omega
    have hvold :=
      supportedValues_of_mono_msgs2_and_old_quorum
        (s := s) (s' := s') (r := r) (v := v)
        htype hr (model_N5T hmodel) hN hT hcorrect hfaulty (hmsgs2_sub r)
        (by simpa [hprev_eq] using htotal) hvnew
    rcases hrounds_conn r hr hnext with hold_empty | hold_wit
    · rw [hold_empty] at hvold
      simp at hvold
    · rcases hold_wit with ⟨w, hwold, hmsgs_old⟩
      have hvw := hunique r hr v hvold w hwold
      exact (hmsgs_old m hm_old hcorrect_m).trans hvw.symm

lemma step1_preserves_existsQuorum1
    {s s' : State} {r v rid : Int}
    (hquorum : existsQuorum1 s r v)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hmsgs1 :
      s'.msgs1 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs1 ∪
            insert { round := Finmap.lookupD rid s.round, src := rid, value := Finmap.lookupD rid s.value }
              (∅ : Finset Msg1))
          s.msgs1) :
    existsQuorum1 s' r v := by
  classical
  unfold existsQuorum1 at hquorum ⊢
  rw [hN, hT, hmsgs1]
  by_cases hr : r = Finmap.lookupD rid s.round
  · subst r
    simp [lookupD_insert_self]
    have hquorum_old :
        2 *
            ↑(Finset.card
              (senders1 s'
                (Finset.filter (fun m => Msg1.value m = v)
                  (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs1)))) >
          s.N + s.T := by
      unfold senders1 allReplicas at hquorum ⊢
      rw [hcorrect, hfaulty]
      exact hquorum
    have hsub_msgs :
        Finset.filter (fun m => Msg1.value m = v) (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs1) ⊆
          Finset.filter (fun m => Msg1.value m = v)
            (insert { round := Finmap.lookupD rid s.round, src := rid, value := Finmap.lookupD rid s.value }
              (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs1)) := by
      intro m hm
      exact Finset.mem_filter.mpr ⟨Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mp hm).1),
        (Finset.mem_filter.mp hm).2⟩
    have hsub' := senders1_mono (s := s') hsub_msgs
    have hcard := Finset.card_le_card hsub'
    omega
  · rw [lookupD_insert_of_ne hr]
    unfold senders1 allReplicas at hquorum ⊢
    rw [hcorrect, hfaulty]
    exact hquorum

lemma existsQuorum1_of_received_subset
    {s : State} {r v : Int} {received : Finset Msg1}
    (hsub_received : received ⊆ Finmap.lookupD r s.msgs1)
    (hweight :
      2 *
          ↑(Finset.card
            (senders1 s (Finset.filter (fun m => Msg1.value m = v) received))) >
        s.N + s.T) :
    existsQuorum1 s r v := by
  unfold existsQuorum1
  have hsub_msgs :
      Finset.filter (fun m => Msg1.value m = v) received ⊆
        Finset.filter (fun m => Msg1.value m = v) (Finmap.lookupD r s.msgs1) := by
    intro m hm
    exact Finset.mem_filter.mpr
      ⟨hsub_received (Finset.mem_filter.mp hm).1, (Finset.mem_filter.mp hm).2⟩
  have hsub := senders1_mono (s := s) hsub_msgs
  have hcard := Finset.card_le_card hsub
  omega

lemma senders1_filter_value_eq_generated
    {s : State} {received : Finset Msg1} {v : Int} :
    senders1 s (Finset.filter (fun m => Msg1.value m = v) received) =
      Finset.filter
        (fun rid => ∃ m ∈ Finset.filter (fun m => v = Msg1.value m) received, rid = Msg1.src m)
        (s.CORRECT ∪ s.FAULTY) := by
  classical
  unfold senders1 allReplicas
  apply Finset.ext
  intro rid
  simp only [Finset.mem_filter]
  constructor
  · intro h
    rcases h with ⟨hall, m, hm, hsrc⟩
    exact ⟨hall, m, ⟨hm.1, hm.2.symm⟩, hsrc⟩
  · intro h
    rcases h with ⟨hall, m, hm, hsrc⟩
    exact ⟨hall, m, ⟨hm.1, hm.2.symm⟩, hsrc⟩

lemma msg1_eq_mk_of_fields {m : Msg1} {r src v : Int}
    (hround : m.round = r) (hsrc : m.src = src) (hvalue : m.value = v) :
    m = Msg1.mk r src v := by
  cases m
  simp at hround hsrc hvalue ⊢
  exact ⟨hround, hsrc, hvalue⟩

lemma correct_received_value_senders_subset_n
    {s : State} {r v : Int} {received : Finset Msg1}
    (htype : type_ok s)
    (hr : r ∈ s.ROUNDS)
    (hreceived : received ⊆ Finmap.lookupD r s.msgs1) :
    Finset.filter
        (fun id => id ∈ senders1 s (Finset.filter (fun m => Msg1.value m = v) received))
        s.CORRECT ⊆
      Finset.filter
        (fun id => Msg1.mk r id v ∈ Finmap.lookupD r s.msgs1)
        s.CORRECT := by
  intro id hid
  rcases Finset.mem_filter.mp hid with ⟨hid_correct, hsender⟩
  unfold senders1 at hsender
  rcases Finset.mem_filter.mp hsender with ⟨_, m, hm, hsrc⟩
  rcases Finset.mem_filter.mp hm with ⟨hm_received, hvalue⟩
  have hm_full := hreceived hm_received
  have hround := msg1_round_eq_of_type_ok (s := s) (r := r) (m := m) htype hr hm_full
  have hmsg_eq := msg1_eq_mk_of_fields
    (m := m) (r := r) (src := id) (v := v) hround.symm hsrc.symm hvalue
  refine Finset.mem_filter.mpr ⟨hid_correct, ?_⟩
  rwa [← hmsg_eq]

lemma correct_received_value_senders_card_le_n
    {s : State} {r v : Int} {received : Finset Msg1}
    (htype : type_ok s)
    (hr : r ∈ s.ROUNDS)
    (hreceived : received ⊆ Finmap.lookupD r s.msgs1) :
    Finset.card
        (Finset.filter
          (fun id => id ∈ senders1 s (Finset.filter (fun m => Msg1.value m = v) received))
          s.CORRECT) ≤
      Finset.card
        (Finset.filter
          (fun id => Msg1.mk r id v ∈ Finmap.lookupD r s.msgs1)
          s.CORRECT) := by
  exact Finset.card_le_card
    (correct_received_value_senders_subset_n
      (s := s) (r := r) (v := v) (received := received) htype hr hreceived)

lemma correct_received_value_senders_card_le_generated
    {s : State} {received : Finset Msg1} {v : Int} :
    Finset.card
        (Finset.filter
          (fun id => id ∈ senders1 s (Finset.filter (fun m => Msg1.value m = v) received))
          s.CORRECT) ≤
      Finset.card
        (Finset.filter
          (fun id => ∃ m ∈ Finset.filter (fun m => v = Msg1.value m) received, id = Msg1.src m)
          (s.CORRECT ∪ s.FAULTY)) := by
  have hsub :
      Finset.filter
          (fun id => id ∈ senders1 s (Finset.filter (fun m => Msg1.value m = v) received))
          s.CORRECT ⊆
        senders1 s (Finset.filter (fun m => Msg1.value m = v) received) := by
    intro id hid
    exact (Finset.mem_filter.mp hid).2
  have hcard := Finset.card_le_card hsub
  calc
    Finset.card
        (Finset.filter
          (fun id => id ∈ senders1 s (Finset.filter (fun m => Msg1.value m = v) received))
          s.CORRECT)
        ≤ Finset.card (senders1 s (Finset.filter (fun m => Msg1.value m = v) received)) := hcard
    _ =
      Finset.card
        (Finset.filter
          (fun id => ∃ m ∈ Finset.filter (fun m => v = Msg1.value m) received, id = Msg1.src m)
          (s.CORRECT ∪ s.FAULTY)) := by
        rw [senders1_filter_value_eq_generated]

lemma received_senders_cover_correct_values_or_faulty
    {s : State} {r : Int} {received : Finset Msg1}
    (htype : type_ok s)
    (hr : r ∈ s.ROUNDS)
    (hreceived : received ⊆ Finmap.lookupD r s.msgs1) :
    Finset.filter (fun id => ∃ m ∈ received, id = Msg1.src m) (s.CORRECT ∪ s.FAULTY) ⊆
      (Finset.filter
          (fun id => id ∈ senders1 s (Finset.filter (fun m => Msg1.value m = 0) received))
          s.CORRECT ∪
        Finset.filter
          (fun id => id ∈ senders1 s (Finset.filter (fun m => Msg1.value m = 1) received))
          s.CORRECT) ∪
        Finset.filter
          (fun id => id ∈ senders1 s received)
          s.FAULTY := by
  intro id hid
  rcases Finset.mem_filter.mp hid with ⟨hall, m, hm_received, hsrc⟩
  rcases Finset.mem_union.mp hall with hid_correct | hid_faulty
  · have hm_full := hreceived hm_received
    unfold type_ok at htype
    have hvalue := (htype.2.2.2.2.1 r hr m hm_full).2.2
    simp at hvalue
    rcases hvalue with hvalue0 | hvalue1
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      left
      refine Finset.mem_filter.mpr ⟨hid_correct, ?_⟩
      unfold senders1 allReplicas
      refine Finset.mem_filter.mpr ⟨hall, m, ?_, hsrc⟩
      exact Finset.mem_filter.mpr ⟨hm_received, hvalue0⟩
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      right
      refine Finset.mem_filter.mpr ⟨hid_correct, ?_⟩
      unfold senders1 allReplicas
      refine Finset.mem_filter.mpr ⟨hall, m, ?_, hsrc⟩
      exact Finset.mem_filter.mpr ⟨hm_received, hvalue1⟩
  · apply Finset.mem_union.mpr
    right
    refine Finset.mem_filter.mpr ⟨hid_faulty, ?_⟩
    unfold senders1 allReplicas
    exact Finset.mem_filter.mpr ⟨hall, m, hm_received, hsrc⟩

lemma received_senders_card_le_correct_values_add_faulty
    {s : State} {r : Int} {received : Finset Msg1}
    (htype : type_ok s)
    (hr : r ∈ s.ROUNDS)
    (hreceived : received ⊆ Finmap.lookupD r s.msgs1) :
    Finset.card (Finset.filter (fun id => ∃ m ∈ received, id = Msg1.src m) (s.CORRECT ∪ s.FAULTY)) ≤
      Finset.card
          (Finset.filter
            (fun id => id ∈ senders1 s (Finset.filter (fun m => Msg1.value m = 0) received))
            s.CORRECT) +
        Finset.card
          (Finset.filter
            (fun id => id ∈ senders1 s (Finset.filter (fun m => Msg1.value m = 1) received))
            s.CORRECT) +
          Finset.card
            (Finset.filter
              (fun id => id ∈ senders1 s received)
              s.FAULTY) := by
  let c0 :=
    Finset.filter
      (fun id => id ∈ senders1 s (Finset.filter (fun m => Msg1.value m = 0) received))
      s.CORRECT
  let c1 :=
    Finset.filter
      (fun id => id ∈ senders1 s (Finset.filter (fun m => Msg1.value m = 1) received))
      s.CORRECT
  let ff :=
    Finset.filter
      (fun id => id ∈ senders1 s received)
      s.FAULTY
  have hsub :
      Finset.filter (fun id => ∃ m ∈ received, id = Msg1.src m) (s.CORRECT ∪ s.FAULTY) ⊆
        (c0 ∪ c1) ∪ ff := by
    simpa [c0, c1, ff] using
      received_senders_cover_correct_values_or_faulty
        (s := s) (r := r) (received := received) htype hr hreceived
  have hcard_sub := Finset.card_le_card hsub
  have hcard_union1 : Finset.card ((c0 ∪ c1) ∪ ff) ≤ Finset.card (c0 ∪ c1) + Finset.card ff :=
    Finset.card_union_le _ _
  have hcard_union0 : Finset.card (c0 ∪ c1) ≤ Finset.card c0 + Finset.card c1 :=
    Finset.card_union_le _ _
  change
    Finset.card (Finset.filter (fun id => ∃ m ∈ received, id = Msg1.src m) (s.CORRECT ∪ s.FAULTY)) ≤
      Finset.card c0 + Finset.card c1 + Finset.card ff
  omega

lemma q2_no_quorum_conclusion_of_generated_received
    {s : State} {r : Int} {received : Finset Msg1}
    (htype : type_ok s)
    (hr : r ∈ s.ROUNDS)
    (hreceived : received ∈ Finset.powerset (Finmap.lookupD r s.msgs1))
    (hreceived_card :
      Finset.card (Finset.filter (fun id => ∃ m ∈ received, id = Msg1.src m) (s.CORRECT ∪ s.FAULTY)) ≥
        s.N - s.T)
    (hno_quorum :
      ∀ v ∈ values,
        2 *
              Finset.card
                (Finset.filter
                  (fun id =>
                    ∃ m ∈ Finset.filter (fun m => v = Msg1.value m) received, id = Msg1.src m)
                  (s.CORRECT ∪ s.FAULTY)) ≤
            s.N + s.T)
    (hN5T : s.N > 5 * s.T) :
    let n0 :=
      Finset.card
        (Finset.filter (fun id => Msg1.mk r id 0 ∈ Finmap.lookupD r s.msgs1) s.CORRECT)
    let n1 :=
      Finset.card
        (Finset.filter (fun id => Msg1.mk r id 1 ∈ Finmap.lookupD r s.msgs1) s.CORRECT)
    let nf :=
      Finset.card
        (Finset.filter
          (fun id => id ∈ senders1 s (Finmap.lookupD r s.msgs1))
          s.FAULTY)
    ∃ x0 ∈ Finset.Icc 0 s.N,
      ∃ x1 ∈ Finset.Icc 0 s.N,
        x0 ≤ n0 ∧ x1 ≤ n1 ∧ x0 + x1 + nf ≥ s.N - s.T ∧
          2 * x0 ≤ s.N + s.T ∧ 2 * x1 ≤ s.N + s.T := by
  classical
  let c0 :=
    Finset.filter
      (fun id => id ∈ senders1 s (Finset.filter (fun m => Msg1.value m = 0) received))
      s.CORRECT
  let c1 :=
    Finset.filter
      (fun id => id ∈ senders1 s (Finset.filter (fun m => Msg1.value m = 1) received))
      s.CORRECT
  let nfset :=
    Finset.filter
      (fun id => id ∈ senders1 s (Finmap.lookupD r s.msgs1))
      s.FAULTY
  have hreceived_sub : received ⊆ Finmap.lookupD r s.msgs1 :=
    Finset.mem_powerset.mp hreceived
  have hc0_n :=
    correct_received_value_senders_card_le_n
      (s := s) (r := r) (v := 0) (received := received) htype hr hreceived_sub
  have hc1_n :=
    correct_received_value_senders_card_le_n
      (s := s) (r := r) (v := 1) (received := received) htype hr hreceived_sub
  have hc0_gen :=
    correct_received_value_senders_card_le_generated
      (s := s) (received := received) (v := 0)
  have hc1_gen :=
    correct_received_value_senders_card_le_generated
      (s := s) (received := received) (v := 1)
  have hcover :=
    received_senders_card_le_correct_values_add_faulty
      (s := s) (r := r) (received := received) htype hr hreceived_sub
  have hfaulty_sub :
      Finset.filter (fun id => id ∈ senders1 s received) s.FAULTY ⊆ nfset := by
    intro id hid
    rcases Finset.mem_filter.mp hid with ⟨hid_faulty, hsender⟩
    refine Finset.mem_filter.mpr ⟨hid_faulty, ?_⟩
    exact senders1_mono (s := s) hreceived_sub hsender
  have hfaulty_card := Finset.card_le_card hfaulty_sub
  have hno0 := hno_quorum 0 (by simp [values])
  have hno1 := hno_quorum 1 (by simp [values])
  have hc0_gen_int :
      (Finset.card c0 : Int) ≤
        Finset.card
          (Finset.filter
            (fun id => ∃ m ∈ Finset.filter (fun m => (0 : Int) = Msg1.value m) received,
              id = Msg1.src m)
            (s.CORRECT ∪ s.FAULTY)) := by
    change
      (Finset.card
        (Finset.filter
          (fun id => id ∈ senders1 s (Finset.filter (fun m => Msg1.value m = 0) received))
          s.CORRECT) : Int) ≤
        Finset.card
          (Finset.filter
            (fun id => ∃ m ∈ Finset.filter (fun m => (0 : Int) = Msg1.value m) received,
              id = Msg1.src m)
            (s.CORRECT ∪ s.FAULTY))
    exact_mod_cast hc0_gen
  have hc1_gen_int :
      (Finset.card c1 : Int) ≤
        Finset.card
          (Finset.filter
            (fun id => ∃ m ∈ Finset.filter (fun m => (1 : Int) = Msg1.value m) received,
              id = Msg1.src m)
            (s.CORRECT ∪ s.FAULTY)) := by
    change
      (Finset.card
        (Finset.filter
          (fun id => id ∈ senders1 s (Finset.filter (fun m => Msg1.value m = 1) received))
          s.CORRECT) : Int) ≤
        Finset.card
          (Finset.filter
            (fun id => ∃ m ∈ Finset.filter (fun m => (1 : Int) = Msg1.value m) received,
              id = Msg1.src m)
            (s.CORRECT ∪ s.FAULTY))
    exact_mod_cast hc1_gen
  have hcover_int :
      (Finset.card
        (Finset.filter (fun id => ∃ m ∈ received, id = Msg1.src m)
          (s.CORRECT ∪ s.FAULTY)) : Int) ≤
        Finset.card c0 + Finset.card c1 +
          Finset.card (Finset.filter (fun id => id ∈ senders1 s received) s.FAULTY) := by
    change
      (Finset.card
        (Finset.filter (fun id => ∃ m ∈ received, id = Msg1.src m)
          (s.CORRECT ∪ s.FAULTY)) : Int) ≤
        Finset.card
          (Finset.filter
            (fun id => id ∈ senders1 s (Finset.filter (fun m => Msg1.value m = 0) received))
            s.CORRECT) +
          Finset.card
            (Finset.filter
              (fun id => id ∈ senders1 s (Finset.filter (fun m => Msg1.value m = 1) received))
              s.CORRECT) +
            Finset.card (Finset.filter (fun id => id ∈ senders1 s received) s.FAULTY)
    exact_mod_cast hcover
  have hfaulty_card_int :
      (Finset.card (Finset.filter (fun id => id ∈ senders1 s received) s.FAULTY) : Int) ≤
        Finset.card nfset := by
    exact_mod_cast hfaulty_card
  refine ⟨(Finset.card c0 : Int), ?_, (Finset.card c1 : Int), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Finset.mem_Icc]
    omega
  · simp only [Finset.mem_Icc]
    omega
  · change (Finset.card c0 : Int) ≤
      Finset.card
        (Finset.filter (fun id => Msg1.mk r id 0 ∈ Finmap.lookupD r s.msgs1) s.CORRECT)
    exact_mod_cast hc0_n
  · change (Finset.card c1 : Int) ≤
      Finset.card
        (Finset.filter (fun id => Msg1.mk r id 1 ∈ Finmap.lookupD r s.msgs1) s.CORRECT)
    exact_mod_cast hc1_n
  · change
      (Finset.card c0 : Int) + (Finset.card c1 : Int) + (Finset.card nfset : Int) ≥ s.N - s.T
    omega
  · have : 2 * (Finset.card c0 : Int) ≤ s.N + s.T := by
      omega
    exact this
  · have : 2 * (Finset.card c1 : Int) ≤ s.N + s.T := by
      omega
    exact this

lemma step2_q2_preserves_q2_requires_no_quorum_faster
    {s s' : State} {rid : Int} {received : Finset Msg1}
    (htype : type_ok s)
    (hq2 : q2_requires_no_quorum_faster s)
    (hrid : rid ∈ s.CORRECT)
    (hreceived : received ∈ Finset.powerset (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs1))
    (hreceived_card :
      Finset.card
          (Finset.filter (fun id => ∃ m ∈ received, id = Msg1.src m) (s.CORRECT ∪ s.FAULTY)) ≥
        s.N - s.T)
    (hno_quorum :
      ∀ v ∈ values,
        2 *
              Finset.card
                (Finset.filter
                  (fun id =>
                    ∃ m ∈ Finset.filter (fun m => v = Msg1.value m) received, id = Msg1.src m)
                  (s.CORRECT ∪ s.FAULTY)) ≤
            s.N + s.T)
    (hN5T : s.N > 5 * s.T)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1 : s'.msgs1 = s.msgs1)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 ∪
            insert { kind := Msg2Kind.Q2, round := Finmap.lookupD rid s.round, src := rid, value := -2 }
              (∅ : Finset Msg2))
          s.msgs2) :
    q2_requires_no_quorum_faster s' := by
  classical
  unfold q2_requires_no_quorum_faster at hq2 ⊢
  intro r hr hq
  rw [hrounds] at hr
  rcases hq with ⟨m, hm, hkind, hcorrect_m⟩
  rw [hcorrect] at hcorrect_m
  rw [hmsgs2] at hm
  by_cases hrid_round : r = Finmap.lookupD rid s.round
  · subst r
    simp [lookupD_insert_self] at hm
    rcases hm with hmnew | hmold
    · have hr_current : Finmap.lookupD rid s.round ∈ s.ROUNDS := by
        unfold type_ok at htype
        exact htype.2.2.1.2 rid hrid
      have hconcl :=
        q2_no_quorum_conclusion_of_generated_received
          (s := s) (r := Finmap.lookupD rid s.round) (received := received)
          htype hr_current hreceived hreceived_card hno_quorum hN5T
      simpa [senders1, allReplicas, hN, hT, hcorrect, hfaulty, hmsgs1] using hconcl
    · have hold' := hq2 (Finmap.lookupD rid s.round) hr ⟨m, hmold, hkind, hcorrect_m⟩
      simpa [senders1, allReplicas, hN, hT, hcorrect, hfaulty, hmsgs1] using hold'
  · rw [lookupD_insert_of_ne hrid_round] at hm
    have hold' := hq2 r hr ⟨m, hm, hkind, hcorrect_m⟩
    simpa [senders1, allReplicas, hN, hT, hcorrect, hfaulty, hmsgs1] using hold'

lemma existsQuorum1_of_generated_step2_weight
    {s : State} {r v : Int} {received : Finset Msg1}
    (hreceived : received ∈ Finset.powerset (Finmap.lookupD r s.msgs1))
    (hweight :
      2 *
            ↑(Finset.card
              (Finset.filter
                (fun rid =>
                  ∃ m ∈ Finset.filter (fun m => v = Msg1.value m) received, rid = Msg1.src m)
                (s.CORRECT ∪ s.FAULTY))) >
          s.N + s.T) :
    existsQuorum1 s r v := by
  have hsub_received : received ⊆ Finmap.lookupD r s.msgs1 :=
    Finset.mem_powerset.mp hreceived
  apply existsQuorum1_of_received_subset (s := s) (r := r) (v := v)
    (received := received) hsub_received
  rw [senders1_filter_value_eq_generated]
  exact hweight

lemma frame_d2_requires_quorum
    {s s' : State}
    (hd2 : d2_requires_quorum s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1 : s'.msgs1 = s.msgs1)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    d2_requires_quorum s' := by
  unfold d2_requires_quorum at hd2 ⊢
  intro r hr v hv hm
  rw [hrounds] at hr
  rcases hm with ⟨m, hm, hkind, hval, hcorrect_m⟩
  rw [hmsgs2] at hm
  rw [hcorrect] at hcorrect_m
  exact frame_existsQuorum1
      (hd2 r hr v hv ⟨m, hm, hkind, hval, hcorrect_m⟩)
      hN hT hcorrect hfaulty hmsgs1

lemma step1_preserves_d2_requires_quorum
    {s s' : State} {rid : Int}
    (hd2 : d2_requires_quorum s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1 :
      s'.msgs1 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs1 ∪
            insert { round := Finmap.lookupD rid s.round, src := rid, value := Finmap.lookupD rid s.value }
              (∅ : Finset Msg1))
          s.msgs1)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    d2_requires_quorum s' := by
  unfold d2_requires_quorum at hd2 ⊢
  intro r hr v hv hm
  rw [hrounds] at hr
  rcases hm with ⟨m, hm, hkind, hval, hcorrect_m⟩
  rw [hmsgs2] at hm
  rw [hcorrect] at hcorrect_m
  exact step1_preserves_existsQuorum1
    (s := s) (s' := s') (rid := rid)
    (hd2 r hr v hv ⟨m, hm, hkind, hval, hcorrect_m⟩)
    hN hT hcorrect hfaulty hmsgs1

lemma step2_q2_preserves_d2_requires_quorum
    {s s' : State} {rid : Int}
    (hd2 : d2_requires_quorum s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1 : s'.msgs1 = s.msgs1)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 ∪
            insert { kind := Msg2Kind.Q2, round := Finmap.lookupD rid s.round, src := rid, value := -2 }
              (∅ : Finset Msg2))
          s.msgs2) :
    d2_requires_quorum s' := by
  classical
  unfold d2_requires_quorum at hd2 ⊢
  intro r hr v hv hm
  rw [hrounds] at hr
  rcases hm with ⟨m, hm, hkind, hval, hcorrect_m⟩
  rw [hcorrect] at hcorrect_m
  rw [hmsgs2] at hm
  by_cases hrid_round : r = Finmap.lookupD rid s.round
  · subst r
    simp [lookupD_insert_self] at hm
    rcases hm with hmnew | hmold
    · rw [hmnew] at hkind
      simp at hkind
    · exact frame_existsQuorum1
        (hd2 (Finmap.lookupD rid s.round) hr v hv ⟨m, hmold, hkind, hval, hcorrect_m⟩)
        hN hT hcorrect hfaulty hmsgs1
  · rw [lookupD_insert_of_ne hrid_round] at hm
    exact frame_existsQuorum1
      (hd2 r hr v hv ⟨m, hm, hkind, hval, hcorrect_m⟩)
      hN hT hcorrect hfaulty hmsgs1

lemma step2_d2_preserves_d2_requires_quorum_of_existsQuorum1
    {s s' : State} {rid newValue : Int}
    (hd2 : d2_requires_quorum s)
    (hnew_quorum : existsQuorum1 s (Finmap.lookupD rid s.round) newValue)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1 : s'.msgs1 = s.msgs1)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 ∪
            insert { kind := Msg2Kind.D2, round := Finmap.lookupD rid s.round, src := rid, value := newValue }
              (∅ : Finset Msg2))
          s.msgs2) :
    d2_requires_quorum s' := by
  classical
  unfold d2_requires_quorum at hd2 ⊢
  intro r hr v hv hm
  rw [hrounds] at hr
  rcases hm with ⟨m, hm, hkind, hval, hcorrect_m⟩
  rw [hcorrect] at hcorrect_m
  rw [hmsgs2] at hm
  by_cases hrid_round : r = Finmap.lookupD rid s.round
  · subst r
    simp [lookupD_insert_self] at hm
    rcases hm with hmnew | hmold
    · rw [hmnew] at hval
      simp at hval
      subst v
      exact frame_existsQuorum1 hnew_quorum hN hT hcorrect hfaulty hmsgs1
    · exact frame_existsQuorum1
        (hd2 (Finmap.lookupD rid s.round) hr v hv ⟨m, hmold, hkind, hval, hcorrect_m⟩)
        hN hT hcorrect hfaulty hmsgs1
  · rw [lookupD_insert_of_ne hrid_round] at hm
    exact frame_existsQuorum1
      (hd2 r hr v hv ⟨m, hm, hkind, hval, hcorrect_m⟩)
      hN hT hcorrect hfaulty hmsgs1

lemma step2_d2_preserves_d2_requires_quorum
    {s s' : State} {rid newValue : Int} {received : Finset Msg1}
    (hd2 : d2_requires_quorum s)
    (hreceived : received ∈ Finset.powerset (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs1))
    (hweight :
      2 *
            ↑(Finset.card
              (Finset.filter
                (fun rid =>
                  ∃ m ∈ Finset.filter (fun m => newValue = Msg1.value m) received,
                    rid = Msg1.src m)
                (s.CORRECT ∪ s.FAULTY))) >
          s.N + s.T)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1 : s'.msgs1 = s.msgs1)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert (Finmap.lookupD rid s.round)
          (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 ∪
            insert { kind := Msg2Kind.D2, round := Finmap.lookupD rid s.round, src := rid, value := newValue }
              (∅ : Finset Msg2))
          s.msgs2) :
    d2_requires_quorum s' := by
  exact step2_d2_preserves_d2_requires_quorum_of_existsQuorum1
    (s := s) (s' := s') (rid := rid) (newValue := newValue)
    hd2
    (existsQuorum1_of_generated_step2_weight
      (s := s) (r := Finmap.lookupD rid s.round) (v := newValue)
      (received := received) hreceived hweight)
    hN hT hcorrect hfaulty hrounds hmsgs1 hmsgs2

lemma step3_preserves_d2_requires_quorum
    {s s' : State}
    (hd2 : d2_requires_quorum s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1 : s'.msgs1 = s.msgs1)
    (hmsgs2 : s'.msgs2 = s.msgs2) :
    d2_requires_quorum s' :=
  frame_d2_requires_quorum hd2 hN hT hcorrect hfaulty hrounds hmsgs1 hmsgs2

lemma faulty_step_preserves_d2_requires_quorum
    {s s' : State} {r_faulty : Int} {f1 : Finset Msg1} {f2d f2q : Finset Msg2}
    (hdisj : s.CORRECT ∩ s.FAULTY = ∅)
    (hd2 : d2_requires_quorum s)
    (hf2d :
      f2d ∈
        Finset.powerset
          (Finset.image (fun x => Msg2.mk Msg2Kind.D2 r_faulty (x).1 (x).2)
            (Finset.product s.FAULTY (insert 0 (insert 1 (∅ : Finset Int))))))
    (hf2q :
      f2q ∈
        Finset.powerset
          (Finset.image (fun src => Msg2.mk Msg2Kind.Q2 r_faulty src (-2)) s.FAULTY))
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1 :
      s'.msgs1 = Finmap.insert r_faulty (Finmap.lookupD r_faulty s.msgs1 ∪ f1) s.msgs1)
    (hmsgs2 : s'.msgs2 =
      Finmap.insert r_faulty (Finmap.lookupD r_faulty s.msgs2 ∪ (f2d ∪ f2q)) s.msgs2) :
    d2_requires_quorum s' := by
  classical
  unfold d2_requires_quorum at hd2 ⊢
  intro r hr v hv hm
  rw [hrounds] at hr
  rcases hm with ⟨m, hm, hkind, hval, hcorrect_m⟩
  rw [hcorrect] at hcorrect_m
  rw [hmsgs2] at hm
  by_cases hr_faulty : r = r_faulty
  · subst r
    simp [lookupD_insert_self] at hm
    rcases hm with hmold | hmnew
    · exact existsQuorum1_faulty_step
        (hd2 r_faulty hr v hv ⟨m, hmold, hkind, hval, hcorrect_m⟩)
        hN hT hcorrect hfaulty hmsgs1
    · rcases hmnew with hmd | hmq
      · have hnot := msg2_d2_src_not_correct_of_mem_faulty_step (s := s) hdisj hf2d hmd
        exact False.elim (hnot hcorrect_m)
      · have hnot := msg2_q2_src_not_correct_of_mem_faulty_step (s := s) hdisj hf2q hmq
        exact False.elim (hnot hcorrect_m)
  · rw [lookupD_insert_of_ne hr_faulty] at hm
    exact existsQuorum1_faulty_step
      (hd2 r hr v hv ⟨m, hm, hkind, hval, hcorrect_m⟩)
      hN hT hcorrect hfaulty hmsgs1

lemma msg1_src_faulty_of_mem_initial
    {s : State} {f : Finset Msg1} {m : Msg1}
    (hf :
      f ∈
        Finset.powerset
          (Finset.image (fun x => Msg1.mk (x).1 ((x).2).1 ((x).2).2)
            (Finset.product s.ROUNDS
              (Finset.product s.FAULTY (insert 0 (insert 1 (∅ : Finset Int)))))))
    (hm : m ∈ f) :
    m.src ∈ s.FAULTY := by
  have hsubset := (Finset.mem_powerset.mp hf) hm
  rcases Finset.mem_image.mp hsubset with ⟨x, hx, rfl⟩
  rcases Finset.mem_product.mp hx with ⟨_, hxTail⟩
  rcases Finset.mem_product.mp hxTail with ⟨hsrc, _⟩
  simpa using hsrc

lemma r_round_src_src_faulty_of_mem_initial
    {s : State} {f : Finset R_round_src} {m : R_round_src}
    (hf :
      f ∈
        Finset.powerset
          (Finset.image (fun x => R_round_src.mk (x).1 (x).2)
            (Finset.product s.ROUNDS s.FAULTY)))
    (hm : m ∈ f) :
    m.src ∈ s.FAULTY := by
  have hsubset := (Finset.mem_powerset.mp hf) hm
  rcases Finset.mem_image.mp hsubset with ⟨x, hx, rfl⟩
  simpa using (Finset.mem_product.mp hx).2

lemma msg1_src_not_correct_of_mem_initial
    {s : State} {f : Finset Msg1} {m : Msg1}
    (hdisj : s.CORRECT ∩ s.FAULTY = ∅)
    (hf :
      f ∈
        Finset.powerset
          (Finset.image (fun x => Msg1.mk (x).1 ((x).2).1 ((x).2).2)
            (Finset.product s.ROUNDS
              (Finset.product s.FAULTY (insert 0 (insert 1 (∅ : Finset Int)))))))
    (hm : m ∈ f) :
    m.src ∉ s.CORRECT := by
  intro hc
  have hfaulty := msg1_src_faulty_of_mem_initial (s := s) hf hm
  have : m.src ∈ s.CORRECT ∩ s.FAULTY := by
    exact Finset.mem_inter.mpr ⟨hc, hfaulty⟩
  simp [hdisj] at this

lemma r_round_src_src_not_correct_of_mem_initial
    {s : State} {f : Finset R_round_src} {m : R_round_src}
    (hdisj : s.CORRECT ∩ s.FAULTY = ∅)
    (hf :
      f ∈
        Finset.powerset
          (Finset.image (fun x => R_round_src.mk (x).1 (x).2)
            (Finset.product s.ROUNDS s.FAULTY)))
    (hm : m ∈ f) :
    m.src ∉ s.CORRECT := by
  intro hc
  have hfaulty := r_round_src_src_faulty_of_mem_initial (s := s) hf hm
  have : m.src ∈ s.CORRECT ∩ s.FAULTY := by
    exact Finset.mem_inter.mpr ⟨hc, hfaulty⟩
  simp [hdisj] at this

/-! ### Agreement safety frontier

The previous proof closed preservation by making `step3` unreachable.  That
lemma depended on over-framing in generated Lean definitions: an inner choice
branch simultaneously assigned `s'.decision` and framed later action writes such
as `s'.round = s.round`.  The lowering now scopes frames to sibling choice
assignments, so `step3` is satisfiable and these obligations are the real proof
work.
-/

lemma init_with_faults_ind_inv {s : State}
    (hmodel : model_assumptions s) (_htype : type_ok s)
    (hinit : init_with_faults s) : ind_inv_13 s := by
  classical
  unfold model_assumptions assumptions_hold at hmodel
  rcases hmodel with ⟨⟨_, _, _, _, _⟩, hdisj, hround_pos, _, _⟩
  unfold init_with_faults at hinit
  rcases hinit with
    ⟨_, init_value, hinit_value, _, f1, hf1, _, f2d, hf2d, _, f2q, hf2q,
      hvalue, hdec_keys, hdec, hround_keys, hround, hstep_keys, hstep,
      hmsgs1_keys, hmsgs1, hmsgs2_keys, hmsgs2, hghost⟩
  unfold ind_inv_13
  refine ⟨?_, ?_⟩
  · unfold no_equivocation1_by_correct
    intro r hr m1 hm1 m2 hm2 hsrc
    have hm1f : m1 ∈ f1 := by
      rw [hmsgs1 r hr] at hm1
      exact (Finset.mem_filter.mp hm1).1
    have hnot := msg1_src_not_correct_of_mem_initial (s := s) hdisj hf1 hm1f
    exact False.elim (hnot hsrc.1)
  · have msg1_src_not_correct :
        ∀ {r : Int}, r ∈ s.ROUNDS →
        ∀ {m : Msg1}, m ∈ Finmap.lookupD r s.msgs1 → m.src ∉ s.CORRECT := by
      intro r hr m hm
      rw [hmsgs1 r hr] at hm
      exact msg1_src_not_correct_of_mem_initial (s := s) hdisj hf1
        (Finset.mem_filter.mp hm).1
    have msg2_src_not_correct :
        ∀ {r : Int}, r ∈ s.ROUNDS →
        ∀ {m : Msg2}, m ∈ Finmap.lookupD r s.msgs2 → m.src ∉ s.CORRECT := by
      intro r hr m hm
      rw [hmsgs2 r hr] at hm
      rcases Finset.mem_union.mp hm with hmD | hmQ
      · rcases Finset.mem_image.mp hmD with ⟨m1, hm1, rfl⟩
        exact msg1_src_not_correct_of_mem_initial (s := s) hdisj hf2d
          (Finset.mem_filter.mp hm1).1
      · rcases Finset.mem_image.mp hmQ with ⟨m1, hm1, rfl⟩
        exact r_round_src_src_not_correct_of_mem_initial (s := s) hdisj hf2q
          (Finset.mem_filter.mp hm1).1
    have msg2_q2_src_faulty :
        ∀ {r : Int}, r ∈ s.ROUNDS →
        ∀ {m : Msg2}, m ∈ Finmap.lookupD r s.msgs2 →
          m.kind = Msg2Kind.Q2 → m.src ∈ s.FAULTY := by
      intro r hr m hm hkind
      rw [hmsgs2 r hr] at hm
      rcases Finset.mem_union.mp hm with hmD | hmQ
      · rcases Finset.mem_image.mp hmD with ⟨m1, hm1, rfl⟩
        simp at hkind
      · rcases Finset.mem_image.mp hmQ with ⟨m1, hm1, rfl⟩
        exact r_round_src_src_faulty_of_mem_initial (s := s) hf2q
          (Finset.mem_filter.mp hm1).1
    refine ⟨?_, ?_⟩
    · unfold no_equivocation2_by_correct
      intro r hr m1 hm1 m2 hm2
      constructor
      · intro _ hcorrect
        exact False.elim (msg2_src_not_correct hr hm1 hcorrect)
      · intro hq
        exact msg2_q2_src_faulty hr hm1 hq.1
    · refine ⟨?_, ?_⟩
      · unfold messages_not_from_future
        intro r hr
        constructor
        · intro m hm hc
          exact False.elim (msg1_src_not_correct hr hm hc)
        · intro m hm hc
          exact False.elim (msg2_src_not_correct hr hm hc)
      · refine ⟨?_, ?_⟩
        · unfold round_needs_sent_messages
          intro id hid r hr
          constructor
          · intro hcase
            rcases hcase with hlt | heq_step
            · rw [hround id hid] at hlt
              have hpos := hround_pos r hr
              omega
            · exact False.elim (heq_step.2 (hstep id hid))
          · constructor
            · intro hlt
              rw [hround id hid] at hlt
              have hpos := hround_pos r hr
              omega
            · intro heq_step
              rw [hstep id hid] at heq_step
              cases heq_step.2
        · refine ⟨?_, ?_⟩
          · unfold decision_defines_value
            intro id hid hne
            exact False.elim (hne (hdec id hid))
          · refine ⟨?_, ?_⟩
            · unfold d2_requires_quorum
              intro r hr v hv hm
              rcases hm with ⟨m, hm, _, _, hcorrect⟩
              exact False.elim (msg2_src_not_correct hr hm hcorrect)
            · refine ⟨?_, ?_⟩
              · unfold q2_requires_no_quorum_faster
                intro r hr hq
                rcases hq with ⟨m, hm, hkind, hcorrect⟩
                exact False.elim (msg2_src_not_correct hr hm hcorrect)
              · refine ⟨?_, ?_⟩
                · unfold rounds_connection
                  intro r hr hnext
                  by_cases hsup : supportedValues s r = ∅
                  · exact Or.inl hsup
                  · right
                    have hnonempty : (supportedValues s r).Nonempty :=
                      Finset.nonempty_iff_ne_empty.mpr hsup
                    obtain ⟨v, hv⟩ := hnonempty
                    refine ⟨v, hv, ?_⟩
                    intro m hm hcorrect
                    exact False.elim (msg1_src_not_correct hnext hm hcorrect)
                · refine ⟨?_, ?_⟩
                  · unfold m1_requires_quorum
                    intro r hr hne hm
                    rcases hm with ⟨m, hm, hcorrect⟩
                    exact False.elim (msg1_src_not_correct hr hm hcorrect)
                  · refine ⟨?_, ?_⟩
                    · unfold value_on_quorum_less_ram
                      intro id hid
                      dsimp
                      intro hgt
                      rw [hround id hid] at hgt
                      omega
                    · refine ⟨?_, ?_⟩
                      · unfold cannot_jump_rounds_without_quorum
                        intro r hr hnext hproc
                        rcases hproc with ⟨id, hid, hround_next, hstep_id⟩
                        rw [hround id hid] at hround_next
                        have hpos := hround_pos r hr
                        omega
                      · refine ⟨?_, ?_⟩
                        · unfold value_lock
                          intro id hid v hv
                          exact Or.inl (hround id hid)
                        · unfold decision_requires_last_quorum_less_ram
                          intro id hid
                          exact Or.inl (hdec id hid)

lemma step1_preserves_ind_inv_if {s s' : State} {rid : Int}
    (hmodel : model_assumptions s) (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (hrid : rid ∈ s.CORRECT)
    (hcompat :
      ∀ r ∈ s.ROUNDS,
        r + 1 = Finmap.lookupD rid s.round →
          supportedValues s r = ∅ ∨
            ∃ v ∈ supportedValues s r,
              Finmap.lookupD rid s.value = v ∧
                ∀ m ∈ Finmap.lookupD (r + 1) s.msgs1,
                  m.src ∈ s.CORRECT → m.value = v)
    (hstep1 : step1 rid s s') :
    ind_inv_13 s' := by
  classical
  unfold ind_inv_13 at hinv
  unfold ind_inv_13
  rcases hinv with
    ⟨hnoeq1, hnoeq2, hfuture, hroundNeeds, hdecval, hd2, hq2, hrounds_conn,
      hm1, hvalueQ, hjumps, hvalueLock, hdecReq⟩
  unfold model_assumptions at hmodel
  rcases hmodel with ⟨_, _, _, hround_pred, _⟩
  unfold step1 at hstep1
  rcases hstep1 with
    ⟨⟨hstep_old, hmsgs1, hstep, _hghost⟩,
      hN, hT, _hF, hcorrect, hfaulty, hrounds, hvalue, hdecision, hround, hmsgs2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact step1_preserves_no_equivocation1
      (s := s) (s' := s') (rid := rid)
      htype hnoeq1 hfuture hrid hstep_old hmsgs1 hcorrect hrounds
  · exact frame_no_equivocation2 hnoeq2 hcorrect hfaulty hrounds hmsgs2
  · exact step1_preserves_messages_not_from_future
      (s := s) (s' := s') (rid := rid)
      hfuture hstep_old hmsgs1 hstep hcorrect hrounds hround hmsgs2
  · exact step1_preserves_round_needs_sent_messages
      (s := s) (s' := s') (rid := rid)
      hroundNeeds hmsgs1 hmsgs2 hstep hcorrect hrounds hround
  · exact step1_preserves_decision_defines_value
      hdecval hcorrect hvalue hdecision
  · exact step1_preserves_d2_requires_quorum
      (s := s) (s' := s') (rid := rid)
      hd2 hN hT hcorrect hfaulty hrounds hmsgs1 hmsgs2
  · exact step1_preserves_q2_requires_no_quorum_faster
      (s := s) (s' := s') (rid := rid)
      hq2 hN hT hcorrect hfaulty hrounds hmsgs1 hmsgs2
  · exact step1_preserves_rounds_connection_if
      (s := s) (s' := s') (rid := rid)
      hrounds_conn hcompat hN hT hcorrect hfaulty hrounds hmsgs1 hmsgs2
  · exact step1_preserves_m1_requires_quorum
      (s := s) (s' := s') (rid := rid)
      hm1 hjumps hround_pred hrid hstep_old hN hT hcorrect hfaulty hrounds hmsgs1 hmsgs2
  · exact step1_preserves_value_on_quorum_less_ram
      hvalueQ hN hT hcorrect hfaulty hvalue hround hmsgs2
  · exact step1_preserves_cannot_jump_rounds_without_quorum
      (s := s) (s' := s') (rid := rid)
      hjumps hN hT hcorrect hfaulty hrounds hround hstep hmsgs2
  · exact frame_value_lock
      hvalueLock hN hT hcorrect hfaulty hvalue hround hmsgs2
  · exact step1_preserves_decision_requires_last_quorum_less_ram
      hdecReq hN hT hcorrect hdecision hround hmsgs2

lemma step1_preserves_ind_inv_of_unique_supported {s s' : State} {rid : Int}
    (hmodel : model_assumptions s) (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (hrid : rid ∈ s.CORRECT)
    (hsupported_unique :
      ∀ r ∈ s.ROUNDS, ∀ v ∈ supportedValues s r, ∀ w ∈ supportedValues s r, v = w)
    (hstep1 : step1 rid s s') :
    ind_inv_13 s' := by
  have hinv_parts := hinv
  unfold ind_inv_13 at hinv_parts
  rcases hinv_parts with
    ⟨_, _, _, _, _, _, _, hrounds_conn, _, _, _, hvalue_lock, _⟩
  have hmodel_parts := hmodel
  unfold model_assumptions at hmodel_parts
  rcases hmodel_parts with ⟨_, _, hround_pos, _, _⟩
  exact step1_preserves_ind_inv_if
    (s := s) (s' := s') (rid := rid)
    hmodel htype hinv
    hrid
    (step1_rounds_connection_compat_of_unique_supported
      (s := s) (rid := rid)
      htype hrounds_conn hvalue_lock hrid hround_pos hsupported_unique)
    hstep1

lemma step1_preserves_ind_inv {s s' : State} {rid : Int}
    (hmodel : model_assumptions s) (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (hrid : rid ∈ s.CORRECT)
    (hstep1 : step1 rid s s') :
    ind_inv_13 s' := by
  exact step1_preserves_ind_inv_of_unique_supported
    (s := s) (s' := s') (rid := rid)
    hmodel htype hinv hrid
    (supportedValues_unique_of_ind_inv hmodel hinv)
    hstep1

lemma step2_preserves_ind_inv_if_rounds_connection_and_value_lock
    {s s' : State} {rid : Int}
    (hmodel : model_assumptions s) (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (hrid : rid ∈ s.CORRECT)
    (hrounds_conn' : rounds_connection s')
    (hvalue_lock' : value_lock s')
    (hstep2 : step2 rid s s') :
    ind_inv_13 s' := by
  classical
  unfold model_assumptions at hmodel
  rcases hmodel with ⟨hassumptions, _, _, _, _⟩
  unfold ind_inv_13 at hinv
  unfold ind_inv_13
  rcases hinv with
    ⟨hnoeq1, hnoeq2, hfuture, hroundNeeds, hdecval, hd2, hq2, _hrounds_conn,
      hm1, hvalueQ, hjumps, _hvalueLock, hdecReq⟩
  unfold step2 at hstep2
  rcases hstep2 with
    ⟨⟨hstep_old, _hpowerset_ne, received, hreceived, hreceived_card, hbranch⟩,
      hN, hT, _hF, hcorrect, hfaulty, hrounds, hvalue, hdecision, hround, hmsgs1⟩
  rcases hbranch with hd2branch | hq2branch
  · rcases hd2branch with
      ⟨_values_ne, newValue, _hnewValue_mem, hweight, hmsgs2, hstep, _hghost⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hrounds_conn', ?_, ?_, ?_, hvalue_lock', ?_⟩
    · exact frame_no_equivocation1 hnoeq1 hcorrect hrounds hmsgs1
    · exact step2_d2_preserves_no_equivocation2
        (s := s) (s' := s') (rid := rid) (v := newValue)
        htype hnoeq2 hfuture hrid hstep_old hmsgs2 hcorrect hfaulty hrounds
    · exact step2_d2_preserves_messages_not_from_future
        (s := s) (s' := s') (rid := rid) (v := newValue)
        hfuture hstep_old hmsgs1 hmsgs2 hstep hcorrect hrounds hround
    · exact step2_d2_preserves_round_needs_sent_messages
        (s := s) (s' := s') (rid := rid) (v := newValue)
        hroundNeeds hstep_old hmsgs1 hmsgs2 hstep hcorrect hrounds hround
    · exact step2_preserves_decision_defines_value hdecval hcorrect hvalue hdecision
    · exact step2_d2_preserves_d2_requires_quorum
        (s := s) (s' := s') (rid := rid) (newValue := newValue) (received := received)
        hd2 hreceived hweight hN hT hcorrect hfaulty hrounds hmsgs1 hmsgs2
    · exact step2_d2_preserves_q2_requires_no_quorum_faster
        (s := s) (s' := s') (rid := rid) (v := newValue)
        hq2 hN hT hcorrect hfaulty hrounds hmsgs1 hmsgs2
    · exact step2_preserves_m1_requires_quorum
        (s := s) (s' := s') (rid := rid)
        (newMsg := { kind := Msg2Kind.D2, round := Finmap.lookupD rid s.round, src := rid, value := newValue })
        hm1 hN hT hcorrect hfaulty hrounds hmsgs1 hmsgs2
    · exact step2_preserves_value_on_quorum_less_ram
        (s := s) (s' := s') (rid := rid)
        (newMsg := { kind := Msg2Kind.D2, round := Finmap.lookupD rid s.round, src := rid, value := newValue })
        hvalueQ hN hT hcorrect hfaulty hvalue hround hmsgs2
    · exact step2_preserves_cannot_jump_rounds_without_quorum
        (s := s) (s' := s') (rid := rid)
        (newMsg := { kind := Msg2Kind.D2, round := Finmap.lookupD rid s.round, src := rid, value := newValue })
        hjumps hN hT hcorrect hfaulty hrounds hround hstep hmsgs2
    · exact step2_d2_preserves_decision_requires_last_quorum_less_ram
        (s := s) (s' := s') (rid := rid) (v := newValue)
        hdecReq hN hT hcorrect hdecision hround hmsgs2
  · rcases hq2branch with ⟨hno_quorum, hmsgs2, hstep, _hghost⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hrounds_conn', ?_, ?_, ?_, hvalue_lock', ?_⟩
    · exact frame_no_equivocation1 hnoeq1 hcorrect hrounds hmsgs1
    · exact step2_q2_preserves_no_equivocation2
        (s := s) (s' := s') (rid := rid)
        htype hnoeq2 hfuture hrid hstep_old hmsgs2 hcorrect hfaulty hrounds
    · exact step2_q2_preserves_messages_not_from_future
        (s := s) (s' := s') (rid := rid)
        hfuture hstep_old hmsgs1 hmsgs2 hstep hcorrect hrounds hround
    · exact step2_q2_preserves_round_needs_sent_messages
        (s := s) (s' := s') (rid := rid)
        hroundNeeds hstep_old hmsgs1 hmsgs2 hstep hcorrect hrounds hround
    · exact step2_preserves_decision_defines_value hdecval hcorrect hvalue hdecision
    · exact step2_q2_preserves_d2_requires_quorum
        (s := s) (s' := s') (rid := rid)
        hd2 hN hT hcorrect hfaulty hrounds hmsgs1 hmsgs2
    · exact step2_q2_preserves_q2_requires_no_quorum_faster
        (s := s) (s' := s') (rid := rid) (received := received)
        htype hq2 hrid hreceived hreceived_card hno_quorum (assumptions_N5T hassumptions)
        hN hT hcorrect hfaulty hrounds hmsgs1 hmsgs2
    · exact step2_preserves_m1_requires_quorum
        (s := s) (s' := s') (rid := rid)
        (newMsg := { kind := Msg2Kind.Q2, round := Finmap.lookupD rid s.round, src := rid, value := -2 })
        hm1 hN hT hcorrect hfaulty hrounds hmsgs1 hmsgs2
    · exact step2_preserves_value_on_quorum_less_ram
        (s := s) (s' := s') (rid := rid)
        (newMsg := { kind := Msg2Kind.Q2, round := Finmap.lookupD rid s.round, src := rid, value := -2 })
        hvalueQ hN hT hcorrect hfaulty hvalue hround hmsgs2
    · exact step2_preserves_cannot_jump_rounds_without_quorum
        (s := s) (s' := s') (rid := rid)
        (newMsg := { kind := Msg2Kind.Q2, round := Finmap.lookupD rid s.round, src := rid, value := -2 })
        hjumps hN hT hcorrect hfaulty hrounds hround hstep hmsgs2
    · exact step2_q2_preserves_decision_requires_last_quorum_less_ram
        (s := s) (s' := s') (rid := rid)
        hdecReq hN hT hcorrect hdecision hround hmsgs2

lemma step2_preserves_value_lock_of_step
    {s s' : State} {rid : Int}
    (hmodel : model_assumptions s) (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (_hrid : rid ∈ s.CORRECT)
    (hstep2 : step2 rid s s') :
    value_lock s' := by
  classical
  unfold step2 at hstep2
  rcases hstep2 with
    ⟨⟨_hstep_old, _hpowerset_ne, _received, _hreceived, _hreceived_card, hbranch⟩,
      hN, hT, _hF, hcorrect, hfaulty, _hrounds, hvalue, _hdecision, hround, _hmsgs1⟩
  rcases hbranch with hd2branch | hq2branch
  · rcases hd2branch with
      ⟨_values_ne, newValue, _hnewValue_mem, _hweight, hmsgs2, _hstep, _hghost⟩
    exact value_lock_preserved_of_mono_msgs2
      (s := s) (s' := s') hmodel htype hinv hN hT hcorrect hfaulty hvalue hround
      (by
        intro r m hm
        rw [hmsgs2]
        by_cases hr : r = Finmap.lookupD rid s.round
        · rw [hr, lookupD_insert_self]
          have hm' : m ∈ Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 := by
            simpa [hr] using hm
          exact Finset.mem_union.mpr (Or.inl hm')
        · rw [lookupD_insert_of_ne hr]
          exact hm)
  · rcases hq2branch with ⟨_hno_quorum, hmsgs2, _hstep, _hghost⟩
    exact value_lock_preserved_of_mono_msgs2
      (s := s) (s' := s') hmodel htype hinv hN hT hcorrect hfaulty hvalue hround
      (by
        intro r m hm
        rw [hmsgs2]
        by_cases hr : r = Finmap.lookupD rid s.round
        · rw [hr, lookupD_insert_self]
          have hm' : m ∈ Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 := by
            simpa [hr] using hm
          exact Finset.mem_union.mpr (Or.inl hm')
        · rw [lookupD_insert_of_ne hr]
          exact hm)

lemma step2_preserves_rounds_connection_of_step
    {s s' : State} {rid : Int}
    (hmodel : model_assumptions s) (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (_hrid : rid ∈ s.CORRECT)
    (hstep2 : step2 rid s s') :
    rounds_connection s' := by
  classical
  unfold step2 at hstep2
  rcases hstep2 with
    ⟨⟨_hstep_old, _hpowerset_ne, _received, _hreceived, _hreceived_card, hbranch⟩,
      hN, hT, _hF, hcorrect, hfaulty, hrounds, _hvalue, _hdecision, _hround, hmsgs1⟩
  rcases hbranch with hd2branch | hq2branch
  · rcases hd2branch with
      ⟨_values_ne, newValue, _hnewValue_mem, _hweight, hmsgs2, _hstep, _hghost⟩
    exact rounds_connection_preserved_of_mono_msgs2
      (s := s) (s' := s') hmodel htype hinv hN hT hcorrect hfaulty hrounds
      (by
        intro r hr m hm _hcorrect_m
        rw [hmsgs1] at hm
        exact hm)
      (by
        intro r m hm
        rw [hmsgs2]
        by_cases hrid_round : r = Finmap.lookupD rid s.round
        · rw [hrid_round, lookupD_insert_self]
          have hm' : m ∈ Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 := by
            simpa [hrid_round] using hm
          exact Finset.mem_union.mpr (Or.inl hm')
        · rw [lookupD_insert_of_ne hrid_round]
          exact hm)
  · rcases hq2branch with ⟨_hno_quorum, hmsgs2, _hstep, _hghost⟩
    exact rounds_connection_preserved_of_mono_msgs2
      (s := s) (s' := s') hmodel htype hinv hN hT hcorrect hfaulty hrounds
      (by
        intro r hr m hm _hcorrect_m
        rw [hmsgs1] at hm
        exact hm)
      (by
        intro r m hm
        rw [hmsgs2]
        by_cases hrid_round : r = Finmap.lookupD rid s.round
        · rw [hrid_round, lookupD_insert_self]
          have hm' : m ∈ Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 := by
            simpa [hrid_round] using hm
          exact Finset.mem_union.mpr (Or.inl hm')
        · rw [lookupD_insert_of_ne hrid_round]
          exact hm)

lemma step3_preserves_cannot_jump_rounds_without_quorum_of_step
    {s s' : State} {rid : Int}
    (hjumps : cannot_jump_rounds_without_quorum s)
    (hstep3 : step3 rid s s') :
    cannot_jump_rounds_without_quorum s' := by
  classical
  unfold step3 at hstep3
  rcases hstep3 with
    ⟨hcore, hN, hT, _hF, hcorrect, hfaulty, hrounds, _hmsgs1, hmsgs2⟩
  rcases hcore with ⟨_hstep_old, _hpowerset_ne, hexists⟩
  obtain ⟨hexists_received, hround, htail⟩ := hexists
  obtain ⟨received, hreceived, hreceived_card, _hnext_round, _hbranch⟩ := hexists_received
  have hstep := htail.1
  unfold cannot_jump_rounds_without_quorum at hjumps ⊢
  intro r hr hnext hproc
  rw [hrounds] at hr hnext
  rcases hproc with ⟨id, hid, hround_id, hstep_id⟩
  rw [hcorrect] at hid
  by_cases hsrc : id = rid
  · subst id
    rw [hround, lookupD_insert_self] at hround_id
    rw [hstep, lookupD_insert_self] at hstep_id
    have hr_eq : r = Finmap.lookupD rid s.round := by
      omega
    rw [hN, hT, hmsgs2, hr_eq]
    have hreceived_sub : received ⊆ Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2 :=
      Finset.mem_powerset.mp hreceived
    have hsub :
        senders2 s received ⊆
          senders2 s' (Finmap.lookupD (Finmap.lookupD rid s.round) s.msgs2) :=
      senders2_mono_frame (s := s) (s' := s') hcorrect hfaulty hreceived_sub
    have hcard := Finset.card_le_card hsub
    have hreceived_card_senders :
        (Finset.card (senders2 s received) : Int) = s.N - s.T := by
      rw [senders2_eq_generated]
      exact hreceived_card
    omega
  · have hsrc_ne : id ≠ rid := hsrc
    rw [hround, lookupD_insert_of_ne hsrc_ne] at hround_id
    rw [hstep, lookupD_insert_of_ne hsrc_ne] at hstep_id
    have hold := hjumps r hr hnext ⟨id, hid, hround_id, hstep_id⟩
    rw [hN, hT, hmsgs2]
    unfold senders2 allReplicas
    rw [hcorrect, hfaulty]
    exact hold

lemma step3_preserves_value_lock_of_step
    {s s' : State} {rid : Int}
    (hmodel : model_assumptions s) (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (hrid : rid ∈ s.CORRECT)
    (hstep3 : step3 rid s s') :
    value_lock s' := by
  classical
  have hmodel_parts := hmodel
  unfold model_assumptions at hmodel_parts
  rcases hmodel_parts with ⟨_, _, hround_pos, _, _⟩
  have hinv_parts := hinv
  unfold ind_inv_13 at hinv_parts
  rcases hinv_parts with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hvalueLock, _⟩
  have hr_current : Finmap.lookupD rid s.round ∈ s.ROUNDS := by
    unfold type_ok at htype
    exact htype.2.2.1.2 rid hrid
  have hround_old_pos : 1 ≤ Finmap.lookupD rid s.round :=
    hround_pos (Finmap.lookupD rid s.round) hr_current
  unfold step3 at hstep3
  rcases hstep3 with
    ⟨hcore, hN, hT, _hF, hcorrect, hfaulty, _hrounds, _hmsgs1, hmsgs2⟩
  rcases hcore with ⟨_hstep_old, _hpowerset_ne, hexists⟩
  obtain ⟨hexists_received, hround, _htail⟩ := hexists
  obtain ⟨received, hreceived, hreceived_card, _hnext_round, hbranch⟩ := hexists_received
  rcases hbranch with hvalue_branch | hrandom_branch
  · rcases hvalue_branch with
      ⟨_values_ne, newValue, hnewValue_mem, hd2_received, hvalue, _hdecision_cases⟩
    exact step3_value_update_preserves_value_lock_if
      (s := s) (s' := s') (rid := rid) (newValue := newValue)
      hvalueLock
      (generated_step3_value_supported_or_empty
        (s := s) (r := Finmap.lookupD rid s.round) (v := newValue)
        (received := received)
        hmodel hinv hr_current hnewValue_mem hreceived hd2_received)
      hround_old_pos hN hT hcorrect hfaulty hvalue hround hmsgs2
  · rcases hrandom_branch with
      ⟨_values_ne, hnext, _hdecision⟩
    rcases hnext with ⟨newValue, hnewValue_mem, hno_value, hvalue⟩
    exact step3_value_update_preserves_value_lock_if
      (s := s) (s' := s') (rid := rid) (newValue := newValue)
      hvalueLock
      (Or.inl
        (generated_step3_random_supported_empty
          (s := s) (r := Finmap.lookupD rid s.round) (received := received)
          htype hr_current hreceived hreceived_card hno_value))
      hround_old_pos hN hT hcorrect hfaulty hvalue hround hmsgs2

lemma step3_preserves_value_on_quorum_less_ram_of_step
    {s s' : State} {rid : Int}
    (hmodel : model_assumptions s) (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (hrid : rid ∈ s.CORRECT)
    (hstep3 : step3 rid s s') :
    value_on_quorum_less_ram s' := by
  classical
  have hmodel_parts := hmodel
  unfold model_assumptions at hmodel_parts
  rcases hmodel_parts with ⟨_, _, _, _, _⟩
  have hinv_parts := hinv
  unfold ind_inv_13 at hinv_parts
  rcases hinv_parts with
    ⟨_, _, _, _, _, _, _, _, _, hvalueQ, _, _, _⟩
  have hr_current : Finmap.lookupD rid s.round ∈ s.ROUNDS := by
    unfold type_ok at htype
    exact htype.2.2.1.2 rid hrid
  unfold step3 at hstep3
  rcases hstep3 with
    ⟨hcore, hN, hT, _hF, hcorrect, hfaulty, _hrounds, _hmsgs1, hmsgs2⟩
  rcases hcore with ⟨_hstep_old, _hpowerset_ne, hexists⟩
  obtain ⟨hexists_received, hround, htail⟩ := hexists
  obtain ⟨received, hreceived, hreceived_card, _hnext_round, hbranch⟩ := hexists_received
  have hstep := htail.1
  unfold value_on_quorum_less_ram at hvalueQ ⊢
  intro id hid
  rw [hcorrect] at hid
  dsimp
  intro hgt
  have frame_other
      {newValue : Int}
      (hvalue : s'.value = Finmap.insert rid newValue s.value)
      (hsrc : id ≠ rid) :
      (2 *
            ↑(Finset.card
              (senders2 s'
                (d2MsgsFor (Finmap.lookupD id s'.value)
                  (Finmap.lookupD (Finmap.lookupD id s'.round - 1) s'.msgs2)))) >
          s'.N + s'.T) ∨
        (let prevMsgs := Finmap.lookupD (Finmap.lookupD id s'.round - 1) s'.msgs2
         let n0 := Finset.card (d2MsgsFor 0 prevMsgs)
         let n1 := Finset.card (d2MsgsFor 1 prevMsgs)
         let nq := Finset.card (q2Msgs prevMsgs)
         ∃ x0 ∈ Finset.Icc 0 s'.N,
           ∃ x1 ∈ Finset.Icc 0 s'.N,
             x0 ≤ n0 ∧ x1 ≤ n1 ∧ x0 + x1 + nq ≥ s'.N - s'.T ∧
               2 * x0 ≤ s'.N + s'.T ∧ 2 * x1 ≤ s'.N + s'.T) := by
    have hgt_old : Finmap.lookupD id s.round > 1 := by
      rw [hround, lookupD_insert_of_ne hsrc] at hgt
      exact hgt
    have hold := hvalueQ id hid hgt_old
    rw [hN, hT, hround, lookupD_insert_of_ne hsrc, hvalue,
      lookupD_insert_of_ne hsrc, hmsgs2]
    simpa [senders2, allReplicas, hcorrect, hfaulty] using hold
  by_cases hsrc : id = rid
  · subst id
    rw [hround, lookupD_insert_self] at hgt
    rcases hbranch with hvalue_branch | hrandom_branch
    · rcases hvalue_branch with
        ⟨_values_ne, newValue, hnewValue_mem, hd2_received, hvalue, hdecision_cases⟩
      rw [hN, hT, hround, hvalue, lookupD_insert_self, lookupD_insert_self, hmsgs2]
      have hprev : Finmap.lookupD rid s.round + 1 - 1 = Finmap.lookupD rid s.round := by
        omega
      rw [hprev]
      rcases hdecision_cases with hdecide | hkeep
      · left
        have hfast := generated_step3_fast_value_quorum
          (s := s) (r := Finmap.lookupD rid s.round) (v := newValue)
          (received := received) hreceived hdecide.1
        simpa [senders2, allReplicas, hcorrect, hfaulty] using hfast
      · right
        exact generated_step3_no_fast_slow_value_quorum
          (s := s) (r := Finmap.lookupD rid s.round) (received := received)
          htype hr_current hreceived hreceived_card
          (generated_step3_no_other_fast_value
            (s := s) (r := Finmap.lookupD rid s.round) (v := newValue)
            (received := received)
            (model_base_of_model hmodel) hinv hr_current hreceived hnewValue_mem hd2_received hkeep.1)
          (model_N5T hmodel)
    · rcases hrandom_branch with
        ⟨_values_ne, hnext, _hdecision⟩
      rcases hnext with ⟨newValue, _hnewValue_mem, hno_value, hvalue⟩
      rw [hN, hT, hround, hvalue, lookupD_insert_self, lookupD_insert_self, hmsgs2]
      have hprev : Finmap.lookupD rid s.round + 1 - 1 = Finmap.lookupD rid s.round := by
        omega
      rw [hprev]
      right
      exact generated_step3_random_slow_value_quorum
        (s := s) (r := Finmap.lookupD rid s.round) (received := received)
        htype hr_current hreceived hreceived_card hno_value (model_N5T hmodel)
  · rcases hbranch with hvalue_branch | hrandom_branch
    · rcases hvalue_branch with
        ⟨_values_ne, newValue, _hnewValue_mem, _hd2_received, hvalue, _hdecision_cases⟩
      exact frame_other hvalue hsrc
    · rcases hrandom_branch with
        ⟨_values_ne, hnext, _hdecision⟩
      rcases hnext with ⟨newValue, _hnewValue_mem, _hno_value, hvalue⟩
      exact frame_other hvalue hsrc

lemma step3_preserves_decision_defines_value_of_step
    {s s' : State} {rid : Int}
    (hmodel : model_assumptions s) (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (hrid : rid ∈ s.CORRECT)
    (hstep3 : step3 rid s s') :
    decision_defines_value s' := by
  classical
  have hbottom := step3_local_decision_bottom_of_ind_inv (model_base_of_model hmodel) htype hinv
  have hinv_parts := hinv
  unfold ind_inv_13 at hinv_parts
  rcases hinv_parts with
    ⟨_, _, _, _, hdecval, _, _, _, _, _, _, _, _⟩
  unfold step3 at hstep3
  rcases hstep3 with
    ⟨hcore, _hN, _hT, _hF, hcorrect, _hfaulty, _hrounds, _hmsgs1, _hmsgs2⟩
  rcases hcore with ⟨hstep_old, _hpowerset_ne, hexists⟩
  obtain ⟨hexists_received, _hround, _htail⟩ := hexists
  obtain ⟨received, hreceived, hreceived_card, _hnext_round, hbranch⟩ := hexists_received
  have hbottom_received := hbottom rid hrid hstep_old received hreceived hreceived_card
  rcases hbranch with hvalue_branch | hrandom_branch
  · rcases hvalue_branch with
      ⟨_values_ne, newValue, hnewValue_mem, hd2_received, hvalue, hdecision_cases⟩
    rcases hdecision_cases with hdecide | hkeep
    · exact step3_decide_preserves_decision_defines_value
        (s := s) (s' := s') (rid := rid) (v := newValue)
        hdecval hvalue hdecide.2 hcorrect
    · exact step3_value_update_preserves_decision_defines_value_if
        (s := s) (s' := s') (rid := rid) (v := newValue)
        hdecval
        (Or.inl
          (hbottom_received.2 newValue hnewValue_mem hd2_received hkeep.1))
        hvalue hkeep.2 hcorrect
  · rcases hrandom_branch with
      ⟨_values_ne, hnext, hdecision⟩
    rcases hnext with ⟨newValue, _hnewValue_mem, hno_value, hvalue⟩
    exact step3_value_update_preserves_decision_defines_value_if
      (s := s) (s' := s') (rid := rid) (v := newValue)
      hdecval
      (Or.inl (hbottom_received.1 hno_value))
      hvalue hdecision hcorrect

lemma step3_preserves_decision_requires_last_quorum_less_ram_of_step
    {s s' : State} {rid : Int}
    (hmodel : model_assumptions s) (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (hrid : rid ∈ s.CORRECT)
    (hstep3 : step3 rid s s') :
    decision_requires_last_quorum_less_ram s' := by
  classical
  have hmodel_parts := hmodel
  unfold model_assumptions at hmodel_parts
  rcases hmodel_parts with ⟨_, _, hround_pos, _, _⟩
  have hbottom := step3_local_decision_bottom_of_ind_inv (model_base_of_model hmodel) htype hinv
  have hinv_parts := hinv
  unfold ind_inv_13 at hinv_parts
  rcases hinv_parts with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hdecReq⟩
  have hr_current : Finmap.lookupD rid s.round ∈ s.ROUNDS := by
    unfold type_ok at htype
    exact htype.2.2.1.2 rid hrid
  have hround_old_pos : 1 ≤ Finmap.lookupD rid s.round :=
    hround_pos (Finmap.lookupD rid s.round) hr_current
  unfold step3 at hstep3
  rcases hstep3 with
    ⟨hcore, hN, hT, _hF, hcorrect, _hfaulty, _hrounds, _hmsgs1, hmsgs2⟩
  rcases hcore with ⟨hstep_old, _hpowerset_ne, hexists⟩
  obtain ⟨hexists_received, hround, htail⟩ := hexists
  obtain ⟨received, hreceived, hreceived_card, _hnext_round, hbranch⟩ := hexists_received
  have hbottom_received := hbottom rid hrid hstep_old received hreceived hreceived_card
  rcases hbranch with hvalue_branch | hrandom_branch
  · rcases hvalue_branch with
      ⟨_values_ne, newValue, hnewValue_mem, hd2_received, _hvalue, hdecision_cases⟩
    rcases hdecision_cases with hdecide | hkeep
    · exact step3_decide_preserves_decision_requires_last_quorum_less_ram_of_generated
        (s := s) (s' := s') (rid := rid) (v := newValue) (received := received)
        hdecReq hround_old_pos hreceived hreceived_card hd2_received hdecide.1
        hN hT hcorrect hdecide.2 hround hmsgs2
    · exact step3_no_decision_preserves_decision_requires_last_quorum_less_ram
        (s := s) (s' := s') (rid := rid)
        hdecReq hround_old_pos hN hT hcorrect hkeep.2 hround hmsgs2
        (Or.inl
          (hbottom_received.2 newValue hnewValue_mem hd2_received hkeep.1))
  · rcases hrandom_branch with
      ⟨_values_ne, hnext, hdecision⟩
    rcases hnext with ⟨_newValue, _hnewValue_mem, hno_value, _hvalue⟩
    exact step3_no_decision_preserves_decision_requires_last_quorum_less_ram
      (s := s) (s' := s') (rid := rid)
      hdecReq hround_old_pos hN hT hcorrect hdecision hround hmsgs2
      (Or.inl (hbottom_received.1 hno_value))

/-- `step3` preservation of the 13 core lemmas: produces `ind_inv_13 s'` and so
needs no agreement/lock predicate at the post-state.  This is what lets the
inductive step run entirely on the 13 Apalache lemmas — agreement is recovered
separately as a single-state fact (`agreement_inv_of_ind_inv_13`). -/
lemma step3_preserves_ind_inv_13_if_frontier
    {s s' : State} {rid : Int}
    (hinv : ind_inv_13 s)
    (hdecval' : decision_defines_value s')
    (hvalueQ' : value_on_quorum_less_ram s')
    (hjumps' : cannot_jump_rounds_without_quorum s')
    (hvalueLock' : value_lock s')
    (hdecReq' : decision_requires_last_quorum_less_ram s')
    (hstep3 : step3 rid s s') :
    ind_inv_13 s' := by
  classical
  unfold ind_inv_13 at hinv
  unfold ind_inv_13
  rcases hinv with
    ⟨hnoeq1, hnoeq2, hfuture, hroundNeeds, _hdecval, hd2, hq2, hrounds_conn,
      hm1, _hvalueQ, _hjumps, _hvalueLock, _hdecReq⟩
  unfold step3 at hstep3
  rcases hstep3 with
    ⟨hcore, hN, hT, _hF, hcorrect, hfaulty, hrounds, hmsgs1, hmsgs2⟩
  rcases hcore with ⟨hstep_old, _hpowerset_ne, hexists⟩
  obtain ⟨_hexists_received, hround, htail⟩ := hexists
  have hstep := htail.1
  refine ⟨?_, ?_, ?_, ?_, hdecval', ?_, ?_, ?_, ?_, hvalueQ', hjumps', hvalueLock', hdecReq'⟩
  · exact frame_no_equivocation1 hnoeq1 hcorrect hrounds hmsgs1
  · exact frame_no_equivocation2 hnoeq2 hcorrect hfaulty hrounds hmsgs2
  · exact step3_preserves_messages_not_from_future
      (s := s) (s' := s') (rid := rid)
      hfuture hstep_old hmsgs1 hmsgs2 hstep hcorrect hrounds hround
  · exact step3_preserves_round_needs_sent_messages
      (s := s) (s' := s') (rid := rid)
      hroundNeeds hstep_old hmsgs1 hmsgs2 hstep hcorrect hrounds hround
  · exact step3_preserves_d2_requires_quorum
      hd2 hN hT hcorrect hfaulty hrounds hmsgs1 hmsgs2
  · exact step3_preserves_q2_requires_no_quorum_faster
      hq2 hN hT hcorrect hfaulty hrounds hmsgs1 hmsgs2
  · exact step3_preserves_rounds_connection
      hrounds_conn hN hT hcorrect hfaulty hrounds hmsgs1 hmsgs2
  · exact step3_preserves_m1_requires_quorum
      hm1 hN hT hcorrect hfaulty hrounds hmsgs1 hmsgs2

lemma faulty_step_preserves_m1_requires_quorum
    {s s' : State} {r_faulty : Int} {f1 : Finset Msg1} {f2d f2q : Finset Msg2}
    (hdisj : s.CORRECT ∩ s.FAULTY = ∅)
    (hm1 : m1_requires_quorum s)
    (hf1 :
      f1 ∈
        Finset.powerset
          (Finset.image (fun x => Msg1.mk r_faulty (x).1 (x).2)
            (Finset.product s.FAULTY (insert 0 (insert 1 (∅ : Finset Int))))))
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hmsgs1 : s'.msgs1 = Finmap.insert r_faulty (Finmap.lookupD r_faulty s.msgs1 ∪ f1) s.msgs1)
    (hmsgs2 : s'.msgs2 =
      Finmap.insert r_faulty (Finmap.lookupD r_faulty s.msgs2 ∪ (f2d ∪ f2q)) s.msgs2) :
    m1_requires_quorum s' := by
  classical
  unfold m1_requires_quorum at hm1 ⊢
  intro r hr hne hm
  rw [hrounds] at hr
  rcases hm with ⟨m, hm, hcorrect_m⟩
  rw [hcorrect] at hcorrect_m
  rw [hmsgs1] at hm
  have hsub_msgs2 :
      Finmap.lookupD (r - 1) s.msgs2 ⊆ Finmap.lookupD (r - 1) s'.msgs2 := by
    intro msg hmsg
    rw [hmsgs2]
    by_cases hr_faulty : r - 1 = r_faulty
    · rw [hr_faulty, lookupD_insert_self]
      have hmsg' : msg ∈ Finmap.lookupD r_faulty s.msgs2 := by
        rwa [hr_faulty] at hmsg
      exact Finset.mem_union.mpr (Or.inl hmsg')
    · rw [lookupD_insert_of_ne hr_faulty]
      exact hmsg
  have hlift (hold : Finset.card (senders2 s (Finmap.lookupD (r - 1) s.msgs2)) ≥ s.N - s.T) :
      Finset.card (senders2 s' (Finmap.lookupD (r - 1) s'.msgs2)) ≥ s'.N - s'.T := by
    have hsub :=
      senders2_mono_frame (s := s) (s' := s')
        hcorrect hfaulty hsub_msgs2
    have hcard := Finset.card_le_card hsub
    rw [hN, hT]
    omega
  by_cases hr_faulty : r = r_faulty
  · subst r
    simp [lookupD_insert_self] at hm
    rcases hm with hmold | hmfaulty
    · exact hlift (hm1 r_faulty hr hne ⟨m, hmold, hcorrect_m⟩)
    · have hnot := msg1_src_not_correct_of_mem_faulty_step (s := s) hdisj hf1 hmfaulty
      exact False.elim (hnot hcorrect_m)
  · rw [lookupD_insert_of_ne hr_faulty] at hm
    exact hlift (hm1 r hr hne ⟨m, hm, hcorrect_m⟩)

lemma faulty_step_preserves_cannot_jump_rounds_without_quorum
    {s s' : State} {r_faulty : Int} {f2d f2q : Finset Msg2}
    (hjumps : cannot_jump_rounds_without_quorum s)
    (hN : s'.N = s.N)
    (hT : s'.T = s.T)
    (hcorrect : s'.CORRECT = s.CORRECT)
    (hfaulty : s'.FAULTY = s.FAULTY)
    (hrounds : s'.ROUNDS = s.ROUNDS)
    (hround : s'.round = s.round)
    (hstep : s'.step = s.step)
    (hmsgs2 :
      s'.msgs2 =
        Finmap.insert r_faulty (Finmap.lookupD r_faulty s.msgs2 ∪ (f2d ∪ f2q)) s.msgs2) :
    cannot_jump_rounds_without_quorum s' := by
  classical
  unfold cannot_jump_rounds_without_quorum at hjumps ⊢
  intro r hr hnext hproc
  rw [hrounds] at hr hnext
  rcases hproc with ⟨id, hid, hround_id, hstep_id⟩
  rw [hcorrect] at hid
  rw [hround] at hround_id
  rw [hstep] at hstep_id
  have hold := hjumps r hr hnext ⟨id, hid, hround_id, hstep_id⟩
  have hsub :
      senders2 s (Finmap.lookupD r s.msgs2) ⊆
        senders2 s' (Finmap.lookupD r s'.msgs2) := by
    apply senders2_mono_frame (s := s) (s' := s') hcorrect hfaulty
    rw [hmsgs2]
    by_cases hr_faulty : r = r_faulty
    · subst r
      intro m hm
      simp [lookupD_insert_self, hm]
    · intro m hm
      rw [lookupD_insert_of_ne hr_faulty]
      exact hm
  have hcard := Finset.card_le_card hsub
  rw [hN, hT]
  omega

lemma faulty_step_preserves_value_lock_of_step
    {s s' : State}
    (hmodel : model_assumptions s)
    (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (hfaulty_step : faulty_step s s') :
    value_lock s' := by
  classical
  unfold faulty_step at hfaulty_step
  rcases hfaulty_step with
    ⟨_hne_rounds,
      ⟨r_faulty, _hr_faulty, _hpow1_ne, _f1, _hf1, _hpow2d_ne, _f2d, _hf2d_ne,
        _hpow2q_ne, _f2q, _hf2q_ne, _hmsgs1, hmsgs2, _hghost⟩,
      hN, hT, _hF, hcorrect, hfaulty, _hrounds, hvalue, _hdecision, hround, _hstep⟩
  -- faulty steps only add messages, so msgs2 grows monotonically; reuse the
  -- shared value_lock-under-monotone-msgs2 lemma (as step2 does).
  exact value_lock_preserved_of_mono_msgs2
    (s := s) (s' := s') hmodel htype hinv hN hT hcorrect hfaulty hvalue hround
    (by
      intro r m hm
      rw [hmsgs2]
      by_cases hr_faulty : r = r_faulty
      · rw [hr_faulty, lookupD_insert_self]
        have hm' : m ∈ Finmap.lookupD r_faulty s.msgs2 := by
          simpa [hr_faulty] using hm
        exact Finset.mem_union.mpr (Or.inl hm')
      · rw [lookupD_insert_of_ne hr_faulty]
        exact hm)

lemma faulty_step_preserves_rounds_connection_of_step
    {s s' : State}
    (hmodel : model_assumptions s)
    (htype : type_ok s)
    (hinv : ind_inv_13 s)
    (hfaulty_step : faulty_step s s') :
    rounds_connection s' := by
  classical
  have hmodel_parts := hmodel
  unfold model_assumptions at hmodel_parts
  rcases hmodel_parts with ⟨_, hdisj, _, _, _⟩
  unfold faulty_step at hfaulty_step
  rcases hfaulty_step with
    ⟨_hne_rounds,
      ⟨r_faulty, _hr_faulty, _hpow1_ne, f1, hf1, _hpow2d_ne, _f2d, _hf2d_ne,
        _hpow2q_ne, _f2q, _hf2q_ne, hmsgs1, hmsgs2, _hghost⟩,
      hN, hT, _hF, hcorrect, hfaulty, hrounds, _hvalue, _hdecision, _hround, _hstep⟩
  exact rounds_connection_preserved_of_mono_msgs2
    (s := s) (s' := s') hmodel htype hinv hN hT hcorrect hfaulty hrounds
    (by
      intro r hr m hm hcorrect_m'
      have hcorrect_m : m.src ∈ s.CORRECT := by
        rw [hcorrect] at hcorrect_m'
        exact hcorrect_m'
      rw [hmsgs1] at hm
      by_cases hr_faulty : r = r_faulty
      · rw [hr_faulty] at hm
        simp [lookupD_insert_self] at hm
        rcases hm with hmold | hmfaulty
        · simpa [hr_faulty] using hmold
        · have hnot := msg1_src_not_correct_of_mem_faulty_step (s := s) hdisj hf1 hmfaulty
          exact False.elim (hnot hcorrect_m)
      · rw [lookupD_insert_of_ne hr_faulty] at hm
        exact hm)
    (by
      intro r m hm
      rw [hmsgs2]
      by_cases hr_faulty : r = r_faulty
      · rw [hr_faulty, lookupD_insert_self]
        have hm' : m ∈ Finmap.lookupD r_faulty s.msgs2 := by
          simpa [hr_faulty] using hm
        exact Finset.mem_union.mpr (Or.inl hm')
      · rw [lookupD_insert_of_ne hr_faulty]
        exact hm)

lemma faulty_step_preserves_ind_inv_if_rounds_connection_and_value_lock
    {s s' : State}
    (hmodel : model_assumptions s)
    (hinv : ind_inv_13 s)
    (hrounds_conn' : rounds_connection s')
    (hvalue_lock' : value_lock s')
    (hfaulty_step : faulty_step s s') :
    ind_inv_13 s' := by
  classical
  unfold model_assumptions at hmodel
  rcases hmodel with ⟨_, hdisj, _, _, _⟩
  unfold ind_inv_13 at hinv
  unfold ind_inv_13
  rcases hinv with
    ⟨hnoeq1, hnoeq2, hfuture, hroundNeeds, hdecval, hd2, hq2, _hrounds_conn,
      hm1, hvalueQ, hjumps, _hvalueLock, hdecReq⟩
  unfold faulty_step at hfaulty_step
  rcases hfaulty_step with
    ⟨_hne_rounds,
      ⟨_r_faulty, _hr_faulty, _hpow1_ne, f1, hf1, _hpow2d_ne, f2d, hf2d, _hpow2q_ne,
        f2q, hf2q, hmsgs1, hmsgs2, _hghost⟩,
      hN, hT, _hF, hcorrect, hfaulty, hrounds, hvalue, hdecision, hround, hstep⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hrounds_conn', ?_, ?_, ?_, hvalue_lock', ?_⟩
  · exact faulty_step_preserves_no_equivocation1
      hdisj hnoeq1 hf1 hmsgs1 hcorrect hrounds
  · exact faulty_step_preserves_no_equivocation2
      hdisj hnoeq2 hf2d hf2q hmsgs2 hcorrect hfaulty hrounds
  · exact faulty_step_preserves_messages_not_from_future
      hdisj hfuture hf1 hf2d hf2q hmsgs1 hmsgs2 hstep hcorrect hrounds hround
  · exact faulty_step_preserves_round_needs_sent_messages
      hroundNeeds hmsgs1 hmsgs2 hstep hcorrect hrounds hround
  · exact faulty_step_preserves_decision_defines_value
      hdecval hcorrect hvalue hdecision
  · exact faulty_step_preserves_d2_requires_quorum
      hdisj hd2 hf2d hf2q hN hT hcorrect hfaulty hrounds hmsgs1 hmsgs2
  · exact faulty_step_preserves_q2_requires_no_quorum_faster
      hdisj hq2 hf2d hf2q hN hT hcorrect hfaulty hrounds hmsgs1 hmsgs2
  · exact faulty_step_preserves_m1_requires_quorum
      hdisj hm1 hf1 hN hT hcorrect hfaulty hrounds hmsgs1 hmsgs2
  · exact faulty_step_preserves_value_on_quorum_less_ram
      hvalueQ hN hT hcorrect hfaulty hvalue hround hmsgs2
  · exact faulty_step_preserves_cannot_jump_rounds_without_quorum
      hjumps hN hT hcorrect hfaulty hrounds hround hstep hmsgs2
  · exact faulty_step_preserves_decision_requires_last_quorum_less_ram
      hdecReq hN hT hcorrect hdecision hround hmsgs2

/-- ## KEY THEOREM 2 of 3 — the non-circular inductive step.

The genuine inductive step on the 13 Apalache lemmas: `ind_inv_13 s` and
`Next s s'` give `ind_inv_13 s'`, with no lock hypotheses at either state.

Every per-action lemma consumes and produces only `ind_inv_13`; the step3 branch
uses the 13-producing `step3_preserves_ind_inv_13_if_frontier`.  No lock predicate
(agreement, `decision_quorum_lock`, `step3_decision_compatibility`, …) is ever
mentioned at either state — which is what removes the circular lock hypotheses. -/
theorem next_preserves_ind_inv_13 {s s' : State}
    (hmodel : model_assumptions s) (htype : type_ok s)
    (h13 : ind_inv_13 s) (hn : Next s s') :
    ind_inv_13 s' := by
  unfold Next step at hn
  rcases hn with hcorrect_step | hfaulty
  · rcases hcorrect_step with ⟨_, rid, hrid, hact⟩
    rcases hact with hstep1 | hstep23
    · exact step1_preserves_ind_inv
        (s := s) (s' := s') (rid := rid)
        hmodel htype h13 hrid hstep1
    · rcases hstep23 with hstep2 | hstep3
      · exact step2_preserves_ind_inv_if_rounds_connection_and_value_lock
          (s := s) (s' := s') (rid := rid)
          hmodel htype h13 hrid
          (step2_preserves_rounds_connection_of_step
            (s := s) (s' := s') (rid := rid)
            hmodel htype h13 hrid hstep2)
          (step2_preserves_value_lock_of_step
            (s := s) (s' := s') (rid := rid)
            hmodel htype h13 hrid hstep2)
          hstep2
      · exact step3_preserves_ind_inv_13_if_frontier
          (s := s) (s' := s') (rid := rid)
          h13
          (step3_preserves_decision_defines_value_of_step
            (s := s) (s' := s') (rid := rid)
            hmodel htype h13 hrid hstep3)
          (step3_preserves_value_on_quorum_less_ram_of_step
            (s := s) (s' := s') (rid := rid)
            hmodel htype h13 hrid hstep3)
          (step3_preserves_cannot_jump_rounds_without_quorum_of_step
            (s := s) (s' := s') (rid := rid)
            (by
              unfold ind_inv_13 at h13
              exact h13.2.2.2.2.2.2.2.2.2.2.1)
            hstep3)
          (step3_preserves_value_lock_of_step
            (s := s) (s' := s') (rid := rid)
            hmodel htype h13 hrid hstep3)
          (step3_preserves_decision_requires_last_quorum_less_ram_of_step
            (s := s) (s' := s') (rid := rid)
            hmodel htype h13 hrid hstep3)
          hstep3
  · exact faulty_step_preserves_ind_inv_if_rounds_connection_and_value_lock
      (s := s) (s' := s')
      hmodel h13
      (faulty_step_preserves_rounds_connection_of_step
        (s := s) (s' := s') hmodel htype h13 hfaulty)
      (faulty_step_preserves_value_lock_of_step
        (s := s) (s' := s') hmodel htype h13 hfaulty)
      hfaulty

/-- ## KEY THEOREM 3 of 3 — the final safety result.

**Agreement holds in every reachable state.**  For any execution `tr` satisfying
the standing assumptions (`model_assumptions`, `type_ok` at each state, a valid
initial state, and `Next`-steps), every state satisfies `agreement_inv`.

The signature carries only the legitimate standing assumptions — the two circular
lock hypotheses of the original (cheating) statement are gone.  The proof inducts
on `ind_inv_13` via KEY THEOREM 2 (`next_preserves_ind_inv_13`) and concludes
agreement at each state via KEY THEOREM 1 (`agreement_inv_of_ind_inv_13`).
`#print axioms` is `[propext, Classical.choice, Quot.sound]`. -/
theorem agreement_inv_invariant {tr : Nat → State}
    (hmodel : ∀ i, model_assumptions (tr i))
    (htype : ∀ i, type_ok (tr i))
    (hinit : init_with_faults (tr 0))
    (hnext : ∀ i, Next (tr i) (tr (i + 1))) :
    ∀ i, agreement_inv (tr i) := by
  -- The 13 Apalache-verified core lemmas are inductive on their own (no locks).
  have h13 : ∀ i, ind_inv_13 (tr i) := by
    intro i
    induction i with
    | zero => exact init_with_faults_ind_inv (hmodel 0) (htype 0) hinit
    | succ n ih => exact next_preserves_ind_inv_13 (hmodel n) (htype n) ih (hnext n)
  -- Agreement at each reachable state is a single-state consequence of the 13
  -- core lemmas (`agreement_inv_of_ind_inv_13`, KEY THEOREM 1).
  intro i
  exact agreement_inv_of_ind_inv_13 (model_base_of_model (hmodel i)) (htype i) (h13 i)

end ben_or
