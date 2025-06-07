/-
Proving the properties of the eventually perfect failure detector.

Copyright (c) 2025 Igor Konnov
Released under MIT license as described in the file LICENSE.
Authors: Igor Konnov, 2025
-/

import Epfd.Propositional
import Epfd.TemporalLemmas

import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Insert

-- The abstract type of processes
variable {Proc : Type} [Fintype Proc] [DecidableEq Proc] [Hashable Proc]

-- The initial delay Δ used by the processes
variable (InitDelay: ℕ)

-- The global stabilization time GST, unknown to the processes
variable (GST: ℕ)

-- The message delay after GST, unknown to the processes
variable (MsgDelay: ℕ)

/-- A process `p` never crashes, i.e., `[](p ∉ crashed)`.  -/
def never_crashes (tr: Trace Proc) (p: Proc): Prop :=
  ∀ i: ℕ,
    p ∉ (tr i).s.crashed

/-- A process `p` never crashes, i.e., `[](p ∈ crashed)`.  -/
def eventually_crashes (tr: Trace Proc) (p: Proc): Prop :=
  ∃ i: ℕ,
    p ∈ (tr i).s.crashed

/--
  Eventually, `p` never registers `q` as alive, i.e., `<>[](q ∉ alive[p])`.
  -/
def eventually_never_alive (tr: Trace Proc) (p q: Proc): Prop :=
  ∃ i: ℕ, ∀ k: ℕ,
    q ∉ (tr (i + k)).s.alive[p]!

/--
  `p` suspects `q` permanently from some point `k`, i.e.,
  `tr[k,...] ⊧ [](q ∈ suspected[p])`.
  -/
def q_is_always_suspected (tr: Trace Proc) (p q: Proc) (i: ℕ): Prop :=
  ∀ k: ℕ,
    q ∈ (tr (i + k)).s.suspected[p]!

/--
  Eventually, `p` suspects `q` permanently, i.e., `<>[](q ∈ suspected[p])`.
  -/
def eventually_q_is_always_suspected (tr: Trace Proc) (p q: Proc): Prop :=
  ∃ i: ℕ,
    q_is_always_suspected tr p q i

/--
  A set of processes `C` is a crashing set if every process in `C`
  eventually crashes, and every process not in `C` never crashes.
 -/
def is_crashing_set (tr: Trace Proc) (C: Finset Proc): Prop :=
  ∀ p: Proc, p ∈ C ↔ eventually_crashes tr p

/--
  An inductive proof schema to show that a state property `P` holds for all states
  in a fair run. We use this lemma to avoid repetitive proofs by induction.
  Surprisingly, we needed this lemma only once so far.
  -/
lemma inductive_inv
    {P: ProtocolState Proc → Prop}
    (tr: Trace Proc)
    (h_is_fair_run: is_fair_run Proc InitDelay GST MsgDelay tr)
    (h_init_P: (s: ProtocolState Proc) → (h_init: init Proc InitDelay s s.all.toList) → P s)
    (h_step_P:
      (s: ProtocolState Proc) → (s': ProtocolState Proc) → (a: Action Proc)
        → (h_s: P s) → (h_next: (next_a Proc InitDelay GST MsgDelay s s' a)) → P s'):
      ∀ i: ℕ,
        P (tr i).s := by
  unfold is_fair_run at h_is_fair_run
  rcases h_is_fair_run with ⟨ h_is_run, _, _, _ ⟩
  unfold is_run at h_is_run
  simp at h_is_run
  rcases h_is_run with ⟨ h_init, h_is_path ⟩
  intro i
  induction i with
  | zero =>
    specialize h_init_P (tr 0).s
    simp [h_init] at h_init_P
    exact h_init_P

  | succ i ih =>
    unfold is_path at h_is_path
    specialize h_is_path i
    specialize h_step_P (tr i).s (tr (i + 1)).s (tr (i + 1)).a
    simp [ih, h_is_path] at h_step_P
    exact h_step_P

/--
  A single step does not decrease the clock value. In temporal logic,
  `[](clock' ≥ clock)`.
  -/
lemma clock_is_monotonic_in_one_step
    (s: ProtocolState Proc) (s': ProtocolState Proc) (a: Action Proc)
    (h_next: next_a Proc InitDelay GST MsgDelay s s' a):
      s'.clock ≥ s.clock := by
  unfold next_a at h_next
  unfold crash rcv_heartbeat_reply advance_clock rcv_heartbeat_request timeout at h_next
  cases a with
  | Init => simp at h_next; rw [h_next]
  | AdvanceClock | RcvHeartbeatRequest _ _ _ | RcvHeartbeatReply _ _ _ | Timeout _ | Crash _ =>
    simp [h_next]

/--
  A single step does not decrease the set of the crashed processes.
  In temporal logic, `[](crashed' ⊇ crashed)`.
  -/
lemma crashed_is_monotonic_in_one_step
    (s: ProtocolState Proc) (s': ProtocolState Proc) (a: Action Proc)
    (h_next: next_a Proc InitDelay GST MsgDelay s s' a):
      s'.crashed ⊇ s.crashed := by
  -- literally the same proof as above
  unfold next_a at h_next
  unfold crash rcv_heartbeat_reply advance_clock rcv_heartbeat_request timeout at h_next
  cases a with
  | Init => simp at h_next; rw [h_next]
  | AdvanceClock | RcvHeartbeatRequest _ _ _ | RcvHeartbeatReply _ _ _ | Timeout _ | Crash _ =>
    simp [h_next]

/--
  The clock grows monotonically in a fair run.
  In temporal logic, `∃ c: ℕ, [](clock = c → [](clock ≥ c))`.
  -/
lemma clock_is_monotonic_in_fair_run
    (tr: Trace Proc)
    (h_is_fair_run: is_fair_run Proc InitDelay GST MsgDelay tr)
    (i: ℕ) (j: ℕ) (h_j_ge_i: j ≥ i):
      (tr j).s.clock ≥ (tr i).s.clock := by
  have : ∃k: ℕ, j = i + k := Nat.exists_eq_add_of_le h_j_ge_i
  rcases this with ⟨ k, rfl ⟩
  induction k with
  | zero => simp
  | succ k ik =>
    have h: i + k ≥ i := by linarith
    simp [h] at ik
    unfold is_fair_run at h_is_fair_run
    rcases h_is_fair_run with ⟨ h_is_run, _ ⟩
    unfold is_run at h_is_run
    rcases h_is_run with ⟨ _, h_is_path ⟩
    unfold is_path at h_is_path
    specialize h_is_path (i + k)
    -- apply next_does_not_decrease_clock to the last step
    have h_last_step_mono :=
      clock_is_monotonic_in_one_step InitDelay GST MsgDelay
        (tr (i + k)).s (tr (i + k + 1)).s (tr (i + k + 1)).a h_is_path
    -- now just apply transitivity
    exact le_trans ik h_last_step_mono

/--
  The set `crashed` grows monotonically in a fair run.

  In temporal logic, `∀p: Proc, [](p ∈ crashed) → [](p ∈ s.crashed))`.
  -/
lemma crashed_is_monotonic_in_fair_run
    (tr: Trace Proc)
    (h_is_fair_run: is_fair_run Proc InitDelay GST MsgDelay tr)
    (p: Proc) (k: ℕ) (h_p_crashed: p ∈ (tr k).s.crashed) (i: ℕ):
      p ∈ (tr (k + i)).s.crashed := by
  induction i with
  | zero => exact h_p_crashed
  | succ i ii =>
    unfold is_fair_run at h_is_fair_run
    rcases h_is_fair_run with ⟨ h_is_run, _ ⟩
    unfold is_run at h_is_run
    rcases h_is_run with ⟨ _, h_is_path ⟩
    unfold is_path at h_is_path
    specialize h_is_path (k + i)
    -- apply crashed_is_monotonic_in_one_step to the last step
    have h_last_step_mono :=
      crashed_is_monotonic_in_one_step InitDelay GST MsgDelay
        (tr (k + i)).s (tr (k + i + 1)).s (tr (k + i + 1)).a h_is_path
    exact h_last_step_mono ii

/--
  Every fair run covers every clock value `t`. Note that this requires fairness.
  Otherwise, the clock may not advance at all.

  In temporal logic, `∀t ∈ ℕ, <>(clock ≥ t)`.
  -/
lemma eventually_clock_is_t
    (tr: Trace Proc)
    (h_is_fair_run: is_fair_run Proc InitDelay GST MsgDelay tr)
    (t: ℕ):
      (∃ i: ℕ, (tr i).s.clock ≥ t) := by
  unfold is_fair_run at h_is_fair_run
  have h_is_fair_run_copy := h_is_fair_run -- otherwise, h_is_fair_run is destroyed
  rcases h_is_fair_run_copy with ⟨ h_is_run, _, _, h_is_fair_clock ⟩
  unfold is_run at h_is_run
  rcases h_is_run with ⟨ h_init, h_is_path ⟩
  unfold init at h_init; unfold is_fair_clock at h_is_fair_clock
  induction t with
  | zero => use 0; simp [h_init]
  | succ t ih =>
    rcases ih with ⟨ i, h_i ⟩
    -- assume on contrary that the clock value never goes above `t`
    by_contra h_clock_le_t
    simp at h_clock_le_t

    specialize h_is_fair_clock i
    rcases h_is_fair_clock with ⟨ j, h_j_clock_advances ⟩ -- clock advances at `j > i`

    unfold is_path at h_is_path
    specialize h_is_path (j - 1)
    unfold next_a at h_is_path

    have h_jj: j - 1 + 1 = j := by omega -- do trivial reindexing
    rw [h_jj] at h_is_path -- replace `j - 1 + 1` with `j`
    have h_clock_advances_at_j: (tr j).a = Action.AdvanceClock := by
      simp [h_j_clock_advances]
    simp [h_clock_advances_at_j, advance_clock] at h_is_path
    have h_mono_clock: (tr i).s.clock ≤ (tr (j - 1)).s.clock := by
      have h_j_gt_i: j > i := by simp [h_j_clock_advances]
      have pred_j_ge_k: j - 1 ≥ i := by linarith [h_j_gt_i]
      apply clock_is_monotonic_in_fair_run
        InitDelay GST MsgDelay tr h_is_fair_run i (j - 1) pred_j_ge_k
    have h_clock_j: (tr j).s.clock ≥ t + 1 := by linarith
    specialize h_clock_le_t j
    linarith [h_clock_j, h_clock_le_t]

/--
  If a process `p` never crashes, then it resets `alive[p]!` to `∅`
  infinitely often.

  In temporal logic, `[](p ∉ crashed) → []<>(alive[p]! = ∅)`.
  -/
lemma eventually_alive_is_empty
    (tr: Trace Proc)
    (h_is_fair_run: is_fair_run Proc InitDelay GST MsgDelay tr)
    (p: Proc)
    (h_p_never_crashes: never_crashes tr p) (k: ℕ)
    (h_i_positive: k > 0):
      ∃ i: ℕ, (tr (k + i)).s.alive[p]! = ∅ := by
  rcases h_is_fair_run with
    ⟨ h_is_run, h_is_rel_comm, h_is_fair_to, h_is_fair_clock ⟩
  unfold is_fair_timeout at h_is_fair_to
  specialize h_is_fair_to k p
  rcases h_is_fair_to with ⟨ j, h_j_clock_ge ⟩
  -- this is the point when `p` triggers next timeout
  specialize h_p_never_crashes (k + j - 1)
  simp [h_p_never_crashes] at h_j_clock_ge
  rcases h_j_clock_ge with ⟨ h_timeout, h_clock_at_timeout ⟩
  unfold is_run at h_is_run
  rcases h_is_run with ⟨ _, h_is_path ⟩
  unfold is_path at h_is_path
  specialize h_is_path (k + j - 1)
  have h_dec_inc: k + j - 1 + 1 = k + j := by omega
  rw [h_dec_inc, h_timeout] at h_is_path
  unfold next_a at h_is_path
  simp at h_is_path
  unfold timeout at h_is_path
  -- extract the update of the set `alive[p]!`
  rcases h_is_path with ⟨ _, _, _, _, _, h_alive_updated, _ ⟩
  have h_alive_is_empty: (tr (k + j)).s.alive[p]! = ∅ := by
    simp [h_alive_updated]
  exact ⟨ j, h_alive_is_empty ⟩

/--
  An auxilliary lemma to get rid of the annoying case of `i = 0`.
  In temporal logic, `¬(clock > 0)`.
  -/
lemma when_clock_is_positive_step_is_non_init
    (tr: Trace Proc)
    (h_is_fair_run: is_fair_run Proc InitDelay GST MsgDelay tr)
    (i: ℕ)
    (h_clock_is_positive: (tr i).s.clock > 0):
      i > 0 := by
  unfold is_fair_run at h_is_fair_run
  rcases h_is_fair_run with ⟨ h_is_run, _ ⟩
  unfold is_run at h_is_run
  rcases h_is_run with ⟨ h_init, _ ⟩
  unfold init at h_init
  rcases h_init with ⟨ _, _, _, _, h_clock_is_zero, _ ⟩
  by_contra h_i_is_zero
  simp at h_i_is_zero
  rw [h_i_is_zero] at h_clock_is_positive
  linarith [h_clock_is_zero, h_clock_is_positive]

/--
  Show that no sent message has a timestamp in the future. In temporal logic,
  `[](∀ m ∈ sent, m.timestamp ≤ clock)`.

  Surprisingly, this requires quite a long proof, though there is nothing
  groundbreaking in it.
  -/
lemma no_sent_from_the_future
    (tr: Trace Proc)
    (h_is_fair_run: is_fair_run Proc InitDelay GST MsgDelay tr):
      ∀ i: ℕ,
        ∀ m ∈ (tr i).s.sent,
          m.timestamp ≤ (tr i).s.clock := by
  let P := fun (s: ProtocolState Proc) => ∀ m ∈ s.sent, m.timestamp ≤ s.clock
  -- show P for the initial state
  have h_init_P: (s: ProtocolState Proc)
      → (h_init: init Proc InitDelay s s.all.toList) → (P s) := by
    intros s h_init
    unfold init at h_init; unfold P
    rcases h_init with ⟨ _, _, h_sent_empty, _, h_clock_zero, _ ⟩
    -- sent is empty, trivial
    simp [h_sent_empty]
  -- show P for a single step
  have h_step_P:
      (s: ProtocolState Proc) → (s': ProtocolState Proc) → (a: Action Proc)
        → (h_s: P s) → (h_next: (next_a Proc InitDelay GST MsgDelay s s' a)) → P s' := by
    intros s s' a h_s h_next
    unfold P; intro m h_m_in_sent
    unfold P at h_s; specialize h_s m
    unfold next_a at h_next; unfold crash rcv_heartbeat_reply at h_next
    cases h: a with
    | Init => -- apply `h_s` directly
      simp [h] at h_next; rw [h_next];
      simp [h_next] at h_m_in_sent
      simp [h_m_in_sent] at h_s
      exact h_s

    | AdvanceClock =>
      -- `s'.sent = s.sent` and `s'.clock = s.clock + 1`, so we apply `h_s` and `linarith`
      simp [h] at h_next
      unfold advance_clock at h_next
      have h_keep_sent: s'.sent = s.sent := by simp [h_next]
      have h_inc_clock: s'.clock = s.clock + 1 := by simp [h_next]
      rw [h_keep_sent] at h_m_in_sent
      specialize h_s h_m_in_sent
      rw [h_inc_clock]
      linarith [h_s]

    | Crash _ | RcvHeartbeatReply _ _ _ =>
      -- `s'.sent = s.sent` and `s'.clock = s.clock`, so we apply `h_s`
      simp [h] at h_next
      have h_keep_sent: s'.sent = s.sent := by simp [h_next]
      have h_keep_clock: s'.clock = s.clock := by simp [h_next]
      rw [h_keep_sent] at h_m_in_sent; rw [h_keep_clock]
      exact h_s h_m_in_sent

    | Timeout p =>
      -- `s'.sent = s.sent ∪ newSent`. Show that `m ∈ newSent` satisfy `P`.
      simp [h] at h_next; unfold timeout at h_next
      have h_keep_clock: s'.clock = s.clock := by simp [h_next]
      let newSent := Finset.image (fun q => {
          kind := MsgTag.HeartbeatRequest, src := p, dst := q,
          timestamp := s.clock : Msg Proc
        }) Finset.univ
      have h_update_sent: s'.sent = s.sent ∪ newSent := by
        unfold newSent
        simp [h_next]
      -- show that all messages in `newSent` satisfy `P`
      have h_all_new_msgs: ∀ m₂ ∈ newSent, m₂.timestamp ≤ s'.clock := by
        unfold newSent
        intro m₂ h_m_in_newSent
        -- apply `Finset.mem_image` to get the definition of `m₂`
        have h_m2_preimage := Finset.mem_image.mp h_m_in_newSent
        rcases h_m2_preimage with ⟨ q₂, q2_in_all, h_m2_eq ⟩
        rw [← h_m2_eq]; simp [h_keep_clock]
      have h_old_or_new: m ∈ s.sent ∨ m ∈ newSent := by
        rw [h_update_sent] at h_m_in_sent
        exact Finset.mem_union.mp h_m_in_sent
      -- make case distinction on whether m is old or new
      cases h_old_or_new with
      | inl h_in_old =>
        -- `m` is old, so `m.timestamp ≤ s.clock` by the inductive hypothesis `h_s`
        rw [h_keep_clock]
        specialize h_s h_in_old
        exact h_s
      | inr h_in_new =>
        -- m is new, apply h_all_new_msgs
        specialize h_all_new_msgs m h_in_new
        exact h_all_new_msgs

    | RcvHeartbeatRequest src dst ts =>
      -- `s'.sent = s.sent ∪ { reply }`. Show that `reply` satisfies `P`.
      simp [h] at h_next
      unfold rcv_heartbeat_request at h_next; simp [h_next]
      let reply := {
        kind := MsgTag.HeartbeatReply, src := dst,
        dst := src, timestamp := s.clock : Msg Proc
      }
      -- we have to show that messages in `s'.sent` satisfy `P`
      have h_update_sent: s'.sent = s.sent ∪ { reply } := by
        unfold reply; simp [h_next]
      -- either `m` in `s.sent` or `m = reply`
      have m_is_old_or_reply: m ∈ s.sent ∨ m = reply := by
        rw [h_update_sent] at h_m_in_sent
        let h := Finset.mem_union.mp h_m_in_sent
        cases h with
        | inl h_in_sent => simp [h_in_sent]
        | inr h_eq_reply => simp [Finset.mem_singleton.mp h_eq_reply]
      -- now, either apply the inductive hypothesis `h_s`, or the definition of `reply`
      cases m_is_old_or_reply with
      | inl h_m_in_old_sent =>
        -- when `m` is in `s.sent`, apply the inductive hypothesis
        specialize h_s h_m_in_old_sent
        exact h_s
      | inr h_m_eq_reply =>
        -- when `m = reply`, apply the definition of `reply`
        unfold reply at h_m_eq_reply
        simp [h_m_eq_reply]
  -- invoke the inductive schema
  exact inductive_inv InitDelay GST MsgDelay tr h_is_fair_run h_init_P h_step_P

/--
  If a process `p` crashes at some point, then no message sent by `p`
  can contain a timestamp greater than the clock value at the time of crashing.

  In temporal logic,
  `∀p: Proc, []((p ∈ crashed) → ∃c ∈ ℕ, c = clock ∧ [](∀m ∈ sent, m.src = p → m.timestamp ≤ c))`.
  -/
lemma crashed_process_does_not_send
    (tr: Trace Proc)
    (h_is_fair_run: is_fair_run Proc InitDelay GST MsgDelay tr)
    (p: Proc) (k: ℕ) (h_p_crashed: p ∈ (tr k).s.crashed):
      ∀ i: ℕ,
        ∀ m ∈ (tr (k + i)).s.sent,
          m.src = p → m.timestamp ≤ (tr k).s.clock := by
  intros i m h_m_in_sent h_src
  -- By monotonicity, `p ∈ crashed` at all times ≥ k
  have h_p_crashed_later : ∀ j, p ∈ (tr (k + j)).s.crashed :=
    fun j => crashed_is_monotonic_in_fair_run
      InitDelay GST MsgDelay tr h_is_fair_run p k h_p_crashed j
  induction i with
  | zero =>
    -- Show that the claim holds for `k` itself. Apply `no_sent_from_the_future`.
    have h := no_sent_from_the_future InitDelay GST MsgDelay tr h_is_fair_run k
    specialize h m h_m_in_sent
    exact h
  | succ i ih =>
    let s := (tr (k + i)).s
    let s' := (tr (k + i + 1)).s
    let a := (tr (k + i + 1)).a
    have h_m_in_sent: m ∈ s'.sent := by exact h_m_in_sent
    -- specialize next_a to `s`, `s'`, and `a`
    have h_next : next_a Proc InitDelay GST MsgDelay s s' a := by
      unfold is_fair_run at h_is_fair_run
      rcases h_is_fair_run with ⟨ h_is_run, _ ⟩
      unfold is_run at h_is_run
      rcases h_is_run with ⟨ _, h_is_path ⟩
      unfold is_path at h_is_path
      exact h_is_path (k + i)
    have h_p_crashed_at_s := h_p_crashed_later i
    -- If `m.src = p`, then `m ∈ s.sent`
    unfold next_a at h_next;
    unfold advance_clock crash rcv_heartbeat_reply at h_next;
    have h_m_in_old_sent : m.src = p → m ∈ s.sent := by
      intro h_src
      cases h_a: a with
      | Init =>
        simp [h_a] at h_next;
        rw [h_next] at h_m_in_sent; exact h_m_in_sent

      | AdvanceClock | Crash _ | RcvHeartbeatReply _ _ _ =>
        simp [h_a] at h_next;
        have :s'.sent = s.sent := by simp [h_next]
        rw [this] at h_m_in_sent; exact h_m_in_sent

      | Timeout q =>
        simp [h_a] at h_next; unfold timeout at h_next;
        have h_q_ne_p: q ≠ p := by
          by_contra h_eq
          rw [h_eq] at h_next
          unfold s at h_next
          simp [h_p_crashed_at_s] at h_next
        let newSent := Finset.image (fun r => {
            kind := MsgTag.HeartbeatRequest, src := q, dst := r,
            timestamp := s.clock : Msg Proc
          }) Finset.univ
        have h_update_sent: s'.sent = s.sent ∪ newSent := by
          unfold newSent
          simp [h_next]
        rw [h_update_sent] at h_m_in_sent
        -- either `m` is in `s.sent`, or `m` is in `newSent`
        have h_m_in_sent_or_in_newSent: m ∈ s.sent ∨ m ∈ newSent := by
          rw [Finset.mem_union] at h_m_in_sent
          exact h_m_in_sent
        -- however, `m` cannot be in `newSent`, as `m.src = p` and `q ≠ p`
        have h_no_p_in_newSent: m ∉ newSent := by
          by_contra h_m_in_newSent
          -- apply `Finset.mem_image` to get the definition of `m`
          have h_m_preimage := Finset.mem_image.mp h_m_in_newSent
          rcases h_m_preimage with ⟨ r, r_in_all, h_m_eq ⟩
          have h_m_eq := Eq.symm h_m_eq -- swap the arguments
          have m_src_eq_q: m.src = q := by rw [h_m_eq]
          rw [m_src_eq_q] at h_src
          exact h_q_ne_p h_src
        simp [h_no_p_in_newSent] at h_m_in_sent_or_in_newSent
        exact h_m_in_sent_or_in_newSent

      | RcvHeartbeatRequest src dst ts =>
        simp [h_a] at h_next
        unfold rcv_heartbeat_request at h_next
        have h_dst_ne_p: dst ≠ p := by
          by_contra h_eq
          rw [h_eq] at h_next
          unfold s at h_next
          simp [h_p_crashed_at_s] at h_next
        let reply := {
          kind := MsgTag.HeartbeatReply, src := dst,
          dst := src, timestamp := s.clock : Msg Proc
        }
        have h_update_sent: s'.sent = s.sent ∪ { reply } := by
          unfold reply; simp [h_next]
        rw [h_update_sent] at h_m_in_sent
        -- either `m` is in `s.sent`, or `m` is `reply`
        have h_m_in_sent_or_reply: m ∈ s.sent ∨ m = reply := by
          let h := Finset.mem_union.mp h_m_in_sent
          cases h with
          | inl h_in_sent => simp [h_in_sent]
          | inr h_eq_reply => simp [Finset.mem_singleton.mp h_eq_reply]
        -- `m` cannot be `reply`, as `reply.src = dst` and `dst ≠ p`
        have : m ≠ reply := by
          by_contra h_eq_reply
          unfold reply at h_eq_reply
          simp [h_eq_reply] at h_src
          rw [h_src] at h_dst_ne_p
          simp at h_dst_ne_p
        simp [this] at h_m_in_sent_or_reply
        exact h_m_in_sent_or_reply
    -- apply the inductive hypothesis `ih`
    simp [h_src] at h_m_in_old_sent
    exact ih h_m_in_old_sent

/--
  For every fair run, if `p` never crashes and `q` does,
  then `p` never registers `q` as alive from some point on.

  In temporal logic, `([]p ∉ crashed ∧ <>q ∈ crashed) → <>[](q ∉ alive[p])`.
  -/
lemma eventually_crashes_implies_never_alive
    (tr: Trace Proc)
    (h_is_fair_run: is_fair_run Proc InitDelay GST MsgDelay tr)
    (p q: Proc)
    (h_p_never_crashes: never_crashes tr p)
    (h_crashes: eventually_crashes tr q):
      eventually_never_alive tr p q := by
  -- eventually, `q` crashes at some point `at_q_crashed`
  unfold eventually_crashes at h_crashes
  rcases h_crashes with ⟨ at_q_crashed, h_q_crashed ⟩
  -- Yet, `p` may still receive heartbeats from `q` from the past.
  -- We jump to the point when `q` crashed `MsgDelay` units in the past,
  -- and the pre-GST heartbeats stop arriving.
  let clock_at_q_crashed := (tr at_q_crashed).s.clock
  let magic_time := (max (GST + MsgDelay) (clock_at_q_crashed + MsgDelay)) + 1
  have h_eventually_magic_time :=
    eventually_clock_is_t InitDelay GST MsgDelay tr h_is_fair_run magic_time
  rcases h_eventually_magic_time with ⟨ at_magic_time, h_clock_at_magic_time ⟩
  -- prove this fact right away, we will need it much later
  have h_magic_time_after_q_crashed: at_magic_time ≥ at_q_crashed := by
    by_contra h_contra; simp at h_contra
    unfold magic_time at h_clock_at_magic_time
    have h: (tr at_magic_time).s.clock ≥ clock_at_q_crashed + MsgDelay + 1 := by omega
    have h_order: at_q_crashed ≥ at_magic_time := by linarith [h_clock_at_magic_time, h]
    have h_clock_order := clock_is_monotonic_in_fair_run InitDelay GST MsgDelay
      tr h_is_fair_run at_magic_time at_q_crashed h_order
    linarith [h_clock_order, h_clock_at_magic_time]
  -- we have to show this auxilliary to make `eventually_alive_is_empty` work
  have h_clock_is_positive: (tr at_magic_time).s.clock > 0 := by omega
  have h_positive := when_clock_is_positive_step_is_non_init
    InitDelay GST MsgDelay tr h_is_fair_run at_magic_time h_clock_is_positive
  -- eventually, `alive[p]!` becomes empty, we start with `at_magic_time`
  have h_alive_is_empty :=
    eventually_alive_is_empty InitDelay GST MsgDelay
      tr h_is_fair_run p h_p_never_crashes at_magic_time h_positive
  rcases h_alive_is_empty with ⟨ at_alive_empty, h_alive_empty ⟩
  -- At this point `at_alive_empty` we have:
  --   (1) `alive[p]! = ∅`,
  --   (2) no pre-GST heartbeats from `q` can arrive
  --   (3) `q` has crashed and no heartbeats from the previous timeout can arrive,
  --       as `MsgDelay` has passed.
  have h_never_alive_from_k:
      ∀ k: ℕ,
        q ∉ (tr (at_magic_time + at_alive_empty + k)).s.alive[p]! := by
    intro k
    induction k with
    | zero => simp [h_alive_empty]
    | succ k ih =>
      -- we have to show that `alive[p]!` remains empty
      unfold is_fair_run at h_is_fair_run
      let h_is_fair_run_copy := h_is_fair_run -- otherwise, h_is_fair_run is destroyed
      rcases h_is_fair_run_copy with ⟨ h_is_run, _, _, _ ⟩
      unfold is_run at h_is_run
      rcases h_is_run with ⟨ _, h_is_path ⟩
      unfold is_path at h_is_path
      specialize h_is_path (at_magic_time + at_alive_empty + k)
      have h_indices: at_magic_time + at_alive_empty + k + 1 =
        at_magic_time + at_alive_empty + (k + 1) := by rfl
      rw [h_indices] at h_is_path
      -- assume that it does not hold at some point `k + 1`
      by_contra h_contra
      unfold next_a at h_is_path
      -- introduce shortcuts, so we don't get lost in indices
      let s := (tr (at_magic_time + at_alive_empty + k)).s
      let s' := (tr (at_magic_time + at_alive_empty + (k + 1))).s
      let a := (tr (at_magic_time + at_alive_empty + (k + 1))).a
      have h_s: s = (tr (at_magic_time + at_alive_empty + k)).s := by rfl
      have h_s': s' = (tr (at_magic_time + at_alive_empty + (k + 1))).s := by rfl
      have h_a: a = (tr (at_magic_time + at_alive_empty + (k + 1))).a := by rfl
      rw  [← h_s, ← h_s', ← h_a] at h_is_path
      rw [← h_s] at ih
      rw [← h_s'] at h_contra
      -- do case analysis on the action `a`
      unfold advance_clock crash rcv_heartbeat_request at h_is_path
      cases h: a
      case Init =>
        simp [h] at h_is_path
        simp [h_is_path, ih] at h_contra
      case AdvanceClock | RcvHeartbeatRequest _ _ _ | Crash _ =>
        simp [h] at h_is_path
        have h_eq: s'.alive = s.alive := by simp [h_is_path]
        rw [h_eq] at h_contra
        simp [ih] at h_contra
      case Timeout q =>
        simp [h] at h_is_path
        unfold timeout at h_is_path
        -- since `Timeout` updates `alive`, we have to do case analysis on `q = p`
        by_cases h_eq: q = p
        case pos =>
          have h_alive_empty: s'.alive[q]! = ∅ := by simp [h_is_path]
          rw [h_eq] at h_alive_empty
          simp [h_alive_empty] at h_contra
        case neg =>
          have h_alive_unchanged: s'.alive[p]! = s.alive[p]! := by
            have :s'.alive = s.alive.insert q ∅ := by simp [h_is_path]
            simp [this, Std.HashMap.getElem!_insert]
            simp [h_eq]
          simp [h_alive_unchanged, ih] at h_contra
      case RcvHeartbeatReply src dst ts =>
        -- this must be the hardest case
        simp [h] at h_is_path
        unfold rcv_heartbeat_reply at h_is_path
        have h_update: s'.alive = s.alive.insert dst (s.alive[dst]! ∪ {src}) :=
          by simp [h_is_path]
        rw [h_update] at h_contra
        -- consider the cases on `dst = p` and `src = q`
        by_cases h_p_eq_dst: dst = p
        case pos =>
          by_cases h_q_eq_src: q = src
          case neg =>
            -- since `q ≠ src`, we have `q ∉ s'.alive[p]!`
            rw [h_p_eq_dst] at h_contra
            simp [Std.HashMap.getElem!_insert] at h_contra
            simp [h_q_eq_src, ih] at h_contra
          case pos =>
            -- `q = src` is the hardest case. We have to show that the crashed `q`
            -- could not send a heartbeat to `p` at this point.
            let reply := {
              kind := MsgTag.HeartbeatReply, src := src, dst := dst, timestamp := ts: Msg Proc
            }
            -- from the step, we have that `reply ∈ s'.sent` and `isMsgTimely GST MsgDelay ts s.clock`
            have h_reply_in_sent: reply ∈ s.sent := by
              unfold reply
              simp [reply] at h_is_path
              simp [h_is_path]
            have h_msg_timely: isMsgTimely GST MsgDelay ts s.clock = true := by simp [h_is_path]
            simp [isMsgTimely] at h_msg_timely
            -- now, recall that `q` has crashed at `at_q_crashed` and it cannot send any longer
            have h_q_does_not_send :=
              crashed_process_does_not_send InitDelay GST MsgDelay
                tr h_is_fair_run q at_q_crashed h_q_crashed
            -- we have to find the point `i` relative to q's crash point that corresponds to `s`
            have h_i: ∃ i: ℕ, (at_q_crashed + i) = (at_magic_time + at_alive_empty + k) := by
              -- since `at_magic_time ≥ at_q_crashed`, we can find such `i`
              have h: at_magic_time + at_alive_empty + k ≥ at_q_crashed := by
                linarith [h_magic_time_after_q_crashed]
              use at_magic_time + at_alive_empty + k - at_q_crashed
              simp [h]
            rcases h_i with ⟨ i, h_i_eq ⟩
            specialize h_q_does_not_send i reply
            unfold reply at h_q_does_not_send
            simp at h_q_does_not_send
            -- swap `src` and `q` in h_q_eq_src
            have h_src_eq_q: src = q := by simp [h_q_eq_src]
            -- show that timestamp `ts` is not later than the clock at `at_q_crashed`
            have h_ts_before_crash: ts ≤ (tr at_q_crashed).s.clock := by
              simp [h_src_eq_q] at h_q_does_not_send
              rw [h_i_eq] at h_q_does_not_send
              unfold reply s at h_reply_in_sent
              rw [h_src_eq_q] at h_reply_in_sent
              simp [h_reply_in_sent] at h_q_does_not_send
              exact h_q_does_not_send
            -- we derive an upper bound and a lower bound on `s.clock`
            have h_clock_upper_bound:
                s.clock ≤ max (GST + MsgDelay) (clock_at_q_crashed + MsgDelay) := by omega
            have h_clock_lower_bound: s.clock ≥ magic_time := by
              unfold s magic_time
              simp [h_magic_time_after_q_crashed]
              have h_order: at_magic_time + at_alive_empty + k ≥ at_magic_time := by linarith
              have h_clock_order :=
                clock_is_monotonic_in_fair_run InitDelay GST MsgDelay
                  tr h_is_fair_run at_magic_time (at_magic_time + at_alive_empty + k) h_order
              simp [h_clock_at_magic_time, h_clock_order]
              omega
            unfold magic_time at h_clock_lower_bound
            -- now the upper bound is smaller than the lower bound, contradiction!
            linarith [h_clock_lower_bound, h_clock_upper_bound]
        case neg =>
          -- `p ≠ dst`, so `s'.alive[p]! = s.alive[p]!`
          simp [Std.HashMap.getElem!_insert] at h_contra
          simp [h_p_eq_dst] at h_contra
          simp [ih] at h_contra
  -- simply use `at_magic_time + at_alive_empty` as a witness of `i`
  have : eventually_never_alive tr p q := by
    use at_magic_time + at_alive_empty
  exact this

/--
  For every fair run, if `p` never crashes and `q` does,
  then, from some point on, `p` always suspects `q`.

  In temporal logic,
  `([]p ∉ crashed ∧ <>q ∈ crashed) → <>[](q ∈ suspected[p])`.
  -/
lemma eventually_crashes_implies_always_suspected
    (tr: Trace Proc)
    (h_is_fair_run: is_fair_run Proc InitDelay GST MsgDelay tr)
    (p q: Proc)
    (h_p_never_crashes: never_crashes tr p)
    (h_crashes: eventually_crashes tr q):
      eventually_q_is_always_suspected tr p q := by
  -- from some point on, `q ∉ alive[p]!`
  have h_never_alive :=
    eventually_crashes_implies_never_alive InitDelay GST MsgDelay
      tr h_is_fair_run p q h_p_never_crashes h_crashes
  unfold eventually_never_alive at h_never_alive
  rcases h_never_alive with ⟨ k, h_never_alive ⟩
  rcases h_is_fair_run with ⟨ h_is_run, _, h_is_fair_to, _ ⟩
  unfold is_fair_timeout at h_is_fair_to
  -- find the next timeout of `p` after `k`, we take `k + 1` to avoid `k = 0`
  specialize h_is_fair_to (k + 1) p
  unfold never_crashes at h_p_never_crashes
  simp [h_p_never_crashes] at h_is_fair_to
  rcases h_is_fair_to with ⟨ j, ⟨h_is_timeout, _⟩⟩
  unfold is_run at h_is_run
  rcases h_is_run with ⟨ _, h_is_path ⟩
  unfold is_path at h_is_path
  -- now, we have to show that `q` is suspected at `k + 1 + j`
  -- extract the update of the set `suspected[p]!`
  have h_eventually_q_is_suspected: q ∈ (tr (k + 1 + j)).s.suspected[p]! := by
    have h_next := h_is_path (k + 1 + j - 1)
    have h_dec_inc: k + 1 + j - 1 + 1 = k + 1 + j := by omega
    rw [h_dec_inc] at h_next
    unfold next_a at h_next
    simp [h_is_timeout] at h_next
    unfold timeout at h_next
    simp [h_next]
    -- `q` is not in `alive[p]!`, so it is suspected
    specialize h_never_alive j
    simp [h_never_alive]
  -- now prove by induction that `q` is suspected at all later points
  have h_q_is_always_suspected:
      ∀ i: ℕ, q ∈ (tr (k + 1 + j + i)).s.suspected[p]! := by
    intro i
    induction i with
    | zero =>
      -- we have shown that above
      exact h_eventually_q_is_suspected
    | succ i ih =>
      -- we have to show that `q` is suspected at `k + 1 + j + (i + 1)`
      specialize h_is_path (k + 1 + j + i)
      -- normalize the indices
      have h_indices: k + 1 + j + (i + 1) = k + 1 + j + i + 1 := by rfl
      rw [h_indices]; subst_eqs
      -- introduce shortcuts, so we don't get lost in the indices
      let s := (tr (k + 1 + j + i)).s
      let s' := (tr (k + 1 + j + i + 1)).s
      -- do case analysis on the action `a`
      unfold next_a at h_is_path
      unfold advance_clock crash rcv_heartbeat_request rcv_heartbeat_reply at h_is_path
      cases h_a: (tr (k + 1 + j + i + 1)).a with
      | Init =>
        simp [h_a] at h_is_path
        rw [← h_is_path] at ih; exact ih

      | AdvanceClock | Crash _ | RcvHeartbeatRequest _ _ _ | RcvHeartbeatReply _ _ _=>
        simp [h_a] at h_is_path
        have h_keep_suspected: s'.suspected = s.suspected := by
          unfold s s'; simp [h_is_path]
        unfold s s' at h_keep_suspected
        rw [← h_keep_suspected] at ih; exact ih

      | Timeout r =>
        simp [h_a] at h_is_path
        unfold timeout at h_is_path
        by_cases h_eq: r = p
        case neg =>
          -- `r ≠ p`, so `s'.suspected[p]! = s.suspected[p]!`
          have h_keep_suspected: s'.suspected[p]! = s.suspected[p]! := by
            unfold s s'
            simp [h_is_path, Std.HashMap.getElem!_insert, h_eq]
          rw [← h_keep_suspected] at ih; exact ih
        case pos =>
          -- `r = p`, so we have to show that `q` is suspected, as it is not in `alive[p]!`
          let nextSuspected := Finset.univ \ s.alive[r]!
          have h_update_suspected: s'.suspected[p]! = nextSuspected := by
            unfold nextSuspected s s'
            simp [h_is_path, Std.HashMap.getElem!_insert, h_eq]
          unfold s' nextSuspected at h_update_suspected
          rw [h_update_suspected, h_eq]
          unfold s
          -- now it remains to show that `q ∉ s.alive[p]!`
          specialize h_never_alive (1 + j + i)
          have : k + 1 + j + i = k + (1 + j + i) := by ac_rfl
          simp [this, h_never_alive]
  -- now apply h_suspected_always to get the result
  unfold eventually_q_is_always_suspected q_is_always_suspected
  use k + 1 + j

/--
  For a set of crashing processes `C` and a trace `tr`, show that if for every
  crashing process `q` and every correct process `p`, it holds that `p`
  eventually suspects `q` forever, then there is a common time point `k` such
  that all correct processes suspect all crashed processes forever.

  In temporal logic, `∀ q ∈ Crashed, ∀ p ∈ Correct, <>[](q ∈ suspected[p]!)`
  implies `<>[] ∀ q ∈ Crashed, ∀ p ∈ Correct, q ∈ suspected[p]!`.
  -/
lemma eventually_always_suspected_meet
    (tr: Trace Proc)
    (Crashed: Finset Proc)
    (h_suspected:
      ∀ q ∈ Crashed,
        ∀ p ∈ Finset.univ \ Crashed,
          eventually_q_is_always_suspected tr p q):
      ∃ k: ℕ,
        ∀ i: ℕ,
          ∀ q ∈ Crashed,
            ∀ p ∈ Finset.univ \ Crashed,
              q ∈ (tr (k + i)).s.suspected[p]! := by
  -- fix the set of correct processes
  let Correct := Finset.univ \ Crashed
  -- we have to bubble up `∃ k: ℕ` two times
  -- bubble up `∃ k: ℕ` the first time
  have bubble1: (q: Proc) → (h_q_crashed: q ∈ Crashed) →
      ∃ k: ℕ, ∀ i: ℕ, ∀ p ∈ Correct, q ∈ (tr (k + i)).s.suspected[p]! := by
    intro q h_q_crashed
    specialize h_suspected q h_q_crashed
    let P (i: ℕ) (p: Proc) := q ∈ (tr i).s.suspected[p]!
    exact forall_FG_implies_FG_forall P Correct h_suspected
  -- the predicate `P` to use in the next instance of `forall_FG_implies_FG_forall`
  let P (i: ℕ) (q: Proc) :=
    ∀ p ∈ Correct, q ∈ (tr i).s.suspected[p]!
  -- bubble up `∃ k: ℕ` the second time
  exact forall_FG_implies_FG_forall P Crashed bubble1

/--
  Strong completeness holds for every run.
  -/
theorem strong_completeness
    (tr: Trace Proc)
    (h_is_fair_run: is_fair_run Proc InitDelay GST MsgDelay tr)
    (Crashed: Finset Proc) (h_is_crashing_set: is_crashing_set tr Crashed):
      ∃ k: ℕ, ∀ i: ℕ, ∀ p q: Proc,
        (p ∉ Crashed ∧ q ∈ Crashed) → q ∈ (tr (k + i)).s.suspected[p]! := by
  -- define the set of the correct processes
  let Correct := Finset.univ \ Crashed
  -- show that all processes in `Correct` never crash
  have h_correct_never_crash:
      ∀ p ∈ Correct, never_crashes tr p := by
    intro p h_p_in_Correct
    unfold never_crashes
    unfold is_crashing_set eventually_crashes at h_is_crashing_set
    have h_p := h_is_crashing_set p
    have h_p_not_in_Crashed: p ∉ Crashed := by
      simp [Correct] at h_p_in_Correct; exact h_p_in_Correct
    simp [h_p_not_in_Crashed] at h_p
    exact h_p
  -- show that all processes in `Crashed` eventually crash
  have h_all_in_Crashed_crash:
      ∀ q ∈ Crashed, eventually_crashes tr q := by
    intro q h_q_in_Crashed
    unfold is_crashing_set at h_is_crashing_set
    specialize h_is_crashing_set q
    simp [h_q_in_Crashed] at h_is_crashing_set
    exact h_is_crashing_set
  -- show that for every pair of a crashed process `q` and a correct process `p`,
  -- there is a point when `p` permanently suspects `q`
  have h_suspected:
      ∀ q ∈ Crashed,
        ∀ p ∈ Correct,
          eventually_q_is_always_suspected tr p q := by
    intro q q_in_Crashed
    intro p p_in_Correct
    have h_q_crashes := h_all_in_Crashed_crash q q_in_Crashed
    have h_p_never_crashes := h_correct_never_crash p p_in_Correct
    apply eventually_crashes_implies_always_suspected InitDelay GST MsgDelay
      tr h_is_fair_run p q h_p_never_crashes h_q_crashes
  -- apply the lemma `eventually_always_suspected_meet` to find a point `k`
  have h_suspected_meet :=
    eventually_always_suspected_meet tr Crashed h_suspected
  -- we are almost there, just transform `h_suspected_meet` a bit
  rcases h_suspected_meet with ⟨k, h_q_suspected_by_p⟩
  use k
  intro i p q ⟨p_not_crashed, q_is_crashed⟩
  have p_is_correct: p ∈ Correct := by unfold Correct; simp [p_not_crashed]
  exact h_q_suspected_by_p i q q_is_crashed p p_is_correct

/-
/-- Strong completeness hold for every run. -/
theorem eventual_strong_accuracy (tr: Trace Proc)
    (h_is_fair_run: is_fair_run Proc InitDelay GST MsgDelay run):
      (is_eventually_strongly_accurate tr) := by
  sorry
-/
