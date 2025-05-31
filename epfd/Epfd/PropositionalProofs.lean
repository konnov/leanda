/-
Proving the properties of eventually perfect failure detector.

Copyright (c) 2025 Igor Konnov
Released under MIT license as described in the file LICENSE.
Authors: Igor Konnov, 2025
-/

import Epfd.Propositional

import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Insert

-- The abstract type of processes
variable {Proc : Type} [DecidableEq Proc] [Hashable Proc]

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
  An inductive proof schema to show that a state property `P` holds for all states
  in a fair run. We use this lemma to avoid repetitive proofs by induction.
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

/-- A single step does not decrease the clock value.  -/
lemma clock_is_monotonic_in_one_step
    (s: ProtocolState Proc) (s': ProtocolState Proc) (a: Action Proc)
    (h_next: next_a Proc InitDelay GST MsgDelay s s' a):
      s'.clock ≥ s.clock := by
  unfold next_a at h_next
  cases a with
  | Init => simp at h_next; rw [h_next]
  | AdvanceClock => unfold advance_clock at h_next; simp [h_next]
  | RcvHeartbeatRequest _ _ _ =>
    unfold rcv_heartbeat_request at h_next; simp [h_next]
  | RcvHeartbeatReply _ _ _ =>
    unfold rcv_heartbeat_reply at h_next; simp [h_next]
  | Timeout _ => unfold timeout at h_next; simp [h_next]
  | Crash _ => unfold crash at h_next; simp [h_next]

/-- A single step does not decrease the set of the crashed processes.  -/
lemma crashed_is_monotonic_in_one_step
    (s: ProtocolState Proc) (s': ProtocolState Proc) (a: Action Proc)
    (h_next: next_a Proc InitDelay GST MsgDelay s s' a):
      s'.crashed ⊇ s.crashed := by
  -- literally the same proof as above
  unfold next_a at h_next
  cases a with
  | Init => simp at h_next; rw [h_next]
  | AdvanceClock => unfold advance_clock at h_next; simp [h_next]
  | RcvHeartbeatRequest _ _ _ =>
    unfold rcv_heartbeat_request at h_next; simp [h_next]
  | RcvHeartbeatReply _ _ _ =>
    unfold rcv_heartbeat_reply at h_next; simp [h_next]
  | Timeout _ => unfold timeout at h_next; simp [h_next]
  | Crash _ => unfold crash at h_next; simp [h_next]

/-- The clock grows monotonically in a fair run. -/
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
    have h: i + k ≥ i := by omega
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

/-- The set `crashed` grows monotonically in a fair run. -/
lemma crashed_is_monotonic_in_fair_run
    (tr: Trace Proc)
    (h_is_fair_run: is_fair_run Proc InitDelay GST MsgDelay tr)
    (p: Proc) (i: ℕ) (h_p_crashed: p ∈ (tr i).s.crashed) (k: ℕ):
      p ∈ (tr (i + k)).s.crashed := by
  induction k with
  | zero => exact h_p_crashed
  | succ k ik =>
    unfold is_fair_run at h_is_fair_run
    rcases h_is_fair_run with ⟨ h_is_run, _ ⟩
    unfold is_run at h_is_run
    rcases h_is_run with ⟨ _, h_is_path ⟩
    unfold is_path at h_is_path
    specialize h_is_path (i + k)
    -- apply crashed_is_monotonic_in_one_step to the last step
    have h_last_step_mono :=
      crashed_is_monotonic_in_one_step InitDelay GST MsgDelay
        (tr (i + k)).s (tr (i + k + 1)).s (tr (i + k + 1)).a h_is_path
    exact h_last_step_mono ik

/--
  Every fair run covers every clock value `t`. Note that this requires fairness.
  Otherwise, the clock may not advance at all.
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

    have h_jj: j - 1 + 1 = j := by omega; -- JJ!
    rw [h_jj] at h_is_path -- replace `j - 1 + 1` with `j`
    have h_clock_advances_at_j: (tr j).a = Action.AdvanceClock := by simp [h_j_clock_advances]
    simp [h_clock_advances_at_j, advance_clock] at h_is_path
    have h_mono_clock: (tr i).s.clock ≤ (tr (j - 1)).s.clock := by
      have h_j_gt_i: j > i := by simp [h_j_clock_advances]
      have pred_j_ge_k: j - 1 ≥ i := by linarith [h_j_gt_i]
      apply clock_is_monotonic_in_fair_run InitDelay GST MsgDelay tr h_is_fair_run i (j - 1) pred_j_ge_k
    have h_clock_j: (tr j).s.clock ≥ t + 1 := by linarith
    specialize h_clock_le_t j
    linarith [h_clock_j, h_clock_le_t]

/--
  For every fair run, there is a set of processes `C` that eventually crash,
  and there is a point `i` after which no more processes crash.
  -/
lemma eventually_crashes_stabilize
    (tr: Trace Proc)
    (h_is_fair_run: is_fair_run Proc InitDelay GST MsgDelay tr):
      ∃ C: Finset Proc,
        ∃ i: ℕ, ∀ k: ℕ,
          C ⊆ (tr 0).s.all ∧ (tr (i + k)).s.crashed = C := by
  -- We could apply the fixpoint theorem to prove this,
  -- but I have not found a good instance of it in Mathlib4 yet.
  sorry

lemma eventually_alive_is_empty
    (tr: Trace Proc)
    (h_is_fair_run: is_fair_run Proc InitDelay GST MsgDelay tr)
    (p: Proc)
    (h_p_never_crashes: never_crashes tr p) (i: ℕ)
    (h_i_positive: i > 0):
      ∃ k: ℕ, (tr (i + k)).s.alive[p]! = ∅ := by
  rcases h_is_fair_run with
    ⟨ h_is_run, h_is_rel_comm, h_is_fair_to, h_is_fair_clock ⟩
  unfold is_fair_timeout at h_is_fair_to
  specialize h_is_fair_to i p
  rcases h_is_fair_to with ⟨ j, h_j_clock_ge ⟩
  -- this is the point when `p` triggers next timeout
  specialize h_p_never_crashes (i + j - 1)
  simp [h_p_never_crashes] at h_j_clock_ge
  rcases h_j_clock_ge with ⟨ h_timeout, h_clock_at_timeout ⟩
  unfold is_run at h_is_run
  rcases h_is_run with ⟨ _, h_is_path ⟩
  unfold is_path at h_is_path
  specialize h_is_path (i + j - 1)
  have h_dec_inc: i + j - 1 + 1 = i + j := by omega
  rw [h_dec_inc, h_timeout] at h_is_path
  unfold next_a at h_is_path
  simp at h_is_path
  unfold timeout at h_is_path
  -- extract the update of the set `alive[p]!`
  rcases h_is_path with ⟨ _, _, _, _, _, h_alive_updated, _ ⟩
  have h_alive_is_empty: (tr (i + j)).s.alive[p]! = ∅ := by
    simp [h_alive_updated]
  exact ⟨ j, h_alive_is_empty ⟩

/-- An auxilliary lemma to get rid of the annoying case of i = 0. -/
lemma when_clock_is_positive_step_is_non_init
    (tr: Trace Proc)
    (h_is_fair_run: is_fair_run Proc InitDelay GST MsgDelay tr)
    (i: ℕ) (h_clock_is_positive: (tr i).s.clock > 0):
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
  Show that no sent message has a timestamp in the future, that is,
  `[](∀ m ∈ sent, m.timestamp ≤ s.clock)`.

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
    unfold next_a at h_next;
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

    | Crash _ =>
      -- `s'.sent = s.sent` and `s'.clock = s.clock`, so we apply `h_s`
      simp [h] at h_next
      unfold crash at h_next
      have h_keep_sent: s'.sent = s.sent := by simp [h_next]
      have h_keep_clock: s'.clock = s.clock := by simp [h_next]
      rw [h_keep_sent] at h_m_in_sent; rw [h_keep_clock]
      simp [h_m_in_sent]
      at h_s; exact h_s

    | RcvHeartbeatReply _ _ _ =>
      -- `s'.sent = s.sent` and `s'.clock = s.clock`, so we apply `h_s`
      simp [h] at h_next
      unfold rcv_heartbeat_reply at h_next
      have h_keep_sent: s'.sent = s.sent := by simp [h_next]
      have h_keep_clock: s'.clock = s.clock := by simp [h_next]
      rw [h_keep_sent] at h_m_in_sent; rw [h_keep_clock]
      simp [h_m_in_sent]
      at h_s; exact h_s

    | Timeout p =>
      -- `s'.sent = s.sent ∪ newSent`. Show that `m ∈ newSent` satisfy `P`.
      simp [h] at h_next; unfold timeout at h_next
      have h_keep_clock: s'.clock = s.clock := by simp [h_next]
      let newSent := Finset.image (fun q => {
          kind := MsgTag.HeartbeatRequest, src := p, dst := q,
          timestamp := s.clock : Msg Proc
        }) s.all
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
        kind := MsgTag.HeartbeatReply, src := src,
        dst := dst, timestamp := s.clock : Msg Proc
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

lemma crashed_process_does_not_send
    (tr: Trace Proc)
    (h_is_fair_run: is_fair_run Proc InitDelay GST MsgDelay tr)
    (p: Proc) (k: ℕ) (h_p_crashed: p ∈ (tr k).s.crashed):
      ∀ i: ℕ,
        ∀ m ∈ (tr (i + k)).s.sent,
          m.src = p → m.timestamp ≤ (tr k).s.clock := by
  intros i m h_m_in_sent h_src
  -- By monotonicity, p ∈ crashed at all times ≥ k
  have h_p_crashed_later : ∀ j, p ∈ (tr (k + j)).s.crashed :=
    fun j => crashed_is_monotonic_in_fair_run InitDelay GST MsgDelay tr h_is_fair_run p k h_p_crashed j
  -- Consider when m was added to sent: it must have been sent by p before it crashed
  -- But after k, p is crashed and cannot send
  -- So m must have been sent at or before time k
  -- Let's show that for any message m with src = p in (tr (i + k)).s.sent, its timestamp ≤ (tr k).s.clock
  -- We proceed by induction on i
  induction i with
  | zero =>
    -- Base case: i = 0, so time = k
    -- At time k, p just crashed, so any message from p in sent must have timestamp ≤ (tr k).s.clock
    -- But p cannot send at time k or later, so any such m must have timestamp ≤ (tr k).s.clock
    -- (If the protocol allows sending at the instant of crashing, then timestamp = (tr k).s.clock is possible)
    -- So the claim holds
    exact le_rfl
  | succ i ih =>
    -- Inductive step: assume the claim holds for i, show for i + 1
    -- Consider m ∈ (tr (k + i + 1)).s.sent with m.src = p
    -- By protocol, sent can only grow by messages sent in this step
    -- So either m ∈ (tr (k + i)).s.sent, or m was added at step (k + i + 1)
    let s := (tr (k + i)).s
    let s' := (tr (k + i + 1)).s
    let a := (tr (k + i + 1)).a
    have h_path : next_a Proc InitDelay GST MsgDelay s s' a :=
      by
        unfold is_fair_run at h_is_fair_run
        rcases h_is_fair_run with ⟨ h_is_run, _ ⟩
        unfold is_run at h_is_run
        rcases h_is_run with ⟨ _, h_is_path ⟩
        unfold is_path at h_is_path
        exact h_is_path (k + i)
    have h_p_crashed_now := h_p_crashed_later (i + 1)
    -- For any m ∈ s'.sent with m.src = p, m ∈ s.sent
    have h_sent_subset : ∀ m, m ∈ s'.sent ∧ m.src = p → m ∈ s.sent :=
      by
        intro m ⟨h_in, h_src⟩
        cases a with
        | Init | AdvanceClock | Timeout _ | Crash _ | RcvHeartbeatRequest _ _ _ | RcvHeartbeatReply _ _ _ =>
          exact h_in
    exact ih m (h_sent_subset m ⟨h_m_in_sent, h_src⟩) h_src

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
      rcases h_is_fair_run with ⟨ h_is_run, _, _, _ ⟩
      unfold is_run at h_is_run
      rcases h_is_run with ⟨ _, h_is_path ⟩
      unfold is_path at h_is_path
      specialize h_is_path (at_magic_time + at_alive_empty + k)
      have h_indices: at_magic_time + at_alive_empty + k + 1 =
        at_magic_time + at_alive_empty + (k + 1) := by omega
      rw [h_indices] at h_is_path
      -- assume that it does not hold at some point `k + 1`
      by_contra h_contra
      unfold next_a at h_is_path
      -- introduce shortcuts, so we don't get lost
      let s := (tr (at_magic_time + at_alive_empty + k)).s
      let s' := (tr (at_magic_time + at_alive_empty + (k + 1))).s
      let a := (tr (at_magic_time + at_alive_empty + (k + 1))).a
      have h_s: s = (tr (at_magic_time + at_alive_empty + k)).s := by rfl
      have h_s': s' = (tr (at_magic_time + at_alive_empty + (k + 1))).s := by rfl
      have h_a: a = (tr (at_magic_time + at_alive_empty + (k + 1))).a := by rfl
      rw  [← h_s, ← h_s', ← h_a] at h_is_path
      rw [← h_s] at ih
      rw [← h_s'] at h_contra
      -- do case analysis on `a`
      cases h: a
      case Init =>
        simp [h] at h_is_path
        simp [h_is_path, ih] at h_contra
      case AdvanceClock =>
        simp [h] at h_is_path
        unfold advance_clock at h_is_path
        have h_eq: s'.alive = s.alive := by simp [h_is_path]
        rw [h_eq] at h_contra
        simp [ih] at h_contra
      case RcvHeartbeatRequest _ _ _ =>
        simp [h] at h_is_path
        unfold rcv_heartbeat_request at h_is_path
        have h_eq: s'.alive = s.alive := by simp [h_is_path]
        simp [h_eq, ih] at h_contra
      case Crash _ =>
        simp [h] at h_is_path
        unfold crash at h_is_path
        have h_eq: s'.alive = s.alive := by simp [h_is_path]
        simp [h_eq, ih] at h_contra
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
            sorry
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
 A simpler-to-prove property that implies `is_strongly_complete`.
 TODO: prove the implication!
 -/
def is_strongly_complete_simpler (tr: Trace Proc)
    (p: Proc) (q: Proc): Prop :=
  (∀ i: ℕ, p ∉ (tr i).s.crashed)
    → ∃ j: ℕ, ∀ k: ℕ,
        q ∈ (tr j).s.crashed → q ∈ (tr (j + k)).s.suspected[p]!

/-- Strong completeness hold for every run. -/
theorem strong_completeness (tr: Trace Proc)
    (h_all: ∀ p: Proc, p ∈ (tr 0).s.all)
    (h_is_fair_run: is_fair_run Proc InitDelay GST MsgDelay tr)
    (p: Proc) (q: Proc):
      (is_strongly_complete_simpler tr p q) := by
  unfold is_fair_run at h_is_fair_run; unfold is_strongly_complete_simpler
  rcases h_is_fair_run with ⟨ h_is_run, h_is_rel_comm, h_is_fair_to, h_is_fair_clock ⟩
  intro h_p_is_correct
  sorry

/-
/-- Strong completeness hold for every run. -/
theorem eventual_strong_accuracy (tr: Trace Proc)
    (h_all: ∀ p: Proc, p ∈ (tr 0).s.all)
    (h_is_fair_run: is_fair_run Proc InitDelay GST MsgDelay run):
      (is_eventually_strongly_accurate tr) := by
  sorry
-/
