/-
Proving the properties of eventually perfect failure detector.

Copyright (c) 2025 Igor Konnov
Released under MIT license as described in the file LICENSE.
Authors: Igor Konnov, 2025
-/

import Epfd.Propositional

import Mathlib.Tactic.Linarith

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
    -- apply next_does_not_decrease_clock to the last step
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

/--
  For every fair run, if `p` never crashes and `q` does,
  then `p` never registers `q` as alive from some point on.
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
  -- We jump to the point when `q` crashes and the pre-GST heartbeats stop arriving.
  let beyond_gst := max (GST + MsgDelay + 1) (at_q_crashed + MsgDelay + 1)
  -- eventually, `alive[p]!` becomes empty, we start with `beyond_gst`
  have h_alive_is_empty :=
    eventually_alive_is_empty InitDelay GST MsgDelay
      tr h_is_fair_run p h_p_never_crashes beyond_gst
  have h_positive: beyond_gst > 0 := by unfold beyond_gst; omega
  simp [h_positive] at h_alive_is_empty
  rcases h_alive_is_empty with ⟨ at_alive_empty, h_alive_empty ⟩
  -- At this timepoint we have:
  --   (1) `alive[p]! = ∅`,
  --   (2) no pre-GST heartbeats from `q` can arrive
  --   (3) `q` has crashed and no heartbeats from the previous timeout can arrive.
  sorry

/--
 A simpler-to-prove property that implies `is_strongly_complete`.
 TODO: prove the implication!
 -/
def is_strongly_complete_simpler (tr: Trace Proc)
    (p: Proc) (q: Proc): Prop :=
  (∀ i: ℕ, p ∉ (tr i).s.crashed)
    → ∃ j: ℕ, ∀ k: ℕ,
        k ≥ j ∧ q ∈ (tr j).s.crashed → q ∈ (tr k).s.suspected[p]!

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
