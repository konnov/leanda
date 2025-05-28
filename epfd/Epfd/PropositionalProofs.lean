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

/--
  A single step does not decrease the clock value.
  -/
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

/--
  A single step does not decrease the set of the crashed processes.
  -/
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

    have h_jj: j - 1 + 1 = j := by omega;
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
