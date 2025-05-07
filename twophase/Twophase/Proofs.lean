/-
A proof of consistency via inductive invariant.

Reusing the old inductive invariant from the first versions of Apalache:

https://github.com/apalache-mc/apalache-tests/blob/1b76b8e70549f6cd71a758b4014e7f7682d7fd44/performance/two-phase/APATwoPhase.tla#L219-L252

Copyright (c) 2025 Igor Konnov
Released under MIT license as described in the file LICENSE.
Authors: Igor Konnov, 2025
-/

import Twophase.Propositional
import Mathlib.Data.Finset.Basic
import Std.Data.HashMap.Lemmas

-- The abstract type of resource managers.
variable { RM : Type } [DecidableEq RM] [Hashable RM]

-- Lemmas that we found with TLC in ca. 2018. Perhaps, they are not the best ones.

def lemma1 (s: ProtocolState RM): Prop :=
  (∃ rm: RM, s.rmState[rm]? = some RMState.Committed) → s.tmState = TMState.Committed

def lemma2 (s: ProtocolState RM) : Prop :=
  s.tmState = TMState.Committed →
      s.tmPrepared = s.all
    ∧ Message.Commit ∈ s.msgs
    ∧ ∀ rm: RM, let rs: Option RMState := s.rmState[rm]?
      rs ≠ some RMState.Working ∧ rs ≠ some RMState.Aborted

def lemma3 (s: ProtocolState RM) : Prop :=
  s.tmState = TMState.Aborted → Message.Abort ∈ s.msgs

def lemma4 (s: ProtocolState RM) : Prop :=
  ∀ rm: RM,
    let rs := s.rmState[rm]?;
      (rm ∈ s.tmPrepared → rs ≠ some RMState.Working ∧ Message.Prepared rm ∈ s.msgs)
    ∧ (rs = some RMState.Working → Message.Prepared rm ∉ s.msgs)
    ∧ (Message.Prepared rm ∈ s.msgs → rs ≠ some RMState.Working)
    ∧ (rs = some RMState.Aborted → (Message.Abort ∈ s.msgs ∨ Message.Prepared rm ∉ s.msgs))

def lemma5 (s: ProtocolState RM) : Prop :=
  Message.Abort ∈ s.msgs →
    (s.tmState = TMState.Aborted
      ∨ ∃ rm: RM,
          s.rmState[rm]? = some RMState.Aborted
        ∧ rm ∉ s.tmPrepared
        ∧ Message.Prepared rm ∉ s.msgs)

def lemma6 (s: ProtocolState RM) : Prop :=
  Message.Commit ∈ s.msgs →
    s.tmPrepared = s.all
      ∧ (s.tmState = TMState.Committed
        ∨ ∃ rm: RM, s.rmState[rm]? = some RMState.Committed)

def invariant (s: ProtocolState RM) : Prop :=
  lemma1 s ∧ lemma2 s ∧ lemma3 s ∧ lemma4 s ∧ lemma5 s ∧ lemma6 s

-- Proving the inductive step
-- We need to prove that the inductive invariant is preserved by the transition function.

-- Effort: 10m
lemma invariant_is_inductive_tm_commit_lemma1 (s: ProtocolState RM) (s': ProtocolState RM)
  (h_tm_commit: tm_commit s s'):
    lemma1 s' := by
    unfold lemma1
    intro h_committed
    exact show s'.tmState = TMState.Committed by
      unfold tm_commit at h_tm_commit
      simp [h_tm_commit]

-- Effort: 25m
lemma invariant_is_inductive_tm_abort_lemma1 (s: ProtocolState RM) (s': ProtocolState RM)
  (h_inv: invariant s) (h_tm_abort: tm_abort s s'): lemma1 s' := by
    unfold lemma1
    unfold tm_abort at h_tm_abort
    have h_no_committed: ∀ rm: RM, s'.rmState[rm]? ≠ some RMState.Committed := by
      intro rm
      by_contra h_some_committed -- assume the opposite
      have h_unchanged_rm_state : s'.rmState = s.rmState := by simp [h_tm_abort]
      simp [h_unchanged_rm_state] at h_some_committed
      have h_tm_committed: s.tmState = TMState.Committed := by
        unfold invariant at h_inv
        rcases h_inv with ⟨h_lemma1, _, _, _, _, _⟩
        unfold lemma1 at h_lemma1
        have h_ex_committed: ∃ rm: RM, s.rmState[rm]? = some RMState.Committed := by exists rm
        simp [h_ex_committed] at h_lemma1
        exact h_lemma1
      -- s.tmState = TMState.Committed contradicts s.tmState = TMState.Init
      have h_tm_init: s.tmState = TMState.Init := by simp [h_tm_abort]
      -- prove the contradiction
      simp [h_tm_init] at h_tm_committed
    simp [h_no_committed]

-- Effort: 20m
lemma invariant_is_inductive_tm_receive_prepared_lemma1 (s: ProtocolState RM) (s': ProtocolState RM)
  (rm: RM) (h_inv: invariant s) (h_tm_rcv_prepared: tm_rcv_prepared s s' rm): lemma1 s' := by
    unfold lemma1
    unfold tm_rcv_prepared at h_tm_rcv_prepared
    have h_tm_state_init: s.tmState = TMState.Init := by simp [h_tm_rcv_prepared]
    have h_tm_state_not_committed: s'.tmState ≠ TMState.Committed := by
      have h_unchanged_tm_state: s'.tmState = s.tmState := by simp [h_tm_rcv_prepared]
      simp [h_unchanged_tm_state, h_tm_state_init]
    simp [h_tm_state_not_committed]
    intro rm
    by_contra h_some_committed -- assume the opposite
    have h_unchanged_rm_state: s'.rmState = s.rmState := by simp [h_tm_rcv_prepared]
    simp [h_unchanged_rm_state] at h_some_committed
    rcases h_inv with ⟨h_lemma1_s, _, _, _, _, _⟩
    unfold lemma1 at h_lemma1_s
    have h_ex_committed: ∃ rm: RM, s.rmState[rm]? = some RMState.Committed := by exists rm
    simp [h_ex_committed] at h_lemma1_s
    simp [h_tm_state_init] at h_lemma1_s

-- Effort: 1h
lemma invariant_is_inductive_rm_prepare_lemma1 (s: ProtocolState RM) (s': ProtocolState RM)
  (rm: RM) (h_inv: invariant s) (h_rm_prepare: rm_prepare s s' rm): lemma1 s' := by
    unfold lemma1
    unfold rm_prepare at h_rm_prepare
    rcases h_inv with ⟨h_lemma1_s, _, _, _, _, _⟩
    unfold lemma1 at h_lemma1_s
    by_cases h_some_committed: ∃ rm: RM, s.rmState[rm]? = some RMState.Committed
    case neg =>
      simp [*] at h_some_committed
      have h_all_not_committed: ∀ (x : RM), s'.rmState[x]? ≠ some RMState.Committed := by
        intro rm₂
        have h_rm_state: s'.rmState = s.rmState.insert rm RMState.Prepared := by
          simp [h_rm_prepare]
        simp [h_rm_state]
        simp [Std.HashMap.getElem?_insert]
        specialize h_some_committed rm₂
        split
        . simp
        . simp [h_some_committed]
      simp [h_all_not_committed]

    case pos =>
      rcases h_some_committed with ⟨rm₂, h_rm2_committed⟩
      have h_rm2_neq_rm : rm₂ ≠ rm := by
        by_contra h_contra -- assume the opposite
        have h_rm_state_working : s.rmState.get? rm = some RMState.Working := by
          rcases h_rm_prepare with ⟨h_rm_state, _⟩
          exact h_rm_state
        simp [h_contra] at h_rm2_committed
        simp [h_rm2_committed] at h_rm_state_working
      have h_rm_state_committed: s'.rmState.get? rm₂ = some RMState.Committed := by
        have h_rm_state: s'.rmState = s.rmState.insert rm RMState.Prepared :=
          by simp [h_rm_prepare]
        simp [h_rm_state]
        simp [Std.HashMap.getElem?_insert]
        have : rm ≠ rm₂ := by
          intro h_contra -- assume the opposite
          simp [h_contra] at h_rm2_neq_rm
        simp [this]
        exact h_rm2_committed

      have h_some_committed_pre: ∃ rm: RM, s.rmState[rm]? = some RMState.Committed := by use rm₂
      have h_some_committed_post: ∃ rm: RM, s'.rmState[rm]? = some RMState.Committed := by
        use rm₂; exact h_rm_state_committed
      simp [h_some_committed_pre] at h_lemma1_s
      have h_unchanged_tm_state: s'.tmState = s.tmState := by simp [h_rm_prepare]
      simp [h_some_committed_post, h_unchanged_tm_state, h_lemma1_s]

-- Effort: 30m
lemma invariant_is_inductive_rm_abort_lemma1 (s: ProtocolState RM) (s': ProtocolState RM)
  (rm: RM) (h_inv: invariant s) (h_rm_abort: rm_choose_to_abort s s' rm): lemma1 s' := by
    unfold lemma1
    unfold rm_choose_to_abort at h_rm_abort
    rcases h_inv with ⟨h_lemma1_s, h_lemma2_s, _, _, _, _⟩
    have h_unchanged_tm_state: s'.tmState = s.tmState := by simp [h_rm_abort]
    have h_tm_not_committed: s'.tmState ≠ TMState.Committed := by
      by_contra h_contra -- assume the opposite
      simp [h_unchanged_tm_state] at h_contra
      unfold lemma2 at h_lemma2_s
      simp [h_contra] at h_lemma2_s
      rcases h_lemma2_s with ⟨_, _, h_no_working⟩
      specialize h_no_working rm
      have h_rm_not_working: s.rmState[rm]? ≠ some RMState.Working := by simp [h_no_working]
      simp [h_rm_not_working] at h_rm_abort
    simp [h_tm_not_committed]
    intro rm₂
    by_cases h_rm2_eq_rm: rm = rm₂
    case pos =>
      rw [h_rm2_eq_rm] at h_rm_abort
      have h_rm2_aborted: s'.rmState[rm]? = some RMState.Aborted := by
        rcases h_rm_abort with ⟨_, h_rm2_aborted, _⟩
        simp [h_rm2_aborted]
        simp [Std.HashMap.getElem?_insert, h_rm2_eq_rm]
      simp [h_rm2_eq_rm] at h_rm2_aborted
      simp [h_rm2_aborted]

    case neg =>
      have h_rm2_state_unchanged: s'.rmState[rm₂]? = s.rmState[rm₂]? := by
        rcases h_rm_abort with ⟨_, h_rm_state_insert, _, _⟩
        simp [h_rm_state_insert]
        simp [Std.HashMap.getElem?_insert, h_rm2_eq_rm]
      simp [h_rm2_state_unchanged]
      have h_rm2_not_committed: s.rmState[rm₂]? ≠ RMState.Committed := by
        by_contra h_contra -- assume the opposite
        unfold lemma1 at h_lemma1_s
        have h_ex_committed: ∃ rm: RM, s.rmState[rm]? = some RMState.Committed := by use rm₂
        simp [h_ex_committed] at h_lemma1_s
        rw [← h_unchanged_tm_state] at h_lemma1_s
        simp [h_tm_not_committed] at h_lemma1_s
      exact h_rm2_not_committed

-- Effort: 3.5h
lemma invariant_is_inductive_tm_commit_lemma2 (s: ProtocolState RM) (s': ProtocolState RM)
  (h_all: ∀ rm: RM, rm ∈ s.all) (h_inv: invariant s) (h_tm_commit: tm_commit s s'):
    lemma2 s' := by
    unfold lemma2
    intro h_committed
    unfold tm_commit at h_tm_commit
    have h_tm_prepared: s'.tmPrepared = s'.all := by
      have h₁: s'.tmPrepared = s.tmPrepared := by simp [h_tm_commit]
      have h₂: s.tmPrepared = s.all := by simp [h_tm_commit]
      have h₃: s'.all = s.all := by simp [h_tm_commit]
      rw [h₁, h₂, h₃]
    have h_commit_msg: Message.Commit ∈ s'.msgs := by simp [h_tm_commit]
    simp [h_tm_prepared, h_commit_msg, h_tm_commit]
    unfold invariant at h_inv
    have h_lemma4_s: lemma4 s := by simp [h_inv]
    unfold lemma4 at h_lemma4_s
    intro rm -- ∀ rm: RM
    specialize h_lemma4_s rm
    have h_rm_in_prepared: rm ∈ s.tmPrepared := by simp [h_tm_commit, h_all]
    apply And.intro
    . exact show ¬s.rmState[rm]? = some RMState.Working by
        exact (h_lemma4_s.left h_rm_in_prepared).left
    . exact show ¬s.rmState[rm]? = some RMState.Aborted by
        by_contra h_contra -- assume the opposite
        have h_two_cases: Message.Abort ∈ s.msgs ∨ Message.Prepared rm ∉ s.msgs := by
          rcases h_lemma4_s with ⟨_, _, _, h⟩
          exact (h h_contra)
        cases h_two_cases
        case inl h_abort_in_msgs =>
          unfold lemma5 at h_inv
          rcases h_inv with ⟨_, _, _, _, lemma5_s, _⟩
          cases lemma5_s h_abort_in_msgs
          case inl h_tm_state_aborted =>
            -- s.tmState = TMState.Aborted contradicts s.tmState = TMState.Committed
            simp [h_tm_state_aborted] at h_tm_commit

          case inr h =>
            rcases h with ⟨rm₂, _, h_rm2_notin_prepared, _⟩
            have h_rm2_in_prepared: rm₂ ∈ s.tmPrepared := by simp [h_tm_commit, h_all]
            apply h_rm2_notin_prepared at h_rm2_in_prepared -- contradiction
            exact h_rm2_in_prepared

        case inr h_prepared_notin_msgs =>
          have : Message.Prepared rm ∈ s.msgs := by
            exact (h_lemma4_s.left h_rm_in_prepared).right
          apply h_prepared_notin_msgs at this -- contradiction
          exact this

-- Effort: 2m
lemma invariant_is_inductive_tm_abort_lemma2 (s: ProtocolState RM) (s': ProtocolState RM)
  (h_tm_abort: tm_abort s s'): lemma2 s' := by
    unfold lemma2
    unfold tm_abort at h_tm_abort
    have h_tm_state_aborted : s'.tmState = TMState.Aborted := by simp [h_tm_abort]
    simp [h_tm_abort]

-- Effort: 2m
lemma invariant_is_inductive_tm_receive_prepared_lemma2 (s: ProtocolState RM) (s': ProtocolState RM)
  (rm: RM) (h_tm_rcv_prepared: tm_rcv_prepared s s' rm): lemma2 s' := by
    unfold lemma2
    unfold tm_rcv_prepared at h_tm_rcv_prepared
    have h_tm_state_init: s.tmState = TMState.Init := by simp [h_tm_rcv_prepared]
    have h_tm_state_not_committed: s'.tmState ≠ TMState.Committed := by
      have h_unchanged_tm_state: s'.tmState = s.tmState := by simp [h_tm_rcv_prepared]
      simp [h_unchanged_tm_state, h_tm_state_init]
    simp [h_tm_state_not_committed]

-- Effort: 30m
lemma invariant_is_inductive_rm_prepare_lemma2 (s: ProtocolState RM) (s': ProtocolState RM)
  (rm: RM) (h_inv: invariant s) (h_rm_prepare: rm_prepare s s' rm): lemma2 s' := by
    unfold lemma2
    unfold rm_prepare at h_rm_prepare
    have h_unchanged_tm_state: s'.tmState = s.tmState := by simp [h_rm_prepare]
    have h_unchanged_tm_prepared: s'.tmPrepared = s.tmPrepared := by simp [h_rm_prepare]
    have h_unchanged_all: s'.all = s.all := by simp [h_rm_prepare]
    simp [h_unchanged_tm_state, h_unchanged_tm_prepared, h_rm_prepare]
    rcases h_inv with ⟨_, h_lemma2_s, _, _, _, _⟩
    unfold lemma2 at h_lemma2_s
    by_cases h_committed: s.tmState = TMState.Committed
    case neg =>
      simp [h_committed]

    case pos =>
      simp [h_committed] at h_lemma2_s
      rcases h_lemma2_s with ⟨h_tm_prepared_eq_all, h_commit_msg, h_no_working⟩
      simp [h_committed, h_tm_prepared_eq_all, h_commit_msg]
      intro rm₂ -- ∀ rm: RM
      by_cases h_rm2_eq_rm: rm = rm₂
      case pos => -- rm = rm₂
        simp [h_rm2_eq_rm]

      case neg => -- rm ≠ rm₂
        simp [Std.HashMap.getElem?_insert]
        have : rm ≠ rm₂ := by intro h_contra; simp [h_contra] at h_rm2_eq_rm
        simp [h_rm2_eq_rm]
        specialize h_no_working rm₂
        exact h_no_working

-- Effort: 10m
lemma invariant_is_inductive_rm_abort_lemma2 (s: ProtocolState RM) (s': ProtocolState RM)
  (rm: RM) (h_inv: invariant s) (h_rm_abort: rm_choose_to_abort s s' rm): lemma2 s' := by
    unfold lemma2
    unfold rm_choose_to_abort at h_rm_abort
    have h_unchanged_tm_state: s'.tmState = s.tmState := by simp [h_rm_abort]
    simp [h_unchanged_tm_state]
    have h_tm_not_committed: s.tmState ≠ TMState.Committed := by
      by_contra h_tm_committed -- assume the opposite
      rcases h_inv with ⟨_, h_lemma2_s, _, _, _, _⟩
      unfold lemma2 at h_lemma2_s
      simp [h_tm_committed] at h_lemma2_s
      rcases h_lemma2_s with ⟨_, _, h_no_working⟩
      specialize h_no_working rm
      have h_rm_working: s.rmState[rm]? = some RMState.Working := by
        rcases h_rm_abort with ⟨h_rm_is_working, _⟩
        exact h_rm_is_working
      simp [h_rm_working] at h_no_working
    simp [h_tm_not_committed]

-- Effort: 5m
lemma invariant_is_inductive_tm_commit_lemma3 (s: ProtocolState RM) (s': ProtocolState RM)
  (h_tm_commit: tm_commit s s'):
      lemma3 s' := by
    unfold lemma3
    unfold tm_commit at h_tm_commit
    have : s'.tmState = TMState.Committed := by simp [h_tm_commit]
    simp [this]

-- Effort: 3m
lemma invariant_is_inductive_tm_abort_lemma3 (s: ProtocolState RM) (s': ProtocolState RM)
  (h_tm_abort: tm_abort s s'): lemma3 s' := by
    unfold lemma3
    unfold tm_abort at h_tm_abort
    have : s'.tmState = TMState.Aborted := by simp [h_tm_abort]
    simp [this]
    have : Message.Abort ∈ s'.msgs := by simp [h_tm_abort]
    assumption

-- Effort: 2m
lemma invariant_is_inductive_tm_receive_prepared_lemma3 (s: ProtocolState RM) (s': ProtocolState RM)
  (rm: RM) (h_tm_rcv_prepared: tm_rcv_prepared s s' rm): lemma3 s' := by
    unfold lemma3
    unfold tm_rcv_prepared at h_tm_rcv_prepared
    have h_tm_state_init: s.tmState = TMState.Init := by simp [h_tm_rcv_prepared]
    have h_tm_state_not_committed: s'.tmState ≠ TMState.Aborted := by
      have h_unchanged_tm_state: s'.tmState = s.tmState := by simp [h_tm_rcv_prepared]
      simp [h_unchanged_tm_state, h_tm_state_init]
    simp [h_tm_state_not_committed]

-- Effort: 5m
lemma invariant_is_inductive_rm_prepare_lemma3 (s: ProtocolState RM) (s': ProtocolState RM)
  (rm: RM) (h_inv: invariant s) (h_rm_prepare: rm_prepare s s' rm): lemma3 s' := by
    unfold lemma3
    unfold rm_prepare at h_rm_prepare
    have h_unchanged_tm_state: s'.tmState = s.tmState := by simp [h_rm_prepare]
    have h_abort: Message.Abort ∈ s'.msgs ↔ Message.Abort ∈ s.msgs := by
      have : s'.msgs = s.msgs ∪ {Message.Prepared rm} := by simp [h_rm_prepare]
      simp [this]
    simp [h_unchanged_tm_state, h_abort]
    rcases h_inv with ⟨_, _, h_lemma3_s, _, _, _⟩
    unfold lemma3 at h_lemma3_s
    exact h_lemma3_s

-- Effort: 45m
lemma invariant_is_inductive_tm_commit_lemma4 (s: ProtocolState RM) (s': ProtocolState RM)
  (h_inv: invariant s) (h_tm_commit: tm_commit s s'): lemma4 s' := by
    unfold lemma4
    unfold tm_commit at h_tm_commit
    unfold invariant at h_inv
    intro rm -- ∀ rm: RM
    have h_unchanged_rm_state : s'.rmState = s.rmState := by simp [h_tm_commit]
    have h_msgs': s'.msgs = s.msgs ∪ {Message.Commit} := by simp [h_tm_commit]
    have h_unchanged_tm_prepared: s'.tmPrepared = s.tmPrepared := by simp [h_tm_commit]
    rcases h_inv with ⟨_, _, _, h_lemma4_s, _, _⟩
    unfold lemma4 at h_lemma4_s
    specialize h_lemma4_s rm
    simp [h_unchanged_rm_state, h_msgs', h_unchanged_tm_prepared]
    exact h_lemma4_s

-- Effort: 15m
lemma invariant_is_inductive_tm_abort_lemma4 (s: ProtocolState RM) (s': ProtocolState RM)
  (h_inv: invariant s) (h_tm_abort: tm_abort s s'): lemma4 s' := by
    unfold lemma4
    unfold tm_abort at h_tm_abort
    have h_unchanged_rm_state : s'.rmState = s.rmState := by simp [h_tm_abort]
    have h_unchanged_tm_prepared: s'.tmPrepared = s.tmPrepared := by simp [h_tm_abort]
    have h_msgs': s'.msgs = s.msgs ∪ {Message.Abort} := by simp [h_tm_abort]
    simp [h_unchanged_rm_state, h_unchanged_tm_prepared, h_msgs']
    unfold invariant at h_inv
    rcases h_inv with ⟨_, _, _, h_lemma4_s, _, _⟩
    unfold lemma4 at h_lemma4_s
    intro rm -- ∀ rm: RM
    specialize h_lemma4_s rm
    simp [*] at h_lemma4_s
    rcases h_lemma4_s with ⟨h_when_tm_prepared, h_no_prepared_in_msgs, h_not_working, _⟩
    apply And.intro
    . exact h_when_tm_prepared
    . apply And.intro
      . exact h_no_prepared_in_msgs
      . exact h_not_working

-- Effort: 1h
lemma invariant_is_inductive_tm_receive_prepared_lemma4 (s: ProtocolState RM) (s': ProtocolState RM)
  (rm: RM) (h_inv: invariant s) (h_tm_rcv_prepared: tm_rcv_prepared s s' rm): lemma4 s' := by
    unfold lemma4
    unfold tm_rcv_prepared at h_tm_rcv_prepared
    unfold invariant at h_inv
    rcases h_inv with ⟨_, _, _, h_lemma4_s, _, _⟩
    unfold lemma4 at h_lemma4_s
    intro rm' -- ∀ rm: RM
    by_cases equal: rm' = rm
    . simp [equal, h_tm_rcv_prepared]
      specialize h_lemma4_s rm
      rcases h_lemma4_s with ⟨_, h_rm_is_working, _, h_rm_is_aborted⟩
      apply And.intro
      . by_contra h_contra -- assume the opposite
        simp [h_contra] at h_rm_is_working
        simp [h_rm_is_working] at h_tm_rcv_prepared
      . have h_prepared_in_msgs: Message.Prepared rm ∈ s.msgs := by simp [h_tm_rcv_prepared]
        simp [h_prepared_in_msgs] at h_rm_is_aborted
        exact h_rm_is_aborted
    . apply And.intro
      . intro h_rm_prime_in_prepared
        have h: s'.tmPrepared = s.tmPrepared ∪ {rm} := by simp [h_tm_rcv_prepared]
        simp [h, equal] at h_rm_prime_in_prepared
        have h_unchanged_msgs: s'.msgs = s.msgs := by simp [h_tm_rcv_prepared]
        have h_unchanged_rm_state: s'.rmState = s.rmState := by simp [h_tm_rcv_prepared]
        simp [h_unchanged_msgs, h_unchanged_rm_state]
        specialize h_lemma4_s rm'
        rcases h_lemma4_s with ⟨h_when_tm_prepared, _, _, _⟩
        simp [h_rm_prime_in_prepared] at h_when_tm_prepared
        exact h_when_tm_prepared
      . have h_unchanged_msgs: s'.msgs = s.msgs := by simp [h_tm_rcv_prepared]
        have h_unchanged_rm_state: s'.rmState = s.rmState := by simp [h_tm_rcv_prepared]
        simp [h_unchanged_msgs, h_unchanged_rm_state, equal]
        specialize h_lemma4_s rm'
        rcases h_lemma4_s with ⟨_, h_rm_is_working, h_prepared_in_msgs, h_rm_is_aborted⟩
        apply And.intro
        . exact h_rm_is_working
        . apply And.intro
          . exact h_prepared_in_msgs
          . exact h_rm_is_aborted

-- Effort: 1h
lemma invariant_is_inductive_rm_prepare_lemma4 (s: ProtocolState RM) (s': ProtocolState RM)
  (rm: RM) (h_inv: invariant s) (h_rm_prepare: rm_prepare s s' rm): lemma4 s' := by
    unfold lemma4
    unfold rm_prepare at h_rm_prepare
    intro rm' -- ∀ rm: RM
    by_cases h_eq: rm = rm'
    case pos =>
      rw [← h_eq]
      have h_rm_prepared: s'.rmState[rm]? = some RMState.Prepared := by simp [h_rm_prepare]
      have h_rm_not_working: s'.rmState[rm]? ≠ some RMState.Working := by
        by_contra h_contra -- assume the opposite
        rw [h_contra] at h_rm_prepared
        injection h_rm_prepared with h_val_eq
        injection h_val_eq
      have h_rm_not_aborted: s'.rmState[rm]? ≠ some RMState.Aborted := by
        by_contra h_contra -- assume the opposite
        rw [h_contra] at h_rm_prepared
        injection h_rm_prepared with h_val_eq
        injection h_val_eq
      have h_prepared_in_msgs: Message.Prepared rm ∈ s'.msgs := by simp [h_rm_prepare]
      simp [h_rm_not_working, h_rm_not_aborted, h_prepared_in_msgs]

    case neg =>
      -- replace s' with s
      have h_unchanged_rm_state: s'.rmState[rm']? = s.rmState[rm']? := by
        rcases h_rm_prepare with ⟨_, h_update_rm_state, _⟩
        simp [h_update_rm_state, Std.HashMap.getElem?_insert, h_eq]
      have h_tm_prepared: s'.tmPrepared = s.tmPrepared := by simp [h_rm_prepare]
      have h_prepared_in_msgs: Message.Prepared rm' ∈ s'.msgs ↔ Message.Prepared rm' ∈ s.msgs := by
        have h_neq: ¬rm' = rm := by
          intro h_contra -- assume the opposite
          simp [h_contra] at h_eq
        simp [h_rm_prepare, h_neq]
      have h_abort_in_msgs: Message.Abort ∈ s'.msgs ↔ Message.Abort ∈ s.msgs := by
        simp [h_rm_prepare]
      simp [h_unchanged_rm_state, h_tm_prepared, h_prepared_in_msgs, h_abort_in_msgs]
      -- now we can apply the invariant
      rcases h_inv with ⟨_, _, _, h_lemma4_s, _, _⟩
      unfold lemma4 at h_lemma4_s
      specialize h_lemma4_s rm'
      exact h_lemma4_s

-- Effort: 25m
lemma invariant_is_inductive_tm_commit_lemma5 (s: ProtocolState RM) (s': ProtocolState RM)
  (h_all: ∀ rm: RM, rm ∈ s.all) (h_inv: invariant s) (h_tm_commit: tm_commit s s'): lemma5 s' := by
    unfold lemma5
    unfold tm_commit at h_tm_commit
    unfold invariant at h_inv
    have h_msgs': s'.msgs = s.msgs ∪ {Message.Commit} := by simp [h_tm_commit]
    simp [h_msgs']
    have : Message.Abort ∉ s.msgs := by
      by_contra h_contra -- assume the opposite
      -- apply lemma5 to s
      have h_two_cases: s.tmState = TMState.Aborted
          ∨ ∃ rm: RM,
                s.rmState[rm]? = some RMState.Aborted
              ∧ rm ∉ s.tmPrepared
              ∧ Message.Prepared rm ∉ s.msgs
          := by
        rcases h_inv with ⟨_, _, _, _, lemma5_s, _⟩
        exact lemma5_s h_contra
      -- TODO: we have pretty much the same proof block as in invariant_is_inductive_tm_commit_lemma2
      cases h_two_cases
      case inl h_tm_state_aborted =>
        -- s.tmState = TMState.Aborted contradicts s.tmState = TMState.Committed
        simp [h_tm_state_aborted] at h_tm_commit
      case inr h =>
        rcases h with ⟨rm₂, _, h_rm2_notin_prepared, _⟩
        have h_rm2_in_prepared: rm₂ ∈ s.tmPrepared := by simp [h_tm_commit, h_all]
        apply h_rm2_notin_prepared at h_rm2_in_prepared -- contradiction
        exact h_rm2_in_prepared
    simp [this]

-- Effort: 3m
lemma invariant_is_inductive_tm_abort_lemma5 (s: ProtocolState RM) (s': ProtocolState RM)
  (h_tm_abort: tm_abort s s'): lemma5 s' := by
    unfold lemma5
    unfold tm_abort at h_tm_abort
    have h_tm_state_aborted : s'.tmState = TMState.Aborted := by simp [h_tm_abort]
    simp [h_tm_state_aborted]

-- Effort: 1h
lemma invariant_is_inductive_tm_receive_prepared_lemma5 (s: ProtocolState RM) (s': ProtocolState RM)
  (rm: RM) (h_inv: invariant s) (h_tm_rcv_prepared: tm_rcv_prepared s s' rm): lemma5 s' := by
    unfold lemma5
    unfold tm_rcv_prepared at h_tm_rcv_prepared
    unfold invariant at h_inv
    have h_unchanged_msgs: s'.msgs = s.msgs := by simp [h_tm_rcv_prepared]
    have h_unchanged_tm_state: s'.tmState = s.tmState := by simp [h_tm_rcv_prepared]
    have h_rm_state: s'.rmState = s.rmState := by simp [h_tm_rcv_prepared]
    have h_tm_state_init: s.tmState = TMState.Init := by simp [h_tm_rcv_prepared]
    simp [h_unchanged_msgs, h_unchanged_tm_state, h_rm_state]
    rcases h_inv with ⟨_, _, _, _, h_lemma5_s, _⟩
    unfold lemma5 at h_lemma5_s
    simp [h_tm_state_init] at h_lemma5_s; simp [h_tm_state_init]
    by_cases h_abort: Message.Abort ∈ s.msgs
    case neg =>
      simp [h_abort]

    case pos =>
      simp [h_abort]; simp [h_abort] at h_lemma5_s
      rcases h_lemma5_s with ⟨rm₂, ⟨h_rm2_aborted, h_rm2_not_prepared, h_rm2_notin_msgs⟩⟩
      have h_rm_neq_rm: rm₂ ≠ rm := by
        by_contra h_contra -- assume the opposite
        have h_rm_prepared: Message.Prepared rm ∈ s.msgs := by simp [h_tm_rcv_prepared]
        rw [h_contra] at h_rm2_notin_msgs
        simp [h_rm_prepared] at h_rm2_notin_msgs
      have h_rm2_not_prepared: rm₂ ∉ s'.tmPrepared := by
        have h_tm_prepared: s'.tmPrepared = s.tmPrepared ∪ {rm}:= by simp [h_tm_rcv_prepared]
        by_contra h_contra -- assume the opposite
        simp [h_tm_prepared, h_rm_neq_rm] at h_contra
        simp [h_contra] at h_rm2_not_prepared
      exists rm₂

-- Effort: 1h
lemma invariant_is_inductive_rm_prepare_lemma5 (s: ProtocolState RM) (s': ProtocolState RM)
  (rm: RM) (h_inv: invariant s) (h_rm_prepare: rm_prepare s s' rm): lemma5 s' := by
    unfold lemma5
    unfold rm_prepare at h_rm_prepare
    have h_abort_in_msgs: Message.Abort ∈ s'.msgs ↔ Message.Abort ∈ s.msgs := by
      simp [h_rm_prepare]
    have h_unchanged_tm_state: s'.tmState = s.tmState := by simp [h_rm_prepare]
    simp [h_abort_in_msgs, h_unchanged_tm_state]
    rcases h_inv with ⟨_, _, _, _, h_lemma5_s, _⟩
    unfold lemma5 at h_lemma5_s
    by_cases h_abort: Message.Abort ∈ s.msgs
    case neg =>
      simp [h_abort]

    case pos =>
      simp [h_abort] at h_lemma5_s; simp [h_abort]
      by_cases h_tm_aborted: s.tmState = TMState.Aborted
      case pos =>
        simp [h_tm_aborted]

      case neg =>
        simp [h_tm_aborted] at h_lemma5_s
        simp [h_tm_aborted]
        rcases h_lemma5_s with ⟨rm₂, ⟨h_rm2_aborted, h_rm2_not_prepared, h_rm2_notin_msgs⟩⟩
        exists rm₂
        have h_rm_neq_rm2: rm ≠ rm₂ := by
          by_contra h_contra -- assume the opposite
          rw [← h_contra] at h_rm2_aborted
          rcases h_rm_prepare with ⟨h_rm_working, _⟩
          simp at h_rm_working
          rw [h_rm2_aborted] at h_rm_working
          injection h_rm_working with h_val_eq
          injection h_val_eq
        have h_unchanged_rm2_state: s'.rmState[rm₂]? = s.rmState[rm₂]? := by
          rcases h_rm_prepare with ⟨_, h_update_rm_state, _⟩
          simp [h_update_rm_state, Std.HashMap.getElem?_insert]
          simp [h_rm_neq_rm2]
        simp [h_unchanged_rm2_state, h_rm2_aborted]
        have h_unchanged_tm_prepared: s'.tmPrepared = s.tmPrepared := by simp [h_rm_prepare]
        simp [h_unchanged_tm_prepared, h_rm2_not_prepared]
        have h_prepared_in_msgs: Message.Prepared rm₂ ∉ s'.msgs ↔ Message.Prepared rm₂ ∉ s.msgs := by
          simp [h_rm_prepare, h_rm2_notin_msgs]
          by_contra h_rm2_eq_rm -- assume the opposite
          rw [h_rm2_eq_rm] at h_rm_neq_rm2
          simp at h_rm_neq_rm2
        simp [h_prepared_in_msgs, h_rm2_notin_msgs]

-- Effort: 5m
lemma invariant_is_inductive_tm_commit_lemma6
  (s: ProtocolState RM) (s': ProtocolState RM) (h_tm_commit: tm_commit s s'): lemma6 s' := by
    unfold lemma6
    unfold tm_commit at h_tm_commit
    -- it's all in h_tm_commit, we just need a bit of rewriting
    have : Message.Commit ∈ s'.msgs := by simp [h_tm_commit]
    simp [this]
    have : s'.tmPrepared = s'.all := by
      have h₁: s'.tmPrepared = s.tmPrepared := by simp [h_tm_commit]
      have h₂: s.tmPrepared = s.all := by simp [h_tm_commit]
      have h₃: s'.all = s.all := by simp [h_tm_commit]
      rw [h₁, h₂, h₃]
    simp [this]
    have : s'.tmState = TMState.Committed := by simp [h_tm_commit]
    simp [this]

-- Effort: 30m
lemma invariant_is_inductive_tm_abort_lemma6 (s: ProtocolState RM) (s': ProtocolState RM)
  (h_inv: invariant s) (h_tm_abort: tm_abort s s'): lemma6 s' := by
    unfold lemma6
    unfold tm_abort at h_tm_abort
    have h_msgs': s'.msgs = s.msgs ∪ {Message.Abort} := by simp [h_tm_abort]
    simp [h_msgs']
    have h_tm_state_aborted: s'.tmState = TMState.Aborted := by simp [h_tm_abort]
    have h_tm_state_init: s.tmState = TMState.Init := by simp [h_tm_abort]
    simp [h_tm_state_aborted]
    have h_unchanged_rm_state: s'.rmState = s.rmState := by simp [h_tm_abort]
    simp [h_unchanged_rm_state]
    unfold invariant at h_inv
    rcases h_inv with ⟨h_lemma1_s, _, _, _, _, h_lemma6_s⟩
    unfold lemma1 at h_lemma1_s
    have h_no_commit_msg : Message.Commit ∉ s.msgs := by
      by_contra h_contra -- assume the opposite
      unfold lemma6 at h_lemma6_s
      apply h_lemma6_s at h_contra
      simp [h_tm_state_init] at h_contra
      have h_no_rm_committed: (∃ rm: RM, s.rmState[rm]? = some RMState.Committed) → False := by
        intro h_committed
        simp [h_tm_state_init] at h_lemma1_s
        rcases h_committed with ⟨rm, h_committed⟩
        specialize h_lemma1_s rm
        simp [h_lemma1_s] at h_committed
      simp [*] at h_no_rm_committed
    simp [h_no_commit_msg]

-- Effort: 7m
lemma invariant_is_inductive_tm_receive_prepared_lemma6 (s: ProtocolState RM) (s': ProtocolState RM)
  (rm: RM) (h_all: ∀ rm: RM, rm ∈ s.all) (h_inv: invariant s) (h_tm_rcv_prepared: tm_rcv_prepared s s' rm): lemma6 s' := by
    unfold lemma6
    unfold tm_rcv_prepared at h_tm_rcv_prepared
    unfold invariant at h_inv
    have h_unchanged_tm_state: s'.tmState = s.tmState := by simp [h_tm_rcv_prepared]
    have h_tm_state_init: s.tmState = TMState.Init := by simp [h_tm_rcv_prepared]
    have h_unchanged_rm_state: s'.rmState = s.rmState := by simp [h_tm_rcv_prepared]
    have h_unchanged_msgs: s'.msgs = s.msgs := by simp [h_tm_rcv_prepared]
    simp [h_unchanged_tm_state, h_tm_state_init, h_unchanged_rm_state, h_unchanged_msgs]
    rcases h_inv with ⟨_, _, _, _, _, h_lemma6_s⟩
    unfold lemma6 at h_lemma6_s
    by_cases h_commit: Message.Commit ∈ s.msgs
    case neg =>
      simp [h_commit]

    case pos =>
      simp [h_commit]
      simp [h_commit] at h_lemma6_s
      simp [h_tm_state_init] at h_lemma6_s
      rcases h_lemma6_s with ⟨h_tm_prepared_eq_all, h_rm_state_committed⟩
      simp [h_rm_state_committed]
      have h_unchanged_all: s'.all = s.all := by simp [h_tm_rcv_prepared]
      simp [h_unchanged_all]
      have h_tm_prepared: s'.tmPrepared = s.tmPrepared ∪ {rm} := by simp [h_tm_rcv_prepared]
      rw [h_tm_prepared, h_tm_prepared_eq_all]
      simp [h_all]

-- Effort: 20m
lemma invariant_is_inductive_rm_prepare_lemma6 (s: ProtocolState RM) (s': ProtocolState RM)
  (rm: RM) (h_inv: invariant s) (h_rm_prepare: rm_prepare s s' rm): lemma6 s' := by
    unfold lemma6
    unfold rm_prepare at h_rm_prepare
    have h_commit_in_msgs: Message.Commit ∈ s'.msgs ↔ Message.Commit ∈ s.msgs := by
      simp [h_rm_prepare]
    have h_unchanged_tm_state: s'.tmState = s.tmState := by simp [h_rm_prepare]
    have h_unchanged_tm_prepared: s'.tmPrepared = s.tmPrepared := by simp [h_rm_prepare]
    have h_unchanged_all: s'.all = s.all := by simp [h_rm_prepare]
    simp [h_commit_in_msgs, h_unchanged_tm_state, h_unchanged_tm_prepared, h_unchanged_all]
    by_cases h_commit: Message.Commit ∈ s.msgs
    case neg =>
      simp [h_commit]

    case pos =>
      simp [h_commit]
      rcases h_inv with ⟨_, _, _, _, _, h_lemma6_s⟩
      unfold lemma6 at h_lemma6_s
      simp [h_commit] at h_lemma6_s
      rcases h_lemma6_s with ⟨h_tm_prepared_eq_all, h_tm_committed_or_rm_committed⟩
      simp [h_tm_prepared_eq_all]
      cases h_tm_committed_or_rm_committed
      case inl h_tm_state_committed =>
        simp [h_tm_state_committed]

      case inr h_rm_state_committed =>
        rcases h_rm_state_committed with ⟨rm₂, h_rm2_committed⟩
        have h_rm2_neq_rm:  rm ≠ rm₂ := by
          by_contra h_contra -- assume the opposite
          rw [← h_contra] at h_rm2_committed
          simp [h_rm2_committed] at h_rm_prepare
        have h_rm2_committed: s'.rmState[rm₂]? = RMState.Committed := by
          rcases h_rm_prepare with ⟨_, h_update_rm_state, _⟩
          simp [h_update_rm_state, Std.HashMap.getElem?_insert]
          simp [h_rm2_neq_rm, h_rm2_committed]
        have h: ∃ rm: RM, s'.rmState[rm]? = some RMState.Committed := by
          exists rm₂
        simp [h]

/--
 Showing that `invariant` is inductive, that is, it is preserved by the transition relation.
-/
theorem invariant_is_inductive (s: ProtocolState RM) (s': ProtocolState RM)
  (h_all: ∀ rm: RM, rm ∈ s.all) (h_inv: invariant s) (h_next: tp_next s s'):
    invariant s' := by
  unfold tp_next at h_next
  cases h_next
  case inl h_tm_commit =>
    -- action tm_commit
    unfold invariant
    -- prove the lemmas one by one
    apply And.intro
    . exact invariant_is_inductive_tm_commit_lemma1 s s' h_tm_commit
    . apply And.intro
      . exact invariant_is_inductive_tm_commit_lemma2 s s' h_all h_inv h_tm_commit
      . apply And.intro
        . apply invariant_is_inductive_tm_commit_lemma3 s s' h_tm_commit
        . apply And.intro
          . exact invariant_is_inductive_tm_commit_lemma4 s s' h_inv h_tm_commit
          . apply And.intro
            . exact invariant_is_inductive_tm_commit_lemma5 s s' h_all h_inv h_tm_commit
            . exact invariant_is_inductive_tm_commit_lemma6 s s' h_tm_commit

  case inr h_rest =>
    cases h_rest
    case inl h_tm_abort =>
      -- action tm_abort
      unfold invariant
      apply And.intro
      . exact invariant_is_inductive_tm_abort_lemma1 s s' h_inv h_tm_abort
      . apply And.intro
        . exact invariant_is_inductive_tm_abort_lemma2 s s' h_tm_abort
        . apply And.intro
          . exact invariant_is_inductive_tm_abort_lemma3 s s' h_tm_abort
          . apply And.intro
            . exact invariant_is_inductive_tm_abort_lemma4 s s' h_inv h_tm_abort
            . apply And.intro
              . exact invariant_is_inductive_tm_abort_lemma5 s s' h_tm_abort
              . exact invariant_is_inductive_tm_abort_lemma6 s s' h_inv h_tm_abort

    case inr h_rest =>
      rcases h_rest with ⟨rm, h_action⟩ -- ∃ rm: RM, action
      cases h_action
      case inl h_tm_rcv_prepared =>
        -- action tm_rcv_prepared
        apply And.intro
        . exact invariant_is_inductive_tm_receive_prepared_lemma1 s s' rm h_inv h_tm_rcv_prepared
        . apply And.intro
          . exact invariant_is_inductive_tm_receive_prepared_lemma2 s s' rm h_tm_rcv_prepared
          . apply And.intro
            . exact invariant_is_inductive_tm_receive_prepared_lemma3 s s' rm h_tm_rcv_prepared
            . apply And.intro
              . exact invariant_is_inductive_tm_receive_prepared_lemma4 s s' rm h_inv h_tm_rcv_prepared
              . apply And.intro
                . exact invariant_is_inductive_tm_receive_prepared_lemma5 s s' rm h_inv h_tm_rcv_prepared
                . exact invariant_is_inductive_tm_receive_prepared_lemma6 s s' rm h_all h_inv h_tm_rcv_prepared

      case inr h_rest =>
        cases h_rest
        case inl h_rm_prepare =>
          -- action rm_prepare
          apply And.intro
          . exact invariant_is_inductive_rm_prepare_lemma1 s s' rm h_inv h_rm_prepare
          . apply And.intro
            . exact invariant_is_inductive_rm_prepare_lemma2 s s' rm h_inv h_rm_prepare
            . apply And.intro
              . exact invariant_is_inductive_rm_prepare_lemma3 s s' rm h_inv h_rm_prepare
              . apply And.intro
                . exact invariant_is_inductive_rm_prepare_lemma4 s s' rm h_inv h_rm_prepare
                . apply And.intro
                  . exact invariant_is_inductive_rm_prepare_lemma5 s s' rm h_inv h_rm_prepare
                  . exact invariant_is_inductive_rm_prepare_lemma6 s s' rm h_inv h_rm_prepare
        case inr h_rest =>
          cases h_rest
          case inl h_rm_abort =>
            sorry

          case inr h_rest =>
            sorry
