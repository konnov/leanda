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
    s.tmState = TMState.Aborted
      ∨ ∃ rm: RM,
          s.rmState[rm]? = some RMState.Aborted
        ∧ rm ∉ s.tmPrepared
        ∧ Message.Prepared rm ∉ s.msgs

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
      simp [h_tm_init] at h_tm_committed
    simp [h_no_committed]

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

-- Effort: 5m
lemma invariant_is_inductive_tm_commit_lemma3 (s: ProtocolState RM) (s': ProtocolState RM)
  (h_tm_commit: tm_commit s s'):
      lemma3 s' := by
    unfold lemma3
    unfold tm_commit at h_tm_commit
    have : s'.tmState = TMState.Committed := by simp [h_tm_commit]
    simp [this]

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
      . sorry
      /-
      . apply And.intro
        . exact invariant_is_inductive_tm_abort_lemma2 s s' h_inv h_tm_abort
        . apply And.intro
          . exact invariant_is_inductive_tm_abort_lemma3 s s' h_tm_abort
          . apply And.intro
            . exact invariant_is_inductive_tm_abort_lemma4 s s' h_inv h_tm_abort
            . apply And.intro
              . exact invariant_is_inductive_tm_abort_lemma5 s s' h_all h_inv h_tm_abort
              . exact invariant_is_inductive_tm_abort_lemma6 s s' h_tm_abort
      -/

    case inr h_rest =>
      sorry
