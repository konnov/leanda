/-
This is a propositional (denotational?) specification of the two-phase
commit, very much in the spirit of the original TLA+ specification. We use this
module to connect the propositional specification with the functional one.

Compare it with the
[TLA+ specification](https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TwoPhase.tla).

Copyright (c) 2025 Igor Konnov
Released under MIT license as described in the file LICENSE.
Authors: Igor Konnov, 2025
-/

import Twophase.Functional

section
-- The abstract type of resource managers.
variable { RM : Type } [DecidableEq RM] [Hashable RM] [Repr RM]

-- The state `s` is the "current" state of the protocol.
variable (s: ProtocolState RM)
-- The state `s'` is the "next" state of the protocol.
variable (s': ProtocolState RM)

/-- The proposition version of `tmRcvPrepared`. -/
def tm_rcv_prepared (rm: RM): Prop :=
    s.tmState = TMState.Init
  ∧ Message.Prepared rm ∈ s.msgs
  ∧ s'.tmPrepared = s.tmPrepared ∪ { rm }

/-- The proposition version of `tmCommit`. -/
def tm_commit: Prop :=
    s.tmState = TMState.Init
  ∧ s.tmPrepared = s.all
  ∧ s'.tmState = TMState.Committed
  ∧ s'.msgs = s.msgs ∪ { Message.Commit }

/-- The proposition version of `tmAbort`. -/
def tm_abort: Prop :=
    s.tmState = TMState.Init
  ∧ s'.tmState = TMState.Aborted
  ∧ s'.msgs = s.msgs ∪ { Message.Abort }

/-- The proposition version of `rmPrepare`. -/
def rm_prepare (rm: RM): Prop :=
    s.rmState.get? rm = RMState.Working
  ∧ s'.rmState.get? rm = RMState.Prepared
  ∧ s'.msgs = s.msgs ∪ { Message.Prepared rm }

-- The proposition version of `rmChooseToAbort`. -/
def rm_choose_to_abort (rm: RM): Prop :=
    s.rmState.get? rm = RMState.Working
  ∧ s'.rmState.get? rm = RMState.Aborted

-- The proposition version of `rmRcvCommitMsg`. -/
def rm_rcv_commit_msg (rm: RM): Prop :=
    Message.Commit ∈ s.msgs
  ∧ s'.rmState.get? rm = RMState.Committed

-- The proposition version of `rmRcvAbortMsg`. -/
def rm_rcv_abort_msg (rm: RM): Prop :=
    Message.Abort ∈ s.msgs
  ∧ s'.rmState.get? rm = RMState.Aborted

-- Connecting the denotational and functional specifications.
-- TODO: someone has to write the proofs :)

theorem tm_rcv_prepared_correct (rm: RM):
    tm_rcv_prepared s s' rm ↔
      tmRcvPrepared RM s rm = some s' := by sorry

theorem tm_commit_correct :
    tm_commit s s' ↔
      tmCommit RM s = some s' := by sorry

theorem tm_abort_correct :
    tm_abort s s' ↔
      tmAbort RM s = some s' := by sorry

theorem rm_prepare_correct (rm: RM):
    rm_prepare s s' rm ↔
      rmPrepare RM s rm = some s' := by sorry

theorem rm_choose_to_abort_correct (rm: RM):
    rm_choose_to_abort s s' rm ↔
      rmChooseToAbort RM s rm = some s' := by sorry

theorem rm_rcv_commit_msg_correct (rm: RM):
    rm_rcv_commit_msg s s' rm ↔
      rmRcvCommitMsg RM s rm = some s' := by sorry

theorem rm_rcv_abort_msg_correct (rm: RM):
    rm_rcv_abort_msg s s' rm ↔
      rmRcvAbortMsg RM s rm = some s' := by sorry
end
