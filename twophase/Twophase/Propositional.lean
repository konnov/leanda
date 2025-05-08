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
import Twophase.System
import Std.Data.HashMap.Lemmas

-- The abstract type of resource managers.
variable { RM : Type } [DecidableEq RM] [Hashable RM]

-- connecting the functional and propositional specifications
section functional
-- The state `s` is the "current" state of the protocol.
variable (s: ProtocolState RM)
-- The state `s'` is the "next" state of the protocol.
variable (s': ProtocolState RM)

/-- The proposition version of `tmRcvPrepared`. -/
def tm_rcv_prepared (rm: RM): Prop :=
    s.tmState = TMState.Init
  ∧ Message.Prepared rm ∈ s.msgs
  ∧ s'.tmPrepared = s.tmPrepared ∪ { rm }
  ∧ s'.tmState = s.tmState
  ∧ s'.rmState = s.rmState
  ∧ s'.msgs = s.msgs
  ∧ s'.all = s.all

/-- The proposition version of `tmCommit`. -/
def tm_commit: Prop :=
    s.tmState = TMState.Init
  ∧ s.tmPrepared = s.all
  ∧ s'.tmState = TMState.Committed
  ∧ s'.msgs = s.msgs ∪ { Message.Commit }
  ∧ s'.tmPrepared = s.tmPrepared
  ∧ s'.rmState = s.rmState
  ∧ s'.all = s.all

/-- The proposition version of `tmAbort`. -/
def tm_abort: Prop :=
    s.tmState = TMState.Init
  ∧ s'.tmState = TMState.Aborted
  ∧ s'.msgs = s.msgs ∪ { Message.Abort }
  ∧ s'.tmPrepared = s.tmPrepared
  ∧ s'.rmState = s.rmState
  ∧ s'.all = s.all

/-- The proposition version of `rmPrepare`. -/
def rm_prepare (rm: RM): Prop :=
    s.rmState.get? rm = RMState.Working
  ∧ s'.rmState = s.rmState.insert rm RMState.Prepared
  ∧ s'.msgs = s.msgs ∪ { Message.Prepared rm }
  ∧ s'.tmState = s.tmState
  ∧ s'.tmPrepared = s.tmPrepared
  ∧ s'.all = s.all

-- The proposition version of `rmChooseToAbort`. -/
def rm_choose_to_abort (rm: RM): Prop :=
    s.rmState.get? rm = RMState.Working
  ∧ s'.rmState = s.rmState.insert rm RMState.Aborted
  ∧ s'.msgs = s.msgs
  ∧ s'.tmState = s.tmState
  ∧ s'.tmPrepared = s.tmPrepared
  ∧ s'.all = s.all

-- The proposition version of `rmRcvCommitMsg`. -/
def rm_rcv_commit_msg (rm: RM): Prop :=
    Message.Commit ∈ s.msgs
  ∧ s'.rmState = s.rmState.insert rm RMState.Committed
  ∧ s'.msgs = s.msgs
  ∧ s'.tmState = s.tmState
  ∧ s'.tmPrepared = s.tmPrepared
  ∧ s'.all = s.all

-- The proposition version of `rmRcvAbortMsg`. -/
def rm_rcv_abort_msg (rm: RM): Prop :=
    Message.Abort ∈ s.msgs
  ∧ s'.rmState = s.rmState.insert rm RMState.Aborted
  ∧ s'.msgs = s.msgs
  ∧ s'.tmState = s.tmState
  ∧ s'.tmPrepared = s.tmPrepared
  ∧ s'.all = s.all

end functional

-- connecting the system and propositional specifications
section system

-- a propositional specification of initialization, similar to Init in TLA+
def tp_init (all: List RM) (s: ProtocolState RM): Prop :=
    s.all = all.toFinset
  ∧ s.rmState = init_rm_state all
  ∧ s.tmState = TMState.Init
  ∧ s.tmPrepared = ∅
  ∧ s.msgs = ∅

-- a propositional specification of a state transition, similar to Next in TLA+
def tp_next (s: ProtocolState RM) (s': ProtocolState RM): Prop :=
    tm_commit s s'
  ∨ tm_abort s s'
  ∨ ∃ rm: RM,
      tm_rcv_prepared s s' rm
    ∨ rm_prepare s s' rm
    ∨ rm_choose_to_abort s s' rm
    ∨ rm_rcv_commit_msg s s' rm
    ∨ rm_rcv_abort_msg s s' rm
end system
