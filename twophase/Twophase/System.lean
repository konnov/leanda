/-
This is a specification of the system level of the two-phase commit protocol.

Copyright (c) 2025 Igor Konnov
Released under MIT license as described in the file LICENSE.
Authors: Igor Konnov, 2025
-/
import Twophase.Functional

/--
Since Lean4 is not TLA+, it does not have a built-in syntax for actions.
Hence, we introduce the type that essentially turns control and data
non-deterministm into inputs. This trick is usually called a "schedule"
or "adversary" in the literature.
-/
inductive Action RM where
  | TMCommit
  | TMAbort
  | TMRcvPrepared(rm: RM)
  | RMPrepare(rm: RM)
  | RMChooseToAbort(rm: RM)
  | RMRcvCommitMsg(rm: RM)
  | RMRcvAbortMsg(rm: RM)
  deriving DecidableEq, Repr

section
-- The abstract type of resource managers.
variable {RM : Type} [DecidableEq RM] [Hashable RM] [Repr RM]

/-- initialize the state of all resource managers to `Working` -/
def init_rm_state (all: List RM) :=
  all.foldl
    (fun m rm => m.insert rm RMState.Working)
    (Std.HashMap.emptyWithCapacity 0)

/-- The initial state of the protocol -/
def init (all: List RM): ProtocolState RM := {
    all := all.toFinset,
    rmState := init_rm_state all,
    tmState := TMState.Init,
    tmPrepared := ∅,
    msgs := ∅
}

/-- The transition function (!) of the protocol. Since we provide `next` with
the action as an argument, `next` is a function, not a relation. -/
def next s a :=
  match a with
  | Action.TMCommit => tmCommit RM s
  | Action.TMAbort => tmAbort _ s
  | Action.TMRcvPrepared rm => tmRcvPrepared _ s rm
  | Action.RMPrepare rm => rmPrepare _ s rm
  | Action.RMChooseToAbort rm => rmChooseToAbort _ s rm
  | Action.RMRcvCommitMsg rm => rmRcvCommitMsg _ s rm
  | Action.RMRcvAbortMsg rm => rmRcvAbortMsg _ s rm
end
