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
inductive Action (N: Nat) where
  | TMCommit
  | TMAbort
  | TMRcvPrepared(rm: RM N)
  | RMPrepare(rm: RM N)
  | RMChooseToAbort(rm: RM N)
  | RMRcvCommitMsg(rm: RM N)
  | RMRcvAbortMsg(rm: RM N)
  deriving DecidableEq, Repr

section
-- The number of resource managers.
variable { N: Nat }

/-- initialize the state of all resource managers to `Working` -/
def init_rm_state :=
  (List.finRange N).foldl
    (fun m rm => m.insert rm RMState.Working)
    (Std.HashMap.emptyWithCapacity 0)

/-- The initial state of the protocol -/
def init: ProtocolState N := {
    rmState := init_rm_state,
    tmState := TMState.Init,
    tmPrepared := ∅,
    msgs := ∅
}

/-- The transition function (!) of the protocol. Since we provide `next` with
the action as an argument, `next` is a function, not a relation. -/
def next (s: ProtocolState N) (a: Action N) :=
  match a with
  | Action.TMCommit => tmCommit s
  | Action.TMAbort => tmAbort s
  | Action.TMRcvPrepared rm => tmRcvPrepared s rm
  | Action.RMPrepare rm => rmPrepare s rm
  | Action.RMChooseToAbort rm => rmChooseToAbort s rm
  | Action.RMRcvCommitMsg rm => rmRcvCommitMsg s rm
  | Action.RMRcvAbortMsg rm => rmRcvAbortMsg s rm
end
