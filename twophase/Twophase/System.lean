/-
This is a specification of the system level of the two-phase commit protocol.

Igor Konnov, 2025
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold
import Twophase.Functional

-- The abstract type of resource managers.
variable (RM : Type) [DecidableEq RM] [Hashable RM] [Repr RM]

/--
Since Lean4 is not TLA+, it does not have a built-in syntax for actions.
Hence, we introduce the type that essentially turns control and data
non-deterministm into inputs. This trick is usually called a "schedule"
or "adversary" in the literature.
-/
inductive Action where
  | TMCommit
  | TMAbort
  | TMRcvPrepared(rm: RM)
  | RMPrepare(rm: RM)
  | RMChooseToAbort(rm: RM)
  | RMRcvCommitMsg(rm: RM)
  | RMRcvAbortMsg(rm: RM)
  deriving DecidableEq, Repr

def init_rm_state (all: List RM): Std.HashMap RM RMState :=
  all.foldl
    (fun m rm => m.insert rm RMState.Working)
    (Std.HashMap.emptyWithCapacity 0)

/-- The initial state of the protocol -/
def init(all: List RM): ProtocolState RM := {
    all := all.toFinset,
    -- initialize the state of all resource managers to `Working`
    rmState := init_rm_state RM all,
    --rmState := Std.HashMap.emptyWithCapacity 0,
    tmState := TMState.Init,
    tmPrepared := ∅,
    msgs := ∅
}

/-- The transition function (!) of the protocol. Since we provide `next` with
the action as an argument, `next` is a function, not a relation. -/
def next(s: ProtocolState RM) (a: Action RM): Option (ProtocolState RM) :=
  match a with
  | Action.TMCommit => tmCommit RM s
  | Action.TMAbort => tmAbort RM s
  | Action.TMRcvPrepared rm => tmRcvPrepared RM s rm
  | Action.RMPrepare rm => rmPrepare RM s rm
  | Action.RMChooseToAbort rm => rmChooseToAbort RM s rm
  | Action.RMRcvCommitMsg rm => rmRcvCommitMsg RM s rm
  | Action.RMRcvAbortMsg rm => rmRcvAbortMsg RM s rm
