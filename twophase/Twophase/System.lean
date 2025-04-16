/-
This is a specification of the system level of the two-phase commit protocol.

Igor Konnov, 2025
-/
import Twophase.Functional

-- The abstract type of resource managers.
variable (RM : Type) [DecidableEq RM] [Hashable RM] [Repr RM]

/--
Since Lean4 is not TLA+, it does not have a built-in syntax for actions.
Hence, we introduce the type that essentially turns control and data
non-deterministm into inputs. This trick is usually called a "schedule"
or "adversary" in the literature.
-/
inductive Schedule where
  | TMCommit
  | TMAbort
  | TMRcvPrepared(rm: RM)
  | RMPrepare(rm: RM)
  | RMChooseToAbort(rm: RM)
  | RMRcvCommitMsg(rm: RM)
  | RMRcvAbortMsg(rm: RM)

/-- The initial state of the protocol -/
def init(all: Finset RM): ProtocolState RM := {
    all := all,
    rmState := Std.HashMap.emptyWithCapacity 0,
    tmState := TMState.Init,
    tmPrepared := ∅,
    msgs := ∅
}

/-- The transition function (!) of the protocol. Since we provide `next` with
the action as an argument, `next` is a function, not a relation. -/
def next(s: ProtocolState RM) (a: Schedule RM): ProtocolState RM :=
  match a with
  | Schedule.TMCommit => tmCommit RM s
  | Schedule.TMAbort => tmAbort RM s
  | Schedule.TMRcvPrepared rm => tmRcvPrepared RM s rm
  | Schedule.RMPrepare rm => rmPrepare RM s rm
  | Schedule.RMChooseToAbort rm => rmChooseToAbort RM s rm
  | Schedule.RMRcvCommitMsg rm => rmRcvCommitMsg RM s rm
  | Schedule.RMRcvAbortMsg rm => rmRcvAbortMsg RM s rm
