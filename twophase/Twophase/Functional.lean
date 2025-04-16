/-
This is a functional specification of the resource managers and transaction
managers in the two-phase commit protocol. The logic closely follows the TLA+
specification of two-phase commit. However, the definitions in this module are
entirely deterministic, that is, they are not actions in the TLA+ sense.
We put together these definitions in the [System module](./System.lean).

One important decision that we make here: If the function arguments are not
applicable to a given state, we return the state unchanged. This aligns very
well with the TLA+ approach, where stuttering is the default.

Compare it with the
[TLA+ specification](https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TwoPhase.tla).

Authors: Igor Konnov, 2025
-/
import Std.Data.HashMap
import Mathlib.Data.Finset.Basic

-- The abstract type of resource managers.
variable (RM : Type) [DecidableEq RM] [Hashable RM] [Repr RM]

/-- A message that sent by either the transaction manager or a resource manager. -/
inductive Message where
    | Commit
    | Abort
    | Prepared(rm: RM)
    deriving DecidableEq

/-- A state of a resource manager. -/
inductive RMState where
    | Working
    | Prepared
    | Committed
    | Aborted
    deriving DecidableEq

/-- A state of the transaction manager. -/
inductive TMState where
    | Init
    | Committed
    | Aborted
    deriving DecidableEq

/-- A state of the Two-phase commit protocol. -/
structure ProtocolState where
    -- The set of the resource managers.
    -- It may differ from run to run, but remains constant during a run.
    all: Finset RM
    rmState: Std.HashMap RM RMState
    tmState: TMState
    tmPrepared: Finset RM
    msgs: Finset (Message RM)

/-- The transaction manager receives a `Prepared` message from a resource manager `rm`. -/
def tmRcvPrepared (s: ProtocolState RM) (rm: RM): ProtocolState RM :=
    if s.tmState = TMState.Init ∧ Message.Prepared rm ∈ s.msgs then {
        s with tmPrepared := s.tmPrepared ∪ { rm },
    } else s

/--
  The transaction manager commits the transaction. Enabled iff the TM is its initial
  state and every RM has sent a `Prepared` message.
 -/
def tmCommit (s: ProtocolState RM): ProtocolState RM :=
    if s.tmState = TMState.Init ∧ s.tmPrepared = s.all then {
        s with
        tmState := TMState.Committed,
        msgs := s.msgs ∪ { Message.Commit }
    } else s

/-- The TM spontaneously aborts the transaction.  -/
def tmAbort (s: ProtocolState RM): ProtocolState RM :=
    if s.tmState = TMState.Init then {
        s with
        tmState := TMState.Aborted,
        msgs := s.msgs ∪ { Message.Abort }
    } else s

/-- Resource manager `rm` prepares. -/
def rmPrepare (s: ProtocolState RM) (rm: RM): ProtocolState RM :=
    if s.rmState.get? rm = RMState.Working then {
        s with
        rmState := s.rmState.insert rm RMState.Prepared,
        msgs := s.msgs ∪ { Message.Prepared rm }
    } else s

/-- Resource manager $rm$ spontaneously decides to abort.  As noted above, `rm`
does not send any message in our simplified spec. -/
def rmChooseToAbort (s: ProtocolState RM) (rm: RM): ProtocolState RM :=
    if s.rmState.get? rm = RMState.Working then {
        s with rmState := s.rmState.insert rm RMState.Aborted,
    } else s

/-- Resource manager `rm` is told by the TM to commit. -/
def rmRcvCommitMsg (s: ProtocolState RM) (rm: RM): ProtocolState RM :=
    if Message.Commit ∈ s.msgs then {
        s with rmState := s.rmState.insert rm RMState.Committed,
    } else s

/-- Resource manager `rm` is told by the TM to abort. -/
def rmRcvAbortMsg(s: ProtocolState RM) (rm: RM): ProtocolState RM :=
    if Message.Abort ∈ s.msgs then {
        s with rmState := s.rmState.insert rm RMState.Aborted,
    } else s
