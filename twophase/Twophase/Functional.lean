/-
This is a functional specification of the resource managers and transaction
managers in the two-phase commit protocol. The logic closely follows the TLA+
specification of two-phase commit. However, the definitions in this module are
entirely deterministic, that is, they are not actions in the TLA+ sense.
We put together these definitions in the [System module](./System.lean).

One important decision that we make here: If the function arguments are not
applicable to a given state, we return `none`.

Compare it with the
[TLA+ specification](https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TwoPhase.tla).

Copyright (c) 2025 Igor Konnov
Released under MIT license as described in the file LICENSE.
Authors: Igor Konnov, 2025
-/
import Std.Data.HashMap
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Fin

/-- A state of a resource manager. -/
inductive RMState where
    | Working
    | Prepared
    | Committed
    | Aborted
    deriving DecidableEq, Repr

/-- A state of the transaction manager. -/
inductive TMState where
    | Init
    | Committed
    | Aborted
    deriving DecidableEq, Repr

/-- A message that sent by either the transaction manager or a resource manager. -/
inductive Message (N: Nat) where
    | Commit
    | Abort
    | Prepared(i: Fin N)
    deriving DecidableEq, Repr

/-- A state of the Two-phase commit protocol. -/
structure ProtocolState (N: Nat) where
    -- The set of the resource managers.
    -- It may differ from run to run, but remains constant during a run.
    rmState: Std.HashMap (Fin N) RMState
    tmState: TMState
    tmPrepared: Finset (Fin N)
    msgs: Finset (Message N)

-- Functional behavior of the protocol
section defs
-- The number of resource managers.
variable { N: Nat }
-- A resource manager is represented by a number from 0 to N-1.
abbrev RM (N: Nat) := Fin N
-- The state `s` is a state of the protocol, explicitly added to all the functions.
variable (s: ProtocolState N)

-- We need this little theorem to construct the set of all resource managers.
-- Fortunately, Lean can prove it itself.
theorem mem_range_le: ∀ x ∈ Finset.range N, x < N := by
    simp

/-- The set of all resource managers. -/
def AllRM: Finset (RM N) :=
    Finset.attachFin (Finset.range N) mem_range_le

/-- The transaction manager receives a `Prepared` message from a resource manager `rm`. -/
def tmRcvPrepared (rm: RM N) :=
    if s.tmState = TMState.Init ∧ Message.Prepared rm ∈ s.msgs then some {
        s with tmPrepared := s.tmPrepared ∪ { rm },
    } else none

/--
  The transaction manager commits the transaction. Enabled iff the TM is its initial
  state and every RM has sent a `Prepared` message.
 -/
def tmCommit :=
    if s.tmState = TMState.Init ∧ s.tmPrepared = AllRM then some {
        s with
        tmState := TMState.Committed,
        msgs := s.msgs ∪ { Message.Commit }
    } else none

/-- The TM spontaneously aborts the transaction.  -/
def tmAbort :=
    if s.tmState = TMState.Init then some {
        s with
        tmState := TMState.Aborted,
        msgs := s.msgs ∪ { Message.Abort }
    } else none

/-- Resource manager `rm` prepares. -/
def rmPrepare (rm: RM N) :=
    if s.rmState.get? rm = RMState.Working then some {
        s with
        rmState := s.rmState.insert rm RMState.Prepared,
        msgs := s.msgs ∪ { Message.Prepared rm }
    } else none

/-- Resource manager $rm$ spontaneously decides to abort.  As noted above, `rm`
does not send any message in our simplified spec. -/
def rmChooseToAbort (rm: RM N) :=
    if s.rmState.get? rm = RMState.Working then some {
        s with rmState := s.rmState.insert rm RMState.Aborted,
    } else none

/-- Resource manager `rm` is told by the TM to commit. -/
def rmRcvCommitMsg (rm: RM N) :=
    if Message.Commit ∈ s.msgs then some {
        s with rmState := s.rmState.insert rm RMState.Committed,
    } else none

/-- Resource manager `rm` is told by the TM to abort. -/
def rmRcvAbortMsg (rm: RM N) :=
    if Message.Abort ∈ s.msgs then some {
        s with rmState := s.rmState.insert rm RMState.Aborted,
    } else none

end defs
