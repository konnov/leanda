/-
Basic definitions for the eventually perfect failure detector.

Copyright (c) 2025 Igor Konnov
Released under MIT license as described in the file LICENSE.
Authors: Igor Konnov, 2025
-/

import Std.Data.HashMap
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-
  An abstract type of all processes. It must be a finite type, so we can explicitly
  refer to all processes in the system.
 -/
variable (Proc : Type) [Fintype Proc] [DecidableEq Proc] [Hashable Proc] [Repr Proc]

/-- A message tag: `HeartbeatRequest` or `HeartbeatReply`. -/
inductive MsgTag where
  | HeartbeatRequest
  | HeartbeatReply
  deriving DecidableEq, Repr

/-- A message that is sent by one process (src) to another process (dst).
    Every message is equipped with a timestamp, which is equal to the
    clock value at the time of sending the message.
 -/
@[ext]
structure Msg where
  kind: MsgTag
  src: Proc
  dst: Proc
  timestamp: ℕ
  deriving DecidableEq, Repr

/--
  A global state of the eventually perfect failure detector:
  - `alive` is a map from each process to the set of processes that it
    considers alive.
  - `suspected` is a map from each process to the set of processes that it
    considers suspected.
  - `delay` is a map from each process to its delay (in clock units).
  - `nextTimeout` maps each process to the point of the next timeout.
  - `sent` is the set of messages that have been sent by the processes.
  - `rcvd` is the set of messages that have been received by the processes.
  - `clock` is a global clock value.
  - `crashed` is the set of processes that have actually crashed.
-/
@[ext] -- this is needed for proofs
structure ProtocolState where
  alive: Std.HashMap Proc (Finset Proc)
  suspected: Std.HashMap Proc (Finset Proc)
  delay: Std.HashMap Proc Nat
  nextTimeout: Std.HashMap Proc Nat
  sent: Finset (Msg Proc)
  rcvd: Finset (Msg Proc)
  clock: Nat
  crashed: Finset Proc

/--
  Given a message that was sent at `timestamp`, can a process receive it at time `clock`.
  -/
def isMsgTimely (GST: Nat) (MsgDelay: Nat) (timestamp: Nat) (clock: Nat): Bool :=
  clock ≥ timestamp && clock ≤ (max GST timestamp) + MsgDelay

example:
  -- After GST, clock must be within [timestamp, timestamp + MsgDelay]
  -- GST = 100, MsgDelay = 5, timestamp = 120, clock = 121
  @isMsgTimely 100 5 120 121 == true := rfl

example:
  -- After GST, clock must be within [timestamp, timestamp + MsgDelay]
  -- GST = 100, MsgDelay = 5, timestamp = 120, clock = 127
  @isMsgTimely 100 5 120 127 == false := rfl

example:
  -- Before GST, we can receive a message much later
  -- GST = 100, MsgDelay = 5, timestamp = 21, clock = 50
  @isMsgTimely 100 5 21 50 == true := rfl

example:
  -- We cannot receive a message earlier than it was sent,
  -- either before or after GST.
  -- GST = 100, MsgDelay = 5, timestamp = 21, clock = 20
    @isMsgTimely 100 5 21 20 == false
  -- GST = 100, MsgDelay = 5, timestamp = 121, clock = 120
  ∧ @isMsgTimely 100 5 121 120 == false
    := by apply And.intro; rfl; rfl
