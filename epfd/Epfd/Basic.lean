/-
Basic definitions for the eventually perfect failure detector.

Copyright (c) 2025 Igor Konnov
Released under MIT license as described in the file LICENSE.
Authors: Igor Konnov, 2025
-/

import Std.Data.HashMap
import Mathlib.Data.Finset.Basic

-- The abstract type of processes
variable (Proc : Type) [DecidableEq Proc] [Hashable Proc] [Repr Proc]

-- The global stabilization time GST, unknown to the processes
/-- A message that is sent by one process (src) to another process (dst).
    Every message is equipped with a timestamp, which is equal to the
    clock value at the time of sending the message.
 -/
inductive Message where
  | HeartbeatRequest (src: Proc) (dst: Proc) (timestamp: Nat)
  | HeartbeatReply (src: Proc) (dst: Proc) (timestamp: Nat)
  deriving DecidableEq, Repr

/-- A global state of the eventually perfect failure detector:
  - `all` is the set of all processes in the system.
  - `alive` is a map from each process to the set of processes that it
    considers alive.
  - `suspected` is a map from each process to the set of processes that it
    considers suspected.
  - `delay` is a map from each process to its delay (in clock units).
  - `msgs` is the set of messages that have been sent by the processes.
  - `rcvd` is the set of messages that have been received by the processes.
  - `clock` is a global clock value.
  - `crashed` is the set of processes that have actually crashed.
  - `nextTimeout` maps each process to the point of the next timeout.
-/
@[ext] -- this is needed for proofs
structure ProtocolState where
  -- The set of all processes.
  -- It may differ from run to run, but remains constant during a run.
  all: Finset Proc
  crashed: Finset Proc
  msgs: Finset (@Message Proc)
  rcvd: Finset (@Message Proc)
  clock: Nat
  alive: Std.HashMap Proc (Finset Proc)
  suspected: Std.HashMap Proc (Finset Proc)
  delay: Std.HashMap Proc Nat
  nextTimeout: Std.HashMap Proc Nat

/--
  Given a message that was sent at `timestamp`, can a process receive it at time `clock`.
  -/
def isMessageTimely (GST: Nat) (MsgDelay: Nat) (timestamp: Nat) (clock: Nat): Bool :=
    timestamp ≥ GST && clock ≥ timestamp && clock ≤ timestamp + MsgDelay
  || timestamp < GST && clock ≥ timestamp

example:
  -- After GST, clock must be within [timestamp, timestamp + MsgDelay]
  -- GST = 100, MsgDelay = 5, timestamp = 120, clock = 121
  @isMessageTimely 100 5 120 121 == true := rfl

example:
  -- After GST, clock must be within [timestamp, timestamp + MsgDelay]
  -- GST = 100, MsgDelay = 5, timestamp = 120, clock = 127
  @isMessageTimely 100 5 120 127 == false := rfl

example:
  -- Before GST, we can receive a message much later
  -- GST = 100, MsgDelay = 5, timestamp = 21, clock = 50
  @isMessageTimely 100 5 21 50 == true := rfl

example:
  -- We cannot receive a message earlier than it was sent,
  -- either before or after GST.
  -- GST = 100, MsgDelay = 5, timestamp = 21, clock = 20
    @isMessageTimely 100 5 21 20 == false
  -- GST = 100, MsgDelay = 5, timestamp = 121, clock = 120
  ∧ @isMessageTimely 100 5 121 120 == false
    := by apply And.intro; rfl; rfl
