/-
This is a propositional specification of eventually perfect failure detector.

We are following Algorithm 2.7 from the book on "Reliable and Secure Distributed
Programming" by Christian Cachin, Rachid Guerraoui, and Luís Rodrigues,
Springer-Heidelberg 2011. This algorithm assumes partial synchrony.

The original eventually perfect failure detector is defined in the paper
"Unreliable Failure Detectors for Reliable Distributed Systems" by Tushar Deepak
Chandra and Sam Toueg, JACM 1996. The original paper assumes reliable
communication.

Copyright (c) 2025 Igor Konnov
Released under MIT license as described in the file LICENSE.
Authors: Igor Konnov, 2025
-/

import Epfd.Basic
import Mathlib.Data.Finset.Image

-- The abstract type of processes
variable {Proc : Type} [DecidableEq Proc] [Hashable Proc] [Repr Proc]

-- The initial delay Δ used by the processes
variable (InitDelay: ℕ)

-- The global stabilization time GST, unknown to the processes
variable (GST: ℕ)

-- The message delay after GST, unknown to the processes
variable (MsgDelay: ℕ)

-- The state `s` is a state of the protocol, explicitly added to all the functions.
variable (s: ProtocolState Proc)

-- The state `s'` is the "next" state of the protocol.
variable (s': ProtocolState Proc)

/--
  A process `dst` receives a heartbeat request from `src`.
  -/
def rcv_heartbeat_request (src: Proc) (dst: Proc) (timestamp: ℕ) :=
    Message.HeartbeatRequest src dst timestamp ∈ s.msgs
  ∧ isMessageTimely GST MsgDelay timestamp s.clock
  ∧ s'.rcvd = s.rcvd ∪ { Message.HeartbeatRequest src dst timestamp }
  ∧ s'.msgs = s.msgs ∪ { Message.HeartbeatReply dst src s.clock }
  ∧ s'.all = s.all
  ∧ s'.crashed = s.crashed
  ∧ s'.clock = s.clock
  ∧ s'.alive = s.alive
  ∧ s'.suspected = s.suspected
  ∧ s'.delay = s.delay
  ∧ s'.nextTimeout = s.nextTimeout

/--
  A process `dst` receives a heartbeat reply from `src`.
  -/
def rcv_heartbeat_reply (src: Proc) (dst: Proc) (timestamp: ℕ) :=
    Message.HeartbeatReply src dst timestamp ∈ s.msgs
  ∧ isMessageTimely GST MsgDelay timestamp s.clock
  ∧ s'.rcvd = s.rcvd ∪ { Message.HeartbeatReply src dst timestamp }
  ∧ let nextAlive := s.alive[dst]! ∪ { src }
    s'.alive = s.alive.insert dst nextAlive
  ∧ s'.msgs = s.msgs
  ∧ s'.all = s.all
  ∧ s'.crashed = s.crashed
  ∧ s'.clock = s.clock
  ∧ s'.suspected = s.suspected
  ∧ s'.delay = s.delay
  ∧ s'.nextTimeout = s.nextTimeout

/--
  A process `p` timeouts.
  -/
def timeout (p: Proc) :=
    s.clock ≥ s.nextTimeout[p]!
  -- if `p` suspects an alive process, increase the delay
  ∧ let nextDelay :=
      if s.alive[p]! ∩ s.suspected[p]! ≠ ∅
      then s.delay[p]! + InitDelay
      else s.delay[p]!
    s'.delay = s.delay.insert p nextDelay
  -- recompute the set of suspected processes
  ∧ let isSuspected (q: Proc) :=
      q ∉ s.alive[p]! ∧ q ∉ s.suspected[p]!         -- trigger Suspect q
        ∨ ((q ∉ s.alive[p]! ∨ q ∉ s.suspected[p]!)  -- trigger Restore q
           ∧ q ∈ s.suspected[p]!)
    let nextSuspected := s.all.filter isSuspected
    s'.suspected = s.suspected.insert p nextSuspected
  -- send heartbeat requests to all processes, including `p` itself
  ∧ s'.msgs = s.msgs ∪ s.all.image (fun q => Message.HeartbeatRequest p q s.clock)
  -- set alive to empty and reset the timer
  ∧ s'.alive = s.alive.insert p ∅
  ∧ s'.nextTimeout = s.nextTimeout.insert p (s.clock + s.delay[p]!)
  -- everything else remains unchanged
  ∧ s'.rcvd = s.rcvd
  ∧ s'.all = s.all
  ∧ s'.crashed = s.crashed
  ∧ s'.clock = s.clock

/--
  A process `p` crashes. Note that this action is not part of the protocol
  itself, but rather a part of the environment (or the adversary).
  -/
def crash (p: Proc) :=
    p ∉ s.crashed
  ∧ s'.crashed = s.crashed ∪ { p }
  ∧ s'.all = s.all
  ∧ s'.msgs = s.msgs
  ∧ s'.rcvd = s.rcvd
  ∧ s'.clock = s.clock
  ∧ s'.alive = s.alive
  ∧ s'.suspected = s.suspected
  ∧ s'.delay = s.delay
  ∧ s'.nextTimeout = s.nextTimeout

/--
  The global system clock advances.
  -/
def advance_clock (delta: ℕ) :=
    delta > 0
  ∧ s'.clock = s.clock + delta
  ∧ s'.crashed = s.crashed
  ∧ s'.all = s.all
  ∧ s'.msgs = s.msgs
  ∧ s'.rcvd = s.rcvd
  ∧ s'.alive = s.alive
  ∧ s'.suspected = s.suspected
  ∧ s'.delay = s.delay
  ∧ s'.nextTimeout = s.nextTimeout

/--
  Initialize a map with the default value `v` for each process in `all`.
  -/
def init_map {α: Type} (all: List Proc) (v: α) : Std.HashMap Proc α :=
    all.foldl (fun m p => m.insert p v) (Std.HashMap.emptyWithCapacity 0)

/--
  The initial state of the protocol.
  -/
def init (all: List Proc): Prop :=
    s.all = all.toFinset
  ∧ s.crashed = ∅
  ∧ s.msgs = ∅
  ∧ s.rcvd = ∅
  ∧ s.clock = 0
  ∧ s.alive = init_map all ∅
  ∧ s.suspected = init_map all ∅
  ∧ s.delay = init_map all InitDelay
  ∧ s.nextTimeout = init_map all InitDelay

/--
  The transition relation of the protocol.
  -/
def next: Prop :=
  ∃ delta: ℕ, advance_clock s s' delta
  ∨ ∃ p q: Proc,
      timeout InitDelay s s' p
    ∨ crash s s' p
    ∨ ∃ timestamp: ℕ,
        rcv_heartbeat_request GST MsgDelay s s' p q timestamp
      ∨ rcv_heartbeat_reply GST MsgDelay s s' p q timestamp
