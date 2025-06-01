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
variable (Proc : Type) [Fintype Proc] [DecidableEq Proc] [Hashable Proc] [Repr Proc]

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
  let req := { kind := MsgTag.HeartbeatRequest, src, dst, timestamp }
  dst ∉ s.crashed
  ∧ req ∈ s.sent
  ∧ isMsgTimely GST MsgDelay timestamp s.clock
  ∧ s'.rcvd = s.rcvd ∪ { req }
  ∧ let reply :=
      { kind := MsgTag.HeartbeatReply, src := dst, dst := src, timestamp := s.clock }
    s'.sent = s.sent ∪ { reply }
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
  let reply := { kind := MsgTag.HeartbeatReply, src, dst, timestamp }
  dst ∉ s.crashed
  ∧ reply ∈ s.sent
  ∧ isMsgTimely GST MsgDelay timestamp s.clock
  ∧ s'.rcvd = s.rcvd ∪ { reply }
  ∧ let nextAlive := s.alive[dst]! ∪ { src }
    s'.alive = s.alive.insert dst nextAlive
  ∧ s'.sent = s.sent
  ∧ s'.crashed = s.crashed
  ∧ s'.clock = s.clock
  ∧ s'.suspected = s.suspected
  ∧ s'.delay = s.delay
  ∧ s'.nextTimeout = s.nextTimeout

/--
  A process `p` timeouts.
  -/
def timeout (p: Proc) :=
    p ∉ s.crashed
  ∧ s.clock = s.nextTimeout[p]!
  -- if `p` suspects an alive process, increase the delay
  ∧ let nextDelay :=
      if s.alive[p]! ∩ s.suspected[p]! ≠ ∅
      then s.delay[p]! + InitDelay
      else s.delay[p]!
    s'.delay = s.delay.insert p nextDelay
  -- recompute the set of suspected processes
  ∧ let nextSuspected := Finset.univ \ s.alive[p]!
      /- q ∉ s.alive[p]! is equivalent to the original code:
        on q ∉ s.alive[p]! ∧ q ∉ s.suspected[p]! trigger Suspect q
        on q ∈ s.alive[p]! ∧ q ∈ s.suspected[p]! trigger Restore q
        else keep q ∈ s.suspected[p]!
       -/
    s'.suspected = s.suspected.insert p nextSuspected
  -- send heartbeat requests to all processes, including `p` itself
  ∧ s'.sent = s.sent ∪ Finset.univ.image (fun q => {
      kind := MsgTag.HeartbeatRequest, src := p, dst := q, timestamp := s.clock
    })
  -- set alive to empty and reset the timer
  ∧ s'.alive = s.alive.insert p ∅
  ∧ s'.nextTimeout = s.nextTimeout.insert p (s.clock + s.delay[p]!)
  -- everything else remains unchanged
  ∧ s'.rcvd = s.rcvd
  ∧ s'.crashed = s.crashed
  ∧ s'.clock = s.clock

/--
  A process `p` crashes. This action is not part of the protocol itself, but
  rather a part of the environment (or the adversary).
  -/
def crash (p: Proc) :=
    p ∉ s.crashed
  ∧ s'.crashed = s.crashed ∪ { p }
  ∧ s'.sent = s.sent
  ∧ s'.rcvd = s.rcvd
  ∧ s'.clock = s.clock
  ∧ s'.alive = s.alive
  ∧ s'.suspected = s.suspected
  ∧ s'.delay = s.delay
  ∧ s'.nextTimeout = s.nextTimeout

/--
  The global system clock advances. We advance the clock by exactly one unit.
  If we had a rational clock, we would have to advance it by `delta` units.
  -/
def advance_clock :=
    s'.clock = s.clock + 1
  ∧ s'.crashed = s.crashed
  ∧ s'.sent = s.sent
  ∧ s'.rcvd = s.rcvd
  ∧ s'.alive = s.alive
  ∧ s'.suspected = s.suspected
  ∧ s'.delay = s.delay
  ∧ s'.nextTimeout = s.nextTimeout

/--
  Initialize a map with the default value `v` for each process in `all`.
  -/
noncomputable def init_map {α: Type} (v: α) : Std.HashMap Proc α :=
    Finset.univ.toList.foldl (fun m p => m.insert p v) (Std.HashMap.emptyWithCapacity 0)

/--
  The initial state of the protocol.
  -/
def init (all: List Proc): Prop :=
    s.all = all.toFinset
  ∧ s.crashed = ∅
  ∧ s.sent = ∅
  ∧ s.rcvd = ∅
  ∧ s.clock = 0
  ∧ s.alive = init_map Proc ∅
  ∧ s.suspected = init_map Proc ∅
  ∧ s.delay = init_map Proc InitDelay
  ∧ s.nextTimeout = init_map Proc InitDelay

/--
  The transition relation of the protocol.
  -/
def next: Prop :=
  advance_clock Proc s s'
    ∨ ∃ p q: Proc,
        timeout Proc InitDelay s s' p
          ∨ crash Proc s s' p
          ∨ ∃ t: ℕ,
              rcv_heartbeat_request Proc GST MsgDelay s s' p q t
                ∨ rcv_heartbeat_reply Proc GST MsgDelay s s' p q t

-- The protocol properties to prove. Here we define the properties
-- as close to the original formulation as possible.
section properties
/--
  Does a sequence of states satisfy *strong completess*?
  We want to prove that every *fair run* (see below) of the protocol
  satisfies this property.
  -/
def is_strongly_complete (seq: ℕ → (ProtocolState Proc)) : Prop :=
  ∃ i: ℕ,
    let s_i := seq i
    ∀ k: ℕ, ∀ p q: Proc,
      let s_k := seq k
      (k ≥ i ∧ p ∉ s_i.crashed ∧ q ∈ s_i.crashed) → q ∈ s_k.suspected[p]!

/--
  Does a sequence of states satisfy *eventual strong accuracy*?
  We want to prove that every *fair run* (see below) of the protocol
  satisfies this property.
  -/
def is_eventually_strongly_accurate (seq: ℕ → (ProtocolState Proc)) : Prop :=
  ∃ i: ℕ,
    ∀ k: ℕ, ∀ p q: Proc,
      let s_i := seq i
      let s_k := seq k
      (k ≥ i ∧ p ∉ s_i.crashed ∧ q ∉ s_i.crashed) → q ∉ s_k.suspected[p]!

end properties

-- Additional machinery to define fairness, as we would not be able
-- to prove the above properties without precisely defining fairness.
section fairness

/--
  The type of actions that can be performed by the protocol.
  -/
inductive Action where
  | Init
  | AdvanceClock
  | Timeout(p: Proc)
  | Crash(p: Proc)
  | RcvHeartbeatRequest(src: Proc) (dst: Proc) (timestamp: ℕ)
  | RcvHeartbeatReply(src: Proc) (dst: Proc) (timestamp: ℕ)

/--
  A refinement of `next` that specifies the action taken.
  -/
def next_a (a: @Action Proc): Prop :=
match a with
| Action.Init =>
    s' = s -- dummy action
| Action.AdvanceClock =>
    advance_clock Proc s s'
| Action.Timeout p =>
    timeout Proc InitDelay s s' p
| Action.Crash p =>
    crash Proc s s' p
| Action.RcvHeartbeatRequest src dst timestamp =>
    rcv_heartbeat_request Proc GST MsgDelay s s' src dst timestamp
| Action.RcvHeartbeatReply src dst timestamp =>
    rcv_heartbeat_reply Proc GST MsgDelay s s' src dst timestamp

/--
  A convenience structure for pairs of states and actions.
  -/
structure StateAction where
  s: ProtocolState Proc
  a: @Action Proc

/--
  A trace is an infinite sequence of pairs:
   - a state and
   - the action that produced the state from the previous one.

  The initial state is produced by the dummy action `Init`.
  We do not enforce the states to be connected by the `next` relation.
  See `is_path` and `is_run` for stronger conditions.
  -/
abbrev Trace := ℕ → StateAction Proc

/--
  Does a trace satisfy the reliable communication property:
  Every messages that is sent by a process `p`
  is received by every correct process `q` at the right time window later.
  -/
def is_reliable_communication (tr: Trace Proc) : Prop :=
  ∀ i: ℕ,
    ∀ m ∈ (tr i).s.sent,
      ∃ j: ℕ,
        let { s := s_j, a := a_j } := (tr j)
        j ≥ i
          ∧ isMsgTimely GST MsgDelay m.timestamp s_j.clock
          ∧ m.dst ∈ s_j.crashed
            ∨ match m.kind with
              | MsgTag.HeartbeatReply =>
                  a_j = Action.RcvHeartbeatReply m.src m.dst m.timestamp
              | MsgTag.HeartbeatRequest =>
                  a_j = Action.RcvHeartbeatRequest m.src m.dst m.timestamp

/--
  Does a sequence of states `seq` process timeouts fairly?
  -/
def is_fair_timeout (tr: Trace Proc): Prop :=
  ∀ i: ℕ,
    ∀ p: Proc,
      ∃ k: ℕ,
        (p ∉ (tr (i + k - 1)).s.crashed → (tr (i + k)).a = Action.Timeout p)
          -- TODO: is this a bit too strong in the presence of is_fair_clock?
          ∧ (tr (i + k)).s.clock = (tr i).s.nextTimeout[p]!

/--
  The global clock is advanced from time to time.
  -/
def is_fair_clock (tr: Trace Proc) : Prop :=
  ∀ i: ℕ,
    ∃ j: ℕ,
      j > i ∧ (tr j).a = Action.AdvanceClock

/--
  An infinite sequence of protocol states is a path, if every pair
  of states `(s_i, s_{i+1})` is a transition via `next`.
  A path does not have to start with an initial state.
  -/
def is_path (tr: Trace Proc) : Prop :=
  ∀ i: ℕ,
    next_a Proc InitDelay GST MsgDelay (tr i).s (tr (i + 1)).s (tr (i + 1)).a

/--
  An infinite sequence of protocol states is a run, if it starts
  with an initial states and it is a run.
  -/
def is_run (tr: Trace Proc) : Prop :=
  let s0 := (tr 0).s
  init Proc InitDelay s0 s0.all.toList
    ∧ is_path Proc InitDelay GST MsgDelay tr

/--
  Does a sequence of states `seq` represent a fair run of the protocol?
  -/
def is_fair_run (tr: Trace Proc) : Prop :=
  is_run Proc InitDelay GST MsgDelay tr
    ∧ is_reliable_communication Proc GST MsgDelay tr
    ∧ is_fair_timeout Proc tr
    ∧ is_fair_clock Proc tr

end fairness
