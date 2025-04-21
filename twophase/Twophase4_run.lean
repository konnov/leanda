/-
A randomised simulation of the Two-phase commit protocol.

Copyright (c) 2025 Igor Konnov
Released under MIT license as described in the file LICENSE.
Authors: Igor Konnov, 2025
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold

import Twophase.Functional
import Twophase.System

-- An instance of four resource managers.
inductive RM
  | RM1
  | RM2
  | RM3
  | RM4
  deriving Repr, DecidableEq, Hashable, Inhabited

def mkAction (action_no: Nat) (rm_no: Nat): @Action RM :=
  let rm := match rm_no with
    | 0 => RM.RM1
    | 1 => RM.RM2
    | 2 => RM.RM3
    | _ => RM.RM4
  match action_no with
  | 0 => Action.TMCommit
  | 1 => Action.TMAbort
  | 2 => Action.TMRcvPrepared rm
  | 3 => Action.RMPrepare rm
  | 4 => Action.RMChooseToAbort rm
  | 5 => Action.RMRcvCommitMsg rm
  | _ => Action.RMRcvAbortMsg rm

def help: String :=
  "❌ Arguments: <number of runs> <number of steps> <invariant> <seed>"

def parseNat (s: String): IO Nat :=
  match s.toNat? with
  | some k => pure k
  | none   => panic! help

-- This is a false invariant to demonstrate that TM can abort.
def noAbortEx (s: ProtocolState RM): Bool :=
  s.tmState ≠ TMState.Aborted

-- This is a false invariant to demonstrate that TM can commit.
def noCommitEx (s: ProtocolState RM): Bool :=
  s.tmState ≠ TMState.Committed

-- This is a false invariant for a trickier property:
-- Even though all resource managers are prepared, the TM can still abort.
def noAbortOnAllPreparedEx (s: ProtocolState RM): Bool :=
  s.tmState = TMState.Aborted → s.tmPrepared ≠ s.all

-- the main invariant of the protocol, namely, that resource managers cannot disagree
def consistentInv (s: ProtocolState RM): Bool :=
  let existsAborted :=
    ∅ ≠ (Finset.filter (fun rm => s.rmState.get? rm = RMState.Aborted) s.all)
  let existsCommitted :=
    ∅ ≠ (Finset.filter (fun rm => s.rmState.get? rm = RMState.Committed) s.all)
  ¬existsAborted ∨ ¬existsCommitted

def main (args: List String): IO UInt32 := do
  -- parse the arguments
  let mut maxSamples := 10000
  let mut maxSteps := 10
  let mut seed := 0
  let mut inv := fun (_: ProtocolState RM) => true
  match args with
  | [ maxSamples_s, maxSteps_s, inv_s, seed_s ] =>
    maxSamples ← parseNat maxSamples_s
    maxSteps ← parseNat maxSteps_s
    seed ← parseNat seed_s
    match inv_s with
    | "noAbortEx" => inv := noAbortEx
    | "noCommitEx" => inv := noCommitEx
    | "noAbortOnAllPreparedEx" => inv := noAbortOnAllPreparedEx
    | "consistentInv" => inv := consistentInv
    | _ =>
      IO.eprintln help;
      return 1

  | _ =>
    IO.eprintln help;
    return 1

  -- run a loop of `maxSamples`
  let mut rng := mkStdGen seed
  for trial in [0:maxSamples] do
    let mut state := init [ RM.RM1, RM.RM2, RM.RM3, RM.RM4 ]
    -- run a loop of `maxSteps` steps
    let mut trace: List (@Action RM) := []
    for _ in [0:maxSteps] do
      let (action_no, next_rng) := randNat rng 0 6
      let (rm_no, next_rng) := randNat next_rng 0 3
      rng := next_rng
      let action := mkAction action_no rm_no
      match next state action with
      | some new_state =>
        state := new_state
        trace := action::trace
      | none => pure ()

      -- check our invariant
      if ¬inv state then
        IO.println s!"❌ Counterexample found after {trial} trials"
        for (a, i) in trace.reverse.zipIdx 0 do
          IO.println s!"#{i}: {repr a}"
        return 1

  return 0
