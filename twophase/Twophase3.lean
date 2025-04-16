-- This module serves as the root of the `Twophase` library.
-- Import modules here that should be built as part of the library.
import Mathlib.Data.Finset.Basic

import Twophase.Functional
import Twophase.System

-- An instance of three resource managers.
inductive RM
  | RM1
  | RM2
  | RM3
  deriving Repr, DecidableEq, Hashable

def gen_action (action_no: Nat) (rm_no: Nat): Action RM :=
  let rm := match rm_no with
    | 0 => RM.RM1
    | 1 => RM.RM2
    | _ => RM.RM3
  match action_no with
  | 0 => Action.TMCommit
  | 1 => Action.TMAbort
  | 2 => Action.TMRcvPrepared rm
  | 3 => Action.RMPrepare rm
  | 4 => Action.RMChooseToAbort rm
  | 5 => Action.RMRcvCommitMsg rm
  | _ => Action.RMRcvAbortMsg rm

def main (args: List String): IO UInt32 := do
  -- parse the arguments
  let mut n := 10
  let mut seed := 0
  match args with
  | [ n_s, seed_s ] =>
    match n_s.toNat? with
    | some k =>
      n := k
    | none   =>
      IO.eprintln s!"❌ Arguments: <number of steps> <seed>";
      return 1
    match seed_s.toNat? with
    | some k =>
      seed := k
    | none   =>
      IO.eprintln s!"❌ Arguments: <number of steps> <seed>";
      return 1
  | _ =>
    IO.eprintln s!"❌ Expected the number of steps as the first argument.";
    return 1

  -- run a loop of n steps
  let mut rng := mkStdGen seed
  let mut state := init RM [ RM.RM1, RM.RM2, RM.RM3 ]
  for i in [0:n] do
    let (action_no, next_rng) := randNat rng 0 6
    let (rm_no, next_rng) := randNat next_rng 0 2
    rng := next_rng
    let action := gen_action action_no rm_no
    match next RM state action with
    | some new_state =>
      state := new_state
      IO.println s!"action {i}: {repr action}"
    | none => pure ()

  return 0
