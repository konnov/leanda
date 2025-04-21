/-
Property-based testing of the two-phase commit protocol with Plausible.

Copyright (c) 2025 Igor Konnov
Released under MIT license as described in the file LICENSE.
Authors: Igor Konnov, 2025
 -/
import Plausible
import Twophase.System

open Plausible

set_option maxRecDepth 1000000

-- An instance of three resource managers.
inductive RM
  | RM1
  | RM2
  | RM3
  | RM4
  deriving Repr, DecidableEq, Hashable, Inhabited

-- define a generator for RM
instance RM.shrinkable: Shrinkable RM where
  shrink := fun (_: RM) => []

def genRm: Gen RM := (Gen.elements [ RM.RM1, RM.RM2, RM.RM3, RM.RM4 ] (by decide))

instance : SampleableExt RM :=
  SampleableExt.mkSelfContained genRm

#sample RM

-- define a generator for Action RM
instance Action.shrinkable: Shrinkable (@Action RM) where
  shrink := fun (_: @Action RM) => []

def genAction: Gen (@Action RM) :=
  Gen.oneOf #[
    Gen.elements [ Action.TMCommit, Action.TMAbort] (by decide),
    (do return (Action.TMRcvPrepared (← genRm))),
    (do return (Action.RMPrepare (← genRm))),
    (do return (Action.RMChooseToAbort (← genRm))),
    (do return (Action.RMRcvCommitMsg (← genRm))),
    (do return (Action.RMRcvAbortMsg (← genRm)))
  ]
  (by decide)

instance : SampleableExt (@Action RM) :=
  SampleableExt.mkSelfContained genAction

#sample @Action RM

def genSchedule: Gen (List (@Action RM)) :=
  Gen.listOf genAction

-- given a concrete schedule, inductively apply the schedule and check the invariant
def applySchedule (s: ProtocolState RM) (schedule: List (@Action RM))
    (inv: ProtocolState RM → Bool): ProtocolState RM :=
  schedule.foldl (fun s a => if inv s then (next s a).getD s else s) s

-- apply a schedule to the initial state
def checkInvariant (schedule: List (@Action RM)) (inv: ProtocolState RM → Bool): Bool :=
  let init_s := init [ RM.RM1, RM.RM2, RM.RM3, RM.RM4 ]
  let last_s := applySchedule init_s schedule inv
  inv last_s

-- noAbortEx
example schedule:
    let inv := fun (s: ProtocolState RM) =>
      s.tmState ≠ TMState.Aborted
    checkInvariant schedule inv
  := by plausible (config := { numInst := 3000, maxSize := 100 })

-- noCommitEx
example schedule:
    let inv := fun (s: ProtocolState RM) =>
      s.tmState ≠ TMState.Committed
    checkInvariant schedule inv
  := by plausible (config := { numInst := 3000, maxSize := 100 })

-- noAbortOnAllPreparedEx
example schedule:
    let inv := fun (s: ProtocolState RM) =>
      s.tmState = TMState.Aborted → s.tmPrepared ≠ { RM.RM1, RM.RM2, RM.RM3, RM.RM4 }
    checkInvariant schedule inv
  := by plausible (config := { numInst := 3000, maxSize := 100 })

-- consistentInv
#eval Testable.check <| ∀ (schedule: List (@Action RM)),
    let inv := fun (s: ProtocolState RM) =>
      let existsAborted :=
        ∅ ≠ (Finset.filter (fun rm => s.rmState.get? rm = RMState.Aborted) s.all)
      let existsCommitted :=
        ∅ ≠ (Finset.filter (fun rm => s.rmState.get? rm = RMState.Committed) s.all)
      ¬existsAborted ∨ ¬existsCommitted
    checkInvariant schedule inv
