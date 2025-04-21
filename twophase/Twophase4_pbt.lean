/-
Property-based testing of the two-phase commit protocol with Plausible.

Copyright (c) 2025 Igor Konnov
Released under MIT license as described in the file LICENSE.
Authors: Igor Konnov, 2025
 -/
import Plausible
import Twophase.System

open Plausible

-- We fix the number of resource managers to 4.
def N : Nat := 4

theorem N_ne_zero: N ≠ 0 :=
  by decide

def genRm: Gen (Fin N) :=
  -- FIXME: figure out how to use `Random.randFin`
  (Gen.elements [
      @Fin.ofNat' N ⟨N_ne_zero⟩ 0,
      @Fin.ofNat' N ⟨N_ne_zero⟩ 1,
      @Fin.ofNat' N ⟨N_ne_zero⟩ 2,
      @Fin.ofNat' N ⟨N_ne_zero⟩ 3
    ]
    (by decide))

instance : Shrinkable (Fin N) where
  shrink := fun (_: Fin N) => []

instance : SampleableExt (Fin N) :=
  SampleableExt.mkSelfContained genRm

-- define a generator for Action RM
instance Action.shrinkable: Shrinkable (Action N) where
  shrink := fun (_: Action N) => []

def genAction: Gen (Action N) :=
  Gen.oneOf #[
    Gen.elements [ Action.TMCommit, Action.TMAbort] (by decide),
    (do return (Action.TMRcvPrepared (← genRm))),
    (do return (Action.RMPrepare (← genRm))),
    (do return (Action.RMChooseToAbort (← genRm))),
    (do return (Action.RMRcvCommitMsg (← genRm))),
    (do return (Action.RMRcvAbortMsg (← genRm)))
  ]
  (by decide)

instance : SampleableExt (Action N) :=
  SampleableExt.mkSelfContained genAction

#sample Action N

def genSchedule: Gen (List (Action N)) :=
  Gen.listOf genAction

-- given a concrete schedule, inductively apply the schedule and check the invariant
def applySchedule (s: ProtocolState N) (schedule: List (Action N))
    (inv: ProtocolState N → Bool): ProtocolState N :=
  schedule.foldl (fun s a => if inv s then (next s a).getD s else s) s

-- apply a schedule to the initial state
def checkInvariant (schedule: List (Action N)) (inv: ProtocolState N → Bool): Bool :=
  let init_s := init
  let last_s := applySchedule init_s schedule inv
  inv last_s

-- noAbortEx
example (schedule: List (Action N)):
    let inv := fun (s: ProtocolState N) =>
      s.tmState ≠ TMState.Aborted
    checkInvariant schedule inv
  := by plausible (config := { numInst := 3000, maxSize := 100 })

-- noCommitEx
example (schedule: List (Action N)):
    let inv := fun (s: ProtocolState N) =>
      s.tmState ≠ TMState.Committed
    checkInvariant schedule inv
  := by plausible (config := { numInst := 3000, maxSize := 100 })

-- noAbortOnAllPreparedEx
example (schedule: List (Action N)):
    let inv := fun (s: ProtocolState N) =>
      s.tmState = TMState.Aborted → s.tmPrepared ≠ AllRM
    checkInvariant schedule inv
  := by plausible (config := { numInst := 3000, maxSize := 100 })

-- consistentInv
#eval Testable.check <| ∀ (schedule: List (Action N)),
    let inv := fun (s: ProtocolState N) =>
      let existsAborted :=
        ∅ ≠ (Finset.filter (fun rm => s.rmState.get? rm = RMState.Aborted) AllRM)
      let existsCommitted :=
        ∅ ≠ (Finset.filter (fun rm => s.rmState.get? rm = RMState.Committed) AllRM)
      ¬existsAborted ∨ ¬existsCommitted
    checkInvariant schedule inv
