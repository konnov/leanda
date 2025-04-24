/-
The tests that are supposed to be failing: We use PBT to find counterexamples.

Copyright (c) 2025 Igor Konnov
Released under MIT license as described in the file LICENSE.
Authors: Igor Konnov, 2025
 -/
import Twophase4_pbt

open Plausible

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
