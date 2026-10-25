/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean -/

import Theorem.CPythonListsort.Code.Correctness.OccurrenceErasureMerges.Part2
import Theorem.CPythonListsort.Code.Correctness.OccurrenceErasureScan
/-!
# Occurrence erasure through merge policy and the top-level scan

This module continues structural occurrence erasure through `merge_at`, the
PowerSort policy, final collapse, cleanup, and the complete listsort evaluator.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

def listSortScanAfterExtension? {kappa : Type u} (fuel : Nat)
    (state : MergeState kappa nu) (lo remaining : Nat)
    (reverse : Bool) (inputSize runLength : Nat) (extensionFuel : Bool) :
    Option (ListSortImplResult kappa nu) :=
  let runLength := runLength
  let extensionFuel := extensionFuel
  if extensionFuel then
    finishListSort? state reverse inputSize (-1) true
  else if runLength = 0 ∨ remaining < runLength then
    none
  else
    match foundNewRun? state runLength with
    | none => none
    | some found =>
        if found.returnCode = 0 ∧ !found.fuelExhausted then
          let newRun : PendingRun :=
            { base := lo
              len := BitVec.ofNat 64 runLength
              power := none }
          let state := pushPendingRun found.state newRun
          listSortScan? fuel state (lo + runLength) (remaining - runLength)
            reverse inputSize
        else
          failFromFoundNewRun? found reverse inputSize

def listSortScanAfterCount? {kappa : Type u} (fuel : Nat)
    (state : MergeState kappa nu) (lo remaining : Nat)
    (reverse : Bool) (inputSize : Nat)
    (counted : CountRunResult kappa nu) :
    Option (ListSortImplResult kappa nu) :=
  let state := { state with data := counted.slice }
  if counted.fuelExhausted then
    finishListSort? state reverse inputSize (-1) true
  else if counted.length = 0 ∨ remaining < counted.length then
    none
  else do
    let nextMinrun := minrunNext state.minrunState
    let state := installMinrunState state nextMinrun.state
    let runLength := counted.length
    let target := nextMinrun.result.toNat
    let force := if remaining ≤ target then remaining else target
    let extended ←
      if (BitVec.ofNat 64 runLength : PySSize).slt nextMinrun.result then
        match binarysort? state state.data (Int.ofNat lo) force runLength with
        | none => none
        | some sorted => some (sorted.slice, force, sorted.fuelExhausted)
      else
        some (state.data, runLength, false)
    let state := { state with data := extended.1 }
    listSortScanAfterExtension? fuel state lo remaining reverse inputSize
      extended.2.1 extended.2.2

end CPythonListsort
