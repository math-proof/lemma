/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean -/

import sympy.atlas.CPythonListsort.Code.Correctness.OccurrenceErasureMerges

/-!
# Occurrence erasure through merge policy and the top-level scan

This module continues structural occurrence erasure through `merge_at`, the
PowerSort policy, final collapse, cleanup, and the complete listsort evaluator.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

def eraseOccurrenceMergeAtResult
    (result : MergeAtResult (Occurrence alpha) nu) : MergeAtResult alpha nu :=
  { result with state := eraseOccurrenceMergeState result.state }

def eraseOccurrenceMergeAtCall
    (call : MergeAtCall (Occurrence alpha) nu) : MergeAtCall alpha nu :=
  { call with
    state := eraseOccurrenceMergeState call.state
    firstB := eraseOccurrenceEntry call.firstB
    lastA := eraseOccurrenceEntry call.lastA }

def eraseOccurrenceMergeAtPreparation :
    MergeAtPreparation (Occurrence alpha) nu → MergeAtPreparation alpha nu
  | .finished result => .finished (eraseOccurrenceMergeAtResult result)
  | .mergeLo call => .mergeLo (eraseOccurrenceMergeAtCall call)
  | .mergeHi call => .mergeHi (eraseOccurrenceMergeAtCall call)

def eraseOccurrenceFoundNewRunResult
    (result : FoundNewRunResult (Occurrence alpha) nu) :
    FoundNewRunResult alpha nu :=
  { result with state := eraseOccurrenceMergeState result.state }

def eraseOccurrenceMergeForceCollapseResult
    (result : MergeForceCollapseResult (Occurrence alpha) nu) :
    MergeForceCollapseResult alpha nu :=
  { result with state := eraseOccurrenceMergeState result.state }

@[simp] theorem eraseOccurrenceMergeAtResult_state
    (result : MergeAtResult (Occurrence alpha) nu) :
    (eraseOccurrenceMergeAtResult result).state =
      eraseOccurrenceMergeState result.state := rfl

@[simp] theorem eraseOccurrenceMergeAtResult_returnCode
    (result : MergeAtResult (Occurrence alpha) nu) :
    (eraseOccurrenceMergeAtResult result).returnCode = result.returnCode := rfl

@[simp] theorem eraseOccurrenceMergeAtResult_fuelExhausted
    (result : MergeAtResult (Occurrence alpha) nu) :
    (eraseOccurrenceMergeAtResult result).fuelExhausted =
      result.fuelExhausted := rfl

@[simp] theorem eraseOccurrenceMergeAtCall_state
    (call : MergeAtCall (Occurrence alpha) nu) :
    (eraseOccurrenceMergeAtCall call).state =
      eraseOccurrenceMergeState call.state := rfl

@[simp] theorem eraseOccurrenceMergeAtCall_firstB
    (call : MergeAtCall (Occurrence alpha) nu) :
    (eraseOccurrenceMergeAtCall call).firstB =
      eraseOccurrenceEntry call.firstB := rfl

@[simp] theorem eraseOccurrenceMergeAtCall_lastA
    (call : MergeAtCall (Occurrence alpha) nu) :
    (eraseOccurrenceMergeAtCall call).lastA =
      eraseOccurrenceEntry call.lastA := rfl

@[simp] theorem eraseOccurrenceMergeAtCall_ssa
    (call : MergeAtCall (Occurrence alpha) nu) :
    (eraseOccurrenceMergeAtCall call).ssa = call.ssa := rfl

@[simp] theorem eraseOccurrenceMergeAtCall_ssb
    (call : MergeAtCall (Occurrence alpha) nu) :
    (eraseOccurrenceMergeAtCall call).ssb = call.ssb := rfl

@[simp] theorem eraseOccurrenceMergeAtCall_na
    (call : MergeAtCall (Occurrence alpha) nu) :
    (eraseOccurrenceMergeAtCall call).na = call.na := rfl

@[simp] theorem eraseOccurrenceMergeAtCall_nb
    (call : MergeAtCall (Occurrence alpha) nu) :
    (eraseOccurrenceMergeAtCall call).nb = call.nb := rfl

@[simp] theorem eraseOccurrenceMergeAtPreparation_state
    (preparation : MergeAtPreparation (Occurrence alpha) nu) :
    (eraseOccurrenceMergeAtPreparation preparation).state =
      eraseOccurrenceMergeState preparation.state := by
  cases preparation <;> rfl

@[simp] theorem eraseOccurrenceFoundNewRunResult_state
    (result : FoundNewRunResult (Occurrence alpha) nu) :
    (eraseOccurrenceFoundNewRunResult result).state =
      eraseOccurrenceMergeState result.state := rfl

@[simp] theorem eraseOccurrenceFoundNewRunResult_returnCode
    (result : FoundNewRunResult (Occurrence alpha) nu) :
    (eraseOccurrenceFoundNewRunResult result).returnCode =
      result.returnCode := rfl

@[simp] theorem eraseOccurrenceFoundNewRunResult_fuelExhausted
    (result : FoundNewRunResult (Occurrence alpha) nu) :
    (eraseOccurrenceFoundNewRunResult result).fuelExhausted =
      result.fuelExhausted := rfl

@[simp] theorem eraseOccurrenceMergeForceCollapseResult_state
    (result : MergeForceCollapseResult (Occurrence alpha) nu) :
    (eraseOccurrenceMergeForceCollapseResult result).state =
      eraseOccurrenceMergeState result.state := rfl

@[simp] theorem eraseOccurrenceMergeForceCollapseResult_returnCode
    (result : MergeForceCollapseResult (Occurrence alpha) nu) :
    (eraseOccurrenceMergeForceCollapseResult result).returnCode =
      result.returnCode := rfl

@[simp] theorem eraseOccurrenceMergeForceCollapseResult_fuelExhausted
    (result : MergeForceCollapseResult (Occurrence alpha) nu) :
    (eraseOccurrenceMergeForceCollapseResult result).fuelExhausted =
      result.fuelExhausted := rfl

private def listSortScanAfterExtension? {kappa : Type u} (fuel : Nat)
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

private def listSortScanAfterCount? {kappa : Type u} (fuel : Nat)
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
