/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean -/

import sympy.atlas.CPythonListsort.Code.Correctness.OriginRelabelMerges
import sympy.atlas.CPythonListsort.Code.Correctness.ScanLoopCorrectness

/-!
# Origin relabeling through policy and scan evaluators

This module continues `OriginRelabelMerges` through the raw `merge_at`,
PowerSort-policy, final-collapse, cleanup, and scan evaluators.  Occurrence
origins are proof metadata: every executable comparison observes only the
underlying value, so uniformly mirroring origins commutes with these
evaluators when the state's comparator is the lifted value comparator.

The statements here are deliberately about the raw, untraced evaluator.  The
trace model records concrete entries and therefore needs its own separately
reviewed transport argument.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-! ## Result and continuation relabelings -/

/-- Relabel the occurrence-bearing state returned by `merge_at`. -/
def mirrorMergeAtResult (size : Nat)
    (result : MergeAtResult (Occurrence alpha) nu) :
    MergeAtResult (Occurrence alpha) nu :=
  { result with state := mirrorMergeState size result.state }

/-- Relabel the occurrence-bearing fields retained at a `merge_at` callsite. -/
def mirrorMergeAtCall (size : Nat)
    (call : MergeAtCall (Occurrence alpha) nu) :
    MergeAtCall (Occurrence alpha) nu :=
  { call with
    state := mirrorMergeState size call.state
    firstB := mirrorSortSliceEntry size call.firstB
    lastA := mirrorSortSliceEntry size call.lastA }

/-- Relabel any continuation selected by `prepareMergeAt?`. -/
def mirrorMergeAtPreparation (size : Nat) :
    MergeAtPreparation (Occurrence alpha) nu →
      MergeAtPreparation (Occurrence alpha) nu
  | .finished result => .finished (mirrorMergeAtResult size result)
  | .mergeLo call => .mergeLo (mirrorMergeAtCall size call)
  | .mergeHi call => .mergeHi (mirrorMergeAtCall size call)

/-- Relabel the occurrence-bearing state returned by `foundNewRun?`. -/
def mirrorFoundNewRunResult (size : Nat)
    (result : FoundNewRunResult (Occurrence alpha) nu) :
    FoundNewRunResult (Occurrence alpha) nu :=
  { result with state := mirrorMergeState size result.state }

/-- Relabel the occurrence-bearing state returned by final collapse. -/
def mirrorMergeForceCollapseResult (size : Nat)
    (result : MergeForceCollapseResult (Occurrence alpha) nu) :
    MergeForceCollapseResult (Occurrence alpha) nu :=
  { result with state := mirrorMergeState size result.state }

/-- Relabel the occurrence-bearing state returned by the top-level scan. -/
def mirrorListSortImplResult (size : Nat)
    (result : ListSortImplResult (Occurrence alpha) nu) :
    ListSortImplResult (Occurrence alpha) nu :=
  { result with state := mirrorMergeState size result.state }

@[simp] theorem mirrorMergeAtResult_state (size : Nat)
    (result : MergeAtResult (Occurrence alpha) nu) :
    (mirrorMergeAtResult size result).state =
      mirrorMergeState size result.state := rfl

@[simp] theorem mirrorMergeAtResult_returnCode (size : Nat)
    (result : MergeAtResult (Occurrence alpha) nu) :
    (mirrorMergeAtResult size result).returnCode = result.returnCode := rfl

@[simp] theorem mirrorMergeAtResult_fuelExhausted (size : Nat)
    (result : MergeAtResult (Occurrence alpha) nu) :
    (mirrorMergeAtResult size result).fuelExhausted =
      result.fuelExhausted := rfl

@[simp] theorem mirrorMergeAtCall_state (size : Nat)
    (call : MergeAtCall (Occurrence alpha) nu) :
    (mirrorMergeAtCall size call).state = mirrorMergeState size call.state := rfl

@[simp] theorem mirrorMergeAtCall_firstB (size : Nat)
    (call : MergeAtCall (Occurrence alpha) nu) :
    (mirrorMergeAtCall size call).firstB =
      mirrorSortSliceEntry size call.firstB := rfl

@[simp] theorem mirrorMergeAtCall_lastA (size : Nat)
    (call : MergeAtCall (Occurrence alpha) nu) :
    (mirrorMergeAtCall size call).lastA =
      mirrorSortSliceEntry size call.lastA := rfl

@[simp] theorem mirrorMergeAtCall_ssa (size : Nat)
    (call : MergeAtCall (Occurrence alpha) nu) :
    (mirrorMergeAtCall size call).ssa = call.ssa := rfl

@[simp] theorem mirrorMergeAtCall_ssb (size : Nat)
    (call : MergeAtCall (Occurrence alpha) nu) :
    (mirrorMergeAtCall size call).ssb = call.ssb := rfl

@[simp] theorem mirrorMergeAtCall_na (size : Nat)
    (call : MergeAtCall (Occurrence alpha) nu) :
    (mirrorMergeAtCall size call).na = call.na := rfl

@[simp] theorem mirrorMergeAtCall_nb (size : Nat)
    (call : MergeAtCall (Occurrence alpha) nu) :
    (mirrorMergeAtCall size call).nb = call.nb := rfl

@[simp] theorem mirrorMergeAtPreparation_state (size : Nat)
    (preparation : MergeAtPreparation (Occurrence alpha) nu) :
    (mirrorMergeAtPreparation size preparation).state =
      mirrorMergeState size preparation.state := by
  cases preparation <;> rfl

@[simp] theorem mirrorFoundNewRunResult_state (size : Nat)
    (result : FoundNewRunResult (Occurrence alpha) nu) :
    (mirrorFoundNewRunResult size result).state =
      mirrorMergeState size result.state := rfl

@[simp] theorem mirrorFoundNewRunResult_returnCode (size : Nat)
    (result : FoundNewRunResult (Occurrence alpha) nu) :
    (mirrorFoundNewRunResult size result).returnCode = result.returnCode := rfl

@[simp] theorem mirrorFoundNewRunResult_fuelExhausted (size : Nat)
    (result : FoundNewRunResult (Occurrence alpha) nu) :
    (mirrorFoundNewRunResult size result).fuelExhausted =
      result.fuelExhausted := rfl

@[simp] theorem mirrorMergeForceCollapseResult_state (size : Nat)
    (result : MergeForceCollapseResult (Occurrence alpha) nu) :
    (mirrorMergeForceCollapseResult size result).state =
      mirrorMergeState size result.state := rfl

@[simp] theorem mirrorMergeForceCollapseResult_returnCode (size : Nat)
    (result : MergeForceCollapseResult (Occurrence alpha) nu) :
    (mirrorMergeForceCollapseResult size result).returnCode =
      result.returnCode := rfl

@[simp] theorem mirrorMergeForceCollapseResult_fuelExhausted (size : Nat)
    (result : MergeForceCollapseResult (Occurrence alpha) nu) :
    (mirrorMergeForceCollapseResult size result).fuelExhausted =
      result.fuelExhausted := rfl

@[simp] theorem mirrorListSortImplResult_state (size : Nat)
    (result : ListSortImplResult (Occurrence alpha) nu) :
    (mirrorListSortImplResult size result).state =
      mirrorMergeState size result.state := rfl

@[simp] theorem mirrorListSortImplResult_returnCode (size : Nat)
    (result : ListSortImplResult (Occurrence alpha) nu) :
    (mirrorListSortImplResult size result).returnCode = result.returnCode := rfl

@[simp] theorem mirrorListSortImplResult_fuelExhausted (size : Nat)
    (result : ListSortImplResult (Occurrence alpha) nu) :
    (mirrorListSortImplResult size result).fuelExhausted =
      result.fuelExhausted := rfl

@[simp] theorem mirrorMergeAtResult_involutive (size : Nat)
    (result : MergeAtResult (Occurrence alpha) nu) :
    mirrorMergeAtResult size (mirrorMergeAtResult size result) = result := by
  cases result
  simp [mirrorMergeAtResult]

@[simp] theorem mirrorMergeAtCall_involutive (size : Nat)
    (call : MergeAtCall (Occurrence alpha) nu) :
    mirrorMergeAtCall size (mirrorMergeAtCall size call) = call := by
  cases call
  simp [mirrorMergeAtCall]

@[simp] theorem mirrorMergeAtPreparation_involutive (size : Nat)
    (preparation : MergeAtPreparation (Occurrence alpha) nu) :
    mirrorMergeAtPreparation size
        (mirrorMergeAtPreparation size preparation) = preparation := by
  cases preparation <;> simp [mirrorMergeAtPreparation]

@[simp] theorem mirrorFoundNewRunResult_involutive (size : Nat)
    (result : FoundNewRunResult (Occurrence alpha) nu) :
    mirrorFoundNewRunResult size (mirrorFoundNewRunResult size result) =
      result := by
  cases result
  simp [mirrorFoundNewRunResult]

@[simp] theorem mirrorMergeForceCollapseResult_involutive (size : Nat)
    (result : MergeForceCollapseResult (Occurrence alpha) nu) :
    mirrorMergeForceCollapseResult size
        (mirrorMergeForceCollapseResult size result) = result := by
  cases result
  simp [mirrorMergeForceCollapseResult]

@[simp] theorem mirrorListSortImplResult_involutive (size : Nat)
    (result : ListSortImplResult (Occurrence alpha) nu) :
    mirrorListSortImplResult size (mirrorListSortImplResult size result) =
      result := by
  cases result
  simp [mirrorListSortImplResult]

/-! ## Scan continuations -/

/-- The continuation shared by the binarysort and already-long-enough arms of
one scan iteration.  This is definitionally the tail of `listSortScan?`; naming
it keeps the origin-parametricity proof aligned with the evaluator's actual
control-flow boundary. -/
private def listSortScanAfterExtension? (fuel : Nat)
    (state : MergeState (Occurrence alpha) nu) (lo remaining : Nat)
    (reverse : Bool) (inputSize runLength : Nat) (extensionFuel : Bool) :
    Option (ListSortImplResult (Occurrence alpha) nu) :=
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

/-- The portion of one scan iteration following a successful natural-run
scan.  It is a definitional factorization of the corresponding `do`-block in
`listSortScan?`, not a second evaluator specification. -/
private def listSortScanAfterCount? (fuel : Nat)
    (state : MergeState (Occurrence alpha) nu) (lo remaining : Nat)
    (reverse : Bool) (inputSize : Nat)
    (counted : CountRunResult (Occurrence alpha) nu) :
    Option (ListSortImplResult (Occurrence alpha) nu) :=
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
