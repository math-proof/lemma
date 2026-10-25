/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean -/

import Structure.CPythonListsort.Code.Correctness.OriginRelabelMerges
import Structure.CPythonListsort.Code.Correctness.ScanLoopCorrectness
import Def.CPythonListsort.Code.Correctness.OriginRelabelScan
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

end CPythonListsort
