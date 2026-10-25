/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean -/

import Theorem.CPythonListsort.Code.Correctness.OccurrenceErasureMerges.Part2
import Def.CPythonListsort.Code.Correctness.OccurrenceErasureScan
/-!
# Occurrence erasure through merge policy and the top-level scan

This module continues structural occurrence erasure through `merge_at`, the
PowerSort policy, final collapse, cleanup, and the complete listsort evaluator.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

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

end CPythonListsort
