/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean -/

import Theorem.CPythonListsort.Code.Correctness.OccurrenceErasureMerges.Part2
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

end CPythonListsort
