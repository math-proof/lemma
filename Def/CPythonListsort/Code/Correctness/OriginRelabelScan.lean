/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean -/

import Structure.CPythonListsort.Code.Correctness.OriginRelabelMerges
import Structure.CPythonListsort.Code.Correctness.ScanLoopCorrectness
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

end CPythonListsort
