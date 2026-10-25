/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanStepCorrectness.lean -/

import Structure.CPythonListsort.Code.Assembly.ListSortTermination
import Def.CPythonListsort.Code.Correctness.BinarysortCorrectness.Part3
import Def.CPythonListsort.Code.Correctness.CountRunCorrectness.Part2
import Def.CPythonListsort.Code.Correctness.FoundNewRunCorrectness
import Theorem.CPythonListsort.Code.Correctness.ScanCorrectnessSupport
import Theorem.CPythonListsort.Code.Correctness.ScanStepSupport
import Def.CPythonListsort.Code.Correctness.ScanStepCorrectness
/-!
# Correctness of one forward scan iteration

This module stops at the recursive-call boundary of `listSortScan?`.  It
combines the already-reviewed safety invariant with pending-run correctness,
the whole-entry unscanned snapshot, and the persistent input permutation.
-/


namespace CPythonListsort

universe u v

variable {α : Type u} {ν : Type v}

/-- Internal boundary between run formation (`count_run` plus optional
`binarysort`) and the policy/push phase.  The explicit `stable` field is the
whole-target premise/output at the binarysort boundary. -/
structure ListSortRunFormationPost
    (lt : BoolComparator α) (source : SortSlice α ν) (hasKeyfunc : Bool)
    (inputSize fuel : Nat) (call : MergeState (Occurrence α) ν)
    (lo scanned remaining : Nat) (reverse : Bool)
    (formed : MergeState (Occurrence α) ν) (consumed : Nat) : Prop where
  positive : 0 < consumed
  within : consumed ≤ remaining
  listlen : formed.listlen = call.listlen
  basekeys : formed.basekeys = call.basekeys
  extent : formed.data.entries.size = call.data.entries.size
  hasValues : formed.a.hasValues = call.a.hasValues
  comparator : formed.key_compare = call.key_compare
  tempInvariant : TempStorageInv formed.a formed.alloced
  tempLive : formed.a.Live
  physicalBound :
    (MergeMemorySnapshot.ofState formed).PhysicalBound
  valuesMode : SortSlice.ValuesModeInvariant formed.a.hasValues formed.data
  poweredPrefix : PoweredPrefix formed
  pendingRunsCorrect : PendingRunsCorrect lt
    (source.entries.map SortSliceEntry.key) formed scanned
  entrySnapshot : EntrySnapshotPermutation source formed.data
  frame : SortSlice.EqualOutsideRange call.data formed.data
    (call.basekeys + scanned) consumed
  sorted : Sorted (occurrenceComparator lt)
    (sortSliceRangeKeys formed.data (call.basekeys + scanned) consumed)
  stable : StableOccurrencePermutation lt
    (canonicalOccurrenceSegment (source.entries.map SortSliceEntry.key)
      (call.basekeys + scanned) consumed)
    (sortSliceRangeKeys formed.data
      (call.basekeys + scanned) consumed).toList
  adaptiveAfter : 0 < remaining - consumed →
    ∃ calls, AdaptiveMinrunScanInvariant formed.listlen calls
      (scanned + consumed) formed.minrunState
  scanEquationBeforeFound :
    listSortScan? (fuel + 1) call lo remaining reverse inputSize =
      listSortAfterExtension?
        (fun nextState nextLo nextRemaining =>
          listSortScan? fuel nextState nextLo nextRemaining reverse inputSize)
        lo remaining reverse inputSize (formed, consumed, false)

end CPythonListsort
