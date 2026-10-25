/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanStepCorrectness.lean -/

import Structure.CPythonListsort.Code.Assembly.ListSortTermination
import Def.CPythonListsort.Code.Correctness.BinarysortCorrectness.Part3
import Def.CPythonListsort.Code.Correctness.CountRunCorrectness.Part2
import Def.CPythonListsort.Code.Correctness.FoundNewRunCorrectness
import Theorem.CPythonListsort.Code.Correctness.ScanCorrectnessSupport
import Theorem.CPythonListsort.Code.Correctness.ScanStepSupport
/-!
# Correctness of one forward scan iteration

This module stops at the recursive-call boundary of `listSortScan?`.  It
combines the already-reviewed safety invariant with pending-run correctness,
the whole-entry unscanned snapshot, and the persistent input permutation.
-/


namespace CPythonListsort

universe u v

variable {α : Type u} {ν : Type v}

/-- Full induction invariant for the occurrence-carrying forward scan. -/
structure ListSortScanCorrectnessInvariant
    (lt : BoolComparator α) (source : SortSlice α ν) (hasKeyfunc : Bool)
    (inputSize : Nat) (state : MergeState (Occurrence α) ν)
    (lo scanned remaining : Nat) : Prop where
  safety : ListSortScanInvariant (occurrenceComparator lt) hasKeyfunc inputSize
    state lo scanned remaining
  pendingRunsCorrect : PendingRunsCorrect lt
    (source.entries.map SortSliceEntry.key) state scanned
  remainderEntries : ScanRemainderEntriesMatch source state scanned
  entrySnapshot : EntrySnapshotPermutation source state.data

/-- Observable result of exactly one nonterminal scan iteration.  The equation
mentions the real raw evaluator and exposes the precise recursive call. -/
structure ListSortScanStepCorrectnessPost
    (lt : BoolComparator α) (source : SortSlice α ν) (hasKeyfunc : Bool)
    (inputSize fuel : Nat) (state : MergeState (Occurrence α) ν)
    (lo scanned remaining : Nat) (reverse : Bool)
    (consumed : Nat) (nextState : MergeState (Occurrence α) ν) : Prop where
  consumedPositive : 0 < consumed
  consumedWithin : consumed ≤ remaining
  consumedPrefixFrame : SortSlice.EqualOutsideRange state.data nextState.data
    state.basekeys (scanned + consumed)
  scanEquation :
    listSortScan? (fuel + 1) state lo remaining reverse inputSize =
      listSortScan? fuel nextState (lo + consumed) (remaining - consumed)
        reverse inputSize
  nextInvariant : ListSortScanCorrectnessInvariant lt source hasKeyfunc
    inputSize nextState (lo + consumed) (scanned + consumed)
      (remaining - consumed)

end CPythonListsort
