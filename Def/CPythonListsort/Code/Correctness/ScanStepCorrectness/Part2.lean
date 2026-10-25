/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanStepCorrectness.lean -/

import Structure.CPythonListsort.Code.Assembly.ListSortTermination
import Def.CPythonListsort.Code.Correctness.BinarysortCorrectness.Part3
import Def.CPythonListsort.Code.Correctness.CountRunCorrectness.Part2
import Def.CPythonListsort.Code.Correctness.FoundNewRunCorrectness
import Theorem.CPythonListsort.Code.Correctness.ScanCorrectnessSupport
import Theorem.CPythonListsort.Code.Correctness.ScanStepSupport
import Structure.CPythonListsort.Code.Correctness.ScanStepCorrectness.Part2
/-!
# Correctness of one forward scan iteration

This module stops at the recursive-call boundary of `listSortScan?`.  It
combines the already-reviewed safety invariant with pending-run correctness,
the whole-entry unscanned snapshot, and the persistent input permutation.
-/


namespace CPythonListsort

universe u v

variable {α : Type u} {ν : Type v}

/-! ## Concrete branch witnesses -/

def scanStepRegressionLt : BoolComparator Nat :=
  fun left right => decide (left < right)

def scanStepRegressionEntry (value origin payload : Nat) :
    SortSliceEntry (Occurrence Nat) Nat :=
  { key := { value := value, origin := origin }, value := some payload }

def scanStepExtensionSlice : SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[scanStepRegressionEntry 99 0 10,
        scanStepRegressionEntry 3 1 11,
        scanStepRegressionEntry 1 2 12,
        scanStepRegressionEntry 2 3 13,
        scanStepRegressionEntry 0 4 14,
        scanStepRegressionEntry 77 5 15] }

def scanStepExtensionState : MergeState (Occurrence Nat) Nat :=
  (initialMergeState (occurrenceComparator scanStepRegressionLt) true
    scanStepExtensionSlice).1

end CPythonListsort
