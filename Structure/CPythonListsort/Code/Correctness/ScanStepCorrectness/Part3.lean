/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanStepCorrectness.lean -/

import Structure.CPythonListsort.Code.Assembly.ListSortTermination
import Def.CPythonListsort.Code.Correctness.BinarysortCorrectness.Part3
import Def.CPythonListsort.Code.Correctness.CountRunCorrectness.Part2
import Def.CPythonListsort.Code.Correctness.FoundNewRunCorrectness
import Theorem.CPythonListsort.Code.Correctness.ScanCorrectnessSupport
import Theorem.CPythonListsort.Code.Correctness.ScanStepSupport
import Def.CPythonListsort.Code.Correctness.ScanStepCorrectness.Part2
/-!
# Correctness of one forward scan iteration

This module stops at the recursive-call boundary of `listSortScan?`.  It
combines the already-reviewed safety invariant with pending-run correctness,
the whole-entry unscanned snapshot, and the persistent input permutation.
-/


namespace CPythonListsort

universe u v

variable {α : Type u} {ν : Type v}

structure ScanStepExtensionRegressionView where
  returnCode : Int
  fuelExhausted : Bool
  pending : List (Nat × Nat)
  entries : List (Nat × Nat × Option Nat)
  deriving DecidableEq, Repr

end CPythonListsort
