/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ListSortCorrectness.lean -/

import Structure.CPythonListsort.Code.Correctness.ScanLoopCorrectness
import Structure.CPythonListsort.Code.Correctness.ReverseModeCorrectness
import Def.CPythonListsort.Code.Correctness.OccurrenceErasureScan.Part2
import Def.CPythonListsort.Code.Correctness.ListSortCorrectness
/-!
# Public functional correctness of listsort

This module packages correctness at the proof-carrying `ListSortInput`
boundary.  The implementation sorts occurrence-tagged keys so origins travel
through every modeled movement; the final post exposes requested-order
sortedness, occurrence-level stability, and the whole key/payload snapshot.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

structure CorrectnessRegressionView where
  returnCode : Int
  fuelExhausted : Bool
  entries : List (Nat × Nat × Option Nat)
  deriving DecidableEq, Repr

end CPythonListsort
