/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ListSortCorrectness.lean -/

module

public import Structure.CPythonListsort.Code.Correctness.ScanLoopCorrectness
public import Structure.CPythonListsort.Code.Correctness.ReverseModeCorrectness
public import Def.CPythonListsort.Code.Correctness.OccurrenceErasureScan.Part2
public import Structure.CPythonListsort.Code.Correctness.ListSortCorrectness

@[expose] public section

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

/-! ## Inhabited boundary witnesses -/

def correctnessRegressionLt : BoolComparator Nat :=
  fun left right => decide (left < right)

def reverseKeyedDuplicateInput : ListSortInput Nat Nat :=
  ListSortInput.keyed #[(2, 20), (1, 10), (1, 11), (2, 21)]

end CPythonListsort
