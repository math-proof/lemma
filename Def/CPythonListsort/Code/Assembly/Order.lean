/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/Order.lean -/

import Def.CPythonListsort.Code.Transcription.Comparator
import Mathlib.Data.List.Sort
import Structure.CPythonListsort.Code.Assembly.Order
/-!
# Order, sortedness, and occurrence-level stability specifications

The sorting implementation accepts a total Boolean comparator.  Correctness
adds a strict-weak-order hypothesis only at the theorem boundary.  Stability
is phrased over occurrence tags that are attached to the input before any
movement; the output cannot be retagged after sorting.
-/


namespace CPythonListsort

universe u

/-- Comparator equivalence: neither value is strictly before the other. -/
def ComparatorEquivalent (lt : BoolComparator α) (a b : α) : Prop :=
  lt a b = false ∧ lt b a = false

/-- An array is sorted when no later entry strictly precedes an earlier one. -/
def Sorted (lt : BoolComparator α) (ys : Array α) : Prop :=
  ys.toList.Pairwise (fun earlier later => lt later earlier = false)

end CPythonListsort
