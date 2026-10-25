/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/Order.lean -/

import Def.CPythonListsort.Code.Transcription.Comparator
import Mathlib.Data.List.Sort
import Structure.CPythonListsort.Code.Assembly.Order.Part2
/-!
# Order, sortedness, and occurrence-level stability specifications

The sorting implementation accepts a total Boolean comparator.  Correctness
adds a strict-weak-order hypothesis only at the theorem boundary.  Stability
is phrased over occurrence tags that are attached to the input before any
movement; the output cannot be retagged after sorting.
-/


namespace CPythonListsort

universe u

/-- Attach immutable origin tags before sorting begins. -/
def tagOccurrences (xs : Array α) : Array (Occurrence α) :=
  xs.zipIdx.map fun entry =>
    { value := entry.1, origin := entry.2 }

/-- Compare tagged occurrences only through their externally visible values. -/
def occurrenceComparator (lt : BoolComparator α) : BoolComparator (Occurrence α) :=
  fun a b => lt a.value b.value

end CPythonListsort
