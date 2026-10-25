/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/Order.lean -/

import Def.CPythonListsort.Code.Transcription.Comparator
import Mathlib.Data.List.Sort
import Theorem.CPythonListsort.Code.Assembly.Order
/-!
# Order, sortedness, and occurrence-level stability specifications

The sorting implementation accepts a total Boolean comparator.  Correctness
adds a strict-weak-order hypothesis only at the theorem boundary.  Stability
is phrased over occurrence tags that are attached to the input before any
movement; the output cannot be retagged after sorting.
-/


namespace CPythonListsort

universe u

/-- An occurrence sequence is a stable permutation of an explicitly chosen
canonical occurrence sequence.  This is the shared stability predicate for
both whole-sort results and intermediate consumed segments: callers choose the
canonical sequence, but may not retag the output after the fact. -/
def StableOccurrencePermutation (lt : BoolComparator α)
    (canonical output : List (Occurrence α)) : Prop :=
  output.Perm canonical ∧
    output.Pairwise fun earlier later =>
      ComparatorEquivalent lt earlier.value later.value →
        earlier.origin < later.origin

end CPythonListsort
