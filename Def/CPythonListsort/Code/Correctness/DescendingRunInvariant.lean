/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunInvariant.lean -/

import Def.CPythonListsort.Code.Assembly.Order.Part4
import Def.CPythonListsort.Code.Correctness.DescendingRunNormalization
/-!
# Stable-order invariant for `count_run`'s descending phase

This file contains only pure list/order algebra.  The executable count-run
proof instantiates it with the range read from the transcribed machine.
-/


namespace CPythonListsort

universe u

namespace DescendingRunSpec

/-- Pairwise relation corresponding to ascending `Sorted` order on occurrence
lists: a later occurrence must not compare strictly before an earlier one. -/
def SortedRelation (lt : BoolComparator α) :
    Occurrence α → Occurrence α → Prop :=
  fun earlier later => occurrenceComparator lt later earlier = false

/-- Pairwise occurrence-stability relation shared with
`StableOccurrencePermutation`. -/
def StableRelation (lt : BoolComparator α) :
    Occurrence α → Occurrence α → Prop :=
  fun earlier later =>
    ComparatorEquivalent lt earlier.value later.value →
      earlier.origin < later.origin

end DescendingRunSpec
end CPythonListsort
