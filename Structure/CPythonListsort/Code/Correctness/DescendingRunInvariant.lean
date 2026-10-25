/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunInvariant.lean -/

import Def.CPythonListsort.Code.Assembly.Order.Part4
import Def.CPythonListsort.Code.Correctness.DescendingRunNormalization
import Def.CPythonListsort.Code.Correctness.DescendingRunInvariant
/-!
# Stable-order invariant for `count_run`'s descending phase

This file contains only pure list/order algebra.  The executable count-run
proof instantiates it with the range read from the transcribed machine.
-/


namespace CPythonListsort

universe u

namespace DescendingRunSpec

/-- The semantic state carried through `count_run`'s descending scan.

`normalize current tailLength` is the stable ascending sequence that would be
obtained by closing the current equality block and reversing the whole scanned
prefix. -/
structure Invariant (lt : BoolComparator α)
    (canonical current : List (Occurrence α)) (tailLength : Nat) : Prop where
  current_ne : current ≠ []
  tail_pos : 0 < tailLength
  tail_le : tailLength ≤ current.length
  sorted : (normalize current tailLength).Pairwise (SortedRelation lt)
  stable : StableOccurrencePermutation lt canonical
    (normalize current tailLength)
  tail_equiv :
    ∀ x ∈ (normalize current tailLength).take tailLength,
      ComparatorEquivalent lt x.value (current.getLast current_ne).value
  rest_greater :
    ∀ x ∈ (normalize current tailLength).drop tailLength,
      lt (current.getLast current_ne).value x.value = true

end DescendingRunSpec
end CPythonListsort
