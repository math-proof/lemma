/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseSliceCorrectness.lean -/

import Def.CPythonListsort.Code.Assembly.ReverseSliceSafety.Part2
/-!
# Exact correctness of slice reversal

This file connects the executable `reverse_slice` transcription to a reusable
mathematical operation on half-open array ranges.  The specification retains
the prefix and suffix verbatim and reverses exactly the selected middle.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

namespace ReverseRangeSpec

/-- Replace the half-open range `[start, stop)` by its reversal. -/
def reverseRangeEntries (xs : Array α) (start stop : Nat) : Array α :=
  (xs.extract 0 start ++ (xs.extract start stop).reverse) ++
    xs.extract stop xs.size

def ReverseRangeLoopInvariant
    (original current : Array α) (start stop i j : Nat) : Prop :=
  current.size = original.size ∧
    start ≤ i ∧ i ≤ stop ∧ start ≤ j ∧ j < stop ∧
    i + j + 1 = start + stop ∧
    ∀ k, current[k]? =
      if i ≤ k ∧ k ≤ j then original[k]?
      else (ReverseRangeSpec.reverseRangeEntries original start stop)[k]?

end ReverseRangeSpec
end CPythonListsort
