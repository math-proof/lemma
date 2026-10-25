/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean -/

import Def.CPythonListsort.Code.Correctness.OriginRelabelEquivariance.Part6
import Def.CPythonListsort.Code.Correctness.ReverseModeAlgebra.Part2
/-!
# Order and stability algebra for reverse mode

These lemmas contain no evaluator reasoning.  They formalize the mathematical
effect of CPython's reverse-before / stable-forward-sort / reverse-after
pattern once evaluator equivariance has supplied the mirrored pre-finish
result.
-/


namespace CPythonListsort

universe u

namespace ReverseStableOccurrencePermutation

/-- Reversing the output turns reverse stability into ordinary stability for
the argument-swapped comparator; the canonical sequence is used only through
permutation and therefore remains unchanged. -/
theorem reverse
    {lt : BoolComparator α} {canonical output : List (Occurrence α)}
    (h : ReverseStableOccurrencePermutation lt canonical output) :
    StableOccurrencePermutation (swappedComparator lt) canonical
      output.reverse := by
  constructor
  · exact output.reverse_perm.trans h.1
  · rw [List.pairwise_reverse]
    apply h.2.imp
    intro earlier later hstable hequivalent
    rw [comparatorEquivalent_swapped] at hequivalent
    exact hstable ⟨hequivalent.2, hequivalent.1⟩

end ReverseStableOccurrencePermutation
end CPythonListsort
