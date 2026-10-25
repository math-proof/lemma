/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean -/

import Def.CPythonListsort.Code.Correctness.OriginRelabelEquivariance.Part6
import Def.CPythonListsort.Code.Correctness.ReverseModeAlgebra
/-!
# Order and stability algebra for reverse mode

These lemmas contain no evaluator reasoning.  They formalize the mathematical
effect of CPython's reverse-before / stable-forward-sort / reverse-after
pattern once evaluator equivariance has supplied the mirrored pre-finish
result.
-/


namespace CPythonListsort

universe u

/-- Either public direction selected by the Boolean mode is again a strict
weak order. -/
theorem BoolStrictWeakOrder.requestedComparator
    {lt : BoolComparator α} (h : BoolStrictWeakOrder lt) (reverse : Bool) :
    BoolStrictWeakOrder (requestedComparator lt reverse) := by
  cases reverse
  · simpa using h
  · simpa using h.swapped

/-- Comparator equivalence is unchanged when the comparator arguments are
swapped. -/
theorem comparatorEquivalent_swapped (lt : BoolComparator α) (left right : α) :
    ComparatorEquivalent (swappedComparator lt) left right ↔
      ComparatorEquivalent lt left right := by
  simp [ComparatorEquivalent, swappedComparator, and_comm]

end CPythonListsort
