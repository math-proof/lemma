/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean -/

import Def.CPythonListsort.Code.Correctness.OriginRelabelEquivariance.Part6
/-!
# Order and stability algebra for reverse mode

These lemmas contain no evaluator reasoning.  They formalize the mathematical
effect of CPython's reverse-before / stable-forward-sort / reverse-after
pattern once evaluator equivariance has supplied the mirrored pre-finish
result.
-/


namespace CPythonListsort

universe u

/-- The argument-swapped comparator requested by `reverse = true`. -/
def swappedComparator (lt : BoolComparator α) : BoolComparator α :=
  fun left right => lt right left

/-- Comparator selected by the public `reverse` flag. -/
def requestedComparator (lt : BoolComparator α) (reverse : Bool) :
    BoolComparator α :=
  if reverse then swappedComparator lt else lt

end CPythonListsort
