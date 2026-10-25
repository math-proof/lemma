/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean -/

import Def.CPythonListsort.Code.Correctness.OriginRelabelEquivariance.Part6
import Theorem.CPythonListsort.Code.Correctness.ReverseModeAlgebra.Part2
/-!
# Order and stability algebra for reverse mode

These lemmas contain no evaluator reasoning.  They formalize the mathematical
effect of CPython's reverse-before / stable-forward-sort / reverse-after
pattern once evaluator equivariance has supplied the mirrored pre-finish
result.
-/


namespace CPythonListsort

universe u

/-- Reverse the physical paired-entry array, keeping each key attached to its
optional payload. -/
def reverseEntries (slice : SortSlice κ ν) : SortSlice κ ν :=
  { entries := slice.entries.reverse }

end CPythonListsort
