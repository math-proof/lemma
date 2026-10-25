/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean -/

import Def.CPythonListsort.Code.Correctness.OriginRelabelEquivariance.Part6
import Def.CPythonListsort.Code.Correctness.ReverseModeAlgebra.Part3
/-!
# Order and stability algebra for reverse mode

These lemmas contain no evaluator reasoning.  They formalize the mathematical
effect of CPython's reverse-before / stable-forward-sort / reverse-after
pattern once evaluator equivariance has supplied the mirrored pre-finish
result.
-/


namespace CPythonListsort

universe u

/-- Reversal cannot change keyed/unkeyed payload representation mode. -/
theorem ValuesModeInvariant.reverseEntries
    {hasKeyfunc : Bool} {slice : SortSlice κ ν}
    (h : ValuesModeInvariant hasKeyfunc slice) :
    ValuesModeInvariant hasKeyfunc slice.reverseEntries := by
  intro index hindex
  have hindex' : index < slice.entries.size := by
    simpa [reverseEntries] using hindex
  have hsource : slice.entries.size - 1 - index < slice.entries.size := by
    omega
  simpa [reverseEntries] using
    h (slice.entries.size - 1 - index) hsource

end CPythonListsort
