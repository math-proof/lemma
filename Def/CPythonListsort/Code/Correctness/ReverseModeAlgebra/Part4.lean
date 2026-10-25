/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean -/

import Def.CPythonListsort.Code.Correctness.OriginRelabelEquivariance.Part6
import Theorem.CPythonListsort.Code.Correctness.ReverseModeAlgebra.Part3
/-!
# Order and stability algebra for reverse mode

These lemmas contain no evaluator reasoning.  They formalize the mathematical
effect of CPython's reverse-before / stable-forward-sort / reverse-after
pattern once evaluator equivariance has supplied the mirrored pre-finish
result.
-/


namespace ListSortInput

/-- A validated top-level input with its complete paired-entry array reversed. -/
def reverseEntries (input : ListSortInput κ ν) : ListSortInput κ ν where
  slice := input.slice.reverseEntries
  hasKeyfunc := input.hasKeyfunc
  valuesMode := input.valuesMode.reverseEntries

end ListSortInput
