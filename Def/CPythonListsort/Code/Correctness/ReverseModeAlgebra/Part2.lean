/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeAlgebra.lean -/

import Def.CPythonListsort.Code.Correctness.OriginRelabelEquivariance.Part6
import Theorem.CPythonListsort.Code.Correctness.ReverseModeAlgebra
/-!
# Order and stability algebra for reverse mode

These lemmas contain no evaluator reasoning.  They formalize the mathematical
effect of CPython's reverse-before / stable-forward-sort / reverse-after
pattern once evaluator equivariance has supplied the mirrored pre-finish
result.
-/


namespace CPythonListsort

universe u

/-- A sequence with descending origins inside each comparator-equivalence
class.  This is the natural intermediate stability contract after origin
mirroring but before CPython's final whole-array reversal. -/
def ReverseStableOccurrencePermutation (lt : BoolComparator α)
    (canonical output : List (Occurrence α)) : Prop :=
  output.Perm canonical ∧
    output.Pairwise fun earlier later =>
      ComparatorEquivalent lt earlier.value later.value →
        later.origin < earlier.origin

end CPythonListsort
