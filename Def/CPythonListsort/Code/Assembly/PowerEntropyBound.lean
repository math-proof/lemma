/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerEntropyBound.lean -/

import Def.CPythonListsort.Code.Equivalence.PowerloopResults.Part2
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
/-!
# Analytic bound for one transcribed node power

The `powerloop` result is one plus the first zero-based quotient-bit position
at which the doubled midpoints differ.  This file turns that exact discrete
characterization into the real logarithmic estimate used by the
Munro--Wild merge-cost argument.
-/


namespace CPythonListsort

/-- The scaled midpoint quotient whose binary low bit is inspected by
`powerloopQuotientBit`. -/
def powerScaledQuotient (x n k : Nat) : Nat :=
  2 ^ k * x / n

end CPythonListsort
