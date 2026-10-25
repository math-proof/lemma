/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/BoundaryPowerGeometry.lean -/

import Def.CPythonListsort.Code.Equivalence.PowerloopResults.Part2
import Mathlib
/-!
# Boundary-power geometry

This file proves the three-run geometry used by CPython's PowerSort policy.
The public theorem is stated for the actual finite-width `powerloop`; the
proof transfers each call to its canonical quotient-bit characterization.
-/


namespace CPythonListsort

/-- The scaled quotient whose low bit is `powerloopQuotientBit`. -/
def scaledQuotient (x n k : Nat) : Nat :=
  2 ^ k * x / n

end CPythonListsort
