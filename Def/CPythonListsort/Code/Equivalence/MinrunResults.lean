/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean -/

import Def.CPythonListsort.Code.Equivalence.Minrun.Part2
import Def.CPythonListsort.Code.Equivalence.PowerloopResults.Part2
import Mathlib
import Structure.CPythonListsort.Code.Equivalence.MinrunResults.Part2
/-!
# Adaptive-minrun sequence results

This file proves the least-exponent characterization and the full-cycle
quotient/remainder properties of CPython's adaptive minrun generator.
-/


namespace CPythonListsort

/-- Iterate the exact-arithmetic minrun recurrence. -/
def minrunSpecTrace : Nat → Nat → Nat → Nat → MinrunSpecTrace
  | 0, _, _, current => { outputs := [], residual := current }
  | calls + 1, listlen, exponent, current =>
      let next := minrunNextSpec listlen current exponent
      let tail := minrunSpecTrace calls listlen exponent next.residual
      { outputs := next.result :: tail.outputs, residual := tail.residual }

end CPythonListsort
