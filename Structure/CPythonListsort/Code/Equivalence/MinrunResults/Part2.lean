/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean -/

import Def.CPythonListsort.Code.Equivalence.Minrun.Part2
import Def.CPythonListsort.Code.Equivalence.PowerloopResults.Part2
import Mathlib
import Theorem.CPythonListsort.Code.Equivalence.MinrunResults
/-!
# Adaptive-minrun sequence results

This file proves the least-exponent characterization and the full-cycle
quotient/remainder properties of CPython's adaptive minrun generator.
-/


namespace CPythonListsort

/-- Natural-number trace of repeated quotient/remainder generator steps. -/
structure MinrunSpecTrace where
  outputs : List Nat
  residual : Nat
  deriving DecidableEq, Repr

end CPythonListsort
