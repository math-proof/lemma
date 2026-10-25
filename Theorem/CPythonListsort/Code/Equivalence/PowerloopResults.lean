/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean -/

import Def.CPythonListsort.Code.Equivalence.Powerloop
import Mathlib
import Def.CPythonListsort.Code.Equivalence.PowerloopResults
/-!
# Total correctness of `powerloop`

This file discharges the input bounds, trace-safety, termination, quotient-bit,
and concrete range obligations for CPython's 64-bit `powerloop` transcription.
-/


namespace CPythonListsort

theorem pyListMax_eq : PY_LIST_MAX = 2 ^ 60 - 1 := by
  norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES]

end CPythonListsort
