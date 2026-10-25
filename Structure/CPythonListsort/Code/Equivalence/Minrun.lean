/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Minrun.lean -/

import Def.CPythonListsort.Code.Transcription.Minrun.Part3
import Mathlib
import Def.CPythonListsort.Code.Equivalence.Minrun
/-!
# Adaptive-minrun equivalence

The theorems in this file project the reviewed 64-bit transcription to the
quotient-and-remainder description in CPython's `Objects/listsort.txt`.
-/


namespace CPythonListsort

/-- Mathematical quotient-and-remainder result of one adaptive-minrun step. -/
structure MinrunNextSpec where
  result : Nat
  residual : Nat
  deriving DecidableEq, Repr

end CPythonListsort
