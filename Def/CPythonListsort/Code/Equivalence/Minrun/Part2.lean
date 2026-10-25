/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Minrun.lean -/

import Def.CPythonListsort.Code.Transcription.Minrun.Part3
import Mathlib
import Structure.CPythonListsort.Code.Equivalence.Minrun
/-!
# Adaptive-minrun equivalence

The theorems in this file project the reviewed 64-bit transcription to the
quotient-and-remainder description in CPython's `Objects/listsort.txt`.
-/


namespace CPythonListsort

/-- The exact-arithmetic specification described by CPython's integer generator. -/
def minrunNextSpec (listlen current exponent : Nat) : MinrunNextSpec :=
  let total := current + listlen
  { result := total / 2 ^ exponent
    residual := total % 2 ^ exponent }

end CPythonListsort
