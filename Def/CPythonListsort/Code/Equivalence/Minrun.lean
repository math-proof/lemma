/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Minrun.lean -/

import Def.CPythonListsort.Code.Transcription.Minrun.Part3
import Mathlib
/-!
# Adaptive-minrun equivalence

The theorems in this file project the reviewed 64-bit transcription to the
quotient-and-remainder description in CPython's `Objects/listsort.txt`.
-/


namespace CPythonListsort

/-- Arbitrary-precision specification of the `merge_init` exponent loop. -/
def minrunExponentSpecLoop : Nat → Nat → Nat → Nat × Bool
  | 0, _, exponent => (exponent, false)
  | fuel + 1, listSize, exponent =>
      if listSize >>> exponent < 64 then
        (exponent, true)
      else
        minrunExponentSpecLoop fuel listSize (exponent + 1)

end CPythonListsort
