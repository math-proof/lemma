/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Powerloop.lean -/

import Def.CPythonListsort.Code.Transcription.Powerloop
import Mathlib
/-!
# `powerloop` recurrence equivalence

This file projects the reviewed 64-bit transcription to a recurrence over
arbitrary-precision natural numbers.  The explicit safety trace records the
signed-comparison and shift-representability obligations inherited from C.
-/


namespace CPythonListsort

/-- Arbitrary-precision observable state corresponding to `PowerloopState`. -/
structure PowerloopNatState where
  result : Nat
  a : Nat
  b : Nat
  stopped : Bool
  deriving DecidableEq, Repr

end CPythonListsort
