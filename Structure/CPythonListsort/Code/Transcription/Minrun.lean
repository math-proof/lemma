/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/Minrun.lean -/

import Def.CPythonListsort.Code.Transcription.Word
/-!
# Adaptive-minrun transcription

Sources: `Objects/listobject.c`, lines 2230-2268 (`merge_init`) and
2745-2754 (`minrun_next`) at CPython commit
`67e6be72be9c0b75a31795ed42f9afb5eb431d47`.
-/


namespace CPythonListsort

/-- The adaptive-minrun fields of CPython's `MergeState`. -/
structure MinrunState where
  listlen : PySSize
  mr_current : PySSize
  mr_e : PySSize
  mr_mask : PySSize
  deriving DecidableEq, Repr

/-- Result of the bounded transcription of `merge_init`'s exponent loop. -/
structure MinrunInitTrace where
  state : MinrunState
  stopped : Bool
  deriving DecidableEq, Repr

end CPythonListsort
