/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/Powerloop.lean -/

import Def.CPythonListsort.Code.Transcription.Word
/-!
# Transcription of CPython `powerloop`

Source: `Objects/listobject.c`, lines 2652-2691 at CPython commit
`67e6be72be9c0b75a31795ed42f9afb5eb431d47`.

The recursive fuel makes the C loop total without `partial`. Sixty-four
iterations are exposed as an adequacy obligation in the equivalence layer.
-/


namespace CPythonListsort

/-- Observable state of the transcribed `powerloop` loop. -/
structure PowerloopState where
  result : Nat
  a : PySSize
  b : PySSize
  stopped : Bool
  deriving DecidableEq, Repr

end CPythonListsort
