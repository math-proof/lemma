/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/Minrun.lean -/

import Def.CPythonListsort.Code.Transcription.Word
import Def.CPythonListsort.Code.Transcription.Minrun.Part2
/-!
# Adaptive-minrun transcription

Sources: `Objects/listobject.c`, lines 2230-2268 (`merge_init`) and
2745-2754 (`minrun_next`) at CPython commit
`67e6be72be9c0b75a31795ed42f9afb5eb431d47`.
-/


namespace CPythonListsort

/-- Observable result of repeatedly calling the transcribed `minrun_next`. -/
structure MinrunRunResult where
  state : MinrunState
  outputs : List Nat
  assertionsPassed : Bool
  deriving DecidableEq, Repr

end CPythonListsort
