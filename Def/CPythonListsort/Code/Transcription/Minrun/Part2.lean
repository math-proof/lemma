/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/Minrun.lean -/

import Def.CPythonListsort.Code.Transcription.Word
import Structure.CPythonListsort.Code.Transcription.Minrun.Part2
/-!
# Adaptive-minrun transcription

Sources: `Objects/listobject.c`, lines 2230-2268 (`merge_init`) and
2745-2754 (`minrun_next`) at CPython commit
`67e6be72be9c0b75a31795ed42f9afb5eb431d47`.
-/


namespace CPythonListsort

/--
Transcription of `minrun_next`: add, check the signed-overflow assertion,
compute the shifted result, then retain the masked residual.
-/
def minrunNext (state : MinrunState) : MinrunNextResult :=
  let current := state.mr_current + state.listlen
  let result := current.sshiftRight state.mr_e.toNat
  { state := { state with mr_current := current &&& state.mr_mask }
    result := result
    assertionPassed := !current.msb }

end CPythonListsort
