/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/Minrun.lean -/

import Def.CPythonListsort.Code.Transcription.Word
import Structure.CPythonListsort.Code.Transcription.Minrun.Part3
/-!
# Adaptive-minrun transcription

Sources: `Objects/listobject.c`, lines 2230-2268 (`merge_init`) and
2745-2754 (`minrun_next`) at CPython commit
`67e6be72be9c0b75a31795ed42f9afb5eb431d47`.
-/


namespace CPythonListsort

/-- Repeated `minrun_next` calls, retaining every emitted target length. -/
def minrunNextN : Nat → MinrunState → MinrunRunResult
  | 0, state => { state := state, outputs := [], assertionsPassed := true }
  | calls + 1, state =>
      let next := minrunNext state
      let tail := minrunNextN calls next.state
      { state := tail.state
        outputs := next.result.toNat :: tail.outputs
        assertionsPassed := next.assertionPassed && tail.assertionsPassed }

end CPythonListsort
