/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean -/

import Def.CPythonListsort.Code.Transcription.MergeHi.Part6
import Def.CPythonListsort.Code.Transcription.MergeLo.Part6
import Def.CPythonListsort.Code.Transcription.MergeAt
/-!
# Pending-stack merge dispatch

This module transcribes CPython's `merge_at`.  The pending-stack replacement
happens before either galloping search, exactly as it does in C, so a later
modeled failure retains that mutation.  The two searches trim entries already
in their final positions and the shorter remaining run selects `merge_lo` or
`merge_hi`.
-/


namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

/-- Observable result of `merge_at`.  Fuel exhaustion comes only from a
bounded nested gallop or merge transcription and is kept separate from the C
return code. -/
structure MergeAtResult (κ : Type u) (ν : Type v) where
  state : MergeState κ ν
  returnCode : Int
  fuelExhausted : Bool

end CPythonListsort
