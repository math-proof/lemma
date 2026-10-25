/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean -/

import Def.CPythonListsort.Code.Transcription.MergeHi.Part6
import Def.CPythonListsort.Code.Transcription.MergeLo.Part6
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

def bindOptionAcross {α : Type w} {β : Type x}
    (value : Option α) (next : α → Option β) : Option β :=
  match value with
  | none => none
  | some value => next value

end CPythonListsort
