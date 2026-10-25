/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/Gallop.lean -/

import Def.CPythonListsort.Code.Transcription.MergeState.Part3
/-!
# Hinted galloping searches

These definitions transcribe CPython's separate `gallop_left` and
`gallop_right` routines.  Keeping the routines separate makes their deliberate
equality asymmetry, and the order of every comparator call, visible.

The searched run starts at the signed index `base`.  Invalid assertion inputs,
failed bounds checks, and failure of the doubling assertion return `none`.
Fuel exhaustion is represented separately in the successful result.
-/


namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

/-- Explicit `Option` sequencing used by the gallop transcription.  It is
public so the traced safety evaluator can prove erasure without duplicating
the transcription's control-flow equations. -/
def gallopBindOptionAcross {α : Type w} {β : Type x}
    (value : Option α) (next : α → Option β) : Option β :=
  match value with
  | none => none
  | some value => next value

end CPythonListsort
