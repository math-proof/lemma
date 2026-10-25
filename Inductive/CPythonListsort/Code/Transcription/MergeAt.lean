/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean -/

import Def.CPythonListsort.Code.Transcription.MergeHi.Part6
import Def.CPythonListsort.Code.Transcription.MergeLo.Part6
import Structure.CPythonListsort.Code.Transcription.MergeAt.Part2
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

/-- The observable continuation selected after `merge_at` has updated the
pending stack and completed both trimming gallops.  Keeping the two merge
continuations explicit makes the exact state and request at the subsequent
`merge_getmem` call available to assembly proofs. -/
inductive MergeAtPreparation (κ : Type u) (ν : Type v) where
  | finished (result : MergeAtResult κ ν)
  | mergeLo (call : MergeAtCall κ ν)
  | mergeHi (call : MergeAtCall κ ν)

end CPythonListsort
