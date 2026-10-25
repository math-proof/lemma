/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeState.lean -/

import Def.CPythonListsort.Code.Transcription.Comparator
import Def.CPythonListsort.Code.Transcription.Minrun.Part3
import Theorem.CPythonListsort.Code.Transcription.SortSlice
import Structure.CPythonListsort.Code.Transcription.MergeState.Part3
/-!
# `MergeState` and pending runs

The C structure mixes pointers, signed machine words, an active prefix of a
fixed-size stack, and temporary storage whose slots may be uninitialized. The
model keeps those observable distinctions while replacing pointers by indices
into one shared `SortSlice` store.
-/


namespace CPythonListsort

universe u v

/-- CPython's mutable `n` is represented by the length of the active pending
array, so it cannot disagree with the modeled stack. -/
def MergeState.n (state : MergeState κ ν) : Nat :=
  state.pending.size

/-- Project the adaptive-minrun fields to the dedicated transcription state. -/
def MergeState.minrunState (state : MergeState κ ν) : MinrunState :=
  { listlen := state.listlen
    mr_current := state.mr_current
    mr_e := state.mr_e
    mr_mask := state.mr_mask }

end CPythonListsort
