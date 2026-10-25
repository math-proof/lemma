/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeState.lean -/

import Def.CPythonListsort.Code.Transcription.Comparator
import Def.CPythonListsort.Code.Transcription.Minrun.Part3
import Theorem.CPythonListsort.Code.Transcription.SortSlice
/-!
# `MergeState` and pending runs

The C structure mixes pointers, signed machine words, an active prefix of a
fixed-size stack, and temporary storage whose slots may be uninitialized. The
model keeps those observable distinctions while replacing pointers by indices
into one shared `SortSlice` store.
-/


namespace CPythonListsort

universe u v

/-- CPython's initial threshold for entering galloping mode. -/
def MIN_GALLOP : PySSize := 7

/-- Number of pointer slots in CPython's inline merge-state buffer. -/
def MERGESTATE_TEMP_SIZE : Nat := 256

end CPythonListsort
