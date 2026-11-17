/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeState.lean -/

module

public import Def.CPythonListsort.Code.Transcription.Comparator
public import Def.CPythonListsort.Code.Transcription.Minrun.Part3
public import Theorem.CPythonListsort.Code.Transcription.SortSlice
public import Inductive.CPythonListsort.Code.Transcription.MergeState
/-!
# `MergeState` and pending runs

The C structure mixes pointers, signed machine words, an active prefix of a
fixed-size stack, and temporary storage whose slots may be uninitialized. The
model keeps those observable distinctions while replacing pointers by indices
into one shared `SortSlice` store.
-/
public section




namespace CPythonListsort

universe u v

/-- Source and destination backing regions for one memcpy-class merge move. -/
structure MergeMemcpyBackings where
  destination : MergeStorageRegion
  source : MergeStorageRegion
  deriving DecidableEq, Repr

end CPythonListsort
