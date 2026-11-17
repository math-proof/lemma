/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeState.lean -/

module

public import Def.CPythonListsort.Code.Transcription.Comparator
public import Def.CPythonListsort.Code.Transcription.Minrun.Part3
public import Theorem.CPythonListsort.Code.Transcription.SortSlice
public import Structure.CPythonListsort.Code.Transcription.MergeState.Part2

@[expose] public section

/-!
# `MergeState` and pending runs

The C structure mixes pointers, signed machine words, an active prefix of a
fixed-size stack, and temporary storage whose slots may be uninitialized. The
model keeps those observable distinctions while replacing pointers by indices
into one shared `SortSlice` store.
-/


namespace CPythonListsort

universe u v

/-- A memcpy-class merge move crosses backing regions rather than aliasing one
region at two potentially overlapping ranges. -/
def MergeMemcpyBackings.Distinct (backings : MergeMemcpyBackings) : Prop :=
  backings.destination ≠ backings.source

end CPythonListsort
