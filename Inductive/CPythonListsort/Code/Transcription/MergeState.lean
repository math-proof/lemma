/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeState.lean -/

import Def.CPythonListsort.Code.Transcription.Comparator
import Def.CPythonListsort.Code.Transcription.Minrun.Part3
import Theorem.CPythonListsort.Code.Transcription.SortSlice
import Structure.CPythonListsort.Code.Transcription.MergeState
/-!
# `MergeState` and pending runs

The C structure mixes pointers, signed machine words, an active prefix of a
fixed-size stack, and temporary storage whose slots may be uninitialized. The
model keeps those observable distinctions while replacing pointers by indices
into one shared `SortSlice` store.
-/


namespace CPythonListsort

universe u v

/-- Whether the temporary key pointer denotes the inline array, heap storage,
or storage that has already been released. -/
inductive TempBacking where
  | inline
  | heap
  | released
  deriving DecidableEq, Repr

/-- The two logically distinct payload regions participating in merge bulk
copies.  `main` is `MergeState.data`; `temporary` is `MergeState.a`. -/
inductive MergeStorageRegion where
  | main
  | temporary
  deriving DecidableEq, Repr

end CPythonListsort
