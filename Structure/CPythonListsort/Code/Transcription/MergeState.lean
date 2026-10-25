/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeState.lean -/

import Def.CPythonListsort.Code.Transcription.Comparator
import Def.CPythonListsort.Code.Transcription.Minrun.Part3
import Theorem.CPythonListsort.Code.Transcription.SortSlice
import Def.CPythonListsort.Code.Transcription.MergeState
/-!
# `MergeState` and pending runs

The C structure mixes pointers, signed machine words, an active prefix of a
fixed-size stack, and temporary storage whose slots may be uninitialized. The
model keeps those observable distinctions while replacing pointers by indices
into one shared `SortSlice` store.
-/


namespace CPythonListsort

universe u v

/-- One active pending run. `base` is an index into `MergeState.data`.
The newest run has no initialized power until `found_new_run` processes its
successor, which is represented by `none`. -/
structure PendingRun where
  base : Nat
  len : PySSize
  power : Option Nat
  deriving DecidableEq, Repr

end CPythonListsort
