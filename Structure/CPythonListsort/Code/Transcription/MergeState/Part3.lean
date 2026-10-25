/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeState.lean -/

import Def.CPythonListsort.Code.Transcription.Comparator
import Def.CPythonListsort.Code.Transcription.Minrun.Part3
import Theorem.CPythonListsort.Code.Transcription.SortSlice
import Def.CPythonListsort.Code.Transcription.MergeState.Part2
/-!
# `MergeState` and pending runs

The C structure mixes pointers, signed machine words, an active prefix of a
fixed-size stack, and temporary storage whose slots may be uninitialized. The
model keeps those observable distinctions while replacing pointers by indices
into one shared `SortSlice` store.
-/


namespace CPythonListsort

universe u v

/-- Temporary merge storage. The outer `Option` represents an allocated slot
whose C contents have not yet been initialized; an entry's own optional value
represents the independent `a.values == NULL` choice. The raw structure admits
arbitrary field combinations; `TempStorageInv` in the adjacent support module
characterizes the representation states reachable from `merge_init`. -/
structure TempStorage (κ : Type u) (ν : Type v) where
  cells : Array (Option (SortSliceEntry κ ν))
  backing : TempBacking
  hasValues : Bool
  deriving DecidableEq, Repr

/-- Version-one transcription of the observable `MergeState` fields.
Comparator-specialization function pointers collapse to `key_compare`. -/
structure MergeState (κ : Type u) (ν : Type v) where
  min_gallop : PySSize
  listlen : PySSize
  basekeys : Nat
  data : SortSlice κ ν
  a : TempStorage κ ν
  alloced : PySSize
  pending : Array PendingRun
  key_compare : BoolComparator κ
  mr_current : PySSize
  mr_e : PySSize
  mr_mask : PySSize

end CPythonListsort
