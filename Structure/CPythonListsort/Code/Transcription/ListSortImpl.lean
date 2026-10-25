/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/ListSortImpl.lean -/

import Def.CPythonListsort.Code.Transcription.Binarysort.Part3
import Def.CPythonListsort.Code.Transcription.CountRun.Part4
import Theorem.CPythonListsort.Code.Transcription.FoundNewRun
import Theorem.CPythonListsort.Code.Transcription.MergeForceCollapse
import Def.CPythonListsort.Code.Transcription.MergeInitStorage
import Def.CPythonListsort.Code.Transcription.MergeMemory.Part3
import Def.CPythonListsort.Code.Transcription.ReverseSlice
/-!
# Snapshot-model `list_sort_impl`

This module assembles the version-one snapshot model of CPython's top-level
sort.  Keys and their optional payloads are already paired, the comparator is
pure and total, and allocator failure is excluded.  Within that boundary the
control flow retains initial/final reverse handling, natural-run discovery,
adaptive minrun extension, policy merges, the unconditional pending push,
final collapse, and temporary-storage cleanup.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Observable result of the snapshot-model top-level transcription. -/
structure ListSortImplResult (κ : Type u) (ν : Type v) where
  state : MergeState κ ν
  returnCode : Int
  fuelExhausted : Bool

end CPythonListsort
