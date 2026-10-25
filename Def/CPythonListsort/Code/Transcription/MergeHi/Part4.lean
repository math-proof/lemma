/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean -/

import Def.CPythonListsort.Code.Transcription.Gallop.Part2
import Def.CPythonListsort.Code.Transcription.MergeMemory.Part3
import Structure.CPythonListsort.Code.Transcription.MergeHi
/-!
# Right-to-left stable merge transcription

This module transcribes CPython's `merge_hi` from the pinned
`Objects/listobject.c`.  The active list remains in `MergeState.data`; the
shorter right run is copied into `MergeState.a`, whose optional cells retain
the distinction between allocated and initialized temporary storage.

The ordinary and galloping loops are represented by a fuel-bounded phase
machine.  Modeled assertion or bounds failures return `none`.  Exhaustion of
the explicit loop or of a nested gallop is instead observable through
`fuelExhausted`, while rejection by `merge_getmem` retains C's `-1` result.

Equality selects B while filling backward, leaving the equal A entry before it
in final forward order.  Galloping retains C's `na == 0` and `nb == 0` branches
for inconsistent but total comparators, including the `na - k` and `nb - k`
conversions from insertion indices to backward block lengths.

Version one has no comparator-error result.  CPython's comparator-error jumps
to `Fail` are deliberately absent, while the temp-to-data copyback shared by
C's `Succeed` and `Fail` labels remains on successful exits.  Distinct
temp/data block copies model `sortslice_memcpy`; blocks moved within `data` use
overlap-safe `SortSlice.memmove?`.
-/


namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

def mergeHiCopyDataDecr? (state : MergeState κ ν) (dst src : Int) :
    Option (MergeHiDataCursorResult κ ν) := do
  let copied ← state.data.copyDecr? dst src
  pure
    { state := { state with data := copied.slice }
      dst := copied.dst
      src := copied.src }

def mergeHiCopyTempDecr? (state : MergeState κ ν) (dst src : Int) :
    Option (MergeHiDataCursorResult κ ν) := do
  let state ← mergeHiCopyTempToData? state dst src
  pure { state := state, dst := dst - 1, src := src - 1 }

end CPythonListsort
