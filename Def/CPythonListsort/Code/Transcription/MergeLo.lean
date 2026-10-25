/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean -/

import Def.CPythonListsort.Code.Transcription.Gallop.Part2
import Def.CPythonListsort.Code.Transcription.MergeMemory.Part3
/-!
# Left-to-right merge transcription

This module transcribes CPython's `merge_lo`.  The main list remains in
`MergeState.data`; the shorter left run is copied into `MergeState.a` before
the merge starts.  Invalid assertion inputs, failed modeled accesses, and
invalid nested gallop calls return `none`.  The allocation guard and bounded
loop exhaustion remain observable and distinct in `MergeLoResult`.

The ordinary and galloping loops are represented by an explicit phase
machine.  Every recursive step consumes at least one live run entry, so the
input-size fuel is exposed only through the result flag and not as a caller
parameter.  Equality selects A while merging forward.  Galloping preserves
the C branch where an inconsistent but total comparator can consume all of A.

Version one has a pure Boolean comparator, so CPython's comparator-error jumps
to `Fail` and their negative result are deliberately absent.  The physical
temp-to-data copyback shared by C's `Succeed` and `Fail` labels remains on the
successful path.  Distinct temp/data block copies model `sortslice_memcpy`;
blocks moved within `data` use overlap-safe `SortSlice.memmove?`.
-/


namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

/-- Short-circuiting option composition used by the exported `merge_lo` core.
The dedicated name keeps later traced/refinement proofs independent of private
declaration names in this module. -/
def mergeLoBindOptionAcross {α : Type w} {β : Type x}
    (value : Option α) (next : α → Option β) : Option β :=
  match value with
  | none => none
  | some value => next value

end CPythonListsort
