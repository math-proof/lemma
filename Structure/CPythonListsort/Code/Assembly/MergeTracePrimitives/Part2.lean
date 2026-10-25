/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean -/

import Def.CPythonListsort.Code.Assembly.MergeMemcpyProvenance
import Def.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part2
/-!
# Typed trace support for merge movement

The merge transcriptions keep the main list in `MergeState.data` and the
shorter run in `MergeState.a`.  `SortSlice`'s two-store movement API cannot be
used directly for that pair because temporary storage has a distinct carrier,
an explicit live/released backing state, and possibly-uninitialized cells.

This module supplies the common traced movement layer used by both merge
directions.  Every access goes through a state-derived wrapper from
`AccessTrace`; in particular, callers cannot manufacture the temporary backing
or either extent.  Bulk `memcpy` executors retain a classified call-site tag,
its exact direction, and its distinct-backing certificate at every recursive
call.  Key accesses for the complete range precede the optional synchronized-
values phase, which is selected solely by `state.a.hasValues`.
-/


namespace CPythonListsort

universe u v

open SortSlice

namespace TempRangeInBounds

/-! ## Structural frame -/

/-- Fields and extents unchanged by every movement primitive in this module.
The main contents and temporary contents are intentionally absent. -/
structure MergeMovementFrame (before after : MergeState κ ν) : Prop where
  minGallop : after.min_gallop = before.min_gallop
  listlen : after.listlen = before.listlen
  basekeys : after.basekeys = before.basekeys
  dataSize : after.data.entries.size = before.data.entries.size
  tempSize : after.a.cells.size = before.a.cells.size
  tempBacking : after.a.backing = before.a.backing
  tempValuesMode : after.a.hasValues = before.a.hasValues
  alloced : after.alloced = before.alloced
  pending : after.pending = before.pending
  comparator : after.key_compare = before.key_compare
  mrCurrent : after.mr_current = before.mr_current
  mrE : after.mr_e = before.mr_e
  mrMask : after.mr_mask = before.mr_mask

end TempRangeInBounds
end CPythonListsort
