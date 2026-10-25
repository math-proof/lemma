/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean -/

import Def.CPythonListsort.Code.Assembly.MergeMemcpyProvenance
import Theorem.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part4
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

namespace MergeMovementFrame

namespace MovementAccessOnly

namespace AccessTrace.HasAccess

/-! ## Main-data one-cell decrement copy -/

/-- State-level wrapper around the shared-store decrementing copy.  Cursor
arithmetic is signed, so copying cell zero legitimately returns `-1`. -/
def mainDataCopyDecrTraced? (state : MergeState κ ν) (dst src : Int) :
    TraceResult (MergeHiDataCursorResult κ ν) :=
  (SortSlice.copyDecrTraced? state.a.hasValues state.data dst src).map
    fun copied =>
      { state := { state with data := copied.slice }
        dst := copied.dst
        src := copied.src }

end AccessTrace.HasAccess
end MovementAccessOnly
end MergeMovementFrame
end TempRangeInBounds
end CPythonListsort
