/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean -/

import Def.CPythonListsort.Code.Assembly.MergeMemcpyProvenance
import Def.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part6
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

structure MainDataCopyDecrPost (state : MergeState κ ν) (dst src : Int)
    (result : MergeHiDataCursorResult κ ν) : Prop where
  success : (mainDataCopyDecrTraced? state dst src).result = some result
  traceSafe : MovementTraceSafe (mainDataCopyDecrTraced? state dst src)
  exactErasure : (mainDataCopyDecrTraced? state dst src).erase =
    mergeHiCopyDataDecr? state dst src
  frame : MergeMovementFrame state result.state
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  dstDecrement : result.dst = dst - 1
  srcDecrement : result.src = src - 1

structure MainDataMemmovePost (state result : MergeState κ ν)
    (dst src : Int) (count : Nat) : Prop where
  success : (mainDataMemmoveTraced? state dst src count).result = some result
  traceSafe : MovementTraceSafe (mainDataMemmoveTraced? state dst src count)
  exactErasure : (mainDataMemmoveTraced? state dst src count).erase =
    mainDataMemmove? state dst src count
  frame : MergeMovementFrame state result
  tempInvariant : TempStorageInv result.a result.alloced
  tempLive : result.a.Live
  valuesMode : SortSlice.ValuesModeInvariant result.a.hasValues result.data
  phaseOrder :
    (mainDataMemmoveTraced? state dst src count).trace.accesses =
      match SortSlice.memmoveDirection dst src with
      | .forward =>
          (SortSlice.memmoveForwardKeysTraced? count state.data dst
            src).trace.accesses ++
            if state.a.hasValues then
              (SortSlice.memmoveForwardValuesTraced? count state.data dst
                src).trace.accesses
            else []
      | .backward =>
          (SortSlice.memmoveBackwardKeysTraced? count state.data dst
            src).trace.accesses ++
            if state.a.hasValues then
              (SortSlice.memmoveBackwardValuesTraced? count state.data dst
                src).trace.accesses
            else []

end AccessTrace.HasAccess
end MovementAccessOnly
end MergeMovementFrame
end TempRangeInBounds
end CPythonListsort
