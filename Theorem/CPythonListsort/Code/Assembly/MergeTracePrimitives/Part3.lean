/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean -/

import Def.CPythonListsort.Code.Assembly.MergeMemcpyProvenance
import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part3
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

namespace MovementTraceSafe

theorem bind (current : TraceResult α) (next : α → TraceResult β)
    (value : α) (hresult : current.result = some value)
    (hcurrent : MovementTraceSafe current)
    (hnext : MovementTraceSafe (next value)) :
    MovementTraceSafe (current.bind next) := by
  rcases hcurrent with ⟨hcurrentFuel, hcurrentPush, hcurrentBounds, hcurrentLive⟩
  rcases hnext with ⟨hnextFuel, hnextPush, hnextBounds, hnextLive⟩
  constructor
  · simp [TraceResult.trace_bind, hresult, hcurrentFuel, hnextFuel]
  · simp [TraceResult.trace_bind, hresult, AccessTrace.compose,
      hcurrentPush, hnextPush]
  · rw [TraceResult.trace_bind, hresult,
      AccessTrace.allAccessesInBounds_compose]
    exact ⟨hcurrentBounds, hnextBounds⟩
  · rw [TraceResult.trace_bind, hresult,
      AccessTrace.tempPayloadAccessesLive_compose]
    exact ⟨hcurrentLive, hnextLive⟩

end MovementTraceSafe
end AccessTrace.HasAccess
end MovementAccessOnly
end MergeMovementFrame
end TempRangeInBounds
end CPythonListsort
