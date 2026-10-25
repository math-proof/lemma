/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean -/

import Def.CPythonListsort.Code.Assembly.MergeMemcpyProvenance
import Def.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part5
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

namespace MovementTempLive

theorem pure (value : α) : MovementTempLive (TraceResult.pure value) :=
  AccessTrace.tempPayloadAccessesLive_empty

theorem map (current : TraceResult α) (transform : α → β)
    (h : MovementTempLive current) : MovementTempLive (current.map transform) := by
  exact h

theorem bind (current : TraceResult α) (next : α → TraceResult β)
    (hcurrent : MovementTempLive current)
    (hnext : ∀ value, MovementTempLive (next value)) :
    MovementTempLive (current.bind next) := by
  cases hresult : current.result with
  | none => simpa [MovementTempLive, TraceResult.trace_bind, hresult] using hcurrent
  | some value =>
      rw [MovementTempLive, TraceResult.trace_bind, hresult,
        AccessTrace.tempPayloadAccessesLive_compose]
      exact ⟨hcurrent, hnext value⟩

end MovementTempLive
end AccessTrace.HasAccess
end MovementAccessOnly
end MergeMovementFrame
end TempRangeInBounds
end CPythonListsort
