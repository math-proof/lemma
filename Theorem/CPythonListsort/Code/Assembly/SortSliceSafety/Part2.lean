/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean -/

import Def.CPythonListsort.Code.Assembly.AccessTrace.Part9
import Mathlib
import Def.CPythonListsort.Code.Assembly.SortSliceSafety.Part2
/-!
# Safety of the `sortslice` movement primitives

The instrumentation in this file is assembled directly from the typed
`SortSlice` access wrappers.  The Boolean `valuesPresent` is the modeled C
pointer mode: synchronized-values events are controlled only by that flag and
never by an individual entry's optional payload.

Bulk operations follow the source's two phases exactly: every key movement is
observed before any synchronized-values movement.  Each phase independently
executes the paired-entry transcription.  This is intentional: one execution
models movement of the key array and the other movement of the values array;
both erase to the same atomic paired-entry operation.
-/


namespace CPythonListsort

universe u v

namespace SortSlice

/-- The explicit displacement bounds imply validity of the advanced cursor. -/
theorem CursorMovementInRange.result
    {slice : SortSlice κ ν} {index amount : Int}
    (h : CursorMovementInRange slice index amount) :
    CursorInRange slice (advance index amount) := by
  rcases h with ⟨hcursor, hlower, hupper⟩
  rcases hcursor with ⟨hindex, _⟩
  simp only [CursorInRange, advance]
  constructor <;> omega

end SortSlice
end CPythonListsort
