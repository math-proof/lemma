/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean -/

import Def.CPythonListsort.Code.Assembly.AccessTrace.Part9
import Mathlib
import Def.CPythonListsort.Code.Assembly.SortSliceSafety
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

/-- Rejected same-backing overlap produces neither a partial access trace nor
an observable traced result, and still obeys exact erasure. -/
theorem memcpyTraced_sameBacking_overlap_rejected (valuesPresent : Bool)
    (count : Nat) (destination : SortSlice κ ν) (dst src : Int)
    (hoverlap : ¬ MemcpyRangesDisjoint dst src count) :
    (memcpyTraced? valuesPresent count destination .sameBacking dst src).result = none ∧
      (memcpyTraced? valuesPresent count destination .sameBacking dst src).trace =
        AccessTrace.empty ∧
      (memcpyTraced? valuesPresent count destination .sameBacking dst src).erase =
        memcpy? count destination .sameBacking dst src := by
  simp [memcpyTraced?, memcpy?, MemcpySource.Admissible, hoverlap,
    TraceResult.failure, TraceResult.erase]

end SortSlice
end CPythonListsort
