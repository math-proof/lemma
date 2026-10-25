/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean -/

import Def.CPythonListsort.Code.Assembly.AccessTrace.Part9
import Mathlib
import Theorem.CPythonListsort.Code.Assembly.SortSliceSafety
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

/-- The exact key-array event pair for one source-language assignment. -/
def keyCopyAccesses (destinationExtent sourceExtent : Nat)
    (dst src : Int) : List AccessEvent :=
  [{ kind := .read, region := .inputKeys,
     index := src, extent := sourceExtent },
   { kind := .write, region := .inputKeys,
     index := dst, extent := destinationExtent }]

/-- The exact optional-values event pair for one source-language assignment. -/
def valuesCopyAccesses (destinationExtent sourceExtent : Nat)
    (dst src : Int) : List AccessEvent :=
  [{ kind := .read, region := .synchronizedValues,
     index := src, extent := sourceExtent },
   { kind := .write, region := .synchronizedValues,
     index := dst, extent := destinationExtent }]

end SortSlice
end CPythonListsort
