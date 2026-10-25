/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortSupport.lean -/

import Def.CPythonListsort.Code.Assembly.ListSortInputMode
import Def.CPythonListsort.Code.Assembly.ReverseSliceSafety.Part2
import Theorem.CPythonListsort.Code.Equivalence.MinrunResults.Part3
import Theorem.CPythonListsort.Code.Policy.PushRunPreservation
import Structure.CPythonListsort.Code.Assembly.ListSortSupport
/-!
# Support lemmas for top-level listsort assembly

This module packages the initialized `MergeState`, the adaptive-minrun state
carried by the scan, and the frame facts for the small top-level transitions.
It deliberately does not define a second listsort evaluator: the traced
top-level assembly consumes the public helpers from the reviewed
`ListSortImpl` transcription.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-! ## Final-reversal phase selection -/

/-- CPython's final reverse acts on saved values in keyed mode and on the key
array itself in unkeyed mode. -/
def finalReversePhase (hasValues : Bool) : ReverseSlicePhase :=
  if hasValues then .values else .keys

end CPythonListsort
