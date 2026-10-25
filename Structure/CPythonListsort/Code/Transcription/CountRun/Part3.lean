/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/CountRun.lean -/

import Def.CPythonListsort.Code.Transcription.MergeState.Part3
import Def.CPythonListsort.Code.Transcription.ReverseSlice
import Def.CPythonListsort.Code.Transcription.CountRun.Part3
/-!
# Natural-run detection transcription

This is a direct, bounded transcription of CPython's `count_run`.  The
pointer `slo` is represented by a shared `SortSlice` together with a signed
base index.  Failed accesses are returned as `none`; exhaustion of one of the
bounded loops is recorded separately in the result.

The comparison branches deliberately retain CPython's argument order.  In
particular, the descending scan first asks whether the next key is smaller
and only asks the reverse comparison when that answer is false.  Blocks whose
adjacent pairs are operationally equivalent (both comparison directions
return false) are reversed as they are encountered before the complete
descending run is reversed.  Interpreting those blocks as key equality, and
therefore as a stability statement, requires the later strict-weak-order node.
-/


namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

/-- Result of the bounded descending probe loop, including the unresolved
operational-equivalence suffix length. -/
structure DescendingScanResult (κ : Type u) (ν : Type v) where
  slice : SortSlice κ ν
  length : Nat
  equalTail : Nat
  fuelExhausted : Bool

end CPythonListsort
