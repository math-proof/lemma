/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/ReverseSlice.lean -/

import Theorem.CPythonListsort.Code.Transcription.SortSlice
/-!
# Slice reversal transcription

The endpoints are signed pointer-like indices and `hi` is exclusive at the
public boundary.  Bounds failures return `none`; bounded-loop exhaustion is a
separate observable flag for later adequacy proofs.  Because a `SortSliceEntry`
contains its optional payload, each swap synchronizes keys and values.
-/


namespace CPythonListsort

universe u v

structure ReverseSliceResult (κ : Type u) (ν : Type v) where
  slice : SortSlice κ ν
  fuelExhausted : Bool
  deriving DecidableEq, Repr

end CPythonListsort
