/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean -/

import Mathlib
import Def.CPythonListsort.Code.Transcription.SortSlice.Part3
/-!
# `sortslice` model and movement primitives

CPython stores keys and optional payload values in parallel pointer arrays.
The Lean model stores their observable pairing as one entry, so every movement
primitive moves a key and its payload atomically.  Integer indices replace raw
pointers.  Failed bounds checks are explicit through `Option`; later safety
proofs establish that transcribed calls return `some`.

`memmove` carries explicit backing provenance.  On one shared store it chooses
its traversal direction from the overlap geometry: a rightward overlapping
move copies from the end, while a leftward move copies from the beginning, so
unread source entries are never overwritten.  A distinct backing instead uses
the source-language's forward two-store copy order, even when its contents
happen to equal the destination.  `memcpy` uses the same provenance distinction
but rejects overlapping same-backing ranges.
-/


namespace CPythonListsort

universe u v

namespace SortSlice

namespace MemcpySource

instance {destination : SortSlice κ ν} (source : MemcpySource destination)
    (dst src : Int) (count : Nat) : Decidable (source.Admissible dst src count) :=
  match source with
  | .sameBacking => inferInstanceAs (Decidable (MemcpyRangesDisjoint dst src count))
  | .distinctBacking _ => isTrue trivial

end MemcpySource
end SortSlice
end CPythonListsort
