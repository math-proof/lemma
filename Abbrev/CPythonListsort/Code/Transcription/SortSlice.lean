/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean -/

import Mathlib
import Def.CPythonListsort.Code.Transcription.SortSlice.Part5
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

/-- Provenance of the source operand of `sortslice_memmove`.  Movement uses the
same dependent backing witness as `memcpy`, but imposes no disjointness
condition: shared storage is handled by overlap-safe traversal instead. -/
abbrev MemmoveSource (destination : SortSlice κ ν) :=
  MemcpySource destination

end SortSlice
end CPythonListsort
