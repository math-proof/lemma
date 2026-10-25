/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean -/

import Mathlib
import Instance.CPythonListsort.Code.Transcription.SortSlice
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

/-- Provenance of the source operand of `memcpy` relative to its destination.

The same-backing constructor carries no second `SortSlice`: its source is the
destination itself by construction.  The distinct-backing constructor is an
explicit provenance assertion and therefore remains distinct even when its
stored contents are extensionally equal to the destination. -/
inductive MemcpySource (destination : SortSlice κ ν) where
  | sameBacking
  | distinctBacking (source : SortSlice κ ν)
  deriving Repr

end SortSlice
end CPythonListsort
