/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean -/

import Mathlib
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

/-- One observable key/payload pair.  `none` models `values == NULL`. -/
structure SortSliceEntry (κ : Type u) (ν : Type v) where
  key : κ
  value : Option ν
  deriving DecidableEq, Repr

/-- Array-backed storage used in place of CPython's synchronized pointer arrays. -/
structure SortSlice (κ : Type u) (ν : Type v) where
  entries : Array (SortSliceEntry κ ν)
  deriving DecidableEq, Repr

end CPythonListsort
