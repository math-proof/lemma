/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean -/

import Mathlib
import Abbrev.CPythonListsort.Code.Transcription.SortSlice
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

/-- General two-store `sortslice_memmove`.  Same-backing movement delegates to
the overlap-safe shared-store implementation, while a distinct backing follows
the C helper's increasing-address source order.  The branch is selected only by
the explicit provenance constructor, never by comparing stored contents. -/
def memmoveFrom? (destination : SortSlice κ ν)
    (source : MemmoveSource destination) (dst src : Int) (count : Nat) :
    Option (SortSlice κ ν) :=
  match source with
  | .sameBacking => destination.memmove? dst src count
  | .distinctBacking source => memcpyCore? count destination source dst src

/-- Pointer advancement becomes signed index arithmetic. -/
def advance (index amount : Int) : Int :=
  index + amount

def overlapExample : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 1, value := some 10 },
        { key := 2, value := some 20 },
        { key := 3, value := some 30 },
        { key := 4, value := some 40 }] }

end SortSlice
end CPythonListsort
