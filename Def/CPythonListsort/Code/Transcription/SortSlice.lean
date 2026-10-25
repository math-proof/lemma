/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean -/

import Mathlib
import Structure.CPythonListsort.Code.Transcription.SortSlice
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

/-- Read an entry through a signed pointer-like index. -/
def read? (slice : SortSlice κ ν) (index : Int) : Option (SortSliceEntry κ ν) :=
  if 0 ≤ index then
    slice.entries[index.toNat]?
  else
    none

/-- Replace an entry through a signed pointer-like index. -/
def write? (slice : SortSlice κ ν) (index : Int) (entry : SortSliceEntry κ ν) :
    Option (SortSlice κ ν) :=
  if hnonnegative : 0 ≤ index then
    let i := index.toNat
    if hinBounds : i < slice.entries.size then
      some { entries := slice.entries.set i entry }
    else
      none
  else
    none

/-- Copy one synchronized entry from `source` into `destination`. -/
def copyFrom? (destination source : SortSlice κ ν) (dst src : Int) :
    Option (SortSlice κ ν) := do
  let entry ← source.read? src
  destination.write? dst entry

/-- Copy one synchronized entry within a shared store. -/
def copy? (slice : SortSlice κ ν) (dst src : Int) : Option (SortSlice κ ν) :=
  copyFrom? slice slice dst src

end SortSlice
end CPythonListsort
