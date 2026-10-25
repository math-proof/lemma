/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean -/

import Mathlib
import Structure.CPythonListsort.Code.Transcription.SortSlice.Part2
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

/-- Copy between the current cursors of two slices, then increment both as
`sortslice_copy_incr` does.  Only the destination store is updated; the source
cursor is nevertheless returned alongside the destination cursor. -/
def copyFromIncr? (destination source : SortSlice κ ν)
    (dst src : Int) : Option (CursorResult κ ν) := do
  let updated ← destination.copyFrom? source dst src
  pure { slice := updated, dst := dst + 1, src := src + 1 }

/-- Copy between the current cursors of two slices, then decrement both as
`sortslice_copy_decr` does.  Only the destination store is updated; the source
cursor is nevertheless returned alongside the destination cursor. -/
def copyFromDecr? (destination source : SortSlice κ ν)
    (dst src : Int) : Option (CursorResult κ ν) := do
  let updated ← destination.copyFrom? source dst src
  pure { slice := updated, dst := dst - 1, src := src - 1 }

/-- Shared-store specialization of `copyFromIncr?`. -/
def copyIncr? (slice : SortSlice κ ν) (dst src : Int) : Option (CursorResult κ ν) :=
  copyFromIncr? slice slice dst src

/-- Shared-store specialization of `copyFromDecr?`. -/
def copyDecr? (slice : SortSlice κ ν) (dst src : Int) : Option (CursorResult κ ν) :=
  copyFromDecr? slice slice dst src

/-- Two equal-length half-open ranges do not overlap.  The formulation admits
empty ranges and ranges that meet exactly at an endpoint. -/
def MemcpyRangesDisjoint (dst src : Int) (count : Nat) : Prop :=
  dst + Int.ofNat count ≤ src ∨ src + Int.ofNat count ≤ dst

end SortSlice
end CPythonListsort
