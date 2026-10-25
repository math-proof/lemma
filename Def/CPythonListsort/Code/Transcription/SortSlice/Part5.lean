/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean -/

import Mathlib
import Inductive.CPythonListsort.Code.Transcription.SortSlice.Part2
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

/-- A leftward move is forward; a genuinely rightward move is backward. -/
def memmoveDirection (dst src : Int) : MovementDirection :=
  if dst ≤ src then .forward else .backward

/-- Forward traversal used by `memmove?` when the destination does not begin
to the right of the source.  Exported for direct trace instrumentation. -/
def memmoveForward? :
    Nat → SortSlice κ ν → Int → Int → Option (SortSlice κ ν)
  | 0, slice, _, _ => some slice
  | count + 1, slice, dst, src => do
      let updated ← slice.copy? dst src
      memmoveForward? count updated (dst + 1) (src + 1)

/-- Backward traversal used by `memmove?` for a rightward move, preventing an
overlapping write from destroying an unread source entry.  Exported for direct
trace instrumentation. -/
def memmoveBackward? :
    Nat → SortSlice κ ν → Int → Int → Option (SortSlice κ ν)
  | 0, slice, _, _ => some slice
  | count + 1, slice, dst, src => do
      let offset := Int.ofNat count
      let updated ← slice.copy? (dst + offset) (src + offset)
      memmoveBackward? count updated dst src

/-- Overlap-safe movement within one store, matching C `memmove` direction. -/
def memmove? (slice : SortSlice κ ν) (dst src : Int) (count : Nat) :
    Option (SortSlice κ ν) :=
  match memmoveDirection dst src with
  | .forward => memmoveForward? count slice dst src
  | .backward => memmoveBackward? count slice dst src

end SortSlice
end CPythonListsort
