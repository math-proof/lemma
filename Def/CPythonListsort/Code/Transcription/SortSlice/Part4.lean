/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/SortSlice.lean -/

import Mathlib
import Instance.CPythonListsort.Code.Transcription.SortSlice.Part2
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

/-- Unchecked forward-copy loop.  Its public wrapper supplies the C `memcpy`
backing-domain check once, before any access occurs. -/
def memcpyCore? :
    Nat → SortSlice κ ν → SortSlice κ ν → Int → Int → Option (SortSlice κ ν)
  | 0, destination, _, _, _ => some destination
  | count + 1, destination, source, dst, src => do
      let updated ← copyFrom? destination source dst src
      memcpyCore? count updated source (dst + 1) (src + 1)

/-- Copy `count` entries using C `memcpy`'s backing discipline.  Overlapping
same-backing ranges are outside the modeled domain and return `none` before any
copy step; distinct backings are not inferred from their contents. -/
def memcpy? (count : Nat) (destination : SortSlice κ ν)
    (source : MemcpySource destination) (dst src : Int) : Option (SortSlice κ ν) :=
  if source.Admissible dst src count then
    memcpyCore? count destination source.store dst src
  else
    none

end SortSlice
end CPythonListsort
