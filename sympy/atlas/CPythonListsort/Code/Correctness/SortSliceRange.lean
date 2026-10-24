/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/SortSliceRange.lean -/

import sympy.atlas.CPythonListsort.Code.Transcription.SortSlice
import Mathlib

/-!
# Half-open `SortSlice` ranges and semantic frames

Correctness proofs reason about the contents moved by the transcribed pointer
operations, rather than only their allocation bounds.  This file supplies one
shared, natural-indexed vocabulary for a half-open range `[start, start + count)`
and for the assertion that an update is confined to such a range.
-/

namespace CPythonListsort

universe u v

/-- Whole key/value entries in the clipped half-open range
`[start, start + count)`. -/
def sortSliceRangeEntries (slice : SortSlice κ ν) (start count : Nat) :
    Array (SortSliceEntry κ ν) :=
  slice.entries.extract start (start + count)

/-- Key projection of `sortSliceRangeEntries`.  Payloads remain paired with
their keys in `sortSliceRangeEntries`; this projection is for the shared
sortedness and occurrence-stability specifications. -/
def sortSliceRangeKeys (slice : SortSlice κ ν) (start count : Nat) :
    Array κ :=
  (sortSliceRangeEntries slice start count).map SortSliceEntry.key

/-- `before` and `after` have the same extent and every half-open range
disjoint from `[start, start + count)` has exactly the same whole entries.

The quantified-range formulation is intentionally compositional: callers can
specialize it directly to the unconsumed suffix, while cell-level proofs may
establish it from their own pointwise write-frame lemmas. -/
def EqualOutsideRange (before after : SortSlice κ ν)
    (start count : Nat) : Prop :=
  before.entries.size = after.entries.size ∧
    ∀ otherStart otherCount,
      otherStart + otherCount ≤ start ∨ start + count ≤ otherStart →
        sortSliceRangeEntries before otherStart otherCount =
          sortSliceRangeEntries after otherStart otherCount

namespace EqualOutsideRange
