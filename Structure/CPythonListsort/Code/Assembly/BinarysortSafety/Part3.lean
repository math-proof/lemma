/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.SortSliceSafety
import Def.CPythonListsort.Code.Transcription.Binarysort.Part3
import Mathlib
import Theorem.CPythonListsort.Code.Assembly.BinarysortSafety.Part2
/-!
# `binarysort` safety

This module instruments CPython's stable binary insertion sort directly from
the traced `SortSlice` primitives.  The trace follows the source phases: read
the key pivot, probe binary-search midpoints, shift keys from right to left,
write the key pivot, and then (when values storage is present) read, shift, and
write the synchronized payloads.  Explicit fuel exhaustion remains observable
but is proved unreachable on source-admitted calls.

Version-one delta: the pinned C `IFLT` can jump to `fail` when comparison
raises, while this snapshot model's `BoolComparator` is pure and total.  The
traced evaluator therefore has no comparator-failure result or comparator
event; exact erasure below is to the reviewed Lean transcription on that
explicitly narrower comparator model.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

namespace BinarysortTraceSafe

/-- Complete contract for the source-ordered key/value shift and insertion. -/
structure BinarysortShiftInsertSafetyPost
    (valuesPresent : Bool) (before : SortSlice κ ν) (base : Int)
    (n ok position : Nat) (pivot : SortSliceEntry κ ν)
    (after : SortSlice κ ν) : Prop where
  resultEq :
    (binarysortShiftInsertTraced? valuesPresent before base ok position
      pivot).result = some after
  traceSafe :
    BinarysortTraceSafe
      (binarysortShiftInsertTraced? valuesPresent before base ok position pivot)
  exactErasure :
    (binarysortShiftInsertTraced? valuesPresent before base ok position
      pivot).erase = do
        let shifted ← before.memmove?
          (base + Int.ofNat (position + 1))
          (base + Int.ofNat position) (ok - position)
        shifted.write? (base + Int.ofNat position) pivot
  valuesMode : SortSlice.ValuesModeInvariant valuesPresent after
  entriesSize : after.entries.size = before.entries.size
  range : SortSlice.RangeInBounds after base n

end BinarysortTraceSafe
end CPythonListsort
