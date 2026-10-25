/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.SortSliceSafety
import Def.CPythonListsort.Code.Transcription.Binarysort.Part3
import Mathlib
import Theorem.CPythonListsort.Code.Assembly.BinarysortSafety
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

/-- Complete result contract for one binary-search call. -/
structure BinarysortSearchSafetyPost
    (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν)
    (base : Int) (pivot : SortSliceEntry κ ν) (left right : Nat)
    (result : BinarySearchResult) : Prop where
  resultEq :
    (binarysortSearchTraced? fuel lt slice base pivot left right).result =
      some result
  resultFuel : result.fuelExhausted = false
  traceSafe :
    BinarysortTraceSafe
      (binarysortSearchTraced? fuel lt slice base pivot left right)
  positionLower : left ≤ result.position
  positionUpper : result.position ≤ right

end BinarysortTraceSafe
end CPythonListsort
