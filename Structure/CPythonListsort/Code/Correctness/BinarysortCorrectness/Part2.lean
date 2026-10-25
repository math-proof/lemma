/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean -/

import Def.CPythonListsort.Code.Assembly.BinarysortSafety.Part2
import Def.CPythonListsort.Code.Assembly.Order.Part4
import Def.CPythonListsort.Code.Correctness.SortSliceRange
import Mathlib.Data.List.InsertIdx
import Def.CPythonListsort.Code.Correctness.BinarysortCorrectness.Part2
/-!
# Functional correctness of `binarysort`

This file proves correctness of the reviewed binary-insertion transcription on
occurrence-carrying keys.  The proof is about the same traced execution covered
by `binarysort_safe`: raw functional correctness is identified with that result
through exact erasure, rather than through a second sorting implementation.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

variable {beta kappa rho : Type*}

/-! ## Raw outer-loop correctness -/

structure BinarysortLoopCorrectnessPost
    (lt : BoolComparator alpha) (canonical : List (Occurrence alpha))
    (state : MergeState (Occurrence alpha) nu)
    (before : SortSlice (Occurrence alpha) nu)
    (base n ok fuel : Nat) (result : BinarysortResult (Occurrence alpha) nu) : Prop where
  resultEq : binarysortLoop? fuel state before (Int.ofNat base) n ok = some result
  resultFuel : result.fuelExhausted = false
  sorted : Sorted (occurrenceComparator lt)
    (sortSliceRangeKeys result.slice base n)
  stable : StableOccurrencePermutation lt canonical
    (sortSliceRangeKeys result.slice base n).toList
  rangeEntriesPerm :
    (sortSliceRangeEntries result.slice base n).toList.Perm
      (sortSliceRangeEntries before base n).toList
  frame : SortSlice.EqualOutsideRange before result.slice base n

/-- Public correctness certificate for the exact traced `binarysort`
execution.  The stability premise is intentionally attached to the whole
target range: binary insertion preserves the pre-existing order of equal
occurrences, so it cannot repair an already non-canonical equal-key suffix. -/
structure BinarysortCorrectnessPost
    (lt : BoolComparator alpha) (canonical : List (Occurrence alpha))
    (state : MergeState (Occurrence alpha) nu)
    (before : SortSlice (Occurrence alpha) nu)
    (base n ok : Nat) (result : BinarysortResult (Occurrence alpha) nu) : Prop where
  safety : BinarysortSafetyPost state before (Int.ofNat base) n ok result
  sorted : Sorted (occurrenceComparator lt)
    (sortSliceRangeKeys result.slice base n)
  stable : StableOccurrencePermutation lt canonical
    (sortSliceRangeKeys result.slice base n).toList
  rangeEntriesPerm :
    (sortSliceRangeEntries result.slice base n).toList.Perm
      (sortSliceRangeEntries before base n).toList
  frame : SortSlice.EqualOutsideRange before result.slice base n
  beforeFrame : ∀ k, k < base → result.slice.entries[k]? = before.entries[k]?
  afterFrame : ∀ k, base + n ≤ k →
    result.slice.entries[k]? = before.entries[k]?

end CPythonListsort
