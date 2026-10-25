/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/Binarysort.lean -/

import Def.CPythonListsort.Code.Transcription.MergeState.Part3
import Structure.CPythonListsort.Code.Transcription.Binarysort
/-!
# Stable binary insertion transcription

Invalid inputs from C's assertion domain and failed modeled array accesses
return `none`.  Fuel exhaustion remains distinct.  A comparator-false result
(including equality for a strict comparator) follows the right-hand branch of
the binary search; stability is therefore obtained for strict comparators.
-/


namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

/-- Fuel-bounded binary-search phase of `binarysort`, exported for exact traced
erasure and safety proofs. -/
def binarysortSearch? :
    Nat → BoolComparator κ → SortSlice κ ν → Int → SortSliceEntry κ ν →
      Nat → Nat → Option BinarySearchResult
  | 0, _, _, _, _, left, right =>
      some { position := left, fuelExhausted := decide (left < right) }
  | fuel + 1, lt, slice, base, pivot, left, right =>
      if left < right then
        let middle := (left + right) / 2
        binarysortBindOptionAcross (slice.read? (base + Int.ofNat middle)) fun entry =>
          if iflt lt pivot.key entry.key then
            binarysortSearch? fuel lt slice base pivot left middle
          else
            binarysortSearch? fuel lt slice base pivot (middle + 1) right
      else
        some { position := left, fuelExhausted := false }

end CPythonListsort
