/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.SortSliceSafety
import Def.CPythonListsort.Code.Transcription.Binarysort.Part3
import Mathlib
import Structure.CPythonListsort.Code.Assembly.BinarysortSafety.Part2
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

/-- Interval width is a sufficient fuel measure: every active comparison
strictly shrinks the unknown interval, so `right - left` units suffice. -/
theorem binarysortSearchTraced_safe
    (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν)
    (base : Int) (pivot : SortSliceEntry κ ν) (left right n : Nat)
    (hrange : SortSlice.RangeInBounds slice base n)
    (hle : left ≤ right) (hright : right ≤ n)
    (hwidth : right - left ≤ fuel) :
    ∃ result,
      BinarysortSearchSafetyPost fuel lt slice base pivot left right result := by
  induction fuel generalizing left right with
  | zero =>
      have heq : left = right := by omega
      subst right
      let result : BinarySearchResult :=
        { position := left, fuelExhausted := false }
      refine ⟨result, ?_⟩
      exact
        { resultEq := by
            simp [binarysortSearchTraced?, TraceResult.pure, result]
          resultFuel := rfl
          traceSafe := by
            simpa [binarysortSearchTraced?, result] using
              (BinarysortTraceSafe.pure result)
          positionLower := Nat.le_refl _
          positionUpper := Nat.le_refl _ }
  | succ fuel ih =>
      by_cases hactive : left < right
      · let middle := (left + right) / 2
        have hmiddleLower : left ≤ middle := by
          dsimp [middle]
          omega
        have hmiddleUpper : middle < right := by
          dsimp [middle]
          omega
        have hmiddleN : middle < n := lt_of_lt_of_le hmiddleUpper hright
        have hindex :=
          indexInBounds_of_range_offset slice base n middle hrange hmiddleN
        rcases read_result_of_indexInBounds slice (base + Int.ofNat middle)
            hindex with ⟨entry, hreadResult, hread⟩
        have hreadSafe := keysRead_safe slice (base + Int.ofNat middle) hindex
        by_cases hlt : lt pivot.key entry.key = true
        · have hnextWidth : middle - left ≤ fuel := by
            dsimp [middle]
            omega
          rcases ih left middle hmiddleLower (Nat.le_trans
              hmiddleUpper.le hright) hnextWidth with ⟨result, hpost⟩
          have htrace : BinarysortTraceSafe
              ((TraceResult.sortSliceKeysRead? slice
                (base + Int.ofNat middle)).bind fun current =>
                  if iflt lt pivot.key current.key then
                    binarysortSearchTraced? fuel lt slice base pivot left middle
                  else
                    binarysortSearchTraced? fuel lt slice base pivot
                      (middle + 1) right) :=
            BinarysortTraceSafe.bind _ _ entry hreadResult hreadSafe
              (by simpa [iflt, hlt] using hpost.traceSafe)
          refine ⟨result, ?_⟩
          exact
            { resultEq := by
                unfold binarysortSearchTraced?
                rw [if_pos hactive]
                dsimp only
                rw [BinarysortTraceSafe.bind_result_of_eq_some _ _ entry
                  hreadResult]
                simpa [middle, iflt, hlt] using hpost.resultEq
              resultFuel := hpost.resultFuel
              traceSafe := by
                simpa [binarysortSearchTraced?, hactive, middle, iflt, hlt]
                  using htrace
              positionLower := hpost.positionLower
              positionUpper := Nat.le_trans hpost.positionUpper hmiddleUpper.le }
        · have hnextWidth : right - (middle + 1) ≤ fuel := by
            dsimp [middle]
            omega
          rcases ih (middle + 1) right (Nat.succ_le_of_lt hmiddleUpper)
              hright hnextWidth with ⟨result, hpost⟩
          have htrace : BinarysortTraceSafe
              ((TraceResult.sortSliceKeysRead? slice
                (base + Int.ofNat middle)).bind fun current =>
                  if iflt lt pivot.key current.key then
                    binarysortSearchTraced? fuel lt slice base pivot left middle
                  else
                    binarysortSearchTraced? fuel lt slice base pivot
                      (middle + 1) right) :=
            BinarysortTraceSafe.bind _ _ entry hreadResult hreadSafe
              (by simpa [iflt, hlt] using hpost.traceSafe)
          refine ⟨result, ?_⟩
          exact
            { resultEq := by
                unfold binarysortSearchTraced?
                rw [if_pos hactive]
                dsimp only
                rw [BinarysortTraceSafe.bind_result_of_eq_some _ _ entry
                  hreadResult]
                simpa [middle, iflt, hlt] using hpost.resultEq
              resultFuel := hpost.resultFuel
              traceSafe := by
                simpa [binarysortSearchTraced?, hactive, middle, iflt, hlt]
                  using htrace
              positionLower := Nat.le_trans hmiddleLower
                (Nat.le_trans (Nat.le_succ middle) hpost.positionLower)
              positionUpper := hpost.positionUpper }
      · have heq : left = right := Nat.le_antisymm hle (Nat.le_of_not_gt hactive)
        subst right
        let result : BinarySearchResult :=
          { position := left, fuelExhausted := false }
        refine ⟨result, ?_⟩
        exact
          { resultEq := by
              simp [binarysortSearchTraced?, TraceResult.pure, result]
            resultFuel := rfl
            traceSafe := by
              simpa [binarysortSearchTraced?, result] using
                (BinarysortTraceSafe.pure result)
            positionLower := Nat.le_refl _
            positionUpper := Nat.le_refl _ }

end BinarysortTraceSafe
end CPythonListsort
