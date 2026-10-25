/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.SortSliceSafety
import Def.CPythonListsort.Code.Transcription.Binarysort.Part3
import Mathlib
import Structure.CPythonListsort.Code.Assembly.BinarysortSafety.Part3
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

/-- The right-to-left shift and both insertion writes are safe whenever the
pivot and insertion position come from the current sorted prefix. -/
theorem binarysortShiftInsertTraced_safe
    (valuesPresent : Bool) (slice : SortSlice κ ν) (base : Int)
    (n ok position : Nat) (pivot : SortSliceEntry κ ν)
    (hrange : SortSlice.RangeInBounds slice base n)
    (hposition : position ≤ ok) (hok : ok < n)
    (hmode : SortSlice.ValuesModeInvariant valuesPresent slice)
    (hpivot : slice.read? (base + Int.ofNat ok) = some pivot) :
    ∃ after,
      BinarysortShiftInsertSafetyPost valuesPresent slice base n ok position
        pivot after := by
  let count := ok - position
  let dst := base + Int.ofNat (position + 1)
  let src := base + Int.ofNat position
  let insertIndex := base + Int.ofNat position
  have hdst : SortSlice.RangeInBounds slice dst count := by
    simpa [dst, count] using shiftDestinationRange slice base n ok position
      hrange hposition hok
  have hsrc : SortSlice.RangeInBounds slice src count := by
    simpa [src, count] using shiftSourceRange slice base n ok position hrange
      hposition hok.le
  have hinsert : SortSlice.IndexInBounds slice insertIndex := by
    apply indexInBounds_of_range_offset slice base n position hrange
    exact lt_of_le_of_lt hposition hok
  have hpivotMode := hmode.read_matches_of_eq_some hpivot
  rcases memmoveBackwardKeysTraced_traceSafe count slice dst src hdst hsrc with
    ⟨keyShifted, hkeyShift, hkeyShiftSafe, hkeyShiftSize⟩
  have hkeyMove :
      SortSlice.memmoveBackward? count slice dst src = some keyShifted := by
    rw [← SortSlice.erase_memmoveBackwardKeysTraced]
    exact hkeyShift
  have hkeyShiftMode :
      SortSlice.ValuesModeInvariant valuesPresent keyShifted :=
    hmode.memmoveBackward_preserved_of_eq_some count hkeyMove
  have hinsertShifted : SortSlice.IndexInBounds keyShifted insertIndex :=
    hinsert.of_size_eq hkeyShiftSize
  rcases SortSlice.write_eq_some_of_indexInBounds keyShifted insertIndex pivot
      hinsertShifted with ⟨keyResult, hkeyWriteRaw⟩
  have hkeyWrite :
      (TraceResult.sortSliceKeysWrite? keyShifted insertIndex pivot).result =
        some keyResult := by
    change (TraceResult.sortSliceKeysWrite? keyShifted insertIndex pivot).erase =
      some keyResult
    simpa using hkeyWriteRaw
  have hkeyWriteSafe := keysWrite_safe keyShifted insertIndex pivot hinsertShifted
  have hkeyPhaseSafe : BinarysortTraceSafe
      ((SortSlice.memmoveBackwardKeysTraced? count slice dst src).bind
        fun shifted =>
          TraceResult.sortSliceKeysWrite? shifted insertIndex pivot) :=
    BinarysortTraceSafe.bind _ _ keyShifted hkeyShift hkeyShiftSafe hkeyWriteSafe
  have hkeyPhaseResult :
      ((SortSlice.memmoveBackwardKeysTraced? count slice dst src).bind
        fun shifted =>
          TraceResult.sortSliceKeysWrite? shifted insertIndex pivot).result =
        some keyResult :=
    (BinarysortTraceSafe.bind_result_of_eq_some _ _ keyShifted hkeyShift).trans
      hkeyWrite
  have hkeyResultMode :
      SortSlice.ValuesModeInvariant valuesPresent keyResult :=
    hkeyShiftMode.write_preserved_of_eq_some hpivotMode hkeyWriteRaw
  have hkeyResultSize : keyResult.entries.size = slice.entries.size :=
    (SortSlice.write_entries_size_of_eq_some keyShifted keyResult insertIndex pivot
      hkeyWriteRaw).trans hkeyShiftSize
  have hkeyResultRange : SortSlice.RangeInBounds keyResult base n :=
    hrange.of_size_eq hkeyResultSize
  cases valuesPresent with
  | false =>
      have hfalseAfterWriteSafe : BinarysortTraceSafe
          ((TraceResult.sortSliceKeysWrite? keyShifted insertIndex pivot).bind
            fun keyResult => TraceResult.pure keyResult) :=
        BinarysortTraceSafe.bind _ _ keyResult hkeyWrite hkeyWriteSafe
          (BinarysortTraceSafe.pure keyResult)
      have hfalseAfterWriteResult :
          ((TraceResult.sortSliceKeysWrite? keyShifted insertIndex pivot).bind
            fun keyResult => TraceResult.pure keyResult).result =
              some keyResult := by
        rw [BinarysortTraceSafe.bind_result_of_eq_some _ _ keyResult hkeyWrite]
        rfl
      have hfalseSafe : BinarysortTraceSafe
          ((SortSlice.memmoveBackwardKeysTraced? count slice dst src).bind
            fun shifted =>
              (TraceResult.sortSliceKeysWrite? shifted insertIndex pivot).bind
                fun keyResult => TraceResult.pure keyResult) :=
        BinarysortTraceSafe.bind _ _ keyShifted hkeyShift hkeyShiftSafe
          hfalseAfterWriteSafe
      have hfalseResult :
          ((SortSlice.memmoveBackwardKeysTraced? count slice dst src).bind
            fun shifted =>
              (TraceResult.sortSliceKeysWrite? shifted insertIndex pivot).bind
                fun keyResult => TraceResult.pure keyResult).result =
            some keyResult := by
        rw [BinarysortTraceSafe.bind_result_of_eq_some _ _ keyShifted hkeyShift]
        exact hfalseAfterWriteResult
      refine ⟨keyResult, ?_⟩
      exact
        { resultEq := by
            simpa [binarysortShiftInsertTraced?, count, dst, src, insertIndex]
              using hfalseResult
          traceSafe := by
            simpa [binarysortShiftInsertTraced?, count, dst, src, insertIndex]
              using hfalseSafe
          exactErasure :=
            erase_binarysortShiftInsertTraced_of_pivot false slice base ok position
              pivot hpivot
          valuesMode := hkeyResultMode
          entriesSize := hkeyResultSize
          range := hkeyResultRange }
  | true =>
      have hpivotIndex : SortSlice.IndexInBounds slice
          (base + Int.ofNat ok) :=
        indexInBounds_of_range_offset slice base n ok hrange hok
      have hvalueRead :
          (TraceResult.sortSliceValuesRead? slice
            (base + Int.ofNat ok)).result = some pivot := by
        change (TraceResult.sortSliceValuesRead? slice
          (base + Int.ofNat ok)).erase = some pivot
        simpa using hpivot
      have hvalueReadSafe := valuesRead_safe slice
        (base + Int.ofNat ok) hpivotIndex
      have hvalueShift :
          (SortSlice.memmoveBackwardValuesTraced? count slice dst src).result =
            some keyShifted := by
        change
          (SortSlice.memmoveBackwardValuesTraced? count slice dst src).erase =
            some keyShifted
        rw [SortSlice.erase_memmoveBackwardValuesTraced]
        exact hkeyMove
      rcases memmoveBackwardValuesTraced_traceSafe count slice dst src hdst hsrc with
        ⟨valueShifted, hvalueShift', hvalueShiftSafe', hvalueShiftSize⟩
      have hvalueShiftedEq : valueShifted = keyShifted := by
        rw [hvalueShift] at hvalueShift'
        exact Option.some.inj hvalueShift'.symm
      subst valueShifted
      have hvalueWrite :
          (TraceResult.sortSliceValuesWrite? keyShifted insertIndex pivot).result =
            some keyResult := by
        change
          (TraceResult.sortSliceValuesWrite? keyShifted insertIndex pivot).erase =
            some keyResult
        simpa using hkeyWriteRaw
      have hvalueWriteSafe :=
        valuesWrite_safe keyShifted insertIndex pivot hinsertShifted
      have hvalueTailSafe : BinarysortTraceSafe
          ((TraceResult.sortSliceValuesRead? slice
            (base + Int.ofNat ok)).bind fun valuePivot =>
              (SortSlice.memmoveBackwardValuesTraced? count slice dst src).bind
                fun shifted =>
                  TraceResult.sortSliceValuesWrite? shifted insertIndex
                    valuePivot) := by
        apply BinarysortTraceSafe.bind _ _ pivot hvalueRead hvalueReadSafe
        exact BinarysortTraceSafe.bind _ _ keyShifted hvalueShift
          hvalueShiftSafe' hvalueWriteSafe
      have hvalueTailResult :
          ((TraceResult.sortSliceValuesRead? slice
            (base + Int.ofNat ok)).bind fun valuePivot =>
              (SortSlice.memmoveBackwardValuesTraced? count slice dst src).bind
                fun shifted =>
                  TraceResult.sortSliceValuesWrite? shifted insertIndex
                    valuePivot).result = some keyResult := by
        rw [BinarysortTraceSafe.bind_result_of_eq_some _ _ pivot hvalueRead]
        rw [BinarysortTraceSafe.bind_result_of_eq_some _ _ keyShifted hvalueShift]
        exact hvalueWrite
      have hafterKeyWriteSafe : BinarysortTraceSafe
          ((TraceResult.sortSliceKeysWrite? keyShifted insertIndex pivot).bind
            fun _ =>
              (TraceResult.sortSliceValuesRead? slice
                (base + Int.ofNat ok)).bind fun valuePivot =>
                  (SortSlice.memmoveBackwardValuesTraced? count slice dst src).bind
                    fun shifted =>
                      TraceResult.sortSliceValuesWrite? shifted insertIndex
                        valuePivot) :=
        BinarysortTraceSafe.bind _ _ keyResult hkeyWrite hkeyWriteSafe
          hvalueTailSafe
      have hafterKeyWriteResult :
          ((TraceResult.sortSliceKeysWrite? keyShifted insertIndex pivot).bind
            fun _ =>
              (TraceResult.sortSliceValuesRead? slice
                (base + Int.ofNat ok)).bind fun valuePivot =>
                  (SortSlice.memmoveBackwardValuesTraced? count slice dst src).bind
                    fun shifted =>
                      TraceResult.sortSliceValuesWrite? shifted insertIndex
                        valuePivot).result = some keyResult := by
        rw [BinarysortTraceSafe.bind_result_of_eq_some _ _ keyResult hkeyWrite]
        exact hvalueTailResult
      have hfullSafe : BinarysortTraceSafe
          ((SortSlice.memmoveBackwardKeysTraced? count slice dst src).bind
            fun keyShifted =>
              (TraceResult.sortSliceKeysWrite? keyShifted insertIndex pivot).bind
                fun _ =>
                  (TraceResult.sortSliceValuesRead? slice
                    (base + Int.ofNat ok)).bind fun valuePivot =>
                      (SortSlice.memmoveBackwardValuesTraced? count slice dst src).bind
                        fun valueShifted =>
                          TraceResult.sortSliceValuesWrite? valueShifted
                            insertIndex valuePivot) :=
        BinarysortTraceSafe.bind _ _ keyShifted hkeyShift hkeyShiftSafe
          hafterKeyWriteSafe
      have hfullResult :
          ((SortSlice.memmoveBackwardKeysTraced? count slice dst src).bind
            fun keyShifted =>
              (TraceResult.sortSliceKeysWrite? keyShifted insertIndex pivot).bind
                fun _ =>
                  (TraceResult.sortSliceValuesRead? slice
                    (base + Int.ofNat ok)).bind fun valuePivot =>
                      (SortSlice.memmoveBackwardValuesTraced? count slice dst src).bind
                        fun valueShifted =>
                          TraceResult.sortSliceValuesWrite? valueShifted
                            insertIndex valuePivot).result = some keyResult := by
        rw [BinarysortTraceSafe.bind_result_of_eq_some _ _ keyShifted hkeyShift]
        exact hafterKeyWriteResult
      refine ⟨keyResult, ?_⟩
      exact
        { resultEq := by
            simpa [binarysortShiftInsertTraced?, count, dst, src, insertIndex]
              using hfullResult
          traceSafe := by
            simpa [binarysortShiftInsertTraced?, count, dst, src, insertIndex]
              using hfullSafe
          exactErasure :=
            erase_binarysortShiftInsertTraced_of_pivot true slice base ok position
              pivot hpivot
          valuesMode := hkeyResultMode
          entriesSize := hkeyResultSize
          range := hkeyResultRange }

end BinarysortTraceSafe
end CPythonListsort
