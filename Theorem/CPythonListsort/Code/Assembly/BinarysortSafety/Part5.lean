/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.SortSliceSafety
import Def.CPythonListsort.Code.Transcription.Binarysort.Part3
import Mathlib
import Structure.CPythonListsort.Code.Assembly.BinarysortSafety.Part5
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

/-- Every source-admitted call succeeds, terminates within the source-supplied
`n` fuel, preserves representation mode and extent, and records only in-bounds
key/value accesses.  No ordering law is assumed of the Boolean comparator. -/
theorem binarysort_safe
    (state : MergeState κ ν) (slice : SortSlice κ ν) (base : Int)
    (n ok : Nat) (hnPositive : 1 ≤ n) (hok : ok ≤ n)
    (hnMax : n ≤ MAX_MINRUN.toNat)
    (hrange : SortSlice.RangeInBounds slice base n)
    (hmode : SortSlice.ValuesModeInvariant state.a.hasValues slice) :
    ∃ result, BinarysortSafetyPost state slice base n ok result := by
  let normalizedOk := if ok = 0 then 1 else ok
  have hnormalized : normalizedOk ≤ n := by
    dsimp [normalizedOk]
    split
    · exact hnPositive
    · exact hok
  have hremaining : n - normalizedOk ≤ n := Nat.sub_le _ _
  rcases binarysortLoopTraced_safe n state slice base n normalizedOk hnormalized
      hremaining hrange hmode with ⟨result, hloop⟩
  have hadmitted : 1 ≤ n ∧ ok ≤ n ∧ n ≤ MAX_MINRUN.toNat :=
    ⟨hnPositive, hok, hnMax⟩
  refine ⟨result, ?_⟩
  exact
    { resultEq := by
        simpa [binarysortTraced?, hadmitted, normalizedOk] using hloop.resultEq
      resultFuel := hloop.resultFuel
      traceFuel := by
        simpa [binarysortTraced?, hadmitted, normalizedOk] using
          hloop.traceSafe.fuel
      noPushes := by
        simpa [binarysortTraced?, hadmitted, normalizedOk] using
          hloop.traceSafe.noPushes
      accessesInBounds := by
        simpa [binarysortTraced?, hadmitted, normalizedOk] using
          hloop.traceSafe.bounds
      tempAccessesLive := by
        simpa [binarysortTraced?, hadmitted, normalizedOk] using
          hloop.traceSafe.tempLive
      exactErasure := erase_binarysortTraced state slice base n ok
      valuesMode := hloop.valuesMode
      sizeEq := hloop.sizeEq
      range := hloop.range }

/-- An active binary-search step records its midpoint key read first, then the
complete trace of exactly the comparator-selected smaller interval.  Comparator
evaluation itself is deliberately not an access event. -/
theorem binarysortSearchTraced_step_trace_order
    (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν)
    (base : Int) (pivot entry : SortSliceEntry κ ν) (left right : Nat)
    (hactive : left < right)
    (hread :
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat ((left + right) / 2))).result = some entry) :
    (binarysortSearchTraced? (fuel + 1) lt slice base pivot left right).trace =
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat ((left + right) / 2))).trace.compose
          (if iflt lt pivot.key entry.key then
            (binarysortSearchTraced? fuel lt slice base pivot left
              ((left + right) / 2)).trace
          else
            (binarysortSearchTraced? fuel lt slice base pivot
              ((left + right) / 2 + 1) right).trace) := by
  change
    (if left < right then
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat ((left + right) / 2))).bind fun current =>
          if iflt lt pivot.key current.key then
            binarysortSearchTraced? fuel lt slice base pivot left
              ((left + right) / 2)
          else
            binarysortSearchTraced? fuel lt slice base pivot
              ((left + right) / 2 + 1) right
    else
      TraceResult.pure { position := left, fuelExhausted := false }).trace = _
  rw [if_pos hactive]
  simp only [TraceResult.trace_bind, hread]
  by_cases hcomparison : iflt lt pivot.key entry.key = true
  · simp only [hcomparison, if_true]
  · simp only [hcomparison, Bool.false_eq_true, if_false]

/-- In values mode the full insertion trace is ordered as key shift, key pivot
write, value pivot read, value shift, and value pivot write. -/
theorem binarysortShiftInsertTraced_values_phase_order
    (slice keyShifted keyResult valueShifted : SortSlice κ ν)
    (base : Int) (ok position : Nat) (pivot valuePivot : SortSliceEntry κ ν)
    (hkeyShift :
      (SortSlice.memmoveBackwardKeysTraced? (ok - position) slice
        (base + Int.ofNat (position + 1))
        (base + Int.ofNat position)).result = some keyShifted)
    (hkeyWrite :
      (TraceResult.sortSliceKeysWrite? keyShifted
        (base + Int.ofNat position) pivot).result = some keyResult)
    (hvalueRead :
      (TraceResult.sortSliceValuesRead? slice
        (base + Int.ofNat ok)).result = some valuePivot)
    (hvalueShift :
      (SortSlice.memmoveBackwardValuesTraced? (ok - position) slice
        (base + Int.ofNat (position + 1))
        (base + Int.ofNat position)).result = some valueShifted) :
    (binarysortShiftInsertTraced? true slice base ok position pivot).trace =
      (SortSlice.memmoveBackwardKeysTraced? (ok - position) slice
        (base + Int.ofNat (position + 1))
        (base + Int.ofNat position)).trace.compose
        ((TraceResult.sortSliceKeysWrite? keyShifted
          (base + Int.ofNat position) pivot).trace.compose
          ((TraceResult.sortSliceValuesRead? slice
            (base + Int.ofNat ok)).trace.compose
            ((SortSlice.memmoveBackwardValuesTraced? (ok - position) slice
              (base + Int.ofNat (position + 1))
              (base + Int.ofNat position)).trace.compose
              (TraceResult.sortSliceValuesWrite? valueShifted
                (base + Int.ofNat position) valuePivot).trace))) := by
  change
    ((SortSlice.memmoveBackwardKeysTraced? (ok - position) slice
      (base + Int.ofNat (position + 1))
      (base + Int.ofNat position)).bind fun currentKeyShifted =>
        (TraceResult.sortSliceKeysWrite? currentKeyShifted
          (base + Int.ofNat position) pivot).bind fun keyResult =>
            if true then
              (TraceResult.sortSliceValuesRead? slice
                (base + Int.ofNat ok)).bind fun currentValuePivot =>
                  (SortSlice.memmoveBackwardValuesTraced? (ok - position) slice
                    (base + Int.ofNat (position + 1))
                    (base + Int.ofNat position)).bind fun currentValueShifted =>
                      TraceResult.sortSliceValuesWrite? currentValueShifted
                        (base + Int.ofNat position) currentValuePivot
            else TraceResult.pure keyResult).trace = _
  simp only [TraceResult.trace_bind, hkeyShift, hkeyWrite, if_true,
    hvalueRead, hvalueShift]

/-- One successful outer iteration observes the pivot, the complete search,
the complete shift/insert, and the recursive iteration trace in that order. -/
theorem binarysortLoopTraced_iteration_trace_order
    (fuel : Nat) (state : MergeState κ ν) (slice updated : SortSlice κ ν)
    (base : Int) (n ok : Nat) (pivot : SortSliceEntry κ ν)
    (search : BinarySearchResult)
    (hpivot :
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat ok)).result = some pivot)
    (hsearch :
      (binarysortSearchTraced? (ok + 1) state.key_compare slice base pivot
        0 ok).result = some search)
    (hsearchFuel : search.fuelExhausted = false)
    (hshift :
      (binarysortShiftInsertTraced? state.a.hasValues slice base ok
        search.position pivot).result = some updated)
    (hactive : ok < n) :
    (binarysortLoopTraced? (fuel + 1) state slice base n ok).trace =
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat ok)).trace.compose
        ((binarysortSearchTraced? (ok + 1) state.key_compare slice base pivot
          0 ok).trace.compose
          ((binarysortShiftInsertTraced? state.a.hasValues slice base ok
            search.position pivot).trace.compose
            (binarysortLoopTraced? fuel state updated base n
              (ok + 1)).trace)) := by
  change
    (if ok < n then
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat ok)).bind fun currentPivot =>
          (binarysortSearchTraced? (ok + 1) state.key_compare slice base
            currentPivot 0 ok).bind fun currentSearch =>
              if currentSearch.fuelExhausted then
                TraceResult.pure
                  ({ slice := slice, fuelExhausted := true } :
                    BinarysortResult κ ν)
              else
                (binarysortShiftInsertTraced? state.a.hasValues slice base ok
                  currentSearch.position currentPivot).bind fun currentUpdated =>
                    binarysortLoopTraced? fuel state currentUpdated base n
                      (ok + 1)
    else
      TraceResult.pure
        ({ slice := slice, fuelExhausted := false } :
          BinarysortResult κ ν)).trace = _
  rw [if_pos hactive]
  simp only [TraceResult.trace_bind, hpivot, hsearch, hsearchFuel,
    Bool.false_eq_true, if_false, hshift]

end BinarysortTraceSafe
end CPythonListsort
