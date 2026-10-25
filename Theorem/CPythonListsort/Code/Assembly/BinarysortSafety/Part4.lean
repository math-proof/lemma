/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.SortSliceSafety
import Def.CPythonListsort.Code.Transcription.Binarysort.Part3
import Mathlib
import Structure.CPythonListsort.Code.Assembly.BinarysortSafety.Part4
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

theorem binarysortLoopTraced_safe
    (fuel : Nat) (state : MergeState κ ν) (slice : SortSlice κ ν)
    (base : Int) (n ok : Nat)
    (hok : ok ≤ n) (hremaining : n - ok ≤ fuel)
    (hrange : SortSlice.RangeInBounds slice base n)
    (hmode : SortSlice.ValuesModeInvariant state.a.hasValues slice) :
    ∃ result,
      BinarysortLoopSafetyPost fuel state slice base n ok result := by
  induction fuel generalizing slice ok with
  | zero =>
      have heq : ok = n := by omega
      subst ok
      let result : BinarysortResult κ ν :=
        { slice := slice, fuelExhausted := false }
      refine ⟨result, ?_⟩
      exact
        { resultEq := by
            simp [binarysortLoopTraced?, TraceResult.pure, result]
          resultFuel := rfl
          traceSafe := by
            simpa [binarysortLoopTraced?, result] using
              (BinarysortTraceSafe.pure result)
          valuesMode := hmode
          sizeEq := rfl
          range := hrange }
  | succ fuel ih =>
      by_cases hactive : ok < n
      · have hpivotIndex : SortSlice.IndexInBounds slice
            (base + Int.ofNat ok) :=
          indexInBounds_of_range_offset slice base n ok hrange hactive
        rcases read_result_of_indexInBounds slice (base + Int.ofNat ok)
            hpivotIndex with ⟨pivot, hpivotResult, hpivot⟩
        have hpivotSafe := keysRead_safe slice (base + Int.ofNat ok) hpivotIndex
        rcases binarysortSearchTraced_safe (ok + 1) state.key_compare slice base
            pivot 0 ok n hrange (Nat.zero_le _) hactive.le (by omega) with
          ⟨search, hsearch⟩
        rcases binarysortShiftInsertTraced_safe state.a.hasValues slice base n ok
            search.position pivot hrange hsearch.positionUpper hactive hmode
            hpivot with ⟨updated, hshift⟩
        have hnextOk : ok + 1 ≤ n := Nat.succ_le_iff.mpr hactive
        have hnextRemaining : n - (ok + 1) ≤ fuel := by omega
        rcases ih updated (ok + 1) hnextOk hnextRemaining hshift.range
            hshift.valuesMode with ⟨result, hrest⟩
        have hshiftRestSafe : BinarysortTraceSafe
            ((binarysortShiftInsertTraced? state.a.hasValues slice base ok
              search.position pivot).bind fun updated =>
                binarysortLoopTraced? fuel state updated base n (ok + 1)) :=
          BinarysortTraceSafe.bind _ _ updated hshift.resultEq hshift.traceSafe
            hrest.traceSafe
        have hafterSearchSafe : BinarysortTraceSafe
            ((binarysortSearchTraced? (ok + 1) state.key_compare slice base pivot
              0 ok).bind fun current =>
                if current.fuelExhausted then
                  TraceResult.pure
                    ({ slice := slice, fuelExhausted := true } :
                      BinarysortResult κ ν)
                else
                  (binarysortShiftInsertTraced? state.a.hasValues slice base ok
                    current.position pivot).bind fun updated =>
                      binarysortLoopTraced? fuel state updated base n (ok + 1)) :=
          BinarysortTraceSafe.bind _ _ search hsearch.resultEq hsearch.traceSafe
            (by simpa [hsearch.resultFuel] using hshiftRestSafe)
        have hfullSafe : BinarysortTraceSafe
            ((TraceResult.sortSliceKeysRead? slice
              (base + Int.ofNat ok)).bind fun pivot =>
                (binarysortSearchTraced? (ok + 1) state.key_compare slice base
                  pivot 0 ok).bind fun search =>
                    if search.fuelExhausted then
                      TraceResult.pure
                        ({ slice := slice, fuelExhausted := true } :
                          BinarysortResult κ ν)
                    else
                      (binarysortShiftInsertTraced? state.a.hasValues slice base
                        ok search.position pivot).bind fun updated =>
                          binarysortLoopTraced? fuel state updated base n
                            (ok + 1)) :=
          BinarysortTraceSafe.bind _ _ pivot hpivotResult hpivotSafe
            hafterSearchSafe
        have hshiftRestResult :
            ((binarysortShiftInsertTraced? state.a.hasValues slice base ok
              search.position pivot).bind fun updated =>
                binarysortLoopTraced? fuel state updated base n
                  (ok + 1)).result = some result := by
          rw [BinarysortTraceSafe.bind_result_of_eq_some _ _ updated
            hshift.resultEq]
          exact hrest.resultEq
        have hafterSearchResult :
            ((binarysortSearchTraced? (ok + 1) state.key_compare slice base pivot
              0 ok).bind fun current =>
                if current.fuelExhausted then
                  TraceResult.pure
                    ({ slice := slice, fuelExhausted := true } :
                      BinarysortResult κ ν)
                else
                  (binarysortShiftInsertTraced? state.a.hasValues slice base ok
                    current.position pivot).bind fun updated =>
                      binarysortLoopTraced? fuel state updated base n
                        (ok + 1)).result = some result := by
          rw [BinarysortTraceSafe.bind_result_of_eq_some _ _ search
            hsearch.resultEq]
          simpa [hsearch.resultFuel] using hshiftRestResult
        have hfullResult :
            ((TraceResult.sortSliceKeysRead? slice
              (base + Int.ofNat ok)).bind fun pivot =>
                (binarysortSearchTraced? (ok + 1) state.key_compare slice base
                  pivot 0 ok).bind fun search =>
                    if search.fuelExhausted then
                      TraceResult.pure
                        ({ slice := slice, fuelExhausted := true } :
                          BinarysortResult κ ν)
                    else
                      (binarysortShiftInsertTraced? state.a.hasValues slice base
                        ok search.position pivot).bind fun updated =>
                          binarysortLoopTraced? fuel state updated base n
                            (ok + 1)).result = some result := by
          rw [BinarysortTraceSafe.bind_result_of_eq_some _ _ pivot hpivotResult]
          exact hafterSearchResult
        refine ⟨result, ?_⟩
        exact
          { resultEq := by
              simpa [binarysortLoopTraced?, hactive] using hfullResult
            resultFuel := hrest.resultFuel
            traceSafe := by
              simpa [binarysortLoopTraced?, hactive] using hfullSafe
            valuesMode := hrest.valuesMode
            sizeEq := hrest.sizeEq.trans hshift.entriesSize
            range := hrest.range }
      · have heq : ok = n := Nat.le_antisymm hok (Nat.le_of_not_gt hactive)
        subst ok
        let result : BinarysortResult κ ν :=
          { slice := slice, fuelExhausted := false }
        refine ⟨result, ?_⟩
        exact
          { resultEq := by
              simp [binarysortLoopTraced?, TraceResult.pure, result]
            resultFuel := rfl
            traceSafe := by
              simpa [binarysortLoopTraced?, result] using
                (BinarysortTraceSafe.pure result)
            valuesMode := hmode
            sizeEq := rfl
            range := hrange }

end BinarysortTraceSafe
end CPythonListsort
