/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean -/

import Def.CPythonListsort.Code.Assembly.ReverseSliceSafety.Part2
import Def.CPythonListsort.Code.Transcription.CountRun.Part4
import Structure.CPythonListsort.Code.Assembly.CountRunSafety.Part3
/-!
# `count_run` safety

The evaluator below mirrors the reviewed `count_run` transcription while
producing its trace compositionally.  The Lean instrumentation reads the
previous entry and then the next entry; its comparator orientation and control
branch match CPython's `IF_NEXT_SMALLER`, without making a claim about C operand
evaluation order.  Every operational-equivalence-block, prefix, and whole-run
reversal delegates to the traced `sortslice_reverse` evaluator proved safe in
`ReverseSliceSafety`.

As in the v1 transcription, `BoolComparator` is total.  CPython's comparator
error/failure return path is therefore outside this model; the safety theorem is
for every total Boolean comparator, including inconsistent ones.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

theorem reverseLastEqualTraced_safe
    (valuesPresent : Bool) (slice : SortSlice κ ν) (base : Int)
    (nremaining n neq : Nat)
    (hrange : SortSlice.RangeInBounds slice base nremaining)
    (hnUpper : n ≤ nremaining) (hneq : neq < n)
    (hMode : SortSlice.ValuesModeInvariant valuesPresent slice) :
    ∃ result,
      ReverseEqualSafetyPost valuesPresent slice base n neq result := by
  by_cases hzero : neq = 0
  · let result : ReverseEqualResult κ ν :=
      { slice := slice, fuelExhausted := false }
    refine ⟨result, ?_⟩
    exact
      { resultEq := by
          simp only [reverseLastEqualTraced?, hzero, if_true]
          rfl
        resultFuel := rfl
        traceSafe := by
          simpa [reverseLastEqualTraced?, hzero, result] using
            (CountTraceSafe.pure result)
        exactErasure := erase_reverseLastEqualTraced _ _ _ _ _
        valuesMode := hMode
        sizeEq := rfl }
  · let count := neq + 1
    let start := base + Int.ofNat n - Int.ofNat count
    have hcountLe : count ≤ n := by
      dsimp [count]
      omega
    have hsubrange : SortSlice.RangeInBounds slice start count := by
      rcases hrange with ⟨hbase, hend⟩
      constructor
      · dsimp [start, count]
        omega
      · dsimp [start, count]
        simp only [Int.ofNat_eq_natCast] at hend ⊢
        omega
    rcases sortsliceReverse_safe valuesPresent slice start count hsubrange hMode with
      ⟨reversed, hreverse⟩
    let result : ReverseEqualResult κ ν :=
      { slice := reversed.slice, fuelExhausted := reversed.fuelExhausted }
    refine ⟨result, ?_⟩
    exact
      { resultEq := by
          simp only [reverseLastEqualTraced?, hzero, if_false]
          change
            ((sortsliceReverseTraced? valuesPresent slice start count).map
              (fun reversed =>
                { slice := reversed.slice
                  fuelExhausted := reversed.fuelExhausted })).result =
              some result
          simp [TraceResult.map, hreverse.resultEq, result]
        resultFuel := by
          exact hreverse.resultFuel
        traceSafe := by
          simp only [reverseLastEqualTraced?, hzero, if_false]
          exact CountTraceSafe.map _ _
            (countTraceSafe_of_reverse _ _ _ _ _ hreverse)
        exactErasure := erase_reverseLastEqualTraced _ _ _ _ _
        valuesMode := hreverse.valuesMode
        sizeEq := hreverse.sizeEq }

end CPythonListsort
