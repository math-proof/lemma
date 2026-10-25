/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean -/

import Def.CPythonListsort.Code.Assembly.ReverseSliceSafety.Part2
import Def.CPythonListsort.Code.Transcription.CountRun.Part4
import Structure.CPythonListsort.Code.Assembly.CountRunSafety.Part5
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

theorem finishDescendingTraced_safe
    (state : MergeState κ ν) (slice : SortSlice κ ν) (base : Int)
    (nremaining n : Nat)
    (hrange : SortSlice.RangeInBounds slice base nremaining)
    (hnPositive : 1 ≤ n) (hnUpper : n ≤ nremaining)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues slice) :
    ∃ result,
      FinishDescendingSafetyPost state slice base nremaining n result := by
  rcases descendingScanTraced_safe nremaining state.a.hasValues
      state.key_compare slice base nremaining n 0 hrange hnPositive hnUpper
      (by omega) (by omega) hMode with ⟨descending, hdescending⟩
  have hrangeDescending :
      SortSlice.RangeInBounds descending.slice base nremaining :=
    hrange.of_size_eq hdescending.sizeEq
  rcases reverseLastEqualTraced_safe state.a.hasValues descending.slice base
      nremaining descending.length descending.equalTail hrangeDescending
      hdescending.lengthBounds.2 hdescending.equalTailLt
      hdescending.valuesMode with ⟨equalTailReversed, hequalTail⟩
  have hrangeEqualTail :
      SortSlice.RangeInBounds equalTailReversed.slice base nremaining :=
    hrangeDescending.of_size_eq hequalTail.sizeEq
  have hwholeRange : SortSlice.RangeInBounds equalTailReversed.slice base
      descending.length := by
    rcases hrangeEqualTail with ⟨hbase, hend⟩
    constructor
    · exact hbase
    · have hlengthCast :
        Int.ofNat descending.length ≤ Int.ofNat nremaining := by
        exact Int.ofNat_le.mpr hdescending.lengthBounds.2
      exact le_trans (by simpa [add_comm] using
        (add_le_add_left hlengthCast base)) hend
  rcases sortsliceReverse_safe state.a.hasValues equalTailReversed.slice base
      descending.length hwholeRange hequalTail.valuesMode with
    ⟨wholeReversed, hwhole⟩
  have hrangeWhole : SortSlice.RangeInBounds wholeReversed.slice base
      nremaining := hrangeEqualTail.of_size_eq hwhole.sizeEq
  rcases ascendingScanTraced_safe nremaining state.key_compare
      wholeReversed.slice base nremaining descending.length hrangeWhole
      (le_trans hnPositive hdescending.lengthBounds.1)
      hdescending.lengthBounds.2 (by omega) with ⟨extended, hextended⟩
  let result : CountRunResult κ ν :=
    { slice := wholeReversed.slice
      length := extended.length
      fuelExhausted := extended.fuelExhausted }
  have hdescendingSafe : CountTraceSafe
      (descendingScanTraced? nremaining state.a.hasValues state.key_compare
        slice base nremaining n 0) := hdescending.traceSafe
  have hequalSafe : CountTraceSafe
      (reverseLastEqualTraced? state.a.hasValues descending.slice base
        descending.length descending.equalTail) := hequalTail.traceSafe
  have hwholeSafe : CountTraceSafe
      (sortsliceReverseTraced? state.a.hasValues equalTailReversed.slice base
        descending.length) :=
    countTraceSafe_of_reverse _ _ _ _ _ hwhole
  have hextendedMapSafe : CountTraceSafe
      ((ascendingScanTraced? nremaining state.key_compare wholeReversed.slice
        base nremaining descending.length).map fun extended =>
          ({ slice := wholeReversed.slice
             length := extended.length
             fuelExhausted := extended.fuelExhausted } : CountRunResult κ ν)) :=
    CountTraceSafe.map _ _ hextended.traceSafe
  have hwholeContinuationSafe : CountTraceSafe
      ((sortsliceReverseTraced? state.a.hasValues equalTailReversed.slice base
        descending.length).bind fun wholeReversed =>
          if wholeReversed.fuelExhausted then
            TraceResult.pure
              ({ slice := wholeReversed.slice
                 length := descending.length
                 fuelExhausted := true } : CountRunResult κ ν)
          else
            (ascendingScanTraced? nremaining state.key_compare
              wholeReversed.slice base nremaining descending.length).map
                fun extended =>
                  ({ slice := wholeReversed.slice
                     length := extended.length
                     fuelExhausted := extended.fuelExhausted } :
                    CountRunResult κ ν)) := by
    apply CountTraceSafe.bind _ _ wholeReversed hwhole.resultEq hwholeSafe
    simpa [hwhole.resultFuel] using hextendedMapSafe
  have hequalContinuationSafe : CountTraceSafe
      ((reverseLastEqualTraced? state.a.hasValues descending.slice base
        descending.length descending.equalTail).bind fun equalTailReversed =>
          if equalTailReversed.fuelExhausted then
            TraceResult.pure
              ({ slice := equalTailReversed.slice
                 length := descending.length
                 fuelExhausted := true } : CountRunResult κ ν)
          else
            (sortsliceReverseTraced? state.a.hasValues equalTailReversed.slice
              base descending.length).bind fun wholeReversed =>
                if wholeReversed.fuelExhausted then
                  TraceResult.pure
                    ({ slice := wholeReversed.slice
                       length := descending.length
                       fuelExhausted := true } : CountRunResult κ ν)
                else
                  (ascendingScanTraced? nremaining state.key_compare
                    wholeReversed.slice base nremaining descending.length).map
                      fun extended =>
                        ({ slice := wholeReversed.slice
                           length := extended.length
                           fuelExhausted := extended.fuelExhausted } :
                          CountRunResult κ ν)) := by
    apply CountTraceSafe.bind _ _ equalTailReversed hequalTail.resultEq hequalSafe
    simpa [hequalTail.resultFuel] using hwholeContinuationSafe
  refine ⟨result, ?_⟩
  exact
    { resultEq := by
        simp only [finishDescendingTraced?, TraceResult.bind,
          hdescending.resultEq, hdescending.resultFuel, Bool.false_eq_true,
          if_false, hequalTail.resultEq, hequalTail.resultFuel,
          hwhole.resultEq, hwhole.resultFuel, TraceResult.map,
          hextended.resultEq]
        rfl
      resultFuel := hextended.resultFuel
      traceSafe := by
        simp only [finishDescendingTraced?]
        apply CountTraceSafe.bind _ _ descending hdescending.resultEq
          hdescendingSafe
        simpa [hdescending.resultFuel] using hequalContinuationSafe
      exactErasure := erase_finishDescendingTraced _ _ _ _ _
      lengthBounds :=
        ⟨le_trans hdescending.lengthBounds.1 hextended.lengthBounds.1,
          hextended.lengthBounds.2⟩
      valuesMode := hwhole.valuesMode
      sizeEq := hwhole.sizeEq.trans
        (hequalTail.sizeEq.trans hdescending.sizeEq) }

end CPythonListsort
