/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean -/

import Def.CPythonListsort.Code.Assembly.ReverseSliceSafety.Part2
import Def.CPythonListsort.Code.Transcription.CountRun.Part4
import Structure.CPythonListsort.Code.Assembly.CountRunSafety.Part2
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

theorem ascendingScanTraced_safe
    (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν)
    (base : Int) (nremaining n : Nat)
    (hrange : SortSlice.RangeInBounds slice base nremaining)
    (hnPositive : 1 ≤ n) (hnUpper : n ≤ nremaining)
    (hfuel : nremaining ≤ n + fuel) :
    ∃ result,
      AscendingScanSafetyPost fuel lt slice base nremaining n result := by
  induction fuel generalizing n with
  | zero =>
      have hstop : ¬n < nremaining := by omega
      let result := ascendingScanResult' n
      refine ⟨result, ?_⟩
      exact
        { resultEq := by
            simp only [ascendingScanTraced?, hstop, if_false]
            rfl
          resultFuel := rfl
          traceSafe := by
            simpa [ascendingScanTraced?, hstop, result,
              ascendingScanResult', ascendingScanResult] using
              (CountTraceSafe.pure result)
          exactErasure := erase_ascendingScanTraced _ _ _ _ _ _
          lengthBounds := ⟨le_rfl, hnUpper⟩ }
  | succ fuel ih =>
      by_cases hactive : n < nremaining
      · have hpreviousIndex : SortSlice.IndexInBounds slice
            (base + Int.ofNat (n - 1)) := by
          rcases hrange with ⟨hbase, hend⟩
          constructor
          · exact add_nonneg hbase (Int.natCast_nonneg _)
          · simp only [Int.ofNat_eq_natCast] at hend ⊢
            omega
        have hnextIndex : SortSlice.IndexInBounds slice
            (base + Int.ofNat n) := by
          rcases hrange with ⟨hbase, hend⟩
          constructor
          · exact add_nonneg hbase (Int.natCast_nonneg _)
          · simp only [Int.ofNat_eq_natCast] at hend ⊢
            omega
        rcases SortSlice.read_eq_some_of_indexInBounds slice _ hpreviousIndex with
          ⟨previous, hpreviousRaw⟩
        rcases SortSlice.read_eq_some_of_indexInBounds slice _ hnextIndex with
          ⟨next, hnextRaw⟩
        have hprevious :
            (TraceResult.sortSliceKeysRead? slice
              (base + Int.ofNat (n - 1))).result = some previous := by
          exact hpreviousRaw
        have hnext :
            (TraceResult.sortSliceKeysRead? slice
              (base + Int.ofNat n)).result = some next := by
          exact hnextRaw
        have hpreviousSafe := countKeyRead_safe slice _ hpreviousIndex
        have hnextSafe := countKeyRead_safe slice _ hnextIndex
        by_cases hsmaller : iflt lt next.key previous.key = true
        · let result := ascendingScanResult' n
          have htailSafe : CountTraceSafe
              ((TraceResult.sortSliceKeysRead? slice
                (base + Int.ofNat n)).bind fun next =>
                  if iflt lt next.key previous.key then
                    TraceResult.pure (ascendingScanResult n false)
                  else
                    ascendingScanTraced? fuel lt slice base nremaining
                      (n + 1)) := by
            apply CountTraceSafe.bind _ _ next hnext hnextSafe
            simpa only [hsmaller, if_true] using
              (CountTraceSafe.pure (ascendingScanResult n false))
          refine ⟨result, ?_⟩
          exact
            { resultEq := by
                simp only [ascendingScanTraced?, hactive, if_true,
                  TraceResult.bind, hprevious, hnext, hsmaller]
                rfl
              resultFuel := rfl
              traceSafe := by
                simp only [ascendingScanTraced?, hactive, if_true]
                exact CountTraceSafe.bind _ _ previous hprevious
                  hpreviousSafe htailSafe
              exactErasure := erase_ascendingScanTraced _ _ _ _ _ _
              lengthBounds := ⟨le_rfl, hnUpper⟩ }
        · have hnextFuel : nremaining ≤ n + 1 + fuel := by omega
          change ¬lt next.key previous.key = true at hsmaller
          rcases ih (n + 1) (by omega) (by omega) hnextFuel with
            ⟨result, hresult⟩
          have htailSafe : CountTraceSafe
              ((TraceResult.sortSliceKeysRead? slice
                (base + Int.ofNat n)).bind fun next =>
                  if iflt lt next.key previous.key then
                    TraceResult.pure (ascendingScanResult n false)
                  else
                    ascendingScanTraced? fuel lt slice base nremaining
                      (n + 1)) := by
            apply CountTraceSafe.bind _ _ next hnext hnextSafe
            simpa only [iflt, hsmaller, Bool.false_eq_true, if_false] using
              hresult.traceSafe
          refine ⟨result, ?_⟩
          exact
            { resultEq := by
                simpa only [ascendingScanTraced?, hactive, if_true,
                  TraceResult.bind, hprevious, hnext, iflt, hsmaller,
                  Bool.false_eq_true, if_false]
                  using hresult.resultEq
              resultFuel := hresult.resultFuel
              traceSafe := by
                simp only [ascendingScanTraced?, hactive, if_true]
                exact CountTraceSafe.bind _ _ previous hprevious
                  hpreviousSafe htailSafe
              exactErasure := erase_ascendingScanTraced _ _ _ _ _ _
              lengthBounds :=
                ⟨le_trans (by omega) hresult.lengthBounds.1,
                  hresult.lengthBounds.2⟩ }
      · let result := ascendingScanResult' n
        refine ⟨result, ?_⟩
        exact
          { resultEq := by
              simp only [ascendingScanTraced?, hactive, if_false]
              rfl
            resultFuel := rfl
            traceSafe := by
              simpa [ascendingScanTraced?, hactive, result,
                ascendingScanResult', ascendingScanResult] using
                (CountTraceSafe.pure result)
            exactErasure := erase_ascendingScanTraced _ _ _ _ _ _
            lengthBounds := ⟨le_rfl, hnUpper⟩ }

end CPythonListsort
