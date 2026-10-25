/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean -/

import Def.CPythonListsort.Code.Assembly.ReverseSliceSafety.Part2
import Def.CPythonListsort.Code.Transcription.CountRun.Part4
import Structure.CPythonListsort.Code.Assembly.CountRunSafety.Part4
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

theorem descendingScanTraced_safe
    (fuel : Nat) (valuesPresent : Bool) (lt : BoolComparator κ)
    (slice : SortSlice κ ν) (base : Int) (nremaining n neq : Nat)
    (hrange : SortSlice.RangeInBounds slice base nremaining)
    (hnPositive : 1 ≤ n) (hnUpper : n ≤ nremaining)
    (hneq : neq < n) (hfuel : nremaining ≤ n + fuel)
    (hMode : SortSlice.ValuesModeInvariant valuesPresent slice) :
    ∃ result,
      DescendingScanSafetyPost fuel valuesPresent lt slice base nremaining n neq
        result := by
  induction fuel generalizing slice n neq with
  | zero =>
      have hstop : ¬n < nremaining := by omega
      let result := descendingScanResult slice n neq false
      refine ⟨result, ?_⟩
      exact
        { resultEq := by
            simp only [descendingScanTraced?, hstop, if_false]
            rfl
          resultFuel := rfl
          traceSafe := by
            simpa [descendingScanTraced?, hstop, result] using
              (CountTraceSafe.pure result)
          exactErasure := erase_descendingScanTraced _ _ _ _ _ _ _ _
          lengthBounds := ⟨le_rfl, hnUpper⟩
          equalTailLt := hneq
          valuesMode := hMode
          sizeEq := rfl }
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
              (base + Int.ofNat (n - 1))).result = some previous :=
          hpreviousRaw
        have hnext :
            (TraceResult.sortSliceKeysRead? slice
              (base + Int.ofNat n)).result = some next :=
          hnextRaw
        have hpreviousSafe := countKeyRead_safe slice _ hpreviousIndex
        have hnextSafe := countKeyRead_safe slice _ hnextIndex
        by_cases hsmaller : iflt lt next.key previous.key = true
        · rcases reverseLastEqualTraced_safe valuesPresent slice base
              nremaining n neq hrange hnUpper hneq hMode with
            ⟨reversed, hreverse⟩
          have hrangeReversed :
              SortSlice.RangeInBounds reversed.slice base nremaining :=
            hrange.of_size_eq hreverse.sizeEq
          have hnextFuel : nremaining ≤ n + 1 + fuel := by omega
          rcases ih reversed.slice (n + 1) 0 hrangeReversed (by omega)
              (by omega) (by omega) hnextFuel hreverse.valuesMode with
            ⟨result, hresult⟩
          have hbranchSafe : CountTraceSafe
              ((reverseLastEqualTraced? valuesPresent slice base n neq).bind
                fun reversed =>
                  if reversed.fuelExhausted then
                    TraceResult.pure
                      (descendingScanResult reversed.slice n 0 true)
                  else
                    descendingScanTraced? fuel valuesPresent lt reversed.slice
                      base nremaining (n + 1) 0) := by
            apply CountTraceSafe.bind _ _ reversed hreverse.resultEq
              hreverse.traceSafe
            simpa [hreverse.resultFuel] using hresult.traceSafe
          have hafterNextSafe : CountTraceSafe
              ((TraceResult.sortSliceKeysRead? slice
                (base + Int.ofNat n)).bind fun next =>
                  if iflt lt next.key previous.key then
                    (reverseLastEqualTraced? valuesPresent slice base n neq).bind
                      fun reversed =>
                        if reversed.fuelExhausted then
                          TraceResult.pure
                            (descendingScanResult reversed.slice n 0 true)
                        else
                          descendingScanTraced? fuel valuesPresent lt
                            reversed.slice base nremaining (n + 1) 0
                  else if iflt lt previous.key next.key then
                    TraceResult.pure (descendingScanResult slice n neq false)
                  else
                    descendingScanTraced? fuel valuesPresent lt slice base
                      nremaining (n + 1) (neq + 1)) := by
            apply CountTraceSafe.bind _ _ next hnext hnextSafe
            simpa only [hsmaller, if_true] using hbranchSafe
          refine ⟨result, ?_⟩
          exact
            { resultEq := by
                simpa only [descendingScanTraced?, hactive, if_true,
                  TraceResult.bind, hprevious, hnext, hsmaller,
                  hreverse.resultEq, hreverse.resultFuel,
                  Bool.false_eq_true, if_false] using hresult.resultEq
              resultFuel := hresult.resultFuel
              traceSafe := by
                simp only [descendingScanTraced?, hactive, if_true]
                exact CountTraceSafe.bind _ _ previous hprevious
                  hpreviousSafe hafterNextSafe
              exactErasure := erase_descendingScanTraced _ _ _ _ _ _ _ _
              lengthBounds :=
                ⟨le_trans (by omega) hresult.lengthBounds.1,
                  hresult.lengthBounds.2⟩
              equalTailLt := hresult.equalTailLt
              valuesMode := hresult.valuesMode
              sizeEq := hresult.sizeEq.trans hreverse.sizeEq }
        · change ¬lt next.key previous.key = true at hsmaller
          by_cases hlarger : iflt lt previous.key next.key = true
          · change lt previous.key next.key = true at hlarger
            let result := descendingScanResult slice n neq false
            have hbranchSafe : CountTraceSafe
                (if iflt lt next.key previous.key then
                  (reverseLastEqualTraced? valuesPresent slice base n neq).bind
                    fun reversed =>
                      if reversed.fuelExhausted then
                        TraceResult.pure
                          (descendingScanResult reversed.slice n 0 true)
                      else
                        descendingScanTraced? fuel valuesPresent lt
                          reversed.slice base nremaining (n + 1) 0
                else if iflt lt previous.key next.key then
                  TraceResult.pure (descendingScanResult slice n neq false)
                else
                  descendingScanTraced? fuel valuesPresent lt slice base
                    nremaining (n + 1) (neq + 1)) := by
              simpa only [iflt, hsmaller, Bool.false_eq_true, if_false,
                hlarger, if_true] using
                (CountTraceSafe.pure (descendingScanResult slice n neq false))
            have hafterNextSafe : CountTraceSafe
                ((TraceResult.sortSliceKeysRead? slice
                  (base + Int.ofNat n)).bind fun next =>
                    if iflt lt next.key previous.key then
                      (reverseLastEqualTraced? valuesPresent slice base n neq).bind
                        fun reversed =>
                          if reversed.fuelExhausted then
                            TraceResult.pure
                              (descendingScanResult reversed.slice n 0 true)
                          else
                            descendingScanTraced? fuel valuesPresent lt
                              reversed.slice base nremaining (n + 1) 0
                    else if iflt lt previous.key next.key then
                      TraceResult.pure (descendingScanResult slice n neq false)
                    else
                      descendingScanTraced? fuel valuesPresent lt slice base
                        nremaining (n + 1) (neq + 1)) :=
              CountTraceSafe.bind _ _ next hnext hnextSafe hbranchSafe
            refine ⟨result, ?_⟩
            exact
              { resultEq := by
                  simp only [descendingScanTraced?, hactive, if_true,
                    TraceResult.bind, hprevious, hnext, iflt, hsmaller,
                    Bool.false_eq_true, if_false, hlarger, result]
                  rfl
                resultFuel := rfl
                traceSafe := by
                  simp only [descendingScanTraced?, hactive, if_true]
                  exact CountTraceSafe.bind _ _ previous hprevious
                    hpreviousSafe hafterNextSafe
                exactErasure := erase_descendingScanTraced _ _ _ _ _ _ _ _
                lengthBounds := ⟨le_rfl, hnUpper⟩
                equalTailLt := hneq
                valuesMode := hMode
                sizeEq := rfl }
          · change ¬lt previous.key next.key = true at hlarger
            have hnextFuel : nremaining ≤ n + 1 + fuel := by omega
            rcases ih slice (n + 1) (neq + 1) hrange (by omega) (by omega)
                (by omega) hnextFuel hMode with ⟨result, hresult⟩
            have hbranchSafe : CountTraceSafe
                (if iflt lt next.key previous.key then
                  (reverseLastEqualTraced? valuesPresent slice base n neq).bind
                    fun reversed =>
                      if reversed.fuelExhausted then
                        TraceResult.pure
                          (descendingScanResult reversed.slice n 0 true)
                      else
                        descendingScanTraced? fuel valuesPresent lt
                          reversed.slice base nremaining (n + 1) 0
                else if iflt lt previous.key next.key then
                  TraceResult.pure (descendingScanResult slice n neq false)
                else
                  descendingScanTraced? fuel valuesPresent lt slice base
                    nremaining (n + 1) (neq + 1)) := by
              simpa only [iflt, hsmaller, hlarger, Bool.false_eq_true,
                if_false] using hresult.traceSafe
            have hafterNextSafe : CountTraceSafe
                ((TraceResult.sortSliceKeysRead? slice
                  (base + Int.ofNat n)).bind fun next =>
                    if iflt lt next.key previous.key then
                      (reverseLastEqualTraced? valuesPresent slice base n neq).bind
                        fun reversed =>
                          if reversed.fuelExhausted then
                            TraceResult.pure
                              (descendingScanResult reversed.slice n 0 true)
                          else
                            descendingScanTraced? fuel valuesPresent lt
                              reversed.slice base nremaining (n + 1) 0
                    else if iflt lt previous.key next.key then
                      TraceResult.pure (descendingScanResult slice n neq false)
                    else
                      descendingScanTraced? fuel valuesPresent lt slice base
                        nremaining (n + 1) (neq + 1)) :=
              CountTraceSafe.bind _ _ next hnext hnextSafe hbranchSafe
            refine ⟨result, ?_⟩
            exact
              { resultEq := by
                  simpa only [descendingScanTraced?, hactive, if_true,
                    TraceResult.bind, hprevious, hnext, iflt, hsmaller,
                    hlarger, Bool.false_eq_true, if_false] using
                    hresult.resultEq
                resultFuel := hresult.resultFuel
                traceSafe := by
                  simp only [descendingScanTraced?, hactive, if_true]
                  exact CountTraceSafe.bind _ _ previous hprevious
                    hpreviousSafe hafterNextSafe
                exactErasure := erase_descendingScanTraced _ _ _ _ _ _ _ _
                lengthBounds :=
                  ⟨le_trans (by omega) hresult.lengthBounds.1,
                    hresult.lengthBounds.2⟩
                equalTailLt := hresult.equalTailLt
                valuesMode := hresult.valuesMode
                sizeEq := hresult.sizeEq }
      · let result := descendingScanResult slice n neq false
        refine ⟨result, ?_⟩
        exact
          { resultEq := by
              simp only [descendingScanTraced?, hactive, if_false]
              rfl
            resultFuel := rfl
            traceSafe := by
              simpa [descendingScanTraced?, hactive, result] using
                (CountTraceSafe.pure result)
            exactErasure := erase_descendingScanTraced _ _ _ _ _ _ _ _
            lengthBounds := ⟨le_rfl, hnUpper⟩
            equalTailLt := hneq
            valuesMode := hMode
            sizeEq := rfl }

end CPythonListsort
