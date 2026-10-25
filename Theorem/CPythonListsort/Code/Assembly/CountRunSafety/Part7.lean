/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean -/

import Def.CPythonListsort.Code.Assembly.ReverseSliceSafety.Part2
import Def.CPythonListsort.Code.Transcription.CountRun.Part4
import Structure.CPythonListsort.Code.Assembly.CountRunSafety.Part6
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

/-- Internal branch proof behind the compact public `countRun_safe` contract. -/
theorem countRun_safe_core (state : MergeState κ ν)
    (slice : SortSlice κ ν)
    (base : Int) (nremaining : Nat)
    (hrange : SortSlice.RangeInBounds slice base nremaining)
    (hpositive : 0 < nremaining)
    (hsizeRepresentable : nremaining ≤ PY_SSIZE_T_MAX)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues slice) :
    ∃ result, CountRunSafetyPost state slice base nremaining result := by
  have hguard : 0 < nremaining ∧ nremaining ≤ PY_SSIZE_T_MAX :=
    ⟨hpositive, hsizeRepresentable⟩
  rcases ascendingScanTraced_safe nremaining state.key_compare slice base
      nremaining 1 hrange (by omega) (by omega) (by omega) with
    ⟨ascending, hascending⟩
  by_cases hcomplete : ascending.length = nremaining
  · let result : CountRunResult κ ν :=
      { slice := slice
        length := ascending.length
        fuelExhausted := false }
    have hcontinuationSafe : CountTraceSafe
        (if ascending.fuelExhausted then
          TraceResult.pure
            ({ slice := slice
               length := ascending.length
               fuelExhausted := true } : CountRunResult κ ν)
        else if ascending.length = nremaining then
          TraceResult.pure result
        else if 1 < ascending.length then
          (TraceResult.sortSliceKeysRead? slice base).bind fun first =>
            (TraceResult.sortSliceKeysRead? slice
              (base + Int.ofNat (ascending.length - 1))).bind fun last =>
                if iflt state.key_compare first.key last.key then
                  TraceResult.pure
                    { slice := slice
                      length := ascending.length
                      fuelExhausted := false }
                else
                  (sortsliceReverseTraced? state.a.hasValues slice base
                    ascending.length).bind fun reversed =>
                      if reversed.fuelExhausted then
                        TraceResult.pure
                          { slice := reversed.slice
                            length := ascending.length + 1
                            fuelExhausted := true }
                      else
                        finishDescendingTraced? state reversed.slice base
                          nremaining (ascending.length + 1)
        else
          finishDescendingTraced? state slice base nremaining
            (ascending.length + 1)) := by
      simpa [hascending.resultFuel, hcomplete] using
        (CountTraceSafe.pure result)
    have htrace : CountTraceSafe
        (countRunTraced? state slice base nremaining) := by
      simp only [countRunTraced?, hguard]
      exact CountTraceSafe.bind _ _ ascending hascending.resultEq
        hascending.traceSafe hcontinuationSafe
    refine ⟨result, ?_⟩
    apply countRunSafetyPost_of state slice base nremaining result
    · simp only [countRunTraced?]
      rw [if_pos hguard]
      simp only [TraceResult.bind, hascending.resultEq,
        hascending.resultFuel, Bool.false_eq_true, if_false, hcomplete,
        if_true]
      simp [TraceResult.pure, result, hcomplete]
    · rfl
    · exact htrace
    · exact hMode
    · rfl
    · exact
        ⟨by simpa [result, hcomplete] using hascending.lengthBounds.1,
          by simp [result, hcomplete]⟩
  · by_cases hlong : 1 < ascending.length
    · have hlengthUpper := hascending.lengthBounds.2
      have hlengthLt : ascending.length < nremaining := by omega
      have hfirstIndex : SortSlice.IndexInBounds slice base := by
        rcases hrange with ⟨hbase, hend⟩
        constructor
        · exact hbase
        · simp only [Int.ofNat_eq_natCast] at hend ⊢
          omega
      have hlastIndex : SortSlice.IndexInBounds slice
          (base + Int.ofNat (ascending.length - 1)) := by
        rcases hrange with ⟨hbase, hend⟩
        constructor
        · exact add_nonneg hbase (Int.natCast_nonneg _)
        · simp only [Int.ofNat_eq_natCast] at hend ⊢
          omega
      rcases SortSlice.read_eq_some_of_indexInBounds slice base hfirstIndex with
        ⟨first, hfirstRaw⟩
      rcases SortSlice.read_eq_some_of_indexInBounds slice
          (base + Int.ofNat (ascending.length - 1)) hlastIndex with
        ⟨last, hlastRaw⟩
      have hfirst :
          (TraceResult.sortSliceKeysRead? slice base).result = some first :=
        hfirstRaw
      have hlast :
          (TraceResult.sortSliceKeysRead? slice
            (base + Int.ofNat (ascending.length - 1))).result = some last :=
        hlastRaw
      have hfirstSafe := countKeyRead_safe slice base hfirstIndex
      have hlastSafe := countKeyRead_safe slice _ hlastIndex
      by_cases hincreasing :
          iflt state.key_compare first.key last.key = true
      · let result : CountRunResult κ ν :=
          { slice := slice
            length := ascending.length
            fuelExhausted := false }
        have htrace : CountTraceSafe
            (countRunTraced? state slice base nremaining) := by
          simp only [countRunTraced?, hguard]
          apply CountTraceSafe.bind _ _ ascending hascending.resultEq
            hascending.traceSafe
          simp only [hascending.resultFuel, Bool.false_eq_true, if_false,
            hcomplete, hlong, if_true]
          apply CountTraceSafe.bind _ _ first hfirst hfirstSafe
          apply CountTraceSafe.bind _ _ last hlast hlastSafe
          simpa only [hincreasing, if_true] using
            (CountTraceSafe.pure result)
        refine ⟨result, ?_⟩
        apply countRunSafetyPost_of state slice base nremaining result
        · simp only [countRunTraced?]
          rw [if_pos hguard]
          simp only [TraceResult.bind, hascending.resultEq,
            hascending.resultFuel, Bool.false_eq_true, if_false, hcomplete,
            hlong, if_true, hfirst, hlast, hincreasing]
          rfl
        · rfl
        · exact htrace
        · exact hMode
        · rfl
        · exact ⟨hascending.lengthBounds.1, hascending.lengthBounds.2⟩
      · have hprefixRange : SortSlice.RangeInBounds slice base
            ascending.length := by
          rcases hrange with ⟨hbase, hend⟩
          constructor
          · exact hbase
          · have hlengthCast :
                Int.ofNat ascending.length ≤ Int.ofNat nremaining :=
                Int.ofNat_le.mpr hascending.lengthBounds.2
            exact le_trans (by simpa [add_comm] using
              (add_le_add_left hlengthCast base)) hend
        rcases sortsliceReverse_safe state.a.hasValues slice base
            ascending.length hprefixRange hMode with ⟨reversed, hreverse⟩
        have hrangeReversed :
            SortSlice.RangeInBounds reversed.slice base nremaining :=
          hrange.of_size_eq hreverse.sizeEq
        rcases finishDescendingTraced_safe state reversed.slice base nremaining
            (ascending.length + 1) hrangeReversed (by omega) (by omega)
            hreverse.valuesMode with ⟨result, hfinish⟩
        have hreverseSafe :=
          countTraceSafe_of_reverse _ _ _ _ _ hreverse
        have hincreasing' :
            ¬state.key_compare first.key last.key = true := by
          simpa [iflt] using hincreasing
        have htrace : CountTraceSafe
            (countRunTraced? state slice base nremaining) := by
          simp only [countRunTraced?, hguard]
          apply CountTraceSafe.bind _ _ ascending hascending.resultEq
            hascending.traceSafe
          simp only [hascending.resultFuel, Bool.false_eq_true, if_false,
            hcomplete, hlong, if_true]
          apply CountTraceSafe.bind _ _ first hfirst hfirstSafe
          apply CountTraceSafe.bind _ _ last hlast hlastSafe
          simp only [iflt, hincreasing', Bool.false_eq_true, if_false]
          apply CountTraceSafe.bind _ _ reversed hreverse.resultEq hreverseSafe
          simpa [hreverse.resultFuel] using hfinish.traceSafe
        refine ⟨result, ?_⟩
        apply countRunSafetyPost_of state slice base nremaining result
        · simp only [countRunTraced?]
          rw [if_pos hguard]
          simp only [TraceResult.bind, hascending.resultEq,
            hascending.resultFuel, Bool.false_eq_true, if_false, hcomplete,
            hlong, if_true, hfirst, hlast, iflt, hincreasing',
            hreverse.resultEq, hreverse.resultFuel, hfinish.resultEq]
        · exact hfinish.resultFuel
        · exact htrace
        · exact hfinish.valuesMode
        · exact hfinish.sizeEq.trans hreverse.sizeEq
        · exact
            ⟨le_trans (by omega) hfinish.lengthBounds.1,
              hfinish.lengthBounds.2⟩
    · have hascendingLower := hascending.lengthBounds.1
      have hascendingUpper := hascending.lengthBounds.2
      have hascendingOne : ascending.length = 1 := by omega
      have honeNotComplete : ¬1 = nremaining := by
        simpa [hascendingOne] using hcomplete
      have hnremainingTwo : 2 ≤ nremaining := by omega
      rcases finishDescendingTraced_safe state slice base nremaining 2 hrange
          (by omega) hnremainingTwo hMode with ⟨result, hfinish⟩
      have htrace : CountTraceSafe
          (countRunTraced? state slice base nremaining) := by
        simp only [countRunTraced?, hguard]
        apply CountTraceSafe.bind _ _ ascending hascending.resultEq
          hascending.traceSafe
        simpa [hascending.resultFuel, hascendingOne, honeNotComplete,
          hlong] using hfinish.traceSafe
      refine ⟨result, ?_⟩
      apply countRunSafetyPost_of state slice base nremaining result
      · simp only [countRunTraced?]
        rw [if_pos hguard]
        simpa [TraceResult.bind, hascending.resultEq,
          hascending.resultFuel, hascendingOne, honeNotComplete, hlong]
          using hfinish.resultEq
      · exact hfinish.resultFuel
      · exact htrace
      · exact hfinish.valuesMode
      · exact hfinish.sizeEq
      · exact ⟨le_trans (by omega) hfinish.lengthBounds.1,
          hfinish.lengthBounds.2⟩

/-- On a nonempty, signed-size-representable in-bounds suffix, `count_run`
succeeds for an arbitrary Boolean comparator, uses no exhausted helper path,
preserves the explicit values mode and backing extent, and returns a run length
inside `[1, nremaining]`. -/
theorem countRun_safe (state : MergeState κ ν) (slice : SortSlice κ ν)
    (base : Int) (nremaining : Nat)
    (hrange : SortSlice.RangeInBounds slice base nremaining)
    (hpositive : 0 < nremaining)
    (hsizeRepresentable : nremaining ≤ PY_SSIZE_T_MAX)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues slice) :
    ∃ result, CountRunSafetyPost state slice base nremaining result :=
  countRun_safe_core state slice base nremaining hrange hpositive
    hsizeRepresentable hMode

/-- One active descending step has the same two-read instrumentation order;
after those reads the `next < previous` arm is selected before the reverse
comparison can control the branch. -/
theorem descendingScanTraced_step_trace_order
    (fuel : Nat) (valuesPresent : Bool) (lt : BoolComparator κ)
    (slice : SortSlice κ ν) (base : Int) (nremaining n neq : Nat)
    (previous next : SortSliceEntry κ ν)
    (hactive : n < nremaining)
    (hprevious :
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat (n - 1))).result = some previous)
    (hnext :
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat n)).result = some next) :
    (descendingScanTraced? (fuel + 1) valuesPresent lt slice base nremaining
      n neq).trace =
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat (n - 1))).trace.compose
      ((TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat n)).trace.compose
        (if iflt lt next.key previous.key then
          (reverseLastEqualTraced? valuesPresent slice base n neq).bind
            fun reversed =>
              if reversed.fuelExhausted then
                TraceResult.pure
                  (descendingScanResult reversed.slice n 0 true)
              else
                descendingScanTraced? fuel valuesPresent lt reversed.slice
                  base nremaining (n + 1) 0
        else if iflt lt previous.key next.key then
          TraceResult.pure (descendingScanResult slice n neq false)
        else
          descendingScanTraced? fuel valuesPresent lt slice base nremaining
            (n + 1) (neq + 1)).trace) := by
  simp only [descendingScanTraced?, hactive, if_true]
  rw [TraceResult.trace_bind, hprevious]
  simp only
  rw [TraceResult.trace_bind, hnext]

/-- Conditioned equation pinning comparator priority: a true
`next < previous` answer selects the equality-block reversal/recursive arm,
independently of the reverse comparison's value.  Comparator calls are not
access-trace events, so this is a branch equation rather than a trace claim. -/
theorem descendingScanTraced_next_smaller_priority
    (fuel : Nat) (valuesPresent : Bool) (lt : BoolComparator κ)
    (slice : SortSlice κ ν) (base : Int) (nremaining n neq : Nat)
    (previous next : SortSliceEntry κ ν)
    (hactive : n < nremaining)
    (hprevious :
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat (n - 1))).result = some previous)
    (hnext :
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat n)).result = some next)
    (hsmaller : iflt lt next.key previous.key = true) :
    (descendingScanTraced? (fuel + 1) valuesPresent lt slice base nremaining
      n neq).result =
      ((reverseLastEqualTraced? valuesPresent slice base n neq).bind
        fun reversed =>
          if reversed.fuelExhausted then
            TraceResult.pure (descendingScanResult reversed.slice n 0 true)
          else
            descendingScanTraced? fuel valuesPresent lt reversed.slice base
              nremaining (n + 1) 0).result := by
  simp only [descendingScanTraced?, hactive, if_true, TraceResult.bind,
    hprevious, hnext, hsmaller]

end CPythonListsort
