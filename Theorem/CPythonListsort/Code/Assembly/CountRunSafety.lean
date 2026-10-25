/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean -/

import Def.CPythonListsort.Code.Assembly.ReverseSliceSafety.Part2
import Def.CPythonListsort.Code.Transcription.CountRun.Part4
import Def.CPythonListsort.Code.Assembly.CountRunSafety
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

@[simp]
theorem erase_descendingScanTraced (fuel : Nat) (valuesPresent : Bool)
    (lt : BoolComparator κ) (slice : SortSlice κ ν) (base : Int)
    (nremaining n neq : Nat) :
    (descendingScanTraced? fuel valuesPresent lt slice base nremaining n neq).erase =
      descendingScan? fuel lt slice base nremaining n neq := by
  induction fuel generalizing slice n neq with
  | zero =>
      by_cases h : n < nremaining <;>
        simp [descendingScanTraced?, descendingScan?, descendingScanResult, h]
  | succ fuel ih =>
      by_cases hactive : n < nremaining
      · simp only [descendingScanTraced?, descendingScan?, hactive, if_true,
          TraceResult.erase_bind, TraceResult.erase_sortSliceKeysRead,
          bind, Option.bind]
        cases hprevious : slice.read? (base + Int.ofNat (n - 1)) with
        | none => simp
        | some previous =>
            simp only
            cases hnext : slice.read? (base + Int.ofNat n) with
            | none => simp
            | some next =>
                simp only
                by_cases hsmaller : iflt lt next.key previous.key = true
                · rw [if_pos hsmaller]
                  simp only [hsmaller, if_true]
                  simp only [TraceResult.erase_bind,
                    erase_reverseLastEqualTraced]
                  cases hreverse : reverseLastEqual? slice base n neq with
                  | none => rfl
                  | some reversed =>
                      by_cases hfuel : reversed.fuelExhausted = true
                      · simp [hfuel, descendingScanResult]
                      · simp [hfuel, ih]
                · rw [if_neg hsmaller]
                  simp only [hsmaller]
                  by_cases hlarger : iflt lt previous.key next.key = true
                  · rw [if_pos hlarger]
                    simp only [hlarger, if_true]
                    rfl
                  · rw [if_neg hlarger]
                    simp only [hlarger]
                    exact ih _ _ _
      · simp [descendingScanTraced?, descendingScan?, hactive,
          descendingScanResult]

@[simp]
theorem erase_countRunTraced (state : MergeState κ ν)
    (slice : SortSlice κ ν) (base : Int) (nremaining : Nat) :
    (countRunTraced? state slice base nremaining).erase =
      countRun? state slice base nremaining := by
  unfold countRunTraced? countRun?
  by_cases hguard : 0 < nremaining ∧ nremaining ≤ PY_SSIZE_T_MAX
  · rw [if_pos hguard, if_pos hguard, TraceResult.erase_bind,
      erase_ascendingScanTraced]
    unfold countRunBindOptionAcross
    cases hascending : ascendingScan? nremaining state.key_compare slice base
        nremaining 1 with
    | none => simp
    | some ascending =>
        simp only [Option.bind_some]
        cases hascendingFuel : ascending.fuelExhausted with
        | true => simp
        | false =>
          simp only [Bool.false_eq_true, if_false]
          by_cases hcomplete : ascending.length = nremaining
          · simp [hcomplete]
          · simp only [hcomplete, if_false]
            by_cases hlong : 1 < ascending.length
            · rw [if_pos hlong, if_pos hlong]
              simp only [TraceResult.erase_bind,
                TraceResult.erase_sortSliceKeysRead]
              cases hfirst : slice.read? base with
              | none => simp
              | some first =>
                  cases hlast : slice.read?
                      (base + Int.ofNat (ascending.length - 1)) with
                  | none => simp
                  | some last =>
                      simp only [bind, Option.bind]
                      cases hcomparison :
                          iflt state.key_compare first.key last.key with
                      | true => simp
                      | false =>
                        simp only [Bool.false_eq_true, if_false,
                          TraceResult.erase_bind,
                          erase_sortsliceReverseTraced]
                        cases hreverse : sortsliceReverse? slice base
                            ascending.length with
                        | none => simp
                        | some reversed =>
                            cases hreverseFuel : reversed.fuelExhausted with
                            | true => simp [hreverseFuel]
                            | false =>
                              simp [hreverseFuel,
                                erase_finishDescendingTraced]
            · rw [if_neg hlong, if_neg hlong]
              exact erase_finishDescendingTraced _ _ _ _ _
  · simp [hguard]

end CPythonListsort
