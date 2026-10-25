import Mathlib
import sympy.Basic
import Def.CPythonListsort.Code.Assembly.CountRunSafety.Part3
open CPythonListsort


namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[ascendingScanTraced_memoryEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
private lemma ascendingScanTraced_memoryEvents_eq_nil
  (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν)
  (base : Int) (nremaining n : Nat) :
  (ascendingScanTraced? fuel lt slice base nremaining n).trace.memoryEvents =
    [] := by
  induction fuel generalizing n with
  | zero =>
    by_cases hactive : n < nremaining
    · simp [ascendingScanTraced?, hactive, TraceResult.markFuelExhausted,
      TraceResult.pure, AccessTrace.empty, AccessTrace.compose,
      AccessTrace.exhausted]
    · simp [ascendingScanTraced?, hactive, TraceResult.pure,
      AccessTrace.empty]
  | succ fuel ih =>
    rw [ascendingScanTraced?]
    by_cases hactive : n < nremaining
    · rw [if_pos hactive]
      apply TraceResult.memoryEvents_bind_eq_nil
      · rfl
      · intro previous
        apply TraceResult.memoryEvents_bind_eq_nil
        · rfl
        · intro next
          by_cases hcomparison : iflt lt next.key previous.key = true
          · rw [if_pos hcomparison]
            rfl
          · rw [if_neg hcomparison]
            exact ih (n + 1)
    · rw [if_neg hactive]
      rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[reverseLastEqualTraced_memoryEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
private lemma reverseLastEqualTraced_memoryEvents_eq_nil
  (valuesPresent : Bool) (slice : SortSlice κ ν) (base : Int)
  (n neq : Nat) :
  (reverseLastEqualTraced? valuesPresent slice base n neq).trace.memoryEvents =
    [] := by
  unfold reverseLastEqualTraced?
  by_cases hzero : neq = 0
  · rw [if_pos hzero]
    rfl
  · rw [if_neg hzero]
    simpa only [TraceResult.memoryEvents_map] using
      (sortsliceReverseTraced_memoryEvents_eq_nil valuesPresent slice
        (base + Int.ofNat n - Int.ofNat (neq + 1)) (neq + 1))

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[descendingScanTraced_memoryEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
private lemma descendingScanTraced_memoryEvents_eq_nil
  (fuel : Nat) (valuesPresent : Bool) (lt : BoolComparator κ)
  (slice : SortSlice κ ν) (base : Int) (nremaining n neq : Nat) :
  (descendingScanTraced? fuel valuesPresent lt slice base nremaining n
    neq).trace.memoryEvents = [] := by
  induction fuel generalizing slice n neq with
  | zero =>
    by_cases hactive : n < nremaining
    · simp [descendingScanTraced?, hactive, TraceResult.markFuelExhausted,
      TraceResult.pure, AccessTrace.empty, AccessTrace.compose,
      AccessTrace.exhausted]
    · simp [descendingScanTraced?, hactive, TraceResult.pure,
      AccessTrace.empty]
  | succ fuel ih =>
    rw [descendingScanTraced?]
    by_cases hactive : n < nremaining
    · rw [if_pos hactive]
      apply TraceResult.memoryEvents_bind_eq_nil
      · rfl
      · intro previous
        apply TraceResult.memoryEvents_bind_eq_nil
        · rfl
        · intro next
          by_cases hnextSmaller :
            iflt lt next.key previous.key = true
          · rw [if_pos hnextSmaller]
            apply TraceResult.memoryEvents_bind_eq_nil
            · exact reverseLastEqualTraced_memoryEvents_eq_nil _ _ _ _ _
            · intro reversed
              by_cases hexhausted : reversed.fuelExhausted = true
              · rw [if_pos hexhausted]
                rfl
              · rw [if_neg hexhausted]
                exact ih reversed.slice (n + 1) 0
          · rw [if_neg hnextSmaller]
            by_cases hpreviousSmaller :
              iflt lt previous.key next.key = true
            · rw [if_pos hpreviousSmaller]
              rfl
            · rw [if_neg hpreviousSmaller]
              exact ih slice (n + 1) (neq + 1)
    · rw [if_neg hactive]
      rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[finishDescendingTraced_memoryEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
private lemma finishDescendingTraced_memoryEvents_eq_nil
  (state : MergeState κ ν) (slice : SortSlice κ ν) (base : Int)
  (nremaining n : Nat) :
  (finishDescendingTraced? state slice base nremaining n).trace.memoryEvents =
    [] := by
  unfold finishDescendingTraced?
  apply TraceResult.memoryEvents_bind_eq_nil
  · exact descendingScanTraced_memoryEvents_eq_nil _ _ _ _ _ _ _ _
  · intro descending
    by_cases hdescendingFuel : descending.fuelExhausted = true
    · rw [if_pos hdescendingFuel]
      rfl
    · rw [if_neg hdescendingFuel]
      apply TraceResult.memoryEvents_bind_eq_nil
      · exact reverseLastEqualTraced_memoryEvents_eq_nil _ _ _ _ _
      · intro equalTailReversed
        by_cases hequalFuel : equalTailReversed.fuelExhausted = true
        · rw [if_pos hequalFuel]
          rfl
        · rw [if_neg hequalFuel]
          apply TraceResult.memoryEvents_bind_eq_nil
          · exact sortsliceReverseTraced_memoryEvents_eq_nil _ _ _ _
          · intro wholeReversed
            by_cases hwholeFuel : wholeReversed.fuelExhausted = true
            · rw [if_pos hwholeFuel]
              rfl
            · rw [if_neg hwholeFuel]
              simpa only [TraceResult.memoryEvents_map] using
                (ascendingScanTraced_memoryEvents_eq_nil nremaining
                  state.key_compare wholeReversed.slice base nremaining
                  descending.length)

end CPythonListsort

namespace CPythonListsort

/--
[countRunTraced_memoryEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
lemma countRunTraced_memoryEvents_eq_nil
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {slice : SortSlice κ ν}
  {base : Int}
  {nremaining : Nat} :
-- imply
  (countRunTraced? state slice base nremaining).trace.memoryEvents = [] := by
-- proof
  unfold countRunTraced?
  by_cases hguard : 0 < nremaining ∧ nremaining ≤ PY_SSIZE_T_MAX
  · rw [if_pos hguard]
    apply TraceResult.memoryEvents_bind_eq_nil
    · exact ascendingScanTraced_memoryEvents_eq_nil _ _ _ _ _ _
    · intro ascending
      by_cases hascendingFuel : ascending.fuelExhausted = true
      · rw [if_pos hascendingFuel]
        rfl
      · rw [if_neg hascendingFuel]
        by_cases hcomplete : ascending.length = nremaining
        · rw [if_pos hcomplete]
          rfl
        · rw [if_neg hcomplete]
          by_cases hlong : 1 < ascending.length
          · rw [if_pos hlong]
            apply TraceResult.memoryEvents_bind_eq_nil
            · rfl
            · intro first
              apply TraceResult.memoryEvents_bind_eq_nil
              · rfl
              · intro last
                by_cases hcomparison :
                  iflt state.key_compare first.key last.key = true
                · rw [if_pos hcomparison]
                  rfl
                · rw [if_neg hcomparison]
                  apply TraceResult.memoryEvents_bind_eq_nil
                  · exact sortsliceReverseTraced_memoryEvents_eq_nil _ _ _ _
                  · intro reversed
                    by_cases hreverseFuel : reversed.fuelExhausted = true
                    · rw [if_pos hreverseFuel]
                      rfl
                    · rw [if_neg hreverseFuel]
                      exact finishDescendingTraced_memoryEvents_eq_nil _ _ _ _ _
          · rw [if_neg hlong]
            exact finishDescendingTraced_memoryEvents_eq_nil _ _ _ _ _
  · rw [if_neg hguard]
    rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[ascendingScanTraced_policyEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
private lemma ascendingScanTraced_policyEvents_eq_nil
  (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν)
  (base : Int) (nremaining n : Nat) :
  (ascendingScanTraced? fuel lt slice base nremaining n).trace.policyEvents =
    [] := by
  induction fuel generalizing n with
  | zero =>
    by_cases hactive : n < nremaining
    · simp [ascendingScanTraced?, hactive, TraceResult.markFuelExhausted,
      TraceResult.pure, AccessTrace.empty, AccessTrace.compose,
      AccessTrace.exhausted]
    · simp [ascendingScanTraced?, hactive, TraceResult.pure,
      AccessTrace.empty]
  | succ fuel ih =>
    rw [ascendingScanTraced?]
    by_cases hactive : n < nremaining
    · rw [if_pos hactive]
      apply TraceResult.policyEvents_bind_eq_nil
      · rfl
      · intro previous
        apply TraceResult.policyEvents_bind_eq_nil
        · rfl
        · intro next
          by_cases hcomparison : iflt lt next.key previous.key = true
          · rw [if_pos hcomparison]
            rfl
          · rw [if_neg hcomparison]
            exact ih (n + 1)
    · rw [if_neg hactive]
      rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[reverseLastEqualTraced_policyEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
private lemma reverseLastEqualTraced_policyEvents_eq_nil
  (valuesPresent : Bool) (slice : SortSlice κ ν) (base : Int)
  (n neq : Nat) :
  (reverseLastEqualTraced? valuesPresent slice base n neq).trace.policyEvents =
    [] := by
  unfold reverseLastEqualTraced?
  by_cases hzero : neq = 0
  · rw [if_pos hzero]
    rfl
  · rw [if_neg hzero]
    simpa only [TraceResult.policyEvents_map] using
      (sortsliceReverseTraced_policyEvents_eq_nil valuesPresent slice
        (base + Int.ofNat n - Int.ofNat (neq + 1)) (neq + 1))

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[descendingScanTraced_policyEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
private lemma descendingScanTraced_policyEvents_eq_nil
  (fuel : Nat) (valuesPresent : Bool) (lt : BoolComparator κ)
  (slice : SortSlice κ ν) (base : Int) (nremaining n neq : Nat) :
  (descendingScanTraced? fuel valuesPresent lt slice base nremaining n
    neq).trace.policyEvents = [] := by
  induction fuel generalizing slice n neq with
  | zero =>
    by_cases hactive : n < nremaining
    · simp [descendingScanTraced?, hactive, TraceResult.markFuelExhausted,
      TraceResult.pure, AccessTrace.empty, AccessTrace.compose,
      AccessTrace.exhausted]
    · simp [descendingScanTraced?, hactive, TraceResult.pure,
      AccessTrace.empty]
  | succ fuel ih =>
    rw [descendingScanTraced?]
    by_cases hactive : n < nremaining
    · rw [if_pos hactive]
      apply TraceResult.policyEvents_bind_eq_nil
      · rfl
      · intro previous
        apply TraceResult.policyEvents_bind_eq_nil
        · rfl
        · intro next
          by_cases hnextSmaller : iflt lt next.key previous.key = true
          · rw [if_pos hnextSmaller]
            apply TraceResult.policyEvents_bind_eq_nil
            · exact reverseLastEqualTraced_policyEvents_eq_nil _ _ _ _ _
            · intro reversed
              by_cases hexhausted : reversed.fuelExhausted = true
              · rw [if_pos hexhausted]
                rfl
              · rw [if_neg hexhausted]
                exact ih reversed.slice (n + 1) 0
          · rw [if_neg hnextSmaller]
            by_cases hpreviousSmaller :
              iflt lt previous.key next.key = true
            · rw [if_pos hpreviousSmaller]
              rfl
            · rw [if_neg hpreviousSmaller]
              exact ih slice (n + 1) (neq + 1)
    · rw [if_neg hactive]
      rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[finishDescendingTraced_policyEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
private lemma finishDescendingTraced_policyEvents_eq_nil
  (state : MergeState κ ν) (slice : SortSlice κ ν) (base : Int)
  (nremaining n : Nat) :
  (finishDescendingTraced? state slice base nremaining n).trace.policyEvents =
    [] := by
  unfold finishDescendingTraced?
  apply TraceResult.policyEvents_bind_eq_nil
  · exact descendingScanTraced_policyEvents_eq_nil _ _ _ _ _ _ _ _
  · intro descending
    by_cases hdescendingFuel : descending.fuelExhausted = true
    · rw [if_pos hdescendingFuel]
      rfl
    · rw [if_neg hdescendingFuel]
      apply TraceResult.policyEvents_bind_eq_nil
      · exact reverseLastEqualTraced_policyEvents_eq_nil _ _ _ _ _
      · intro equalTailReversed
        by_cases hequalFuel : equalTailReversed.fuelExhausted = true
        · rw [if_pos hequalFuel]
          rfl
        · rw [if_neg hequalFuel]
          apply TraceResult.policyEvents_bind_eq_nil
          · exact sortsliceReverseTraced_policyEvents_eq_nil _ _ _ _
          · intro wholeReversed
            by_cases hwholeFuel : wholeReversed.fuelExhausted = true
            · rw [if_pos hwholeFuel]
              rfl
            · rw [if_neg hwholeFuel]
              simpa only [TraceResult.policyEvents_map] using
                (ascendingScanTraced_policyEvents_eq_nil nremaining
                  state.key_compare wholeReversed.slice base nremaining
                  descending.length)

end CPythonListsort

namespace CPythonListsort

/--
[countRunTraced_policyEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
lemma countRunTraced_policyEvents_eq_nil
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {slice : SortSlice κ ν}
  {base : Int}
  {nremaining : Nat} :
-- imply
  (countRunTraced? state slice base nremaining).trace.policyEvents = [] := by
-- proof
  unfold countRunTraced?
  by_cases hguard : 0 < nremaining ∧ nremaining ≤ PY_SSIZE_T_MAX
  · rw [if_pos hguard]
    apply TraceResult.policyEvents_bind_eq_nil
    · exact ascendingScanTraced_policyEvents_eq_nil _ _ _ _ _ _
    · intro ascending
      by_cases hascendingFuel : ascending.fuelExhausted = true
      · rw [if_pos hascendingFuel]
        rfl
      · rw [if_neg hascendingFuel]
        by_cases hcomplete : ascending.length = nremaining
        · rw [if_pos hcomplete]
          rfl
        · rw [if_neg hcomplete]
          by_cases hlong : 1 < ascending.length
          · rw [if_pos hlong]
            apply TraceResult.policyEvents_bind_eq_nil
            · rfl
            · intro first
              apply TraceResult.policyEvents_bind_eq_nil
              · rfl
              · intro last
                by_cases hcomparison :
                  iflt state.key_compare first.key last.key = true
                · rw [if_pos hcomparison]
                  rfl
                · rw [if_neg hcomparison]
                  apply TraceResult.policyEvents_bind_eq_nil
                  · exact sortsliceReverseTraced_policyEvents_eq_nil _ _ _ _
                  · intro reversed
                    by_cases hreverseFuel : reversed.fuelExhausted = true
                    · rw [if_pos hreverseFuel]
                      rfl
                    · rw [if_neg hreverseFuel]
                      exact finishDescendingTraced_policyEvents_eq_nil _ _ _ _ _
          · rw [if_neg hlong]
            exact finishDescendingTraced_policyEvents_eq_nil _ _ _ _ _
  · rw [if_neg hguard]
    rfl

end CPythonListsort

namespace CPythonListsort

/--
[erase_ascendingScanTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
lemma erase_ascendingScanTraced
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {slice : SortSlice κ ν}
  {base : Int}
  {nremaining n : Nat} :
-- imply
  (ascendingScanTraced? fuel lt slice base nremaining n).erase = ascendingScan? fuel lt slice base nremaining n := by
-- proof
  induction fuel generalizing n with
  | zero =>
    by_cases h : n < nremaining <;>
      simp [ascendingScanTraced?, ascendingScan?, ascendingScanResult, h]
  | succ fuel ih =>
    by_cases h : n < nremaining
    · simp only [ascendingScanTraced?, ascendingScan?, h, if_true,
      TraceResult.erase_bind, TraceResult.erase_sortSliceKeysRead]
      unfold countRunBindOptionAcross
      cases hprevious : slice.read? (base + Int.ofNat (n - 1)) with
      | none => simp
      | some previous =>
        simp only [Option.bind_some]
        cases hnext : slice.read? (base + Int.ofNat n) with
        | none => simp
        | some next =>
          simp only [Option.bind_some]
          by_cases hcomparison : iflt lt next.key previous.key = true
          · change lt next.key previous.key = true at hcomparison
            simp [hcomparison, ascendingScanResult]
          · have hcomparison' : ¬lt next.key previous.key = true := by
            simpa [iflt] using hcomparison
            simp [hcomparison', ih]
    · simp [ascendingScanTraced?, ascendingScan?, h, ascendingScanResult]

end CPythonListsort

namespace CPythonListsort

/--
[erase_reverseLastEqualTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
lemma erase_reverseLastEqualTraced
  {κ : Type u}
  {ν : Type v}
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {base : Int}
  {n neq : Nat} :
-- imply
  (reverseLastEqualTraced? valuesPresent slice base n neq).erase = reverseLastEqual? slice base n neq := by
-- proof
  by_cases hzero : neq = 0
  · simp [reverseLastEqualTraced?, reverseLastEqual?, hzero]
  · simp only [reverseLastEqualTraced?, reverseLastEqual?, hzero, if_false,
    TraceResult.erase_map, erase_sortsliceReverseTraced]
    cases hreverse : sortsliceReverse? slice
      (base + Int.ofNat n - Int.ofNat (neq + 1)) (neq + 1) <;>
      simp

end CPythonListsort

namespace CPythonListsort

/--
[erase_finishDescendingTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
lemma erase_finishDescendingTraced
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {slice : SortSlice κ ν}
  {base : Int}
  {nremaining n : Nat} :
-- imply
  (finishDescendingTraced? state slice base nremaining n).erase = finishDescending? state slice base nremaining n := by
-- proof
  unfold finishDescendingTraced? finishDescending?
  rw [TraceResult.erase_bind, erase_descendingScanTraced]
  cases hdescending : descendingScan? nremaining state.key_compare slice base
    nremaining n 0 with
  | none => rfl
  | some descending =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases hdescendingFuel : descending.fuelExhausted with
    | true => simp only [if_true, TraceResult.erase_pure]
    | false =>
      simp only [Bool.false_eq_true, if_false, TraceResult.erase_bind,
        erase_reverseLastEqualTraced]
      cases hequal : reverseLastEqual? descending.slice base descending.length
        descending.equalTail with
      | none => simp only [Option.bind_none]
      | some equalTailReversed =>
        simp only [Option.bind_some]
        cases hequalFuel : equalTailReversed.fuelExhausted with
        | true =>
          simp only [if_true, TraceResult.erase_pure]
        | false =>
          simp only [Bool.false_eq_true, if_false,
            TraceResult.erase_bind, erase_sortsliceReverseTraced]
          cases hwhole : sortsliceReverse? equalTailReversed.slice base
            descending.length with
          | none => simp only [Option.bind_none]
          | some wholeReversed =>
            simp only [Option.bind_some]
            cases hwholeFuel : wholeReversed.fuelExhausted with
            | true =>
              simp only [if_true, TraceResult.erase_pure]
            | false =>
              simp only [Bool.false_eq_true, if_false,
                TraceResult.erase_map, erase_ascendingScanTraced]
              unfold countRunBindOptionAcross
              cases ascendingScan? nremaining state.key_compare
                wholeReversed.slice base nremaining descending.length <;>
                rfl

end CPythonListsort

namespace CPythonListsort.CountTraceSafe

variable {κ : Type u} {ν : Type v}
/--
[pure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
private lemma pure (value : α) :
  CountTraceSafe (TraceResult.pure value) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact AccessTrace.allAccessesInBounds_empty
  · exact AccessTrace.tempPayloadAccessesLive_empty

end CPythonListsort.CountTraceSafe

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[countKeyRead_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
private lemma countKeyRead_safe (slice : SortSlice κ ν) (index : Int)
  (hindex : SortSlice.IndexInBounds slice index) :
  CountTraceSafe (TraceResult.sortSliceKeysRead? slice index) := by
  constructor
  all_goals
    simp [AccessTrace.singletonAccess, AccessTrace.allAccessesInBounds,
      AccessTrace.tempPayloadAccessesLive, AccessEvent.InBounds,
      AccessEvent.TempPayloadLive, SortSlice.IndexInBounds] at hindex ⊢
  all_goals aesop

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[countTraceSafe_of_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
private lemma countTraceSafe_of_reverse
  (valuesPresent : Bool) (slice : SortSlice κ ν) (base : Int) (n : Nat)
  (result : ReverseSliceResult κ ν)
  (hpost : ReverseSliceSafetyPost slice valuesPresent base n result) :
  CountTraceSafe (sortsliceReverseTraced? valuesPresent slice base n) :=
  ⟨hpost.traceFuel, hpost.noPushes, hpost.accessesInBounds,
    hpost.tempAccessesLive⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[countRunSafetyPost_of](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
private lemma countRunSafetyPost_of
  (state : MergeState κ ν) (slice : SortSlice κ ν) (base : Int)
  (nremaining : Nat) (result : CountRunResult κ ν)
  (hresult : (countRunTraced? state slice base nremaining).result = some result)
  (hresultFuel : result.fuelExhausted = false)
  (htrace : CountTraceSafe (countRunTraced? state slice base nremaining))
  (hMode : SortSlice.ValuesModeInvariant state.a.hasValues result.slice)
  (hsize : result.slice.entries.size = slice.entries.size)
  (hlength : 1 ≤ result.length ∧ result.length ≤ nremaining) :
  CountRunSafetyPost state slice base nremaining result :=
  { resultEq := hresult
    resultFuel := hresultFuel
    traceFuel := htrace.fuel
    accessesInBounds := htrace.bounds
    tempAccessesLive := htrace.tempLive
    noPushes := htrace.noPushes
    exactErasure := erase_countRunTraced _ _ _ _
    valuesMode := hMode
    sizeEq := hsize
    lengthBounds := hlength }

end CPythonListsort

namespace CPythonListsort

/--
[countRun_install_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
lemma countRun_install_frame
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {result : CountRunResult κ ν} :
-- imply
  let after : MergeState κ ν := { state with data := result.slice } after.min_gallop = state.min_gallop ∧ after.listlen = state.listlen ∧ after.basekeys = state.basekeys ∧ after.a = state.a ∧ after.alloced = state.alloced ∧ after.pending = state.pending ∧ after.key_compare = state.key_compare ∧ after.mr_current = state.mr_current ∧ after.mr_e = state.mr_e ∧ after.mr_mask = state.mr_mask := by
-- proof
  simp

end CPythonListsort

namespace CPythonListsort

/--
[ascendingScanTraced_step_trace_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
lemma ascendingScanTraced_step_trace_order
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {slice : SortSlice κ ν}
  {base : Int}
  {nremaining n : Nat}
  {previous next : SortSliceEntry κ ν}
-- given
  (hactive : n < nremaining)
  (hprevious : (TraceResult.sortSliceKeysRead? slice (base + Int.ofNat (n - 1))).result = some previous)
  (hnext : (TraceResult.sortSliceKeysRead? slice (base + Int.ofNat n)).result = some next) :
-- imply
  (ascendingScanTraced? (fuel + 1) lt slice base nremaining n).trace = (TraceResult.sortSliceKeysRead? slice (base + Int.ofNat (n - 1))).trace.compose ((TraceResult.sortSliceKeysRead? slice (base + Int.ofNat n)).trace.compose (if iflt lt next.key previous.key then TraceResult.pure (ascendingScanResult n false) else ascendingScanTraced? fuel lt slice base nremaining (n + 1)).trace) := by
-- proof
  simp only [ascendingScanTraced?, hactive, if_true]
  rw [TraceResult.trace_bind, hprevious]
  simp only
  rw [TraceResult.trace_bind, hnext]

end CPythonListsort

namespace CPythonListsort

/--
[finishDescendingTraced_trace_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
lemma finishDescendingTraced_trace_order
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {slice : SortSlice κ ν}
  {base : Int}
  {nremaining n : Nat}
  {descending : DescendingScanResult κ ν}
  {equalTail : ReverseEqualResult κ ν}
  {whole : ReverseSliceResult κ ν}
-- given
  (hdescending : (descendingScanTraced? nremaining state.a.hasValues state.key_compare slice base nremaining n 0).result = some descending)
  (hdescendingFuel : descending.fuelExhausted = false)
  (hequal : (reverseLastEqualTraced? state.a.hasValues descending.slice base descending.length descending.equalTail).result = some equalTail)
  (hequalFuel : equalTail.fuelExhausted = false)
  (hwhole : (sortsliceReverseTraced? state.a.hasValues equalTail.slice base descending.length).result = some whole)
  (hwholeFuel : whole.fuelExhausted = false) :
-- imply
  (finishDescendingTraced? state slice base nremaining n).trace = (descendingScanTraced? nremaining state.a.hasValues state.key_compare slice base nremaining n 0).trace.compose ((reverseLastEqualTraced? state.a.hasValues descending.slice base descending.length descending.equalTail).trace.compose ((sortsliceReverseTraced? state.a.hasValues equalTail.slice base descending.length).trace.compose (ascendingScanTraced? nremaining state.key_compare whole.slice base nremaining descending.length).trace)) := by
-- proof
  simp [finishDescendingTraced?, TraceResult.trace_bind, hdescending,
    hdescendingFuel, hequal, hequalFuel, hwhole, hwholeFuel, TraceResult.map]

end CPythonListsort

namespace CPythonListsort

/--
[countRunTraced_singleton_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
lemma countRunTraced_singleton_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (countRunTraced? (countRunRegressionState countRunSingletonSlice) countRunSingletonSlice 0 1).result.map (fun result => (result.length, result.fuelExhausted, result.slice.entries.toList)) = some (1, false, countRunSingletonSlice.entries.toList) ∧ (countRunTraced? (countRunRegressionState countRunSingletonSlice) countRunSingletonSlice 0 1).trace = AccessTrace.empty := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[countRunTraced_full_ascending_no_reread_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
lemma countRunTraced_full_ascending_no_reread_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (countRunTraced? (countRunRegressionState countRunAscendingSlice) countRunAscendingSlice 0 4).result.map (fun result => (result.length, result.fuelExhausted, result.slice.entries.toList)) = some (4, false, countRunAscendingSlice.entries.toList) ∧ (countRunTraced? (countRunRegressionState countRunAscendingSlice) countRunAscendingSlice 0 4).trace.accesses.map (fun event => (event.kind, event.region, event.index)) = [(.read, .inputKeys, 0), (.read, .inputKeys, 1), (.read, .inputKeys, 1), (.read, .inputKeys, 2), (.read, .inputKeys, 2), (.read, .inputKeys, 3)] := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[countRunTraced_descending_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
lemma countRunTraced_descending_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (countRunTraced? (countRunRegressionState countRunDescendingSlice) countRunDescendingSlice 0 4).result.map (fun result => (result.length, result.fuelExhausted, result.slice.entries.toList)) = some (4, false, [{ key := 1, value := none }, { key := 2, value := none }, { key := 3, value := none }, { key := 4, value := none }]) ∧ (countRunTraced? (countRunRegressionState countRunDescendingSlice) countRunDescendingSlice 0 4).trace.fuelExhausted = false := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[countRunTraced_first_last_gate_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
lemma countRunTraced_first_last_gate_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (countRunTraced? (countRunRegressionState countRunGateSlice) countRunGateSlice 0 3).result.map (fun result => (result.length, result.fuelExhausted, result.slice.entries.toList)) = some (2, false, countRunGateSlice.entries.toList) ∧ (countRunTraced? (countRunRegressionState countRunGateSlice) countRunGateSlice 0 3).trace.accesses.map (fun event => (event.kind, event.region, event.index)) = [(.read, .inputKeys, 0), (.read, .inputKeys, 1), (.read, .inputKeys, 1), (.read, .inputKeys, 2), (.read, .inputKeys, 0), (.read, .inputKeys, 1)] := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[countRunTraced_tagged_equal_block_order_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
lemma countRunTraced_tagged_equal_block_order_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (countRunTraced? (countRunValuesRegressionState countRunTaggedEqualSlice) countRunTaggedEqualSlice 0 4).result.map (fun result => (result.length, result.fuelExhausted, result.slice.entries.toList)) = some (4, false, [{ key := 1, value := some 10 }, { key := 2, value := some 20 }, { key := 2, value := some 21 }, { key := 3, value := some 30 }]) ∧ (countRunTraced? (countRunValuesRegressionState countRunTaggedEqualSlice) countRunTaggedEqualSlice 0 4).trace.accesses.map (fun event => (event.kind, event.region, event.index)) = [(.read, .inputKeys, 0), (.read, .inputKeys, 1), (.read, .inputKeys, 1), (.read, .inputKeys, 2), (.read, .inputKeys, 2), (.read, .inputKeys, 3), (.read, .inputKeys, 1), (.read, .inputKeys, 2), (.write, .inputKeys, 1), (.write, .inputKeys, 2), (.read, .synchronizedValues, 1), (.read, .synchronizedValues, 2), (.write, .synchronizedValues, 1), (.write, .synchronizedValues, 2), (.read, .inputKeys, 0), (.read, .inputKeys, 3), (.write, .inputKeys, 0), (.write, .inputKeys, 3), (.read, .inputKeys, 1), (.read, .inputKeys, 2), (.write, .inputKeys, 1), (.write, .inputKeys, 2), (.read, .synchronizedValues, 0), (.read, .synchronizedValues, 3), (.write, .synchronizedValues, 0), (.write, .synchronizedValues, 3), (.read, .synchronizedValues, 1), (.read, .synchronizedValues, 2), (.write, .synchronizedValues, 1), (.write, .synchronizedValues, 2)] := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[countRunTraced_descending_then_ascending_extension_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
lemma countRunTraced_descending_then_ascending_extension_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (countRunTraced? (countRunRegressionState countRunExtensionSlice) countRunExtensionSlice 0 7).result.map (fun result => (result.length, result.fuelExhausted, result.slice.entries.toList)) = some (6, false, [{ key := 1, value := none }, { key := 2, value := none }, { key := 3, value := none }, { key := 3, value := none }, { key := 4, value := none }, { key := 5, value := none }, { key := 0, value := none }]) := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[countRunTraced_constant_true_priority_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
lemma countRunTraced_constant_true_priority_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (countRunTraced? (countRunConstantTrueState countRunGateSlice) countRunGateSlice 0 3).result.map (fun result => (result.length, result.fuelExhausted)) = some (3, false) ∧ (countRunTraced? (countRunConstantTrueState countRunGateSlice) countRunGateSlice 0 3).trace.accesses.map (fun event => event.index) = [0, 1, 1, 2, 0, 2, 0, 2] := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[ascendingScanTraced_zero_fuel_active_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
lemma ascendingScanTraced_zero_fuel_active_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (ascendingScanTraced? 0 (fun (left right : Nat) => decide (left < right)) countRunAscendingSlice 0 4 1).result.map (fun result => result.fuelExhausted) = some true ∧ (ascendingScanTraced? 0 (fun (left right : Nat) => decide (left < right)) countRunAscendingSlice 0 4 1).trace.fuelExhausted = true := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[descendingScanTraced_zero_fuel_active_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
lemma descendingScanTraced_zero_fuel_active_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (descendingScanTraced? 0 false (fun (left right : Nat) => decide (left < right)) countRunDescendingSlice 0 4 2 0).result.map (fun result => result.fuelExhausted) = some true ∧ (descendingScanTraced? 0 false (fun (left right : Nat) => decide (left < right)) countRunDescendingSlice 0 4 2 0).trace.fuelExhausted = true := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[countRunTraced_zero_remaining_failure_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
lemma countRunTraced_zero_remaining_failure_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (countRunTraced? (countRunRegressionState countRunSingletonSlice) countRunSingletonSlice 0 0).result = none ∧ (countRunTraced? (countRunRegressionState countRunSingletonSlice) countRunSingletonSlice 0 0).trace = AccessTrace.empty := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[countRunTraced_oob_failure_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
lemma countRunTraced_oob_failure_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (countRunTraced? (countRunRegressionState countRunSingletonSlice) countRunSingletonSlice 0 2).result = none ∧ (countRunTraced? (countRunRegressionState countRunSingletonSlice) countRunSingletonSlice 0 2).trace.accesses = [{ kind := .read, region := .inputKeys, index := 0, extent := 1 }, { kind := .read, region := .inputKeys, index := 1, extent := 1 }] ∧ ¬(countRunTraced? (countRunRegressionState countRunSingletonSlice) countRunSingletonSlice 0 2).trace.allAccessesInBounds := by
-- proof
  decide

end CPythonListsort

/--
[erase_descendingScanTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
private lemma erase_descendingScanTraced_eq
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {valuesPresent : Bool}
  {lt : BoolComparator κ}
  {slice : SortSlice κ ν}
  {base : Int}
  {nremaining n neq : Nat} :
-- imply
  (descendingScanTraced? fuel valuesPresent lt slice base nremaining n neq).erase = descendingScan? fuel lt slice base nremaining n neq := by
-- proof
  apply CPythonListsort.erase_descendingScanTraced fuel valuesPresent lt slice base nremaining n neq

/--
[erase_countRunTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
private lemma erase_countRunTraced_eq
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {slice : SortSlice κ ν}
  {base : Int}
  {nremaining : Nat} :
-- imply
  (countRunTraced? state slice base nremaining).erase = countRun? state slice base nremaining := by
-- proof
  apply CPythonListsort.erase_countRunTraced state slice base nremaining

/--
[countRun_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
private lemma countRun_safe_eq
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {slice : SortSlice κ ν}
  {base : Int}
  {nremaining : Nat}
-- given
  (hrange : SortSlice.RangeInBounds slice base nremaining)
  (hpositive : 0 < nremaining)
  (hsizeRepresentable : nremaining ≤ PY_SSIZE_T_MAX)
  (hMode : SortSlice.ValuesModeInvariant state.a.hasValues slice) :
-- imply
  ∃ result, CountRunSafetyPost state slice base nremaining result := by
-- proof
  apply CPythonListsort.countRun_safe state slice base nremaining hrange hpositive hsizeRepresentable hMode

/--
[descendingScanTraced_step_trace_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
private lemma descendingScanTraced_step_trace_order_eq
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {valuesPresent : Bool}
  {lt : BoolComparator κ}
  {slice : SortSlice κ ν}
  {base : Int}
  {nremaining n neq : Nat}
  {previous next : SortSliceEntry κ ν}
-- given
  (hactive : n < nremaining)
  (hprevious : (TraceResult.sortSliceKeysRead? slice (base + Int.ofNat (n - 1))).result = some previous)
  (hnext : (TraceResult.sortSliceKeysRead? slice (base + Int.ofNat n)).result = some next) :
-- imply
  (descendingScanTraced? (fuel + 1) valuesPresent lt slice base nremaining n neq).trace = (TraceResult.sortSliceKeysRead? slice (base + Int.ofNat (n - 1))).trace.compose ((TraceResult.sortSliceKeysRead? slice (base + Int.ofNat n)).trace.compose (if iflt lt next.key previous.key then (reverseLastEqualTraced? valuesPresent slice base n neq).bind fun reversed => if reversed.fuelExhausted then TraceResult.pure (descendingScanResult reversed.slice n 0 true) else descendingScanTraced? fuel valuesPresent lt reversed.slice base nremaining (n + 1) 0 else if iflt lt previous.key next.key then TraceResult.pure (descendingScanResult slice n neq false) else descendingScanTraced? fuel valuesPresent lt slice base nremaining (n + 1) (neq + 1)).trace) := by
-- proof
  apply CPythonListsort.descendingScanTraced_step_trace_order fuel valuesPresent lt slice base nremaining n neq previous next hactive hprevious hnext

/--
[descendingScanTraced_next_smaller_priority](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean)
-/
@[path]
private lemma descendingScanTraced_next_smaller_priority_eq
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {valuesPresent : Bool}
  {lt : BoolComparator κ}
  {slice : SortSlice κ ν}
  {base : Int}
  {nremaining n neq : Nat}
  {previous next : SortSliceEntry κ ν}
-- given
  (hactive : n < nremaining)
  (hprevious : (TraceResult.sortSliceKeysRead? slice (base + Int.ofNat (n - 1))).result = some previous)
  (hnext : (TraceResult.sortSliceKeysRead? slice (base + Int.ofNat n)).result = some next)
  (hsmaller : iflt lt next.key previous.key = true) :
-- imply
  (descendingScanTraced? (fuel + 1) valuesPresent lt slice base nremaining n neq).result = ((reverseLastEqualTraced? valuesPresent slice base n neq).bind fun reversed => if reversed.fuelExhausted then TraceResult.pure (descendingScanResult reversed.slice n 0 true) else descendingScanTraced? fuel valuesPresent lt reversed.slice base nremaining (n + 1) 0).result := by
-- proof
  apply CPythonListsort.descendingScanTraced_next_smaller_priority fuel valuesPresent lt slice base nremaining n neq previous next hactive hprevious hnext hsmaller


-- created on 2026-10-23
