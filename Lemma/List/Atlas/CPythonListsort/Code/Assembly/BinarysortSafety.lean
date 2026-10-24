import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Assembly.BinarysortSafety
open CPythonListsort CPythonListsort.BinarysortTraceSafe


namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[binarysortSearchTraced_memoryEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma binarysortSearchTraced_memoryEvents_eq_nil
  (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν)
  (base : Int) (pivot : SortSliceEntry κ ν) (left right : Nat) :
  (binarysortSearchTraced? fuel lt slice base pivot left
    right).trace.memoryEvents = [] := by
  induction fuel generalizing left right with
  | zero =>
    by_cases hactive : left < right
    · simp [binarysortSearchTraced?, hactive,
      TraceResult.markFuelExhausted, TraceResult.pure,
      AccessTrace.empty, AccessTrace.compose, AccessTrace.exhausted]
    · simp [binarysortSearchTraced?, hactive, TraceResult.pure,
      AccessTrace.empty]
  | succ fuel ih =>
    rw [binarysortSearchTraced?]
    by_cases hactive : left < right
    · rw [if_pos hactive]
      apply TraceResult.memoryEvents_bind_eq_nil
      · rfl
      · intro entry
        by_cases hcomparison : iflt lt pivot.key entry.key = true
        · rw [if_pos hcomparison]
          exact ih left ((left + right) / 2)
        · rw [if_neg hcomparison]
          exact ih (((left + right) / 2) + 1) right
    · rw [if_neg hactive]
      rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[copyKeysFromTraced_memoryEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma copyKeysFromTraced_memoryEvents_eq_nil
  (destination source : SortSlice κ ν) (dst src : Int) :
  (SortSlice.copyKeysFromTraced? destination source dst
    src).trace.memoryEvents = [] := by
  unfold SortSlice.copyKeysFromTraced?
  apply TraceResult.memoryEvents_bind_eq_nil
  · rfl
  · intro entry
    rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[copyValuesFromTraced_memoryEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma copyValuesFromTraced_memoryEvents_eq_nil
  (destination source : SortSlice κ ν) (dst src : Int) :
  (SortSlice.copyValuesFromTraced? destination source dst
    src).trace.memoryEvents = [] := by
  unfold SortSlice.copyValuesFromTraced?
  apply TraceResult.memoryEvents_bind_eq_nil
  · rfl
  · intro entry
    rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[memmoveBackwardKeysTraced_memoryEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma memmoveBackwardKeysTraced_memoryEvents_eq_nil
  (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
  (SortSlice.memmoveBackwardKeysTraced? count slice dst
    src).trace.memoryEvents = [] := by
  induction count generalizing slice with
  | zero => rfl
  | succ count ih =>
    rw [SortSlice.memmoveBackwardKeysTraced?]
    apply TraceResult.memoryEvents_bind_eq_nil
    · exact copyKeysFromTraced_memoryEvents_eq_nil _ _ _ _
    · intro updated
      exact ih updated

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[memmoveBackwardValuesTraced_memoryEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma memmoveBackwardValuesTraced_memoryEvents_eq_nil
  (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
  (SortSlice.memmoveBackwardValuesTraced? count slice dst
    src).trace.memoryEvents = [] := by
  induction count generalizing slice with
  | zero => rfl
  | succ count ih =>
    rw [SortSlice.memmoveBackwardValuesTraced?]
    apply TraceResult.memoryEvents_bind_eq_nil
    · exact copyValuesFromTraced_memoryEvents_eq_nil _ _ _ _
    · intro updated
      exact ih updated

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[binarysortShiftInsertTraced_memoryEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma binarysortShiftInsertTraced_memoryEvents_eq_nil
  (valuesPresent : Bool) (slice : SortSlice κ ν) (base : Int)
  (ok position : Nat) (pivot : SortSliceEntry κ ν) :
  (binarysortShiftInsertTraced? valuesPresent slice base ok position
    pivot).trace.memoryEvents = [] := by
  unfold binarysortShiftInsertTraced?
  apply TraceResult.memoryEvents_bind_eq_nil
  · exact memmoveBackwardKeysTraced_memoryEvents_eq_nil _ _ _ _
  · intro keyShifted
    apply TraceResult.memoryEvents_bind_eq_nil
    · rfl
    · intro keyResult
      cases valuesPresent
      · rfl
      · apply TraceResult.memoryEvents_bind_eq_nil
        · rfl
        · intro valuePivot
          apply TraceResult.memoryEvents_bind_eq_nil
          · exact memmoveBackwardValuesTraced_memoryEvents_eq_nil _ _ _ _
          · intro valueShifted
            rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[binarysortLoopTraced_memoryEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma binarysortLoopTraced_memoryEvents_eq_nil
  (fuel : Nat) (state : MergeState κ ν) (slice : SortSlice κ ν)
  (base : Int) (n ok : Nat) :
  (binarysortLoopTraced? fuel state slice base n ok).trace.memoryEvents =
    [] := by
  induction fuel generalizing slice ok with
  | zero =>
    by_cases hactive : ok < n
    · simp [binarysortLoopTraced?, hactive, TraceResult.markFuelExhausted,
      TraceResult.pure, AccessTrace.empty, AccessTrace.compose,
      AccessTrace.exhausted]
    · simp [binarysortLoopTraced?, hactive, TraceResult.pure,
      AccessTrace.empty]
  | succ fuel ih =>
    rw [binarysortLoopTraced?]
    by_cases hactive : ok < n
    · rw [if_pos hactive]
      apply TraceResult.memoryEvents_bind_eq_nil
      · rfl
      · intro pivot
        apply TraceResult.memoryEvents_bind_eq_nil
        · exact binarysortSearchTraced_memoryEvents_eq_nil _ _ _ _ _ _ _
        · intro search
          by_cases hexhausted : search.fuelExhausted = true
          · rw [if_pos hexhausted]
            rfl
          · rw [if_neg hexhausted]
            apply TraceResult.memoryEvents_bind_eq_nil
            · exact binarysortShiftInsertTraced_memoryEvents_eq_nil _ _ _ _ _ _
            · intro updated
              exact ih updated (ok + 1)
    · rw [if_neg hactive]
      rfl

end CPythonListsort

namespace CPythonListsort

/--
[binarysortTraced_memoryEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma binarysortTraced_memoryEvents_eq_nil
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {slice : SortSlice κ ν}
  {base : Int}
  {n ok : Nat} :
-- imply
  (binarysortTraced? state slice base n ok).trace.memoryEvents = [] := by
-- proof
  unfold binarysortTraced?
  by_cases hadmitted : 1 ≤ n ∧ ok ≤ n ∧ n ≤ MAX_MINRUN.toNat
  · rw [if_pos hadmitted]
    exact binarysortLoopTraced_memoryEvents_eq_nil _ _ _ _ _ _
  · rw [if_neg hadmitted]
    rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[binarysortSearchTraced_policyEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma binarysortSearchTraced_policyEvents_eq_nil
  (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν)
  (base : Int) (pivot : SortSliceEntry κ ν) (left right : Nat) :
  (binarysortSearchTraced? fuel lt slice base pivot left
    right).trace.policyEvents = [] := by
  induction fuel generalizing left right with
  | zero =>
    by_cases hactive : left < right
    · simp [binarysortSearchTraced?, hactive,
      TraceResult.markFuelExhausted, TraceResult.pure,
      AccessTrace.empty, AccessTrace.compose, AccessTrace.exhausted]
    · simp [binarysortSearchTraced?, hactive, TraceResult.pure,
      AccessTrace.empty]
  | succ fuel ih =>
    rw [binarysortSearchTraced?]
    by_cases hactive : left < right
    · rw [if_pos hactive]
      apply TraceResult.policyEvents_bind_eq_nil
      · rfl
      · intro entry
        by_cases hcomparison : iflt lt pivot.key entry.key = true
        · rw [if_pos hcomparison]
          exact ih left ((left + right) / 2)
        · rw [if_neg hcomparison]
          exact ih (((left + right) / 2) + 1) right
    · rw [if_neg hactive]
      rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[memmoveBackwardKeysTraced_policyEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma memmoveBackwardKeysTraced_policyEvents_eq_nil
  (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
  (SortSlice.memmoveBackwardKeysTraced? count slice dst
    src).trace.policyEvents = [] := by
  induction count generalizing slice with
  | zero => rfl
  | succ count ih =>
    rw [SortSlice.memmoveBackwardKeysTraced?]
    apply TraceResult.policyEvents_bind_eq_nil
    · unfold SortSlice.copyKeysFromTraced?
      apply TraceResult.policyEvents_bind_eq_nil <;> intros <;> rfl
    · intro updated
      exact ih updated

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[memmoveBackwardValuesTraced_policyEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma memmoveBackwardValuesTraced_policyEvents_eq_nil
  (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
  (SortSlice.memmoveBackwardValuesTraced? count slice dst
    src).trace.policyEvents = [] := by
  induction count generalizing slice with
  | zero => rfl
  | succ count ih =>
    rw [SortSlice.memmoveBackwardValuesTraced?]
    apply TraceResult.policyEvents_bind_eq_nil
    · unfold SortSlice.copyValuesFromTraced?
      apply TraceResult.policyEvents_bind_eq_nil <;> intros <;> rfl
    · intro updated
      exact ih updated

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[binarysortShiftInsertTraced_policyEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma binarysortShiftInsertTraced_policyEvents_eq_nil
  (valuesPresent : Bool) (slice : SortSlice κ ν) (base : Int)
  (ok position : Nat) (pivot : SortSliceEntry κ ν) :
  (binarysortShiftInsertTraced? valuesPresent slice base ok position
    pivot).trace.policyEvents = [] := by
  unfold binarysortShiftInsertTraced?
  apply TraceResult.policyEvents_bind_eq_nil
  · exact memmoveBackwardKeysTraced_policyEvents_eq_nil _ _ _ _
  · intro keyShifted
    apply TraceResult.policyEvents_bind_eq_nil
    · rfl
    · intro keyResult
      cases valuesPresent
      · rfl
      · apply TraceResult.policyEvents_bind_eq_nil
        · rfl
        · intro valuePivot
          apply TraceResult.policyEvents_bind_eq_nil
          · exact memmoveBackwardValuesTraced_policyEvents_eq_nil _ _ _ _
          · intro valueShifted
            rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[binarysortLoopTraced_policyEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma binarysortLoopTraced_policyEvents_eq_nil
  (fuel : Nat) (state : MergeState κ ν) (slice : SortSlice κ ν)
  (base : Int) (n ok : Nat) :
  (binarysortLoopTraced? fuel state slice base n ok).trace.policyEvents =
    [] := by
  induction fuel generalizing slice ok with
  | zero =>
    by_cases hactive : ok < n
    · simp [binarysortLoopTraced?, hactive, TraceResult.markFuelExhausted,
      TraceResult.pure, AccessTrace.empty, AccessTrace.compose,
      AccessTrace.exhausted]
    · simp [binarysortLoopTraced?, hactive, TraceResult.pure,
      AccessTrace.empty]
  | succ fuel ih =>
    rw [binarysortLoopTraced?]
    by_cases hactive : ok < n
    · rw [if_pos hactive]
      apply TraceResult.policyEvents_bind_eq_nil
      · rfl
      · intro pivot
        apply TraceResult.policyEvents_bind_eq_nil
        · exact binarysortSearchTraced_policyEvents_eq_nil _ _ _ _ _ _ _
        · intro search
          by_cases hexhausted : search.fuelExhausted = true
          · rw [if_pos hexhausted]
            rfl
          · rw [if_neg hexhausted]
            apply TraceResult.policyEvents_bind_eq_nil
            · exact binarysortShiftInsertTraced_policyEvents_eq_nil _ _ _ _ _ _
            · intro updated
              exact ih updated (ok + 1)
    · rw [if_neg hactive]
      rfl

end CPythonListsort

namespace CPythonListsort

/--
[binarysortTraced_policyEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma binarysortTraced_policyEvents_eq_nil
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {slice : SortSlice κ ν}
  {base : Int}
  {n ok : Nat} :
-- imply
  (binarysortTraced? state slice base n ok).trace.policyEvents = [] := by
-- proof
  unfold binarysortTraced?
  by_cases hadmitted : 1 ≤ n ∧ ok ≤ n ∧ n ≤ MAX_MINRUN.toNat
  · rw [if_pos hadmitted]
    exact binarysortLoopTraced_policyEvents_eq_nil _ _ _ _ _ _
  · rw [if_neg hadmitted]
    rfl

end CPythonListsort

namespace CPythonListsort

/--
[erase_binarysortSearchTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma erase_binarysortSearchTraced
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {slice : SortSlice κ ν}
  {base : Int}
  {pivot : SortSliceEntry κ ν}
  {left right : Nat} :
-- imply
  (binarysortSearchTraced? fuel lt slice base pivot left right).erase = binarysortSearch? fuel lt slice base pivot left right := by
-- proof
  induction fuel generalizing left right with
  | zero =>
    by_cases hactive : left < right <;>
      simp [binarysortSearchTraced?, binarysortSearch?, hactive]
  | succ fuel ih =>
    by_cases hactive : left < right
    · let middle := (left + right) / 2
      simp only [binarysortSearchTraced?, binarysortSearch?, hactive, if_true,
        TraceResult.erase_bind, TraceResult.erase_sortSliceKeysRead]
      cases hread : slice.read? (base + Int.ofNat middle) with
      | none => simp [binarysortBindOptionAcross]
      | some entry =>
        by_cases hlt : lt pivot.key entry.key = true <;>
          simp [binarysortBindOptionAcross, iflt, hlt, ih]
    · simp [binarysortSearchTraced?, binarysortSearch?, hactive]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[memmove_backward_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma memmove_backward_eq (slice : SortSlice κ ν) (base : Int)
  (position count : Nat) :
  slice.memmove? (base + Int.ofNat (position + 1))
    (base + Int.ofNat position) count =
    SortSlice.memmoveBackward? count slice
      (base + Int.ofNat (position + 1)) (base + Int.ofNat position) := by
  simp [SortSlice.memmove?, SortSlice.memmoveDirection]

end CPythonListsort

namespace CPythonListsort

/--
[erase_binarysortShiftInsertTraced_of_pivot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma erase_binarysortShiftInsertTraced_of_pivot
  {κ : Type u}
  {ν : Type v}
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {base : Int}
  {ok position : Nat}
  {pivot : SortSliceEntry κ ν}
-- given
  (hpivot : slice.read? (base + Int.ofNat ok) = some pivot) :
-- imply
  (binarysortShiftInsertTraced? valuesPresent slice base ok position pivot).erase = (do let shifted ← slice.memmove? (base + Int.ofNat (position + 1)) (base + Int.ofNat position) (ok - position) shifted.write? (base + Int.ofNat position) pivot) := by
-- proof
  unfold binarysortShiftInsertTraced?
  simp only [TraceResult.erase_bind,
    SortSlice.erase_memmoveBackwardKeysTraced,
    TraceResult.erase_sortSliceKeysWrite]
  rw [memmove_backward_eq]
  cases hshift : SortSlice.memmoveBackward? (ok - position) slice
    (base + Int.ofNat (position + 1)) (base + Int.ofNat position) with
  | none => simp
  | some shifted =>
    have hshift' :
      SortSlice.memmoveBackward? (ok - position) slice
        (base + (position : Int) + 1) (base + (position : Int)) =
        some shifted := by
      simpa [Int.ofNat_eq_natCast, add_assoc] using hshift
    have hshift'' :
      SortSlice.memmoveBackward? (ok - position) slice
        (base + ((position : Int) + 1)) (base + (position : Int)) =
        some shifted := by
      simpa [add_assoc] using hshift'
    cases hwrite : shifted.write? (base + Int.ofNat position) pivot with
    | none =>
      have hwrite' : shifted.write? (base + (position : Int)) pivot = none := by
        simpa [Int.ofNat_eq_natCast] using hwrite
      simp [hwrite']
    | some inserted =>
      have hwrite' :
        shifted.write? (base + (position : Int)) pivot = some inserted := by
        simpa [Int.ofNat_eq_natCast] using hwrite
      cases valuesPresent
      · simp [hwrite']
      · have hpivot' :
        slice.read? (base + (ok : Int)) = some pivot := by
        simpa [Int.ofNat_eq_natCast] using hpivot
        simp [hpivot', hshift'', hwrite']

end CPythonListsort

namespace CPythonListsort

/--
[erase_binarysortLoopTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma erase_binarysortLoopTraced
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {state : MergeState κ ν}
  {slice : SortSlice κ ν}
  {base : Int}
  {n ok : Nat} :
-- imply
  (binarysortLoopTraced? fuel state slice base n ok).erase = binarysortLoop? fuel state slice base n ok := by
-- proof
  induction fuel generalizing slice ok with
  | zero =>
    by_cases hactive : ok < n <;>
      simp [binarysortLoopTraced?, binarysortLoop?, hactive]
  | succ fuel ih =>
    by_cases hactive : ok < n
    · rw [binarysortLoopTraced?, binarysortLoop?, if_pos hactive,
      if_pos hactive]
      simp only [TraceResult.erase_bind,
        TraceResult.erase_sortSliceKeysRead]
      cases hpivot : slice.read? (base + Int.ofNat ok) with
      | none => simp [binarysortBindOptionAcross]
      | some pivot =>
        simp only [Option.bind_some, binarysortBindOptionAcross]
        rw [erase_binarysortSearchTraced]
        cases hsearch : binarysortSearch? (ok + 1) state.key_compare slice
          base pivot 0 ok with
        | none => simp
        | some search =>
          simp only [Option.bind_some]
          cases hexhausted : search.fuelExhausted
          · simp only [Bool.false_eq_true, if_false,
            TraceResult.erase_bind]
            rw [erase_binarysortShiftInsertTraced_of_pivot _ _ _ _ _ _
              hpivot]
            simp [ih, Option.bind_assoc]
          · simp
    · simp [binarysortLoopTraced?, binarysortLoop?, hactive]

end CPythonListsort

namespace CPythonListsort

/--
[erase_binarysortTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma erase_binarysortTraced
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {slice : SortSlice κ ν}
  {base : Int}
  {n ok : Nat} :
-- imply
  (binarysortTraced? state slice base n ok).erase = binarysort? state slice base n ok := by
-- proof
  unfold binarysortTraced? binarysort?
  by_cases hadmitted : 1 ≤ n ∧ ok ≤ n ∧ n ≤ MAX_MINRUN.toNat
  · simp [hadmitted, erase_binarysortLoopTraced]
  · simp [hadmitted]

end CPythonListsort

namespace CPythonListsort.BinarysortTraceSafe

/--
[bind_result_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma bind_result_of_eq_some
  {κ : Type u}
  {ν : Type v}
  {current : TraceResult α}
  {next : α → TraceResult β}
  {value : α}
-- given
  (hresult : current.result = some value) :
-- imply
  (current.bind next).result = (next value).result := by
-- proof
  change (current.bind next).erase = (next value).erase
  rw [TraceResult.erase_bind]
  change current.result.bind (fun item => (next item).result) = _
  rw [hresult]
  rfl

end CPythonListsort.BinarysortTraceSafe

namespace CPythonListsort.BinarysortTraceSafe

/--
[pure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma pure
  {κ : Type u}
  {ν : Type v}
  {value : α} :
-- imply
  BinarysortTraceSafe (TraceResult.pure value) := by
-- proof
  exact
    { fuel := rfl
      noPushes := rfl
      bounds := AccessTrace.allAccessesInBounds_empty
      tempLive := AccessTrace.tempPayloadAccessesLive_empty }

end CPythonListsort.BinarysortTraceSafe

namespace CPythonListsort.BinarysortTraceSafe

/--
[bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma bind
  {κ : Type u}
  {ν : Type v}
  {current : TraceResult α}
  {next : α → TraceResult β}
  {value : α}
-- given
  (hresult : current.result = some value)
  (hcurrent : BinarysortTraceSafe current)
  (hnext : BinarysortTraceSafe (next value)) :
-- imply
  BinarysortTraceSafe (current.bind next) := by
-- proof
  constructor
  · simp [TraceResult.trace_bind, hresult, hcurrent.fuel, hnext.fuel]
  · simp [TraceResult.trace_bind, hresult, AccessTrace.compose,
    hcurrent.noPushes, hnext.noPushes]
  · rw [TraceResult.trace_bind, hresult,
    AccessTrace.allAccessesInBounds_compose]
    exact ⟨hcurrent.bounds, hnext.bounds⟩
  · rw [TraceResult.trace_bind, hresult,
    AccessTrace.tempPayloadAccessesLive_compose]
    exact ⟨hcurrent.tempLive, hnext.tempLive⟩

end CPythonListsort.BinarysortTraceSafe

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[keysRead_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma keysRead_safe (slice : SortSlice κ ν) (index : Int)
  (hindex : SortSlice.IndexInBounds slice index) :
  BinarysortTraceSafe (TraceResult.sortSliceKeysRead? slice index) := by
  constructor
  · simp [TraceResult.trace_sortSliceKeysRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceKeysRead, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_sortSliceKeysRead]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds, SortSlice.IndexInBounds] using hindex
  · simp [TraceResult.trace_sortSliceKeysRead,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[valuesRead_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma valuesRead_safe (slice : SortSlice κ ν) (index : Int)
  (hindex : SortSlice.IndexInBounds slice index) :
  BinarysortTraceSafe (TraceResult.sortSliceValuesRead? slice index) := by
  constructor
  · simp [TraceResult.trace_sortSliceValuesRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceValuesRead, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_sortSliceValuesRead]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds, SortSlice.IndexInBounds] using hindex
  · simp [TraceResult.trace_sortSliceValuesRead,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[keysWrite_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma keysWrite_safe (slice : SortSlice κ ν) (index : Int)
  (entry : SortSliceEntry κ ν)
  (hindex : SortSlice.IndexInBounds slice index) :
  BinarysortTraceSafe (TraceResult.sortSliceKeysWrite? slice index entry) := by
  constructor
  · simp [TraceResult.trace_sortSliceKeysWrite, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceKeysWrite, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_sortSliceKeysWrite]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds, SortSlice.IndexInBounds] using hindex
  · simp [TraceResult.trace_sortSliceKeysWrite,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[valuesWrite_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma valuesWrite_safe (slice : SortSlice κ ν) (index : Int)
  (entry : SortSliceEntry κ ν)
  (hindex : SortSlice.IndexInBounds slice index) :
  BinarysortTraceSafe (TraceResult.sortSliceValuesWrite? slice index entry) := by
  constructor
  · simp [TraceResult.trace_sortSliceValuesWrite, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceValuesWrite, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_sortSliceValuesWrite]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds, SortSlice.IndexInBounds] using hindex
  · simp [TraceResult.trace_sortSliceValuesWrite,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

end CPythonListsort

namespace CPythonListsort.BinarysortTraceMetadata

variable {κ : Type u} {ν : Type v}
/--
[pure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma pure (value : α) :
  BinarysortTraceMetadata (TraceResult.pure value) :=
⟨rfl, rfl, AccessTrace.tempPayloadAccessesLive_empty⟩

end CPythonListsort.BinarysortTraceMetadata

namespace CPythonListsort.BinarysortTraceMetadata

variable {κ : Type u} {ν : Type v}
/--
[keysRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma keysRead (slice : SortSlice κ ν) (index : Int) :
  BinarysortTraceMetadata (TraceResult.sortSliceKeysRead? slice index) := by
  constructor
  · simp [TraceResult.trace_sortSliceKeysRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceKeysRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceKeysRead,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

end CPythonListsort.BinarysortTraceMetadata

namespace CPythonListsort.BinarysortTraceMetadata

variable {κ : Type u} {ν : Type v}
/--
[valuesRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma valuesRead (slice : SortSlice κ ν) (index : Int) :
  BinarysortTraceMetadata (TraceResult.sortSliceValuesRead? slice index) := by
  constructor
  · simp [TraceResult.trace_sortSliceValuesRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceValuesRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceValuesRead,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

end CPythonListsort.BinarysortTraceMetadata

namespace CPythonListsort.BinarysortTraceMetadata

variable {κ : Type u} {ν : Type v}
/--
[keysWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma keysWrite (slice : SortSlice κ ν) (index : Int)
  (entry : SortSliceEntry κ ν) :
  BinarysortTraceMetadata
    (TraceResult.sortSliceKeysWrite? slice index entry) := by
  constructor
  · simp [TraceResult.trace_sortSliceKeysWrite, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceKeysWrite, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceKeysWrite,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

end CPythonListsort.BinarysortTraceMetadata

namespace CPythonListsort.BinarysortTraceMetadata

variable {κ : Type u} {ν : Type v}
/--
[valuesWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma valuesWrite (slice : SortSlice κ ν) (index : Int)
  (entry : SortSliceEntry κ ν) :
  BinarysortTraceMetadata
    (TraceResult.sortSliceValuesWrite? slice index entry) := by
  constructor
  · simp [TraceResult.trace_sortSliceValuesWrite, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceValuesWrite, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceValuesWrite,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

end CPythonListsort.BinarysortTraceMetadata

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[indexInBounds_of_range_offset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma indexInBounds_of_range_offset
  (slice : SortSlice κ ν) (base : Int) (n offset : Nat)
  (hrange : SortSlice.RangeInBounds slice base n)
  (hoffset : offset < n) :
  SortSlice.IndexInBounds slice (base + Int.ofNat offset) := by
  obtain ⟨hbase, hend⟩ := hrange
  constructor
  · exact add_nonneg hbase (Int.natCast_nonneg _)
  · have hoffsetInt : Int.ofNat offset < Int.ofNat n :=
    (Int.ofNat_lt).2 hoffset
    omega

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[read_result_of_indexInBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma read_result_of_indexInBounds (slice : SortSlice κ ν)
  (index : Int) (hindex : SortSlice.IndexInBounds slice index) :
  ∃ entry,
    (TraceResult.sortSliceKeysRead? slice index).result = some entry ∧
      slice.read? index = some entry := by
  rcases SortSlice.read_eq_some_of_indexInBounds slice index hindex with
    ⟨entry, hread⟩
  refine ⟨entry, ?_, hread⟩
  change (TraceResult.sortSliceKeysRead? slice index).erase = some entry
  simpa using hread

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[shiftSourceRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma shiftSourceRange
  (slice : SortSlice κ ν) (base : Int) (n ok position : Nat)
  (hrange : SortSlice.RangeInBounds slice base n)
  (hposition : position ≤ ok) (hok : ok ≤ n) :
  SortSlice.RangeInBounds slice (base + Int.ofNat position)
    (ok - position) := by
  obtain ⟨hbase, hend⟩ := hrange
  constructor
  · exact add_nonneg hbase (Int.natCast_nonneg _)
  · have hsumNat : position + (ok - position) = ok :=
    Nat.add_sub_of_le hposition
    have hsumInt :
      Int.ofNat position + Int.ofNat (ok - position) = Int.ofNat ok := by
      simpa using congrArg Int.ofNat hsumNat
    have hokn : Int.ofNat ok ≤ Int.ofNat n := (Int.ofNat_le).2 hok
    calc
      base + Int.ofNat position + Int.ofNat (ok - position) =
        base + Int.ofNat ok := by rw [add_assoc, hsumInt]
      _ ≤ base + Int.ofNat n := by
        simpa [add_comm] using add_le_add_left hokn base
      _ ≤ Int.ofNat slice.entries.size := hend

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[shiftDestinationRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma shiftDestinationRange
  (slice : SortSlice κ ν) (base : Int) (n ok position : Nat)
  (hrange : SortSlice.RangeInBounds slice base n)
  (hposition : position ≤ ok) (hok : ok < n) :
  SortSlice.RangeInBounds slice (base + Int.ofNat (position + 1))
    (ok - position) := by
  obtain ⟨hbase, hend⟩ := hrange
  constructor
  · exact add_nonneg hbase (Int.natCast_nonneg _)
  · have hsumNat : position + 1 + (ok - position) = ok + 1 := by omega
    have hsumInt :
      Int.ofNat (position + 1) + Int.ofNat (ok - position) =
        Int.ofNat (ok + 1) := by
      simpa using congrArg Int.ofNat hsumNat
    have hokn : Int.ofNat (ok + 1) ≤ Int.ofNat n :=
      (Int.ofNat_le).2 (Nat.succ_le_iff.mpr hok)
    calc
      base + Int.ofNat (position + 1) + Int.ofNat (ok - position) =
        base + Int.ofNat (ok + 1) := by rw [add_assoc, hsumInt]
      _ ≤ base + Int.ofNat n := by
        simpa [add_comm] using add_le_add_left hokn base
      _ ≤ Int.ofNat slice.entries.size := hend

end CPythonListsort

namespace CPythonListsort

/--
[binarysort_midpoint_callsite_geometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma binarysort_midpoint_callsite_geometry
  {κ : Type u}
  {ν : Type v}
  {slice : SortSlice κ ν}
  {base : Int}
  {n left right fuel : Nat}
-- given
  (hrange : SortSlice.RangeInBounds slice base n)
  (hactive : left < right)
  (hright : right ≤ n)
  (hnMax : n ≤ MAX_MINRUN.toNat)
  (hwidth : right - left ≤ fuel + 1) :
-- imply
  let middle := (left + right) / 2 left ≤ middle ∧ middle < right ∧ SortSlice.IndexInBounds slice (base + Int.ofNat middle) ∧ middle - left ≤ fuel ∧ right - (middle + 1) ≤ fuel ∧ left + right ≤ 2 * MAX_MINRUN.toNat ∧ left + right ≤ PY_SSIZE_T_MAX := by
-- proof
  dsimp only
  have hmiddleLower : left ≤ (left + right) / 2 := by omega
  have hmiddleUpper : (left + right) / 2 < right := by omega
  have hsumSmall : left + right ≤ 2 * MAX_MINRUN.toNat := by omega
  have hsumWord : left + right ≤ PY_SSIZE_T_MAX := by
    apply hsumSmall.trans
    have hmaxMinrun : MAX_MINRUN.toNat = 64 := by decide
    rw [hmaxMinrun]
    norm_num [PY_SSIZE_T_MAX]
  refine ⟨hmiddleLower, hmiddleUpper, ?_, by omega, by omega, hsumSmall,
    hsumWord⟩
  exact indexInBounds_of_range_offset slice base n ((left + right) / 2)
    hrange (lt_of_lt_of_le hmiddleUpper hright)

end CPythonListsort

namespace CPythonListsort

/--
[binarysort_shift_callsite_geometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma binarysort_shift_callsite_geometry
  {κ : Type u}
  {ν : Type v}
  {slice : SortSlice κ ν}
  {base : Int}
  {n ok position : Nat}
-- given
  (hrange : SortSlice.RangeInBounds slice base n)
  (hposition : position ≤ ok)
  (hok : ok < n) :
-- imply
  SortSlice.RangeInBounds slice (base + Int.ofNat position) (ok - position) ∧ SortSlice.RangeInBounds slice (base + Int.ofNat (position + 1)) (ok - position) ∧ SortSlice.IndexInBounds slice (base + Int.ofNat position) ∧ SortSlice.IndexInBounds slice (base + Int.ofNat ok) := by
-- proof
  exact
    ⟨shiftSourceRange slice base n ok position hrange hposition hok.le,
      shiftDestinationRange slice base n ok position hrange hposition hok,
      indexInBounds_of_range_offset slice base n position hrange
        (lt_of_le_of_lt hposition hok),
      indexInBounds_of_range_offset slice base n ok hrange hok⟩

end CPythonListsort

namespace CPythonListsort

/--
[binarysortKeyShiftTraced_high_to_low](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma binarysortKeyShiftTraced_high_to_low
  {κ : Type u}
  {ν : Type v}
  {count : Nat}
  {slice : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : SortSlice.RangeInBounds slice dst (count + 1))
  (hsrc : SortSlice.RangeInBounds slice src (count + 1)) :
-- imply
  ∃ first, (SortSlice.copyKeysFromTraced? slice slice (dst + Int.ofNat count) (src + Int.ofNat count)).result = some first ∧ (SortSlice.memmoveBackwardKeysTraced? (count + 1) slice dst src).trace.accesses = SortSlice.keyCopyAccesses slice.entries.size slice.entries.size (dst + Int.ofNat count) (src + Int.ofNat count) ++ (SortSlice.memmoveBackwardKeysTraced? count first dst src).trace.accesses := by
-- proof
  have hdstLast := hdst.last
  have hsrcLast := hsrc.last
  rcases SortSlice.copyFrom_eq_some_of_bounds slice slice
    (dst + Int.ofNat count) (src + Int.ofNat count) hdstLast hsrcLast with
    ⟨first, hcopy⟩
  have hfirst :
    (SortSlice.copyKeysFromTraced? slice slice
      (dst + Int.ofNat count) (src + Int.ofNat count)).result = some first := by
    change (SortSlice.copyKeysFromTraced? slice slice
      (dst + Int.ofNat count) (src + Int.ofNat count)).erase = some first
    simpa using hcopy
  refine ⟨first, hfirst, ?_⟩
  simp only [SortSlice.memmoveBackwardKeysTraced?, TraceResult.trace_bind,
    hfirst, AccessTrace.compose]
  rw [SortSlice.copyKeysFromTraced_accesses slice slice
    (dst + Int.ofNat count) (src + Int.ofNat count) hdstLast hsrcLast]

end CPythonListsort

namespace CPythonListsort

/--
[binarysortValuesShiftTraced_high_to_low](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma binarysortValuesShiftTraced_high_to_low
  {κ : Type u}
  {ν : Type v}
  {count : Nat}
  {slice : SortSlice κ ν}
  {dst src : Int}
-- given
  (hdst : SortSlice.RangeInBounds slice dst (count + 1))
  (hsrc : SortSlice.RangeInBounds slice src (count + 1)) :
-- imply
  ∃ first, (SortSlice.copyValuesFromTraced? slice slice (dst + Int.ofNat count) (src + Int.ofNat count)).result = some first ∧ (SortSlice.memmoveBackwardValuesTraced? (count + 1) slice dst src).trace.accesses = SortSlice.valuesCopyAccesses slice.entries.size slice.entries.size (dst + Int.ofNat count) (src + Int.ofNat count) ++ (SortSlice.memmoveBackwardValuesTraced? count first dst src).trace.accesses := by
-- proof
  have hdstLast := hdst.last
  have hsrcLast := hsrc.last
  rcases SortSlice.copyFrom_eq_some_of_bounds slice slice
    (dst + Int.ofNat count) (src + Int.ofNat count) hdstLast hsrcLast with
    ⟨first, hcopy⟩
  have hfirst :
    (SortSlice.copyValuesFromTraced? slice slice
      (dst + Int.ofNat count) (src + Int.ofNat count)).result = some first := by
    change (SortSlice.copyValuesFromTraced? slice slice
      (dst + Int.ofNat count) (src + Int.ofNat count)).erase = some first
    simpa using hcopy
  refine ⟨first, hfirst, ?_⟩
  simp only [SortSlice.memmoveBackwardValuesTraced?, TraceResult.trace_bind,
    hfirst, AccessTrace.compose]
  rw [SortSlice.copyValuesFromTraced_accesses slice slice
    (dst + Int.ofNat count) (src + Int.ofNat count) hdstLast hsrcLast]

end CPythonListsort

namespace CPythonListsort

/--
[binarysortSearchTraced_zero_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma binarysortSearchTraced_zero_active
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {slice : SortSlice κ ν}
  {base : Int}
  {pivot : SortSliceEntry κ ν}
  {left right : Nat}
-- given
  (hactive : left < right) :
-- imply
  (binarysortSearchTraced? 0 lt slice base pivot left right).result.map (fun result => result.fuelExhausted) = some true ∧ (binarysortSearchTraced? 0 lt slice base pivot left right).trace.fuelExhausted = true := by
-- proof
  simp [binarysortSearchTraced?, hactive, TraceResult.pure,
    TraceResult.markFuelExhausted, AccessTrace.compose, AccessTrace.exhausted]

end CPythonListsort

namespace CPythonListsort

/--
[binarysortLoopTraced_zero_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma binarysortLoopTraced_zero_active
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {slice : SortSlice κ ν}
  {base : Int}
  {n ok : Nat}
-- given
  (hactive : ok < n) :
-- imply
  (binarysortLoopTraced? 0 state slice base n ok).result.map (fun result => result.fuelExhausted) = some true ∧ (binarysortLoopTraced? 0 state slice base n ok).trace.fuelExhausted = true := by
-- proof
  simp [binarysortLoopTraced?, hactive, TraceResult.pure,
    TraceResult.markFuelExhausted, AccessTrace.compose, AccessTrace.exhausted]

end CPythonListsort

namespace CPythonListsort

/--
[binarysort_singleton_ok_zero_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma binarysort_singleton_ok_zero_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (binarysortTraced? binarysortSingletonRegressionState binarysortSingletonRegressionSlice 0 1 0).result.map (fun result => (result.fuelExhausted, result.slice.entries.toList)) = some (false, binarysortSingletonRegressionSlice.entries.toList) ∧ (binarysortTraced? binarysortSingletonRegressionState binarysortSingletonRegressionSlice 0 1 0).trace = AccessTrace.empty := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[binarysort_pair_ok_zero_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma binarysort_pair_ok_zero_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (binarysortTraced? binarysortPairRegressionState binarysortPairRegressionSlice 0 2 0).result.map (fun result => (result.fuelExhausted, result.slice.entries.toList)) = some (false, [{ key := 1, value := some 10 }, { key := 2, value := some 20 }]) ∧ (binarysortTraced? binarysortPairRegressionState binarysortPairRegressionSlice 0 2 0).trace.accesses = [{ kind := .read, region := .inputKeys, index := 1, extent := 2 }, { kind := .read, region := .inputKeys, index := 0, extent := 2 }, { kind := .read, region := .inputKeys, index := 0, extent := 2 }, { kind := .write, region := .inputKeys, index := 1, extent := 2 }, { kind := .write, region := .inputKeys, index := 0, extent := 2 }, { kind := .read, region := .synchronizedValues, index := 1, extent := 2 }, { kind := .read, region := .synchronizedValues, index := 0, extent := 2 }, { kind := .write, region := .synchronizedValues, index := 1, extent := 2 }, { kind := .write, region := .synchronizedValues, index := 0, extent := 2 }] := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[binarysort_oob_attempted_read_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma binarysort_oob_attempted_read_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (binarysortTraced? binarysortSingletonRegressionState binarysortSingletonRegressionSlice 0 2 1).result = none ∧ (binarysortTraced? binarysortSingletonRegressionState binarysortSingletonRegressionSlice 0 2 1).trace.accesses = [{ kind := .read, region := .inputKeys, index := 1, extent := 1 }] ∧ ¬(binarysortTraced? binarysortSingletonRegressionState binarysortSingletonRegressionSlice 0 2 1).trace.allAccessesInBounds := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[binarysort_unkeyed_no_values_trace_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma binarysort_unkeyed_no_values_trace_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (binarysortTraced? binarysortUnkeyedRegressionState binarysortUnkeyedRegressionSlice 0 2 0).result.map (fun result => (result.fuelExhausted, result.slice.entries.toList)) = some (false, [{ key := 1, value := none }, { key := 2, value := none }]) ∧ (binarysortTraced? binarysortUnkeyedRegressionState binarysortUnkeyedRegressionSlice 0 2 0).trace.accesses = [{ kind := .read, region := .inputKeys, index := 1, extent := 2 }, { kind := .read, region := .inputKeys, index := 0, extent := 2 }, { kind := .read, region := .inputKeys, index := 0, extent := 2 }, { kind := .write, region := .inputKeys, index := 1, extent := 2 }, { kind := .write, region := .inputKeys, index := 0, extent := 2 }] := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[binarysort_insert_front_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma binarysort_insert_front_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (binarysortShiftInsertTraced? true binarysortRegressionSlice 0 2 0 { key := 1, value := some 10 }).result.map (·.entries.toList) = some [{ key := 1, value := some 10 }, { key := 3, value := some 30 }, { key := 4, value := some 40 }] ∧ (binarysortShiftInsertTraced? true binarysortRegressionSlice 0 2 0 { key := 1, value := some 10 }).trace.accesses = [{ kind := .read, region := .inputKeys, index := 1, extent := 3 }, { kind := .write, region := .inputKeys, index := 2, extent := 3 }, { kind := .read, region := .inputKeys, index := 0, extent := 3 }, { kind := .write, region := .inputKeys, index := 1, extent := 3 }, { kind := .write, region := .inputKeys, index := 0, extent := 3 }, { kind := .read, region := .synchronizedValues, index := 2, extent := 3 }, { kind := .read, region := .synchronizedValues, index := 1, extent := 3 }, { kind := .write, region := .synchronizedValues, index := 2, extent := 3 }, { kind := .read, region := .synchronizedValues, index := 0, extent := 3 }, { kind := .write, region := .synchronizedValues, index := 1, extent := 3 }, { kind := .write, region := .synchronizedValues, index := 0, extent := 3 }] := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[binarysort_insert_end_no_shift_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma binarysort_insert_end_no_shift_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (binarysortShiftInsertTraced? true binarysortEqualRegressionSlice 0 2 2 { key := 2, value := some 21 }).result = some binarysortEqualRegressionSlice ∧ (binarysortShiftInsertTraced? true binarysortEqualRegressionSlice 0 2 2 { key := 2, value := some 21 }).trace.accesses = [{ kind := .write, region := .inputKeys, index := 2, extent := 3 }, { kind := .read, region := .synchronizedValues, index := 2, extent := 3 }, { kind := .write, region := .synchronizedValues, index := 2, extent := 3 }] := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[binarysort_equal_pivot_stability_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma binarysort_equal_pivot_stability_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (binarysortSearchTraced? 4 binarysortTaggedEqualRegressionState.key_compare binarysortTaggedEqualRegressionSlice 0 { key := 1, value := some 12 } 0 3).result.map (fun result => (result.position, result.fuelExhausted)) = some (2, false) ∧ (binarysortTraced? binarysortTaggedEqualRegressionState binarysortTaggedEqualRegressionSlice 0 4 3).result.map (fun result => (result.fuelExhausted, result.slice.entries.toList)) = some (false, [{ key := 1, value := some 10 }, { key := 1, value := some 11 }, { key := 1, value := some 12 }, { key := 2, value := some 20 }]) := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[binarysort_invalid_guard_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma binarysort_invalid_guard_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (binarysortTraced? binarysortSingletonRegressionState binarysortSingletonRegressionSlice 0 0 0).result = none ∧ (binarysortTraced? binarysortSingletonRegressionState binarysortSingletonRegressionSlice 0 0 0).trace = AccessTrace.empty := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[binarysort_zero_fuel_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
lemma binarysort_zero_fuel_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (binarysortSearchTraced? 0 binarysortRegressionState.key_compare binarysortEqualRegressionSlice 0 { key := 2, value := some 21 } 0 1).result.map (·.fuelExhausted) = some true ∧ (binarysortSearchTraced? 0 binarysortRegressionState.key_compare binarysortEqualRegressionSlice 0 { key := 2, value := some 21 } 0 1).trace.fuelExhausted = true ∧ (binarysortLoopTraced? 0 binarysortRegressionState binarysortEqualRegressionSlice 0 1 0).result.map (·.fuelExhausted) = some true ∧ (binarysortLoopTraced? 0 binarysortRegressionState binarysortEqualRegressionSlice 0 1 0).trace.fuelExhausted = true := by
-- proof
  decide

end CPythonListsort

/--
[binarysortSearchTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma binarysortSearchTraced_safe_eq
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {slice : SortSlice κ ν}
  {base : Int}
  {pivot : SortSliceEntry κ ν}
  {left right n : Nat}
-- given
  (hrange : SortSlice.RangeInBounds slice base n)
  (hle : left ≤ right)
  (hright : right ≤ n)
  (hwidth : right - left ≤ fuel) :
-- imply
  ∃ result, BinarysortSearchSafetyPost fuel lt slice base pivot left right result := by
-- proof
  apply CPythonListsort.binarysortSearchTraced_safe fuel lt slice base pivot left right n hrange hle hright hwidth

/--
[binarysortShiftInsertTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma binarysortShiftInsertTraced_safe_eq
  {κ : Type u}
  {ν : Type v}
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {base : Int}
  {n ok position : Nat}
  {pivot : SortSliceEntry κ ν}
-- given
  (hrange : SortSlice.RangeInBounds slice base n)
  (hposition : position ≤ ok)
  (hok : ok < n)
  (hmode : SortSlice.ValuesModeInvariant valuesPresent slice)
  (hpivot : slice.read? (base + Int.ofNat ok) = some pivot) :
-- imply
  ∃ after, BinarysortShiftInsertSafetyPost valuesPresent slice base n ok position pivot after := by
-- proof
  apply CPythonListsort.binarysortShiftInsertTraced_safe valuesPresent slice base n ok position pivot hrange hposition hok hmode hpivot

/--
[binarysort_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma binarysort_safe_eq
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {slice : SortSlice κ ν}
  {base : Int}
  {n ok : Nat}
-- given
  (hnPositive : 1 ≤ n)
  (hok : ok ≤ n)
  (hnMax : n ≤ MAX_MINRUN.toNat)
  (hrange : SortSlice.RangeInBounds slice base n)
  (hmode : SortSlice.ValuesModeInvariant state.a.hasValues slice) :
-- imply
  ∃ result, BinarysortSafetyPost state slice base n ok result := by
-- proof
  apply CPythonListsort.binarysort_safe state slice base n ok hnPositive hok hnMax hrange hmode

/--
[binarysortSearchTraced_step_trace_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma binarysortSearchTraced_step_trace_order_eq
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {lt : BoolComparator κ}
  {slice : SortSlice κ ν}
  {base : Int}
  {pivot entry : SortSliceEntry κ ν}
  {left right : Nat}
-- given
  (hactive : left < right)
  (hread : (TraceResult.sortSliceKeysRead? slice (base + Int.ofNat ((left + right) / 2))).result = some entry) :
-- imply
  (binarysortSearchTraced? (fuel + 1) lt slice base pivot left right).trace = (TraceResult.sortSliceKeysRead? slice (base + Int.ofNat ((left + right) / 2))).trace.compose (if iflt lt pivot.key entry.key then (binarysortSearchTraced? fuel lt slice base pivot left ((left + right) / 2)).trace else (binarysortSearchTraced? fuel lt slice base pivot ((left + right) / 2 + 1) right).trace) := by
-- proof
  apply CPythonListsort.binarysortSearchTraced_step_trace_order fuel lt slice base pivot entry left right hactive hread

/--
[binarysortShiftInsertTraced_values_phase_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma binarysortShiftInsertTraced_values_phase_order_eq
  {κ : Type u}
  {ν : Type v}
  {slice keyShifted keyResult valueShifted : SortSlice κ ν}
  {base : Int}
  {ok position : Nat}
  {pivot valuePivot : SortSliceEntry κ ν}
-- given
  (hkeyShift : (SortSlice.memmoveBackwardKeysTraced? (ok - position) slice (base + Int.ofNat (position + 1)) (base + Int.ofNat position)).result = some keyShifted)
  (hkeyWrite : (TraceResult.sortSliceKeysWrite? keyShifted (base + Int.ofNat position) pivot).result = some keyResult)
  (hvalueRead : (TraceResult.sortSliceValuesRead? slice (base + Int.ofNat ok)).result = some valuePivot)
  (hvalueShift : (SortSlice.memmoveBackwardValuesTraced? (ok - position) slice (base + Int.ofNat (position + 1)) (base + Int.ofNat position)).result = some valueShifted) :
-- imply
  (binarysortShiftInsertTraced? true slice base ok position pivot).trace = (SortSlice.memmoveBackwardKeysTraced? (ok - position) slice (base + Int.ofNat (position + 1)) (base + Int.ofNat position)).trace.compose ((TraceResult.sortSliceKeysWrite? keyShifted (base + Int.ofNat position) pivot).trace.compose ((TraceResult.sortSliceValuesRead? slice (base + Int.ofNat ok)).trace.compose ((SortSlice.memmoveBackwardValuesTraced? (ok - position) slice (base + Int.ofNat (position + 1)) (base + Int.ofNat position)).trace.compose (TraceResult.sortSliceValuesWrite? valueShifted (base + Int.ofNat position) valuePivot).trace))) := by
-- proof
  apply CPythonListsort.binarysortShiftInsertTraced_values_phase_order slice keyShifted keyResult valueShifted base ok position pivot valuePivot hkeyShift hkeyWrite hvalueRead hvalueShift

/--
[binarysortLoopTraced_iteration_trace_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean)
-/
@[path]
private lemma binarysortLoopTraced_iteration_trace_order_eq
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {state : MergeState κ ν}
  {slice updated : SortSlice κ ν}
  {base : Int}
  {n ok : Nat}
  {pivot : SortSliceEntry κ ν}
  {search : BinarySearchResult}
-- given
  (hpivot : (TraceResult.sortSliceKeysRead? slice (base + Int.ofNat ok)).result = some pivot)
  (hsearch : (binarysortSearchTraced? (ok + 1) state.key_compare slice base pivot 0 ok).result = some search)
  (hsearchFuel : search.fuelExhausted = false)
  (hshift : (binarysortShiftInsertTraced? state.a.hasValues slice base ok search.position pivot).result = some updated)
  (hactive : ok < n) :
-- imply
  (binarysortLoopTraced? (fuel + 1) state slice base n ok).trace = (TraceResult.sortSliceKeysRead? slice (base + Int.ofNat ok)).trace.compose ((binarysortSearchTraced? (ok + 1) state.key_compare slice base pivot 0 ok).trace.compose ((binarysortShiftInsertTraced? state.a.hasValues slice base ok search.position pivot).trace.compose (binarysortLoopTraced? fuel state updated base n (ok + 1)).trace)) := by
-- proof
  apply CPythonListsort.binarysortLoopTraced_iteration_trace_order fuel state slice updated base n ok pivot search hpivot hsearch hsearchFuel hshift hactive


-- created on 2026-10-23
