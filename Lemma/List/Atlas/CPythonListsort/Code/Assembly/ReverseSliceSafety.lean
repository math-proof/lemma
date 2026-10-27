import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.CPythonListsort.Code.Assembly.ReverseSliceSafety.Part2
open CPythonListsort CPythonListsort.ReverseSlicePhase


namespace CPythonListsort.ReverseSlicePhase

/--
[erase_readTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
lemma erase_readTraced
  {κ : Type u}
  {ν : Type v}
  {phase : ReverseSlicePhase}
  {slice : SortSlice κ ν}
  {index : Int} :
-- imply
  (phase.readTraced? slice index).erase = slice.read? index := by
-- proof
  cases phase <;> rfl

end CPythonListsort.ReverseSlicePhase

namespace CPythonListsort.ReverseSlicePhase

/--
[erase_writeTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
lemma erase_writeTraced
  {κ : Type u}
  {ν : Type v}
  {phase : ReverseSlicePhase}
  {slice : SortSlice κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν} :
-- imply
  (phase.writeTraced? slice index entry).erase = slice.write? index entry := by
-- proof
  cases phase <;> rfl

end CPythonListsort.ReverseSlicePhase

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[reverseSlicePhaseRead_memoryEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
private lemma reverseSlicePhaseRead_memoryEvents_eq_nil
  (phase : ReverseSlicePhase) (slice : SortSlice κ ν) (index : Int) :
  (phase.readTraced? slice index).trace.memoryEvents = [] := by
  cases phase <;> rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[reverseSlicePhaseWrite_memoryEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
private lemma reverseSlicePhaseWrite_memoryEvents_eq_nil
  (phase : ReverseSlicePhase) (slice : SortSlice κ ν) (index : Int)
  (entry : SortSliceEntry κ ν) :
  (phase.writeTraced? slice index entry).trace.memoryEvents = [] := by
  cases phase <;> rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[reverseSlicePhaseLoopTraced_memoryEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
private lemma reverseSlicePhaseLoopTraced_memoryEvents_eq_nil
  (fuel : Nat) (phase : ReverseSlicePhase) (slice : SortSlice κ ν)
  (lo hi : Int) :
  (reverseSlicePhaseLoopTraced? fuel phase slice lo hi).trace.memoryEvents =
    [] := by
  induction fuel generalizing slice lo hi with
  | zero =>
    by_cases hactive : lo < hi
    · simp [reverseSlicePhaseLoopTraced?, hactive,
      TraceResult.markFuelExhausted, TraceResult.pure,
      AccessTrace.empty, AccessTrace.compose, AccessTrace.exhausted]
    · simp [reverseSlicePhaseLoopTraced?, hactive, TraceResult.pure,
      AccessTrace.empty]
  | succ fuel ih =>
    rw [reverseSlicePhaseLoopTraced?]
    by_cases hactive : lo < hi
    · rw [if_pos hactive]
      apply TraceResult.memoryEvents_bind_eq_nil
      · exact reverseSlicePhaseRead_memoryEvents_eq_nil _ _ _
      · intro left
        apply TraceResult.memoryEvents_bind_eq_nil
        · exact reverseSlicePhaseRead_memoryEvents_eq_nil _ _ _
        · intro right
          apply TraceResult.memoryEvents_bind_eq_nil
          · exact reverseSlicePhaseWrite_memoryEvents_eq_nil _ _ _ _
          · intro afterLeft
            apply TraceResult.memoryEvents_bind_eq_nil
            · exact reverseSlicePhaseWrite_memoryEvents_eq_nil _ _ _ _
            · intro afterRight
              exact ih afterRight (lo + 1) (hi - 1)
    · rw [if_neg hactive]
      rfl

end CPythonListsort

namespace CPythonListsort

/--
[reverseSlicePhaseTraced_memoryEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
lemma reverseSlicePhaseTraced_memoryEvents_eq_nil
  {κ : Type u}
  {ν : Type v}
  {phase : ReverseSlicePhase}
  {slice : SortSlice κ ν}
-- given
  (lo hi : Int) :
-- imply
  (reverseSlicePhaseTraced? phase slice lo hi).trace.memoryEvents = [] := by
-- proof
  unfold reverseSlicePhaseTraced?
  by_cases hordered : lo ≤ hi
  · rw [if_pos hordered]
    by_cases hactive : lo < hi
    · rw [if_pos hactive]
      exact reverseSlicePhaseLoopTraced_memoryEvents_eq_nil _ _ _ _ _
    · rw [if_neg hactive]
      rfl
  · rw [if_neg hordered]
    rfl

end CPythonListsort

namespace CPythonListsort

/--
[sortsliceReverseTraced_memoryEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
lemma sortsliceReverseTraced_memoryEvents_eq_nil
  {κ : Type u}
  {ν : Type v}
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {base : Int}
  {n : Nat} :
-- imply
  (sortsliceReverseTraced? valuesPresent slice base n).trace.memoryEvents = [] := by
-- proof
  unfold sortsliceReverseTraced?
  apply TraceResult.memoryEvents_bind_eq_nil
  · exact reverseSlicePhaseTraced_memoryEvents_eq_nil _ _ _ _
  · intro keyResult
    cases valuesPresent
    · rfl
    · exact reverseSlicePhaseTraced_memoryEvents_eq_nil _ _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[reverseSlicePhaseLoopTraced_policyEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
private lemma reverseSlicePhaseLoopTraced_policyEvents_eq_nil
  (fuel : Nat) (phase : ReverseSlicePhase) (slice : SortSlice κ ν)
  (lo hi : Int) :
  (reverseSlicePhaseLoopTraced? fuel phase slice lo hi).trace.policyEvents =
    [] := by
  induction fuel generalizing slice lo hi with
  | zero =>
    by_cases hactive : lo < hi
    · simp [reverseSlicePhaseLoopTraced?, hactive,
      TraceResult.markFuelExhausted, TraceResult.pure,
      AccessTrace.empty, AccessTrace.compose, AccessTrace.exhausted]
    · simp [reverseSlicePhaseLoopTraced?, hactive, TraceResult.pure,
      AccessTrace.empty]
  | succ fuel ih =>
    rw [reverseSlicePhaseLoopTraced?]
    by_cases hactive : lo < hi
    · rw [if_pos hactive]
      apply TraceResult.policyEvents_bind_eq_nil
      · cases phase <;> rfl
      · intro left
        apply TraceResult.policyEvents_bind_eq_nil
        · cases phase <;> rfl
        · intro right
          apply TraceResult.policyEvents_bind_eq_nil
          · cases phase <;> rfl
          · intro afterLeft
            apply TraceResult.policyEvents_bind_eq_nil
            · cases phase <;> rfl
            · intro afterRight
              exact ih afterRight (lo + 1) (hi - 1)
    · rw [if_neg hactive]
      rfl

end CPythonListsort

namespace CPythonListsort

/--
[reverseSlicePhaseTraced_policyEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
lemma reverseSlicePhaseTraced_policyEvents_eq_nil
  {κ : Type u}
  {ν : Type v}
  {phase : ReverseSlicePhase}
  {slice : SortSlice κ ν}
-- given
  (lo hi : Int) :
-- imply
  (reverseSlicePhaseTraced? phase slice lo hi).trace.policyEvents = [] := by
-- proof
  unfold reverseSlicePhaseTraced?
  by_cases hordered : lo ≤ hi
  · rw [if_pos hordered]
    by_cases hactive : lo < hi
    · rw [if_pos hactive]
      exact reverseSlicePhaseLoopTraced_policyEvents_eq_nil _ _ _ _ _
    · rw [if_neg hactive]
      rfl
  · rw [if_neg hordered]
    rfl

end CPythonListsort

namespace CPythonListsort

/--
[sortsliceReverseTraced_policyEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
lemma sortsliceReverseTraced_policyEvents_eq_nil
  {κ : Type u}
  {ν : Type v}
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {base : Int}
  {n : Nat} :
-- imply
  (sortsliceReverseTraced? valuesPresent slice base n).trace.policyEvents = [] := by
-- proof
  unfold sortsliceReverseTraced?
  apply TraceResult.policyEvents_bind_eq_nil
  · exact reverseSlicePhaseTraced_policyEvents_eq_nil _ _ _ _
  · intro keyResult
    cases valuesPresent
    · rfl
    · exact reverseSlicePhaseTraced_policyEvents_eq_nil _ _ _ _

end CPythonListsort

namespace CPythonListsort

/--
[erase_reverseSlicePhaseLoopTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
lemma erase_reverseSlicePhaseLoopTraced
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {phase : ReverseSlicePhase}
  {slice : SortSlice κ ν}
-- given
  (lo hi : Int) :
-- imply
  (reverseSlicePhaseLoopTraced? fuel phase slice lo hi).erase = reverseSliceLoop? fuel slice lo hi := by
-- proof
  induction fuel generalizing slice lo hi with
  | zero =>
    by_cases h : lo < hi <;>
      simp [reverseSlicePhaseLoopTraced?, reverseSliceLoop?, h,
        reverseSliceResult]
  | succ fuel ih =>
    by_cases h : lo < hi
    · cases phase <;>
      simp [reverseSlicePhaseLoopTraced?, reverseSliceLoop?, h,
        TraceResult.erase_bind, ih]
    · simp [reverseSlicePhaseLoopTraced?, reverseSliceLoop?, h,
      reverseSliceResult]

end CPythonListsort

namespace CPythonListsort

/--
[erase_reverseSlicePhaseTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
lemma erase_reverseSlicePhaseTraced
  {κ : Type u}
  {ν : Type v}
  {phase : ReverseSlicePhase}
  {slice : SortSlice κ ν}
-- given
  (lo hi : Int) :
-- imply
  (reverseSlicePhaseTraced? phase slice lo hi).erase = reverseSlice? slice lo hi := by
-- proof
  unfold reverseSlicePhaseTraced? reverseSlice?
  by_cases hordered : lo ≤ hi
  · rw [if_pos hordered, if_pos hordered]
    by_cases hactive : lo < hi
    · rw [if_pos hactive, if_pos hactive]
      exact erase_reverseSlicePhaseLoopTraced _ _ _ _ _
    · rw [if_neg hactive, if_neg hactive]
      rfl
  · rw [if_neg hordered, if_neg hordered]
    rfl

end CPythonListsort

namespace CPythonListsort

/--
[erase_reverseSliceTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
lemma erase_reverseSliceTraced
  {κ : Type u}
  {ν : Type v}
  {slice : SortSlice κ ν}
-- given
  (lo hi : Int) :
-- imply
  (reverseSliceTraced? slice lo hi).erase = reverseSlice? slice lo hi := by
-- proof
  simp [reverseSliceTraced?]

end CPythonListsort

namespace CPythonListsort

/--
[erase_sortsliceReverseTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
lemma erase_sortsliceReverseTraced
  {κ : Type u}
  {ν : Type v}
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {base : Int}
  {n : Nat} :
-- imply
  (sortsliceReverseTraced? valuesPresent slice base n).erase = sortsliceReverse? slice base n := by
-- proof
  cases valuesPresent
  · simp [sortsliceReverseTraced?, sortsliceReverse?, TraceResult.erase_bind]
  · unfold sortsliceReverseTraced? sortsliceReverse?
    rw [TraceResult.erase_bind, erase_reverseSlicePhaseTraced]
    cases hresult : reverseSlice? slice base (base + Int.ofNat n) with
    | none => rfl
    | some result =>
      simp only [Option.bind_some, if_true, erase_reverseSlicePhaseTraced]
      exact hresult

end CPythonListsort

namespace CPythonListsort.ReverseTraceSafe

variable {κ : Type u} {ν : Type v}
/--
[pure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
private lemma pure (value : α) :
  ReverseTraceSafe (TraceResult.pure value) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact AccessTrace.allAccessesInBounds_empty
  · exact AccessTrace.tempPayloadAccessesLive_empty

end CPythonListsort.ReverseTraceSafe

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[reversePhaseRead_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
private lemma reversePhaseRead_safe (phase : ReverseSlicePhase)
  (slice : SortSlice κ ν) (index : Int)
  (hindex : SortSlice.IndexInBounds slice index) :
  ReverseTraceSafe (phase.readTraced? slice index) := by
  cases phase <;> constructor
  all_goals
    simp [ReverseSlicePhase.readTraced?, AccessTrace.singletonAccess,
      AccessTrace.allAccessesInBounds, AccessTrace.tempPayloadAccessesLive,
      AccessEvent.InBounds, AccessEvent.TempPayloadLive,
      SortSlice.IndexInBounds] at hindex ⊢
  all_goals aesop

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[reversePhaseWrite_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
private lemma reversePhaseWrite_safe (phase : ReverseSlicePhase)
  (slice : SortSlice κ ν) (index : Int) (entry : SortSliceEntry κ ν)
  (hindex : SortSlice.IndexInBounds slice index) :
  ReverseTraceSafe (phase.writeTraced? slice index entry) := by
  cases phase <;> constructor
  all_goals
    simp [ReverseSlicePhase.writeTraced?, AccessTrace.singletonAccess,
      AccessTrace.allAccessesInBounds, AccessTrace.tempPayloadAccessesLive,
      AccessEvent.InBounds, AccessEvent.TempPayloadLive,
      SortSlice.IndexInBounds] at hindex ⊢
  all_goals aesop

end CPythonListsort

namespace CPythonListsort

/--
[reverseSlicePhaseLoopTraced_swap_trace_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
lemma reverseSlicePhaseLoopTraced_swap_trace_order
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {phase : ReverseSlicePhase}
  {slice : SortSlice κ ν}
  {left right : SortSliceEntry κ ν}
  {afterLeft afterRight : SortSlice κ ν}
-- given
  (lo hi : Int)
  (hactive : lo < hi)
  (hleft : (phase.readTraced? slice lo).result = some left)
  (hright : (phase.readTraced? slice hi).result = some right)
  (hafterLeft : (phase.writeTraced? slice lo right).result = some afterLeft)
  (hafterRight : (phase.writeTraced? afterLeft hi left).result = some afterRight) :
-- imply
  (reverseSlicePhaseLoopTraced? (fuel + 1) phase slice lo hi).trace = (phase.readTraced? slice lo).trace.compose ((phase.readTraced? slice hi).trace.compose ((phase.writeTraced? slice lo right).trace.compose ((phase.writeTraced? afterLeft hi left).trace.compose (reverseSlicePhaseLoopTraced? fuel phase afterRight (lo + 1) (hi - 1)).trace))) := by
-- proof
  simp [reverseSlicePhaseLoopTraced?, hactive, TraceResult.trace_bind,
    hleft, hright, hafterLeft, hafterRight]

end CPythonListsort

namespace CPythonListsort

/--
[sortsliceReverseTraced_values_trace_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
lemma sortsliceReverseTraced_values_trace_order
  {κ : Type u}
  {ν : Type v}
  {slice : SortSlice κ ν}
  {base : Int}
  {n : Nat}
  {keyResult : ReverseSliceResult κ ν}
-- given
  (hkey : (reverseSlicePhaseTraced? .keys slice base (base + Int.ofNat n)).result = some keyResult) :
-- imply
  (sortsliceReverseTraced? true slice base n).trace = (reverseSlicePhaseTraced? .keys slice base (base + Int.ofNat n)).trace.compose (reverseSlicePhaseTraced? .values slice base (base + Int.ofNat n)).trace := by
-- proof
  rw [sortsliceReverseTraced?, TraceResult.trace_bind, hkey]
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[sortsliceReverseTraced_no_values_trace_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
lemma sortsliceReverseTraced_no_values_trace_order
  {κ : Type u}
  {ν : Type v}
  {slice : SortSlice κ ν}
  {base : Int}
  {n : Nat} :
-- imply
  (sortsliceReverseTraced? false slice base n).trace = (reverseSlicePhaseTraced? .keys slice base (base + Int.ofNat n)).trace := by
-- proof
  unfold sortsliceReverseTraced?
  rw [TraceResult.trace_bind]
  cases (reverseSlicePhaseTraced? .keys slice base
    (base + Int.ofNat n)).result <;>
      simp [TraceResult.pure, AccessTrace.compose_empty_right]

end CPythonListsort

namespace CPythonListsort

/--
[sortsliceReverseTraced_empty_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
lemma sortsliceReverseTraced_empty_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (sortsliceReverseTraced? true reverseRegressionSlice 2 0).result.map (fun result => (result.fuelExhausted, result.slice.entries.toList)) = some (false, reverseRegressionSlice.entries.toList) ∧ (sortsliceReverseTraced? true reverseRegressionSlice 2 0).trace = AccessTrace.empty := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[sortsliceReverseTraced_empty_one_past_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
lemma sortsliceReverseTraced_empty_one_past_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (sortsliceReverseTraced? true reverseRegressionSlice 4 0).result.map (fun result => (result.fuelExhausted, result.slice.entries.toList)) = some (false, reverseRegressionSlice.entries.toList) ∧ (sortsliceReverseTraced? true reverseRegressionSlice 4 0).trace = AccessTrace.empty := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[sortsliceReverseTraced_singleton_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
lemma sortsliceReverseTraced_singleton_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (sortsliceReverseTraced? true reverseRegressionSlice 1 1).result.map (fun result => (result.fuelExhausted, result.slice.entries.toList)) = some (false, reverseRegressionSlice.entries.toList) ∧ (sortsliceReverseTraced? true reverseRegressionSlice 1 1).trace = AccessTrace.empty := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[sortsliceReverseTraced_odd_center_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
lemma sortsliceReverseTraced_odd_center_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (sortsliceReverseTraced? true reverseRegressionSlice 0 3).result.map (fun result => (result.fuelExhausted, result.slice.entries.toList)) = some (false, [{ key := 2, value := some 12 }, { key := 1, value := some 11 }, { key := 0, value := some 10 }, { key := 3, value := some 13 }]) ∧ (sortsliceReverseTraced? true reverseRegressionSlice 0 3).trace.accesses.map (fun event => (event.kind, event.region, event.index)) = [(.read, .inputKeys, 0), (.read, .inputKeys, 2), (.write, .inputKeys, 0), (.write, .inputKeys, 2), (.read, .synchronizedValues, 0), (.read, .synchronizedValues, 2), (.write, .synchronizedValues, 0), (.write, .synchronizedValues, 2)] := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[sortsliceReverseTraced_no_values_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
lemma sortsliceReverseTraced_no_values_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (sortsliceReverseTraced? false reverseNoValuesRegressionSlice 0 4).result.map (fun result => (result.fuelExhausted, result.slice.entries.toList)) = some (false, [{ key := 3, value := none }, { key := 2, value := none }, { key := 1, value := none }, { key := 0, value := none }]) ∧ (sortsliceReverseTraced? false reverseNoValuesRegressionSlice 0 4).trace.accesses.all (fun event => event.region = .inputKeys) = true := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[sortsliceReverseTraced_two_swap_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
lemma sortsliceReverseTraced_two_swap_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (sortsliceReverseTraced? true reverseRegressionSlice 0 4).result.map (fun result => (result.fuelExhausted, result.slice.entries.toList)) = some (false, [{ key := 3, value := some 13 }, { key := 2, value := some 12 }, { key := 1, value := some 11 }, { key := 0, value := some 10 }]) ∧ (sortsliceReverseTraced? true reverseRegressionSlice 0 4).trace.accesses.map (fun event => (event.kind, event.region, event.index)) = [(.read, .inputKeys, 0), (.read, .inputKeys, 3), (.write, .inputKeys, 0), (.write, .inputKeys, 3), (.read, .inputKeys, 1), (.read, .inputKeys, 2), (.write, .inputKeys, 1), (.write, .inputKeys, 2), (.read, .synchronizedValues, 0), (.read, .synchronizedValues, 3), (.write, .synchronizedValues, 0), (.write, .synchronizedValues, 3), (.read, .synchronizedValues, 1), (.read, .synchronizedValues, 2), (.write, .synchronizedValues, 1), (.write, .synchronizedValues, 2)] := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[reverseSlicePhaseLoopTraced_zero_fuel_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
lemma reverseSlicePhaseLoopTraced_zero_fuel_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (reverseSlicePhaseLoopTraced? 0 .keys reverseRegressionSlice 0 1).result.map (fun result => result.fuelExhausted) = some true ∧ (reverseSlicePhaseLoopTraced? 0 .keys reverseRegressionSlice 0 1).trace.fuelExhausted = true := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[reverseSliceTraced_reversed_range_failure_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
lemma reverseSliceTraced_reversed_range_failure_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (reverseSliceTraced? reverseRegressionSlice 3 2).result = none ∧ (reverseSliceTraced? reverseRegressionSlice 3 2).trace = AccessTrace.empty := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[reverseSliceTraced_oob_failure_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
lemma reverseSliceTraced_oob_failure_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (reverseSliceTraced? reverseRegressionSlice 0 5).result = none ∧ (reverseSliceTraced? reverseRegressionSlice 0 5).trace.accesses = [{ kind := .read, region := .inputKeys, index := 0, extent := 4 }, { kind := .read, region := .inputKeys, index := 4, extent := 4 }] ∧ ¬(reverseSliceTraced? reverseRegressionSlice 0 5).trace.allAccessesInBounds := by
-- proof
  decide

end CPythonListsort

/--
[reverseSlicePhaseTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
private lemma reverseSlicePhaseTraced_safe_eq
  {κ : Type u}
  {ν : Type v}
  {phase : ReverseSlicePhase}
  {slice : SortSlice κ ν}
  {valuesPresent : Bool}
-- given
  (lo hi : Int)
  (hlo : 0 ≤ lo)
  (hhi : hi ≤ Int.ofNat slice.entries.size)
  (hordered : lo ≤ hi)
  (_hphase : phase = .keys ∨ valuesPresent = true)
  (hMode : SortSlice.ValuesModeInvariant valuesPresent slice) :
-- imply
  ∃ result, ReverseSlicePhaseSafetyPost phase slice lo hi valuesPresent result := by
-- proof
  apply CPythonListsort.reverseSlicePhaseTraced_safe phase slice lo hi valuesPresent hlo hhi hordered _hphase hMode

/--
[sortsliceReverse_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean)
-/
@[path]
private lemma sortsliceReverse_safe_eq
  {κ : Type u}
  {ν : Type v}
  {valuesPresent : Bool}
  {slice : SortSlice κ ν}
  {base : Int}
  {n : Nat}
-- given
  (hrange : SortSlice.RangeInBounds slice base n)
  (hMode : SortSlice.ValuesModeInvariant valuesPresent slice) :
-- imply
  ∃ result, ReverseSliceSafetyPost slice valuesPresent base n result := by
-- proof
  apply CPythonListsort.sortsliceReverse_safe valuesPresent slice base n hrange hMode


-- created on 2026-10-23
