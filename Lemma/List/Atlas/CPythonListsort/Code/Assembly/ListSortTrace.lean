import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Assembly.ListSortTrace
open CPythonListsort


namespace CPythonListsort

/--
[listSortInitialReverseTraced_unkeyed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma listSortInitialReverseTraced_unkeyed
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {inputSize : Nat}
-- given
  (hMode : state.a.hasValues = false) :
-- imply
  listSortInitialReverseTraced? state inputSize = sortsliceReverseTraced? false state.data 0 inputSize := by
-- proof
  simp [listSortInitialReverseTraced?, hMode]

end CPythonListsort

namespace CPythonListsort

/--
[listSortInitialReverseTraced_keyed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma listSortInitialReverseTraced_keyed
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {inputSize : Nat}
-- given
  (hMode : state.a.hasValues = true) :
-- imply
  listSortInitialReverseTraced? state inputSize = sortsliceReverseTraced? true state.data 0 inputSize := by
-- proof
  simp [listSortInitialReverseTraced?, hMode]

end CPythonListsort

namespace CPythonListsort

/--
[listSortInitialReverseTraced_trace_keyed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma listSortInitialReverseTraced_trace_keyed
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {inputSize : Nat}
  {keyResult : ReverseSliceResult κ ν}
-- given
  (hMode : state.a.hasValues = true)
  (hKey : (reverseSlicePhaseTraced? .keys state.data 0 (Int.ofNat inputSize)).result = some keyResult) :
-- imply
  (listSortInitialReverseTraced? state inputSize).trace = (reverseSlicePhaseTraced? .keys state.data 0 (Int.ofNat inputSize)).trace.compose (reverseSlicePhaseTraced? .values state.data 0 (Int.ofNat inputSize)).trace := by
-- proof
  rw [listSortInitialReverseTraced?, hMode]
  simpa using
    sortsliceReverseTraced_values_trace_order state.data 0 inputSize keyResult
      (by simpa using hKey)

end CPythonListsort

namespace CPythonListsort

/--
[listSortInitialReverseTraced_trace_unkeyed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma listSortInitialReverseTraced_trace_unkeyed
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {inputSize : Nat}
-- given
  (hMode : state.a.hasValues = false) :
-- imply
  (listSortInitialReverseTraced? state inputSize).trace = (reverseSlicePhaseTraced? .keys state.data 0 (Int.ofNat inputSize)).trace := by
-- proof
  rw [listSortInitialReverseTraced?, hMode]
  simpa using
    sortsliceReverseTraced_no_values_trace_order state.data 0 inputSize

end CPythonListsort

namespace CPythonListsort

/--
[finishListSortTraced_trace_keyed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma finishListSortTraced_trace_keyed
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {inputSize : Nat}
  {returnCode : Int}
  {fuelExhausted : Bool}
  {reversed : ReverseSliceResult κ ν}
-- given
  (hMode : state.a.hasValues = true)
  (hSize : 1 < inputSize)
  (hReversed : (reverseSlicePhaseTraced? .values state.data 0 (Int.ofNat inputSize)).result = some reversed) :
-- imply
  (finishListSortTraced? state true inputSize returnCode fuelExhausted).trace = (reverseSlicePhaseTraced? .values state.data 0 (Int.ofNat inputSize)).trace.compose (AccessTrace.singletonMemoryEvent (listSortCleanupMemoryEvent { state with data := reversed.slice })) := by
-- proof
  unfold finishListSortTraced?
  rw [if_pos (by simp [hSize])]
  simp only [hMode, finalReversePhase, if_true]
  rw [TraceResult.trace_bind, hReversed]
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[finishListSortTraced_trace_unkeyed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma finishListSortTraced_trace_unkeyed
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {inputSize : Nat}
  {returnCode : Int}
  {fuelExhausted : Bool}
  {reversed : ReverseSliceResult κ ν}
-- given
  (hMode : state.a.hasValues = false)
  (hSize : 1 < inputSize)
  (hReversed : (reverseSlicePhaseTraced? .keys state.data 0 (Int.ofNat inputSize)).result = some reversed) :
-- imply
  (finishListSortTraced? state true inputSize returnCode fuelExhausted).trace = (reverseSlicePhaseTraced? .keys state.data 0 (Int.ofNat inputSize)).trace.compose (AccessTrace.singletonMemoryEvent (listSortCleanupMemoryEvent { state with data := reversed.slice })) := by
-- proof
  unfold finishListSortTraced?
  rw [if_pos (by simp [hSize])]
  simp only [hMode, finalReversePhase, Bool.false_eq_true, if_false]
  rw [TraceResult.trace_bind, hReversed]
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[finishListSortTraced_cleanup_event_inactive_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma finishListSortTraced_cleanup_event_inactive_exact
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {reverse : Bool}
  {inputSize : Nat}
  {returnCode : Int}
  {fuelExhausted : Bool}
-- given
  (hInactive : (reverse && decide (1 < inputSize)) = false) :
-- imply
  (finishListSortTraced? state reverse inputSize returnCode fuelExhausted).trace.memoryEvents = [listSortCleanupMemoryEvent state] := by
-- proof
  unfold finishListSortTraced?
  rw [if_neg (by simpa using hInactive)]
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[finishListSortTraced_cleanup_event_active_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma finishListSortTraced_cleanup_event_active_exact
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {reverse : Bool}
  {inputSize : Nat}
  {returnCode : Int}
  {fuelExhausted : Bool}
  {reversed : ReverseSliceResult κ ν}
-- given
  (hActive : (reverse && decide (1 < inputSize)) = true)
  (hReversed : (reverseSlicePhaseTraced? (finalReversePhase state.a.hasValues) state.data 0 (Int.ofNat inputSize)).result = some reversed) :
-- imply
  (finishListSortTraced? state reverse inputSize returnCode fuelExhausted).trace.memoryEvents = (reverseSlicePhaseTraced? (finalReversePhase state.a.hasValues) state.data 0 (Int.ofNat inputSize)).trace.memoryEvents ++ [listSortCleanupMemoryEvent { state with data := reversed.slice }] := by
-- proof
  unfold finishListSortTraced?
  rw [if_pos (by simpa using hActive), TraceResult.trace_bind, hReversed]
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[listSortInitialReverseTraced_policyEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma listSortInitialReverseTraced_policyEvents_eq_nil
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {inputSize : Nat} :
-- imply
  (listSortInitialReverseTraced? state inputSize).trace.policyEvents = [] :=
-- proof
sortsliceReverseTraced_policyEvents_eq_nil _ _ _ _

end CPythonListsort

namespace CPythonListsort

/--
[finishListSortTraced_policyEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma finishListSortTraced_policyEvents_eq_nil
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {reverse : Bool}
  {inputSize : Nat}
  {returnCode : Int}
  {fuelExhausted : Bool} :
-- imply
  (finishListSortTraced? state reverse inputSize returnCode fuelExhausted).trace.policyEvents = [] := by
-- proof
  unfold finishListSortTraced?
  by_cases hactive : (reverse && decide (1 < inputSize)) = true
  · rw [if_pos hactive]
    apply TraceResult.policyEvents_bind_eq_nil
    · exact reverseSlicePhaseTraced_policyEvents_eq_nil _ _ _ _
    · intro reversed
      rfl
  · rw [if_neg hactive]
    rfl

end CPythonListsort

namespace CPythonListsort

/--
[failFromFoundNewRunTraced_policyEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma failFromFoundNewRunTraced_policyEvents_eq_nil
  {κ : Type u}
  {ν : Type v}
  {result : FoundNewRunResult κ ν}
  {reverse : Bool}
  {inputSize : Nat} :
-- imply
  (failFromFoundNewRunTraced? result reverse inputSize).trace.policyEvents = [] :=
-- proof
finishListSortTraced_policyEvents_eq_nil _ _ _ _ _

end CPythonListsort

namespace CPythonListsort

/--
[failFromCollapseTraced_policyEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma failFromCollapseTraced_policyEvents_eq_nil
  {κ : Type u}
  {ν : Type v}
  {result : MergeForceCollapseResult κ ν}
  {reverse : Bool}
  {inputSize : Nat} :
-- imply
  (failFromCollapseTraced? result reverse inputSize).trace.policyEvents = [] :=
-- proof
finishListSortTraced_policyEvents_eq_nil _ _ _ _ _

end CPythonListsort

namespace CPythonListsort

/--
[listSortAfterExtensionTraced_policyEvents_of_success](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma listSortAfterExtensionTraced_policyEvents_of_success
  {κ : Type u}
  {ν : Type v}
  {next : MergeState κ ν → Nat → Nat → TraceResult (ListSortImplResult κ ν)}
  {state : MergeState κ ν}
  {lo remaining runLength : Nat}
  {reverse : Bool}
  {inputSize naturalLength target : Nat}
  {found : FoundNewRunResult κ ν}
-- given
  (hValid : ¬(runLength = 0 ∨ remaining < runLength))
  (hFound : (foundNewRunTraced? state runLength).result = some found)
  (hSuccess : found.returnCode = 0 ∧ !found.fuelExhausted) :
-- imply
  let newRun : PendingRun := { base := lo len := BitVec.ofNat 64 runLength power := none } (listSortAfterExtensionTraced? next lo remaining reverse inputSize naturalLength target (state, runLength, false)).trace.policyEvents = (foundNewRunTraced? state runLength).trace.policyEvents ++ [.formed { run := RunSpan.ofPendingRun newRun depthAfter := found.state.pending.size + 1 naturalLength := naturalLength target := target remainingBefore := remaining }] ++ (next (pushPendingRun found.state newRun) (lo + runLength) (remaining - runLength)).trace.policyEvents := by
-- proof
  dsimp only
  simp only [listSortAfterExtensionTraced?, Bool.false_eq_true, if_false]
  rw [if_neg hValid, TraceResult.policyEvents_bind, hFound]
  simp only [hSuccess, true_and, if_true]
  rw [TraceResult.policyEvents_bind]
  have hPushResult :
    (pushFormedRunTraced found.state
      { base := lo, len := BitVec.ofNat 64 runLength, power := none }
      naturalLength target remaining).result =
      some (pushPendingRun found.state
        { base := lo, len := BitVec.ofNat 64 runLength, power := none }) :=
    erase_pushFormedRunTraced _ _ _ _ _
  rw [hPushResult]
  simp [trace_pushFormedRunTraced, AccessTrace.singletonFormedRun,
    pushPendingRun, List.append_assoc]

end CPythonListsort

namespace CPythonListsort

/--
[listSortScanTraced_zero_fuel_active_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma listSortScanTraced_zero_fuel_active_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (listSortScanTraced? 0 listSortZeroFuelRegressionState 0 2 false 2).result.map (fun result => (result.returnCode, result.fuelExhausted)) = some (-1, true) ∧ (listSortScanTraced? 0 listSortZeroFuelRegressionState 0 2 false 2).trace.fuelExhausted = true ∧ (listSortScanTraced? 0 listSortZeroFuelRegressionState 0 2 false 2).erase = listSortScan? 0 listSortZeroFuelRegressionState 0 2 false 2 := by
-- proof
  constructor
  · decide
  constructor
  · decide
  · rfl

end CPythonListsort

namespace CPythonListsort

/--
[listSortImplTraced_initial_event_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma listSortImplTraced_initial_event_head
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {input : SortSlice κ ν}
-- given
  (reverse hasKeyfunc : Bool)
  (hSize : input.entries.size ≤ PY_LIST_MAX) :
-- imply
  (listSortImplTraced? lt reverse hasKeyfunc input).trace.memoryEvents.head? = some (.initial (MergeMemorySnapshot.ofState (initialMergeState lt hasKeyfunc input).1)) := by
-- proof
  simp [listSortImplTraced?, hSize, TraceResult.prependMemoryEvent,
    AccessTrace.compose, AccessTrace.singletonMemoryEvent]

end CPythonListsort

namespace CPythonListsort

/--
[listSortImplTraced_oversize_no_initial_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma listSortImplTraced_oversize_no_initial_event
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {input : SortSlice κ ν}
-- given
  (reverse hasKeyfunc : Bool)
  (hSize : ¬ input.entries.size ≤ PY_LIST_MAX) :
-- imply
  (listSortImplTraced? lt reverse hasKeyfunc input).result = none ∧ (listSortImplTraced? lt reverse hasKeyfunc input).trace.memoryEvents = [] := by
-- proof
  simp [listSortImplTraced?, hSize, TraceResult.failure,
    AccessTrace.empty]

end CPythonListsort

namespace CPythonListsort

/--
[listSortImplTraced_formedRun_policy_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma listSortImplTraced_formedRun_policy_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (listSortImplTraced? (fun left right : Nat => decide (left < right)) false false formedRunPolicyRegressionInput).trace.policyEvents = [.formed { run := { base := 0, len := 3 } depthAfter := 1 naturalLength := 3 target := 3 remainingBefore := 3 }] := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[listSortImplTraced_extendedRun_policy_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma listSortImplTraced_extendedRun_policy_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (listSortImplTraced? (fun left right : Nat => decide (left < right)) false false formedRunExtensionRegressionInput).trace.policyEvents = [.formed { run := { base := 0, len := 8 } depthAfter := 1 naturalLength := 2 target := 8 remainingBefore := 8 }] := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[erase_finishListSortTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma erase_finishListSortTraced
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {reverse : Bool}
  {inputSize : Nat}
  {returnCode : Int}
  {fuelExhausted : Bool} :
-- imply
  (finishListSortTraced? state reverse inputSize returnCode fuelExhausted).erase = finishListSort? state reverse inputSize returnCode fuelExhausted := by
-- proof
  unfold finishListSortTraced? finishListSort?
  by_cases hreverse : (reverse && decide (1 < inputSize)) = true
  · rw [if_pos hreverse, if_pos hreverse]
    simp only [TraceResult.erase_bind, erase_finalReversePhaseTraced,
      sortsliceReverse?, Int.zero_add]
    cases hresult : reverseSlice? state.data 0 (Int.ofNat inputSize) <;>
      simp
  · rw [if_neg hreverse, if_neg hreverse]
    simp [TraceResult.pure, TraceResult.erase]

end CPythonListsort

namespace CPythonListsort

/--
[erase_listSortInitialReverseTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma erase_listSortInitialReverseTraced
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {inputSize : Nat} :
-- imply
  (listSortInitialReverseTraced? state inputSize).erase = sortsliceReverse? state.data 0 inputSize :=
-- proof
erase_sortsliceReverseTraced state.a.hasValues state.data 0 inputSize

end CPythonListsort

namespace CPythonListsort

/--
[erase_failFromFoundNewRunTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma erase_failFromFoundNewRunTraced
  {κ : Type u}
  {ν : Type v}
  {result : FoundNewRunResult κ ν}
  {reverse : Bool}
  {inputSize : Nat} :
-- imply
  (failFromFoundNewRunTraced? result reverse inputSize).erase = failFromFoundNewRun? result reverse inputSize := by
-- proof
  simp [failFromFoundNewRunTraced?, failFromFoundNewRun?]

end CPythonListsort

namespace CPythonListsort

/--
[erase_failFromCollapseTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma erase_failFromCollapseTraced
  {κ : Type u}
  {ν : Type v}
  {result : MergeForceCollapseResult κ ν}
  {reverse : Bool}
  {inputSize : Nat} :
-- imply
  (failFromCollapseTraced? result reverse inputSize).erase = failFromCollapse? result reverse inputSize := by
-- proof
  simp [failFromCollapseTraced?, failFromCollapse?]

end CPythonListsort

namespace CPythonListsort

/--
[erase_listSortAfterExtensionTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma erase_listSortAfterExtensionTraced
  {κ : Type u}
  {ν : Type v}
  {nextTraced : MergeState κ ν → Nat → Nat → TraceResult (ListSortImplResult κ ν)}
  {next : MergeState κ ν → Nat → Nat → Option (ListSortImplResult κ ν)}
  {lo remaining : Nat}
  {reverse : Bool}
  {inputSize : Nat}
  {naturalLength target : Nat}
  {extension : MergeState κ ν × Nat × Bool}
-- given
  (hNext : ∀ state lo remaining, (nextTraced state lo remaining).erase = next state lo remaining)
  (hFound : ∀ (state : MergeState κ ν) (runLength : Nat), (foundNewRunTraced? state runLength).erase = foundNewRun? state runLength) :
-- imply
  (listSortAfterExtensionTraced? nextTraced lo remaining reverse inputSize naturalLength target extension).erase = listSortAfterExtension? next lo remaining reverse inputSize extension := by
-- proof
  unfold listSortAfterExtensionTraced? listSortAfterExtension?
  by_cases hfuel : extension.2.2 = true
  · rw [if_pos hfuel, if_pos hfuel, erase_finishListSortTraced]
  · rw [if_neg hfuel, if_neg hfuel]
    by_cases hinvalid : extension.2.1 = 0 ∨ remaining < extension.2.1
    · rw [if_pos hinvalid, if_pos hinvalid]
      rfl
    · rw [if_neg hinvalid, if_neg hinvalid, TraceResult.erase_bind,
      hFound]
      cases hfound : foundNewRun? extension.1 extension.2.1 with
      | none => simp
      | some found =>
        simp only [Option.bind_some]
        by_cases hsuccess :
          found.returnCode = 0 ∧ !found.fuelExhausted
        · rw [if_pos hsuccess, if_pos hsuccess,
          TraceResult.erase_bind, erase_pushFormedRunTraced]
          simpa [pushPendingRun] using
            hNext (pushPendingRun found.state
              { base := lo
                len := BitVec.ofNat 64 extension.2.1
                power := none })
              (lo + extension.2.1) (remaining - extension.2.1)
        · rw [if_neg hsuccess, if_neg hsuccess,
          erase_failFromFoundNewRunTraced]

end CPythonListsort

namespace CPythonListsort

/--
[erase_listSortAfterCountTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma erase_listSortAfterCountTraced
  {κ : Type u}
  {ν : Type v}
  {nextTraced : MergeState κ ν → Nat → Nat → TraceResult (ListSortImplResult κ ν)}
  {next : MergeState κ ν → Nat → Nat → Option (ListSortImplResult κ ν)}
  {state : MergeState κ ν}
  {lo remaining : Nat}
  {reverse : Bool}
  {inputSize : Nat}
  {counted : CountRunResult κ ν}
-- given
  (hNext : ∀ state lo remaining, (nextTraced state lo remaining).erase = next state lo remaining)
  (hFound : ∀ (state : MergeState κ ν) (runLength : Nat), (foundNewRunTraced? state runLength).erase = foundNewRun? state runLength) :
-- imply
  (listSortAfterCountTraced? nextTraced state lo remaining reverse inputSize counted).erase = listSortAfterCount? next state lo remaining reverse inputSize counted := by
-- proof
  unfold listSortAfterCountTraced? listSortAfterCount?
  by_cases hfuel : counted.fuelExhausted = true
  · rw [if_pos hfuel, if_pos hfuel, erase_finishListSortTraced]
  · rw [if_neg hfuel, if_neg hfuel]
    by_cases hinvalid : counted.length = 0 ∨ remaining < counted.length
    · rw [if_pos hinvalid, if_pos hinvalid]
      rfl
    · rw [if_neg hinvalid, if_neg hinvalid]
      let countedState : MergeState κ ν := { state with data := counted.slice }
      let nextMinrun := minrunNext countedState.minrunState
      let installed := installMinrunState countedState nextMinrun.state
      let force := if remaining ≤ nextMinrun.result.toNat then
        remaining else nextMinrun.result.toNat
      by_cases hextend :
        ((BitVec.ofNat 64 counted.length : PySSize).slt
          nextMinrun.result) = true
      · rw [if_pos hextend, if_pos hextend, TraceResult.erase_bind,
        erase_binarysortTraced]
        cases hsorted : binarysort? installed installed.data (Int.ofNat lo)
          force counted.length with
        | none => simp
        | some sorted =>
          simp only [Option.bind_some]
          exact erase_listSortAfterExtensionTraced nextTraced next hNext
            hFound lo remaining reverse inputSize counted.length
              nextMinrun.result.toNat
              ({ installed with data := sorted.slice }, force,
                sorted.fuelExhausted)
      · rw [if_neg hextend, if_neg hextend]
        exact erase_listSortAfterExtensionTraced nextTraced next hNext hFound
          lo remaining reverse inputSize counted.length
            nextMinrun.result.toNat (installed, counted.length, false)

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[listSortAfterCount_eq_scan_succ_of_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
private lemma listSortAfterCount_eq_scan_succ_of_count
  (fuel : Nat) (state : MergeState κ ν) (lo remaining : Nat)
  (reverse : Bool) (inputSize : Nat) (counted : CountRunResult κ ν)
  (hRemaining : remaining ≠ 0)
  (hCounted : countRun? state state.data (Int.ofNat lo) remaining =
    some counted) :
  listSortAfterCount?
    (fun nextState nextLo nextRemaining =>
      listSortScan? fuel nextState nextLo nextRemaining reverse inputSize)
    state lo remaining reverse inputSize counted =
    listSortScan? (fuel + 1) state lo remaining reverse inputSize := by
  rw [listSortScan?]
  simp only [hRemaining, if_false, hCounted]
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[erase_listSortScanTraced_of_helper_erasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma erase_listSortScanTraced_of_helper_erasure
  {κ : Type u}
  {ν : Type v}
-- given
  (hFound : ∀ (state : MergeState κ ν) (runLength : Nat), (foundNewRunTraced? state runLength).erase = foundNewRun? state runLength)
  (hCollapse : ∀ (state : MergeState κ ν), (mergeForceCollapseTraced? state).erase = mergeForceCollapse? state) :
-- imply
  ∀ (fuel : Nat) (state : MergeState κ ν) (lo remaining : Nat) (reverse : Bool) (inputSize : Nat), (listSortScanTraced? fuel state lo remaining reverse inputSize).erase = listSortScan? fuel state lo remaining reverse inputSize := by
-- proof
  intro fuel
  induction fuel with
  | zero =>
    intro state lo remaining reverse inputSize
    by_cases hremaining : remaining = 0
    · rw [listSortScanTraced?, listSortScan?, if_pos hremaining,
      if_pos hremaining, TraceResult.erase_bind, hCollapse]
      cases hcollapsed : mergeForceCollapse? state with
      | none => simp
      | some collapsed =>
        simp only [Option.bind_some]
        by_cases hsuccess :
          collapsed.returnCode = 0 ∧ !collapsed.fuelExhausted
        · rw [if_pos hsuccess, if_pos hsuccess,
          erase_finishListSortTraced]
        · rw [if_neg hsuccess, if_neg hsuccess,
          erase_failFromCollapseTraced]
    · rw [listSortScanTraced?, listSortScan?, if_neg hremaining,
      if_neg hremaining, TraceResult.erase_markFuelExhausted,
      erase_finishListSortTraced]
  | succ fuel ih =>
    intro state lo remaining reverse inputSize
    by_cases hremaining : remaining = 0
    · rw [listSortScanTraced?, listSortScan?, if_pos hremaining,
      if_pos hremaining, TraceResult.erase_bind, hCollapse]
      cases hcollapsed : mergeForceCollapse? state with
      | none => simp
      | some collapsed =>
        simp only [Option.bind_some]
        by_cases hsuccess :
          collapsed.returnCode = 0 ∧ !collapsed.fuelExhausted
        · rw [if_pos hsuccess, if_pos hsuccess,
          erase_finishListSortTraced]
        · rw [if_neg hsuccess, if_neg hsuccess,
          erase_failFromCollapseTraced]
    · rw [listSortScanTraced?, if_neg hremaining, TraceResult.erase_bind,
      erase_countRunTraced]
      cases hcounted : countRun? state state.data (Int.ofNat lo) remaining with
      | none =>
        rw [listSortScan?]
        rw [if_neg hremaining, hcounted]
        rfl
      | some counted =>
        simp only [Option.bind_some]
        calc
          (listSortAfterCountTraced?
            (fun nextState nextLo nextRemaining =>
              listSortScanTraced? fuel nextState nextLo nextRemaining
                reverse inputSize)
            state lo remaining reverse inputSize counted).erase =
            listSortAfterCount?
              (fun nextState nextLo nextRemaining =>
                listSortScan? fuel nextState nextLo nextRemaining reverse
                  inputSize)
              state lo remaining reverse inputSize counted :=
            erase_listSortAfterCountTraced
              (fun nextState nextLo nextRemaining =>
                listSortScanTraced? fuel nextState nextLo nextRemaining
                  reverse inputSize)
              (fun nextState nextLo nextRemaining =>
                listSortScan? fuel nextState nextLo nextRemaining reverse
                  inputSize)
              (fun nextState nextLo nextRemaining =>
                ih nextState nextLo nextRemaining reverse inputSize)
              hFound state lo remaining reverse inputSize counted
          _ = listSortScan? (fuel + 1) state lo remaining reverse
            inputSize :=
            listSortAfterCount_eq_scan_succ_of_count fuel state lo remaining
              reverse inputSize counted hremaining hcounted

end CPythonListsort

namespace CPythonListsort

/--
[erase_listSortImplTraced_of_helper_erasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma erase_listSortImplTraced_of_helper_erasure
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {input : SortSlice κ ν}
-- given
  (hFound : ∀ (state : MergeState κ ν) (runLength : Nat), (foundNewRunTraced? state runLength).erase = foundNewRun? state runLength)
  (hCollapse : ∀ (state : MergeState κ ν), (mergeForceCollapseTraced? state).erase = mergeForceCollapse? state)
  (reverse hasKeyfunc : Bool) :
-- imply
  (listSortImplTraced? lt reverse hasKeyfunc input).erase = listSortImpl? lt reverse hasKeyfunc input := by
-- proof
  unfold listSortImplTraced? listSortImpl?
  by_cases hsize : input.entries.size ≤ PY_LIST_MAX
  · rw [if_pos hsize, if_pos hsize,
    TraceResult.erase_prependMemoryEvent]
    let initialized := initialMergeState lt hasKeyfunc input
    let state := initialized.1
    by_cases hinit : (!initialized.2) = true
    · rw [if_pos hinit, if_pos hinit,
      TraceResult.erase_markFuelExhausted, erase_finishListSortTraced]
    · rw [if_neg hinit, if_neg hinit]
      by_cases hsmall : input.entries.size < 2
      · rw [if_pos hsmall, if_pos hsmall, erase_finishListSortTraced]
      · rw [if_neg hsmall, if_neg hsmall]
        by_cases hreverse : reverse = true
        · rw [if_pos hreverse, if_pos hreverse, TraceResult.erase_bind,
          erase_listSortInitialReverseTraced]
          cases hreversed : sortsliceReverse? state.data 0 input.entries.size with
          | none => simp
          | some reversed =>
            simp only [Option.bind_some]
            by_cases hfuel : reversed.fuelExhausted = true
            · rw [if_pos hfuel, if_pos hfuel,
              erase_finishListSortTraced]
            · rw [if_neg hfuel, if_neg hfuel]
              exact erase_listSortScanTraced_of_helper_erasure hFound
                hCollapse input.entries.size
                { state with data := reversed.slice } 0 input.entries.size
                reverse input.entries.size
        · rw [if_neg hreverse, if_neg hreverse]
          exact erase_listSortScanTraced_of_helper_erasure hFound hCollapse
            input.entries.size state 0 input.entries.size reverse
            input.entries.size
  · rw [if_neg hsize, if_neg hsize]
    rfl

end CPythonListsort

namespace CPythonListsort

/--
[erase_listSortTraced_of_helper_erasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean)
-/
@[path]
lemma erase_listSortTraced_of_helper_erasure
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {reverse : Bool}
  {input : ListSortInput κ ν}
-- given
  (hFound : ∀ (state : MergeState κ ν) (runLength : Nat), (foundNewRunTraced? state runLength).erase = foundNewRun? state runLength)
  (hCollapse : ∀ (state : MergeState κ ν), (mergeForceCollapseTraced? state).erase = mergeForceCollapse? state) :
-- imply
  (listSortTraced? lt reverse input).erase = listSort? lt reverse input := by
-- proof
  exact erase_listSortImplTraced_of_helper_erasure hFound hCollapse lt reverse
    input.hasKeyfunc input.slice

end CPythonListsort


-- created on 2026-10-23
