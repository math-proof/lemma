import Mathlib
import sympy.Basic
import Structure.CPythonListsort.Code.Assembly.ListSortPolicyEndpoints


namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[initialScanInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortPolicyBridge.lean)
-/
@[path]
active iteration. -/
private lemma initialScanInvariant
  (lt : BoolComparator κ) (input : ListSortInput κ ν)
  (hActive : 2 ≤ input.slice.entries.size)
  (hSize : input.slice.entries.size ≤ PY_LIST_MAX) :
  ListSortScanInvariant lt input.hasKeyfunc input.slice.entries.size
    (initialMergeState lt input.hasKeyfunc input.slice).1 0 0
    input.slice.entries.size := by
  have hPackage := initialMergeState_package lt input.hasKeyfunc input.slice
    hSize input.valuesMode
  refine
    { inputSizeLower := hActive
      inputSizeMax := hSize
      listlen := hPackage.listlenRoundtrip
      listlenNonnegative := hPackage.listlenNonnegative
      basekeys := hPackage.basekeys
      dataExtent := by simp
      cursor := by simp [hPackage.basekeys]
      partition := by simp
      pendingLayout := hPackage.pendingLayout
      poweredPrefix := hPackage.poweredPrefix
      tempInvariant := hPackage.tempInvariant
      tempLive := hPackage.tempLive
      physicalSlotsBound := by
        simpa [MergeMemorySnapshot.PhysicalBound,
          MergeMemorySnapshot.ofState] using hPackage.physicalSlotsBound
      hasValues := hPackage.hasValues
      valuesMode := hPackage.valuesMode
      comparator := hPackage.comparator
      adaptive := ?_ }
  intro _hRemaining
  refine ⟨0, ?_⟩
  have hInitial := adaptiveMinrunScanInvariant_initial
    (initialMergeState lt input.hasKeyfunc input.slice).1.listlen
    hPackage.listlenNonnegative
    (by simpa [hPackage.listlenRoundtrip] using hSize)
  simpa [hPackage.minrunState] using hInitial

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[withDataForPolicy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortPolicyBridge.lean)
-/
@[path]
extent and values-mode relation are unchanged. -/
private lemma ListSortScanInvariant.withDataForPolicy
  {lt : BoolComparator κ} {hasKeyfunc : Bool} {inputSize : Nat}
  {state : MergeState κ ν} {lo scanned remaining : Nat}
  (hInv : ListSortScanInvariant lt hasKeyfunc inputSize state lo scanned
    remaining)
  (slice : SortSlice κ ν)
  (hSize : slice.entries.size = state.data.entries.size)
  (hMode : SortSlice.ValuesModeInvariant state.a.hasValues slice) :
  ListSortScanInvariant lt hasKeyfunc inputSize { state with data := slice }
    lo scanned remaining := by
  refine
    { inputSizeLower := hInv.inputSizeLower
      inputSizeMax := hInv.inputSizeMax
      listlen := hInv.listlen
      listlenNonnegative := hInv.listlenNonnegative
      basekeys := hInv.basekeys
      dataExtent := hSize.trans hInv.dataExtent
      cursor := hInv.cursor
      partition := hInv.partition
      pendingLayout := ?_
      poweredPrefix := hInv.poweredPrefix
      tempInvariant := hInv.tempInvariant
      tempLive := hInv.tempLive
      physicalSlotsBound := hInv.physicalSlotsBound
      hasValues := hInv.hasValues
      valuesMode := hMode
      comparator := hInv.comparator
      adaptive := hInv.adaptive }
  exact pendingLayout_of_policy_frame state { state with data := slice }
    scanned hInv.pendingLayout rfl rfl hSize rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[initialScanPowerForestInv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortPolicyBridge.lean)
-/
@[path]
empty pending stack. -/
private lemma initialScanPowerForestInv
  (lt : BoolComparator κ) (input : ListSortInput κ ν)
  (hSize : input.slice.entries.size ≤ PY_LIST_MAX) :
  ScanPowerForestInv input.runSpan []
    (initialMergeState lt input.hasKeyfunc input.slice).1 := by
  have hPackage := initialMergeState_package lt input.hasKeyfunc input.slice
    hSize input.valuesMode
  refine
    { inputMax := by simpa [ListSortInput.runSpan] using hSize
      basekeys_eq := by simpa [ListSortInput.runSpan] using hPackage.basekeys
      listlen_eq := ?_
      aligned := ?_
      newestRootLeaf := .empty }
  · simp [ListSortInput.runSpan, initialMergeState, minrunInitTraced]
  · rw [hPackage.pending]
    exact .nil

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[reversedScanPowerForestInv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortPolicyBridge.lean)
-/
@[path]
private lemma reversedScanPowerForestInv
  (lt : BoolComparator κ) (input : ListSortInput κ ν)
  (hSize : input.slice.entries.size ≤ PY_LIST_MAX)
  (reversed : ReverseSliceResult κ ν) :
  ScanPowerForestInv input.runSpan []
    { (initialMergeState lt input.hasKeyfunc input.slice).1 with
      data := reversed.slice } := by
  exact scanPowerForestInv_of_policy_frame input.runSpan []
    (initialMergeState lt input.hasKeyfunc input.slice).1
    { (initialMergeState lt input.hasKeyfunc input.slice).1 with
      data := reversed.slice }
    (initialScanPowerForestInv lt input hSize) rfl rfl rfl

end CPythonListsort

namespace CPythonListsort

/--
[listSortTraced_policyBridge_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortPolicyBridge.lean)
-/
@[path]
lemma listSortTraced_policyBridge_active
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {reverse : Bool}
  {input : ListSortInput κ ν}
-- given
  (hSize : input.slice.entries.size ≤ PY_LIST_MAX)
  (hActive : 2 ≤ input.slice.entries.size) :
-- imply
  StrongPolicyTraceReplaySplit input.runSpan [] reverse input.slice.entries.size (listSortTraced? lt reverse input) := by
-- proof
  let state := (initialMergeState lt input.hasKeyfunc input.slice).1
  have hPackage := initialMergeState_package lt input.hasKeyfunc input.slice
    hSize input.valuesMode
  have hStopped : (initialMergeState lt input.hasKeyfunc input.slice).2 = true :=
    hPackage.minrunStopped
  have hNotSmall : ¬ input.slice.entries.size < 2 := by omega
  have hInitialInv := initialScanInvariant lt input hActive hSize
  have hInitialPower := initialScanPowerForestInv lt input hSize
  cases reverse with
  | false =>
    have hScan := listSortScan_policyReplay_core input.slice.entries.size
      state 0 0 input.slice.entries.size false input.slice.entries.size lt
      input.hasKeyfunc input.runSpan [] (by simpa [state] using hInitialInv)
      (le_refl _) (by simp [ListSortInput.runSpan])
      (by simp [ListSortInput.runSpan])
      (by
        unfold PolicyForestMatches
        simpa [state] using hPackage.pending)
      (by simpa [state] using hInitialPower)
    apply hScan.of_policyEvents_eq_and_reached
    · simp [listSortTraced?, listSortImplTraced?, hSize, hStopped,
      hNotSmall, state]
    · intro openState collapsed hReached
      have hWrapped := ListSortScanReachedCollapse.prependMemoryEvent
        (listSortScanTraced? input.slice.entries.size state 0
          input.slice.entries.size false input.slice.entries.size)
        (.initial (MergeMemorySnapshot.ofState state)) hReached
      simpa [listSortTraced?, listSortImplTraced?, hSize, hStopped,
        hNotSmall, state] using hWrapped
  | true =>
    have hRange : SortSlice.RangeInBounds state.data 0
      input.slice.entries.size := by
      constructor
      · omega
      · rw [show state.data.entries.size = input.slice.entries.size by
        simp [state]]
        simp
    rcases sortsliceReverse_safe state.a.hasValues state.data 0
      input.slice.entries.size hRange
      (by simpa [state] using hPackage.valuesMode) with
      ⟨reversed, hReversed⟩
    let reversedState : MergeState κ ν :=
      { state with data := reversed.slice }
    have hReversedInv : ListSortScanInvariant lt input.hasKeyfunc
      input.slice.entries.size reversedState 0 0
      input.slice.entries.size := by
      apply ListSortScanInvariant.withDataForPolicy
        (by simpa [state] using hInitialInv) reversed.slice
      · simpa [state] using hReversed.sizeEq
      · simpa [reversedState] using hReversed.valuesMode
    have hReversedPower : ScanPowerForestInv input.runSpan []
      reversedState := by
      simpa [reversedState, state] using
        reversedScanPowerForestInv lt input hSize reversed
    have hScan := listSortScan_policyReplay_core input.slice.entries.size
      reversedState 0 0 input.slice.entries.size true
      input.slice.entries.size lt input.hasKeyfunc input.runSpan []
      hReversedInv (le_refl _) (by simp [ListSortInput.runSpan])
      (by simp [ListSortInput.runSpan])
      (by
        unfold PolicyForestMatches
        simpa [reversedState, state] using hPackage.pending)
      hReversedPower
    have hInitialReverseEq :
      (listSortInitialReverseTraced? state
        input.slice.entries.size).result = some reversed := by
      simpa [listSortInitialReverseTraced?] using hReversed.resultEq
    let afterReverse : ReverseSliceResult κ ν →
      TraceResult (ListSortImplResult κ ν) := fun nextReversed =>
      let nextState : MergeState κ ν :=
        { state with data := nextReversed.slice }
      if nextReversed.fuelExhausted then
        finishListSortTraced? nextState true input.slice.entries.size (-1)
          true
      else
        listSortScanTraced? input.slice.entries.size nextState 0
          input.slice.entries.size true input.slice.entries.size
    apply hScan.of_policyEvents_eq_and_reached
    · have hReverseNil := listSortInitialReverseTraced_policyEvents_eq_nil
      state input.slice.entries.size
      simp [listSortTraced?, listSortImplTraced?, hSize, hStopped,
        hNotSmall, state, TraceResult.policyEvents_bind,
        hInitialReverseEq, hReversed.resultFuel, reversedState, hReverseNil]
    · intro openState collapsed hReached
      have hTail : ListSortScanReachedCollapse true
        input.slice.entries.size openState collapsed
        (afterReverse reversed) := by
        simpa [afterReverse, hReversed.resultFuel, reversedState] using
          hReached
      have hBound := ListSortScanReachedCollapse.through_bind
        (listSortInitialReverseTraced? state input.slice.entries.size)
        afterReverse reversed hInitialReverseEq hTail
      have hWrapped := ListSortScanReachedCollapse.prependMemoryEvent
        ((listSortInitialReverseTraced? state input.slice.entries.size).bind
          afterReverse)
        (.initial (MergeMemorySnapshot.ofState state)) hBound
      simpa [listSortTraced?, listSortImplTraced?, hSize, hStopped,
        hNotSmall, state, afterReverse] using hWrapped

end CPythonListsort


-- created on 2026-10-23
