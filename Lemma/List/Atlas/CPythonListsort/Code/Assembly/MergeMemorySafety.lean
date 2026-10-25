import Mathlib
import sympy.Basic
import Def.CPythonListsort.Code.Assembly.MergeMemorySafety
open CPythonListsort


namespace CPythonListsort

/--
[listSortImpl_mergeMemory_lifecycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemorySafety.lean)
-/
@[path]
lemma listSortImpl_mergeMemory_lifecycle
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {input : SortSlice κ ν}
-- given
  (reverse hasKeyfunc : Bool)
  (hSize : input.entries.size ≤ PY_LIST_MAX)
  (hMode : SortSlice.ValuesModeInvariant hasKeyfunc input) :
-- imply
  ∃ result, (listSortImplTraced? lt reverse hasKeyfunc input).result = some result ∧ (listSortImplTraced? lt reverse hasKeyfunc input).trace.MergeMemoryLifecycle hasKeyfunc (MergeMemorySnapshot.ofState (initialMergeState lt hasKeyfunc input).1) (MergeMemorySnapshot.ofState result.state) := by
-- proof
  rcases listSortImplTraced_safe lt reverse hasKeyfunc input hSize hMode with
    ⟨result, hSafe⟩
  exact ⟨result, hSafe.resultEq, hSafe.memoryLifecycle⟩

end CPythonListsort

namespace CPythonListsort

/--
[listSortImpl_mergeMemory_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemorySafety.lean)
-/
@[path]
lemma listSortImpl_mergeMemory_safe
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {input : SortSlice κ ν}
-- given
  (reverse hasKeyfunc : Bool)
  (hSize : input.entries.size ≤ PY_LIST_MAX)
  (hMode : SortSlice.ValuesModeInvariant hasKeyfunc input) :
-- imply
  ∃ result, ListSortImplMergeMemorySafetyPost lt reverse hasKeyfunc input result := by
-- proof
  rcases listSortImplTraced_safe lt reverse hasKeyfunc input hSize hMode with
    ⟨result, hSafe⟩
  exact ⟨result,
    { resultEq := hSafe.resultEq
      returnCode := hSafe.returnCode
      resultFuel := hSafe.resultFuel
      traceFuel := hSafe.traceSafety.fuel
      exactErasure := hSafe.exactErasure
      rawResultEq := by
        calc
          listSortImpl? lt reverse hasKeyfunc input =
            (listSortImplTraced? lt reverse hasKeyfunc input).erase :=
            hSafe.exactErasure.symm
          _ = (listSortImplTraced? lt reverse hasKeyfunc input).result := rfl
          _ = some result := hSafe.resultEq
      allAccessesInBounds := hSafe.traceSafety.accessesInBounds
      tempPayloadAccessesLive := hSafe.traceSafety.tempAccessesLive
      stackDepthMax := hSafe.traceSafety.stackDepth
      stackDepthBelowCapacity := by norm_num [MAX_MERGE_PENDING]
      initialPhysicalBound := by
        have hInitial := initialMergeState_package lt hasKeyfunc input hSize hMode
        simpa [MergeMemorySnapshot.PhysicalBound,
          MergeMemorySnapshot.ofState] using hInitial.physicalSlotsBound
      memoryLifecycle := hSafe.memoryLifecycle
      finalTempInvariant := hSafe.finalTempInvariant
      finalValuesMode := hSafe.finalValuesMode
      finalHasValues := hSafe.finalHasValues
      finalPhysicalBound := hSafe.finalPhysicalBound
      memcpyProvenance :=
        mergeMemcpyCallsiteProvenance (κ := κ) (ν := ν) }⟩

end CPythonListsort

namespace CPythonListsort

/--
[listSort_mergeMemory_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemorySafety.lean)
-/
@[path]
lemma listSort_mergeMemory_safe
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {reverse : Bool}
  {input : ListSortInput κ ν}
-- given
  (hSize : input.slice.entries.size ≤ PY_LIST_MAX) :
-- imply
  ∃ result, ListSortMergeMemorySafetyPost lt reverse input result := by
-- proof
  obtain ⟨result, hSafe⟩ := listSortTraced_safe lt reverse input hSize
  exact ⟨result,
    { resultEq := hSafe.resultEq
      returnCode := hSafe.returnCode
      resultFuel := hSafe.resultFuel
      traceFuel := hSafe.traceSafety.fuel
      exactErasure := hSafe.exactErasure
      rawResultEq := by
        calc
          listSort? lt reverse input =
            (listSortTraced? lt reverse input).erase :=
            hSafe.exactErasure.symm
          _ = (listSortTraced? lt reverse input).result := rfl
          _ = some result := hSafe.resultEq
      allAccessesInBounds := hSafe.traceSafety.accessesInBounds
      tempPayloadAccessesLive := hSafe.traceSafety.tempAccessesLive
      stackDepthMax := hSafe.traceSafety.stackDepth
      stackDepthBelowCapacity := by norm_num [MAX_MERGE_PENDING]
      initialPhysicalBound := by
        have hInitial := initialMergeState_package lt input.hasKeyfunc
          input.slice hSize input.valuesMode
        simpa [MergeMemorySnapshot.PhysicalBound,
          MergeMemorySnapshot.ofState] using hInitial.physicalSlotsBound
      memoryLifecycle := hSafe.memoryLifecycle
      finalTempInvariant := hSafe.finalTempInvariant
      finalValuesMode := hSafe.finalValuesMode
      finalHasValues := hSafe.finalHasValues
      finalPhysicalBound := hSafe.finalPhysicalBound
      memcpyProvenance :=
        mergeMemcpyCallsiteProvenance (κ := κ) (ν := ν) }⟩

end CPythonListsort

namespace CPythonListsort

/--
[listSort_unkeyedArray_mergeMemory_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemorySafety.lean)
-/
@[path]
lemma listSort_unkeyedArray_mergeMemory_safe
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {reverse : Bool}
  {keys : Array κ}
-- given
  (hSize : keys.size ≤ PY_LIST_MAX) :
-- imply
  ∃ result, ListSortMergeMemorySafetyPost lt reverse (ListSortInput.unkeyed keys) result := by
-- proof
  apply listSort_mergeMemory_safe lt reverse (ListSortInput.unkeyed keys)
  simpa [ListSortInput.unkeyed, ListSortInput.unkeyedAs] using hSize
/-! ## Exact top-level lifecycle regressions
The two empty-input regressions below are kernel-checked structural proofs.
The three larger executable regressions are deliberately isolated
compiler-checked proof leaves: they evaluate the complete top-level model, but
no theorem or definition consumes them.  They are listed by name in the
roadmap's two-tier proof-trust ledger.
-/
namespace MergeMemoryRegression

end CPythonListsort

namespace CPythonListsort

/--
[listSort_mergeMemory_empty_unkeyed_trace_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemorySafety.lean)
-/
@[path]
lemma listSort_mergeMemory_empty_unkeyed_trace_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  let input := MergeMemoryRegression.emptyUnkeyed let state := (initialMergeState MergeMemoryRegression.natLt input.hasKeyfunc input.slice).1 (listSortTraced? MergeMemoryRegression.natLt false input).trace.memoryEvents = [.initial (MergeMemorySnapshot.ofState state), .cleanup (MergeMemorySnapshot.ofState state) (MergeMemorySnapshot.ofState (mergeFreemem state))] := by
-- proof
  dsimp only
  have hSize : MergeMemoryRegression.emptyUnkeyed.slice.entries.size ≤
    PY_LIST_MAX := by
    simp [MergeMemoryRegression.emptyUnkeyed,
      ListSortInput.unkeyedAs]
  have hPackage := initialMergeState_package MergeMemoryRegression.natLt
    MergeMemoryRegression.emptyUnkeyed.hasKeyfunc
    MergeMemoryRegression.emptyUnkeyed.slice hSize
    MergeMemoryRegression.emptyUnkeyed.valuesMode
  have hSmall : MergeMemoryRegression.emptyUnkeyed.slice.entries.size < 2 := by
    simp [MergeMemoryRegression.emptyUnkeyed,
      ListSortInput.unkeyedAs]
  simp [listSortTraced?, listSortImplTraced?, hSize,
    hPackage.minrunStopped, hSmall, finishListSortTraced?,
    listSortCleanupMemoryEvent, TraceResult.pure,
    TraceResult.appendMemoryEvent, TraceResult.prependMemoryEvent,
    AccessTrace.empty, AccessTrace.singletonMemoryEvent, AccessTrace.compose]

end CPythonListsort

namespace CPythonListsort

/--
[listSort_mergeMemory_empty_keyed_trace_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemorySafety.lean)
-/
@[path]
lemma listSort_mergeMemory_empty_keyed_trace_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  let input := MergeMemoryRegression.emptyKeyed let state := (initialMergeState MergeMemoryRegression.natLt input.hasKeyfunc input.slice).1 (listSortTraced? MergeMemoryRegression.natLt false input).trace.memoryEvents = [.initial (MergeMemorySnapshot.ofState state), .cleanup (MergeMemorySnapshot.ofState state) (MergeMemorySnapshot.ofState (mergeFreemem state))] ∧ (MergeMemorySnapshot.ofState state).hasValues = true := by
-- proof
  dsimp only
  have hSize : MergeMemoryRegression.emptyKeyed.slice.entries.size ≤
    PY_LIST_MAX := by
    simp [MergeMemoryRegression.emptyKeyed, ListSortInput.keyed]
  have hPackage := initialMergeState_package MergeMemoryRegression.natLt
    MergeMemoryRegression.emptyKeyed.hasKeyfunc
    MergeMemoryRegression.emptyKeyed.slice hSize
    MergeMemoryRegression.emptyKeyed.valuesMode
  have hSmall : MergeMemoryRegression.emptyKeyed.slice.entries.size < 2 := by
    simp [MergeMemoryRegression.emptyKeyed, ListSortInput.keyed]
  constructor
  · simp [listSortTraced?, listSortImplTraced?, hSize,
    hPackage.minrunStopped, hSmall, finishListSortTraced?,
    listSortCleanupMemoryEvent, TraceResult.pure,
    TraceResult.appendMemoryEvent, TraceResult.prependMemoryEvent,
    AccessTrace.empty, AccessTrace.singletonMemoryEvent,
    AccessTrace.compose]
  · exact hPackage.hasValues.trans (by
    simp [MergeMemoryRegression.emptyKeyed, ListSortInput.keyed])

end CPythonListsort

namespace CPythonListsort

/--
[listSort_mergeMemory_lo_event_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemorySafety.lean)
-/
@[path]
lemma listSort_mergeMemory_lo_event_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  MergeMemoryRegression.directions MergeMemoryRegression.loInput = [.lo] := by
-- proof
  native_decide

end CPythonListsort

namespace CPythonListsort

/--
[listSort_mergeMemory_lo_aggregate_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemorySafety.lean)
-/
@[path]
lemma listSort_mergeMemory_lo_aggregate_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  ∃ result, ListSortMergeMemorySafetyPost MergeMemoryRegression.natLt false MergeMemoryRegression.loInput result := by
-- proof
  apply listSort_mergeMemory_safe
  norm_num [MergeMemoryRegression.loInput,
    MergeMemoryRegression.twoRunKeys, ListSortInput.unkeyedAs, PY_LIST_MAX,
    PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES]

end CPythonListsort

namespace CPythonListsort

/--
[listSort_mergeMemory_hi_event_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemorySafety.lean)
-/
@[path]
lemma listSort_mergeMemory_hi_event_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  MergeMemoryRegression.directions MergeMemoryRegression.hiInput = [.hi] := by
-- proof
  native_decide

end CPythonListsort

namespace CPythonListsort

/--
[listSort_mergeMemory_released_growth_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemorySafety.lean)
-/
@[path]
lemma listSort_mergeMemory_released_growth_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  MergeMemoryRegression.growthSummaries = [(some .inline, .heap, 129), (none, .heap, 129), (some .released, .heap, 258)] := by
-- proof
  native_decide

end CPythonListsort


-- created on 2026-10-23
