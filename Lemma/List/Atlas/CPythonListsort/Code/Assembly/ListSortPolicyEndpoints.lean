import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Assembly.ListSortPolicyEndpoints
open CPythonListsort


namespace CPythonListsort

/--
[listSortTraced_policy_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortPolicyEndpoints.lean)
-/
@[path]
lemma listSortTraced_policy_empty
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {reverse : Bool}
  {input : ListSortInput κ ν}
-- given
  (hEmpty : input.slice.entries.size = 0) :
-- imply
  ∃ result, ListSortPolicyEndpointPost lt reverse input result .empty [] := by
-- proof
  have hSize : input.slice.entries.size ≤ PY_LIST_MAX := by omega
  have hSmall : input.slice.entries.size < 2 := by omega
  have hPackage := initialMergeState_package lt input.hasKeyfunc input.slice
    hSize input.valuesMode
  rcases listSortTraced_safe lt reverse input hSize with
    ⟨result, hResult⟩
  have hPolicy :
    (listSortTraced? lt reverse input).trace.policyEvents = [] := by
    simpa [listSortTraced?, listSortImplTraced?, hSize,
      hPackage.minrunStopped, hSmall,
      TraceResult.policyEvents_prependMemoryEvent] using
      (finishListSortTraced_policyEvents_eq_nil
        (initialMergeState lt input.hasKeyfunc input.slice).1 reverse
        input.slice.entries.size 0 false)
  refine ⟨result, ?_⟩
  refine
    { resultEq := hResult.resultEq
      returnCode := hResult.returnCode
      resultFuel := hResult.resultFuel
      policyEvents := hPolicy
      normalizedReplay := ?_
      rawFormedLengths := ?_
      normalizedFormedLengths := ?_
      planRunLengths := rfl
      rawLogicalMergeCost := ?_
      planMergeCost := rfl }
  · rw [hPolicy]
    change replayTopLevelMergePlan?
      { base := 0, len := input.slice.entries.size } [] = some .empty
    rw [hEmpty]
    exact replayTopLevelMergePlan_empty 0
  · simp [hPolicy]
  · rw [hPolicy]
    change topLevelFormedLengths
      { base := 0, len := input.slice.entries.size } [] = []
    rw [hEmpty]
    exact topLevelFormedLengths_empty 0
  · simp [hPolicy]

end CPythonListsort

namespace CPythonListsort

/--
[listSortTraced_policy_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortPolicyEndpoints.lean)
-/
@[path]
lemma listSortTraced_policy_singleton
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {reverse : Bool}
  {input : ListSortInput κ ν}
-- given
  (hSingleton : input.slice.entries.size = 1) :
-- imply
  ∃ result, ListSortPolicyEndpointPost lt reverse input result (.tree (.leaf 1)) [1] := by
-- proof
  have hSize : input.slice.entries.size ≤ PY_LIST_MAX := by
    simp [hSingleton, PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES]
  have hSmall : input.slice.entries.size < 2 := by omega
  have hPackage := initialMergeState_package lt input.hasKeyfunc input.slice
    hSize input.valuesMode
  rcases listSortTraced_safe lt reverse input hSize with
    ⟨result, hResult⟩
  have hPolicy :
    (listSortTraced? lt reverse input).trace.policyEvents = [] := by
    simpa [listSortTraced?, listSortImplTraced?, hSize,
      hPackage.minrunStopped, hSmall,
      TraceResult.policyEvents_prependMemoryEvent] using
      (finishListSortTraced_policyEvents_eq_nil
        (initialMergeState lt input.hasKeyfunc input.slice).1 reverse
        input.slice.entries.size 0 false)
  refine ⟨result, ?_⟩
  refine
    { resultEq := hResult.resultEq
      returnCode := hResult.returnCode
      resultFuel := hResult.resultFuel
      policyEvents := hPolicy
      normalizedReplay := ?_
      rawFormedLengths := ?_
      normalizedFormedLengths := ?_
      planRunLengths := rfl
      rawLogicalMergeCost := ?_
      planMergeCost := rfl }
  · rw [hPolicy]
    change replayTopLevelMergePlan?
      { base := 0, len := input.slice.entries.size } [] =
        some (.tree (.leaf 1))
    rw [hSingleton]
    exact replayTopLevelMergePlan_singleton 0
  · simp [hPolicy]
  · rw [hPolicy]
    change topLevelFormedLengths
      { base := 0, len := input.slice.entries.size } [] = [1]
    rw [hSingleton]
    exact topLevelFormedLengths_singleton 0
  · simp [hPolicy]

end CPythonListsort


-- created on 2026-10-23
