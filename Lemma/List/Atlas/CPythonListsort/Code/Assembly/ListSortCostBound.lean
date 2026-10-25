import Mathlib
import sympy.Basic
import Def.CPythonListsort.Code.Assembly.ListSortCostBound
open CPythonListsort


namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[replayTopLevelMergePlan_formedLengthRelation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortCostBound.lean)
-/
@[path]
metadata of every genuine formed event.  The proof handles the empty and
singleton normalization branches explicitly; neither may fabricate a formed
event. -/
private theorem replayTopLevelMergePlan_formedLengthRelation
  {input : RunSpan} {events : List PolicyEvent} {plan : MergePlan}
  (hreplay : replayTopLevelMergePlan? input events = some plan) :
  ∀ push, .formed push ∈ events → FormedLengthRelation push := by
  by_cases hzero : input.len = 0
  · rw [replayTopLevelMergePlan?, if_pos hzero] at hreplay
    by_cases hevents : events = []
    · subst events
      simp
    · rw [if_neg hevents] at hreplay
      contradiction
  · rw [replayTopLevelMergePlan?, if_neg hzero] at hreplay
    by_cases hone : input.len = 1
    · rw [if_pos hone] at hreplay
      by_cases hevents : events = []
      · subst events
        simp
      · rw [if_neg hevents] at hreplay
        contradiction
    · rw [if_neg hone] at hreplay
      unfold replayMergePlan? at hreplay
      cases hforest : replayPolicyEvents? input events with
      | none => simp [hforest] at hreplay
      | some forest =>
        exact replayPolicyEvents_formedLengthRelation hforest

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[powerPlan_naturalProfile_entropyBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortCostBound.lean)
-/
@[path]
by the finite-width PowerSort lemma. -/
private theorem powerPlan_naturalProfile_entropyBound
  (input : ListSortInput κ ν)
  (hSize : input.slice.entries.size ≤ PY_LIST_MAX)
  (plan : MergePlan)
  (hvalid : PowerMergePlanValid input.runSpan.base
    (BitVec.ofNat 64 input.runSpan.len) plan) :
  let profile := naturalRunProfileOfPowerPlan input hSize plan hvalid
  (plan.mergeCost : Real) ≤
    (input.slice.entries.size : Real) * profile.entropy +
      2 * (input.slice.entries.size : Real) := by
  dsimp only
  have hbound := hvalid.mergeCost_le_entropy_add_two
  have hlengths : hvalid.runProfile.lengths = plan.runLengths := by
    rfl
  simp only [RunProfile.entropy, RunProfile.fractions] at hbound ⊢
  rw [hlengths] at hbound
  simpa [naturalRunProfileOfPowerPlan, ListSortInput.runSpan,
    listSizeWord_toNat hSize] using hbound

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[listsort_mergeCost_bound_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortCostBound.lean)
-/
@[path]
private lemma listsort_mergeCost_bound_empty
  (lt : BoolComparator κ) (reverse : Bool) (input : ListSortInput κ ν)
  (hSize : input.slice.entries.size ≤ PY_LIST_MAX)
  (hEmpty : input.slice.entries.size = 0) :
  ∃ (result : ListSortImplResult κ ν)
    (profile : RunProfile input.slice.entries.size)
    (implementationPlan powerSortPlan : MergePlan),
    ListSortMergeCostPost lt reverse input result profile
      implementationPlan powerSortPlan := by
  rcases listSortTraced_safe lt reverse input hSize with
    ⟨result, hsafety⟩
  rcases listSortTraced_policy_empty lt reverse input hEmpty with
    ⟨endpointResult, hendpoint⟩
  have hresultEq : endpointResult = result :=
    Option.some.inj (hendpoint.resultEq.symm.trans hsafety.resultEq)
  subst endpointResult
  let profile : RunProfile input.slice.entries.size :=
    { lengths := []
      sum_eq := by simp [hEmpty]
      positive := by simp }
  have hpower : PowerMergePlanValid input.runSpan.base
    (BitVec.ofNat 64 input.runSpan.len) MergePlan.empty := by
    simp [PowerMergePlanValid, ListSortInput.runSpan, hEmpty]
  have hentropy : (0 : Real) ≤
    (input.slice.entries.size : Real) * profile.entropy +
      2 * (input.slice.entries.size : Real) := by
    simp [hEmpty]
  have hoptimal : (0 : Real) ≤
    (optimalAlphabeticMergeCost profile.lengths : Real) +
      2 * (input.slice.entries.size : Real) := by
    simp [profile, hEmpty]
  refine ⟨result, profile, .empty, .empty, ?_⟩
  refine
    { safety := hsafety
      normalizedReplay := hendpoint.normalizedReplay
      profileLengths := ?_
      implementationLeaves := ?_
      implementationCost := ?_
      weightedPathCost := MergePlan.mergeCost_eq_weightedPathLength .empty
      formedLengthRelation := ?_
      powerLeaves := ?_
      powerValid := hpower
      implementation_le_power := by rfl
      entropyBound := ?_
      optimalAlphabeticBound := ?_
      emptyCase := ?_
      singletonCase := ?_
      activeCase := ?_ }
  · simpa [profile] using hendpoint.normalizedFormedLengths.symm
  · rfl
  · simpa [MergePlan.mergeCost] using hendpoint.rawLogicalMergeCost.symm
  · intro push hpush
    rw [hendpoint.policyEvents] at hpush
    simp at hpush
  · rfl
  · simpa [hendpoint.rawLogicalMergeCost] using hentropy
  · simpa [hendpoint.rawLogicalMergeCost] using hoptimal
  · intro _
    exact ⟨hendpoint.policyEvents, rfl, rfl, rfl,
      hendpoint.rawLogicalMergeCost⟩
  · intro hone
    omega
  · intro hactive
    omega

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[listsort_mergeCost_bound_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortCostBound.lean)
-/
@[path]
private lemma listsort_mergeCost_bound_singleton
  (lt : BoolComparator κ) (reverse : Bool) (input : ListSortInput κ ν)
  (hSize : input.slice.entries.size ≤ PY_LIST_MAX)
  (hSingleton : input.slice.entries.size = 1) :
  ∃ result profile implementationPlan powerSortPlan,
    ListSortMergeCostPost lt reverse input result profile
      implementationPlan powerSortPlan := by
  rcases listSortTraced_safe lt reverse input hSize with
    ⟨result, hsafety⟩
  rcases listSortTraced_policy_singleton lt reverse input hSingleton with
    ⟨endpointResult, hendpoint⟩
  have hresultEq : endpointResult = result :=
    Option.some.inj (hendpoint.resultEq.symm.trans hsafety.resultEq)
  subst endpointResult
  let profile : RunProfile input.slice.entries.size :=
    { lengths := [1]
      sum_eq := by simp [hSingleton]
      positive := by simp }
  let singletonPlan : MergePlan := .tree (.leaf 1)
  have hpower : PowerMergePlanValid input.runSpan.base
    (BitVec.ofNat 64 input.runSpan.len) singletonPlan := by
    simp only [ListSortInput.runSpan, hSingleton]
    rw [powerMergePlanValid_singleton_iff]
    norm_num
  have hentropy : (0 : Real) ≤
    (input.slice.entries.size : Real) * profile.entropy +
      2 * (input.slice.entries.size : Real) := by
    have hprofileEntropy : profile.entropy = 0 := by
      simp [profile, RunProfile.entropy, RunProfile.fractions,
        binaryEntropy, binaryEntropyTerm, Real.logb, hSingleton]
    rw [hprofileEntropy]
    positivity
  have hoptimal : (0 : Real) ≤
    (optimalAlphabeticMergeCost profile.lengths : Real) +
      2 * (input.slice.entries.size : Real) := by
    simp [profile, hSingleton]
  refine ⟨result, profile, singletonPlan, singletonPlan, ?_⟩
  refine
    { safety := hsafety
      normalizedReplay := hendpoint.normalizedReplay
      profileLengths := ?_
      implementationLeaves := ?_
      implementationCost := ?_
      weightedPathCost :=
        MergePlan.mergeCost_eq_weightedPathLength singletonPlan
      formedLengthRelation := ?_
      powerLeaves := ?_
      powerValid := hpower
      implementation_le_power := by rfl
      entropyBound := ?_
      optimalAlphabeticBound := ?_
      emptyCase := ?_
      singletonCase := ?_
      activeCase := ?_ }
  · simpa [profile] using hendpoint.normalizedFormedLengths.symm
  · rfl
  · simpa [singletonPlan, MergePlan.mergeCost, MergeTree.mergeCost] using
    hendpoint.rawLogicalMergeCost.symm
  · intro push hpush
    rw [hendpoint.policyEvents] at hpush
    simp at hpush
  · rfl
  · simpa [hendpoint.rawLogicalMergeCost] using hentropy
  · simpa [hendpoint.rawLogicalMergeCost] using hoptimal
  · intro hzero
    omega
  · intro _
    exact ⟨hendpoint.policyEvents, rfl, rfl, rfl,
      hendpoint.rawLogicalMergeCost⟩
  · intro hactive
    omega

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[listsort_mergeCost_bound_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortCostBound.lean)
-/
@[path]
private lemma listsort_mergeCost_bound_active
  (lt : BoolComparator κ) (reverse : Bool) (input : ListSortInput κ ν)
  (hSize : input.slice.entries.size ≤ PY_LIST_MAX)
  (hActive : 2 ≤ input.slice.entries.size) :
  ∃ result profile implementationPlan powerSortPlan,
    ListSortMergeCostPost lt reverse input result profile
      implementationPlan powerSortPlan := by
  rcases listSortTraced_safe lt reverse input hSize with
    ⟨result, hsafety⟩
  rcases listSortTraced_policyBridge_active lt reverse input hSize hActive with
    ⟨openState, openForest, closedForest, scanEvents, collapseEvents,
      collapsed, witness⟩
  have hopenMax : openState.listlen.toNat ≤ PY_LIST_MAX := by
    rw [witness.openPowerInv.listlen_eq,
      listSizeWord_toNat witness.openPowerInv.inputMax]
    exact witness.openPowerInv.inputMax
  have hcollapseRaw := mergeForceCollapse_cpythonForceCollapseCost
    openState input.runSpan.len collapsed hopenMax witness.replay.openLayout
    witness.openTempInvariant witness.openTempLive witness.openValuesMode
    witness.replay.collapseSafety
  have hcollapseCost :
    CPythonForceCollapseCost (openForestLengths openForest)
      (PolicyEvent.logicalMergeCost collapseEvents) := by
    rw [← witness.replay.openMatch.openForestLengths_eq_pendingRunLengths]
      at hcollapseRaw
    simpa [witness.replay.collapseEvents_eq] using hcollapseRaw
  have hscanCost :
    forestMergeCost openForest =
      PolicyEvent.logicalMergeCost scanEvents := by
    have hcost := replayPolicyEventsFrom_cost
      (policyForestInv_empty input.runSpan) witness.replay.scanReplay
    simpa using hcost
  rcases witness.replay.collapseSafety.finalRun with
    ⟨finalRun, hfinalPending, hfinalBase, hfinalEnd⟩
  have hfinalSize : collapsed.state.pending.size = 1 := by
    have hlength := congrArg List.length hfinalPending
    simpa using hlength
  have hclosedLength : closedForest.length = 1 := by
    rw [witness.replay.closedMatch.length_eq, hfinalSize]
  rcases List.length_eq_one_iff.mp hclosedLength with
    ⟨closedRoot, hclosedForest⟩
  have hrootSpan :
    closedRoot.span = RunSpan.ofPendingRun finalRun := by
    have hmatch := witness.replay.closedMatch
    unfold PolicyForestMatches at hmatch
    rw [hclosedForest, hfinalPending] at hmatch
    simpa using hmatch
  have hfinalLength : finalRun.len.toNat = input.runSpan.len := by
    simp only [PendingRun.endIndex] at hfinalEnd
    omega
  have hclosedSpan : closedRoot.span = input.runSpan := by
    rw [hrootSpan]
    simp [RunSpan.ofPendingRun, hfinalBase,
      witness.openPowerInv.basekeys_eq, hfinalLength]
  let events := (listSortTraced? lt reverse input).trace.policyEvents
  have hfullReplayFrom :
    replayPolicyEventsFrom? input.runSpan [] events =
      some closedForest := by
    dsimp only [events]
    rw [witness.replay.traceSplit, replayPolicyEventsFrom_append,
      witness.replay.scanReplay]
    exact witness.replay.collapseReplay
  have hfullReplay :
    replayPolicyEvents? input.runSpan events = some [closedRoot] := by
    rw [← hclosedForest]
    simpa [replayPolicyEvents?] using hfullReplayFrom
  let implementationPlan : MergePlan := .tree closedRoot.tree
  have hmergeReplay :
    replayMergePlan? input.runSpan events = some implementationPlan := by
    unfold replayMergePlan?
    rw [hfullReplay]
    simpa [implementationPlan] using
      normalizePolicyForest_singleton input.runSpan closedRoot hclosedSpan
  have hzero : input.runSpan.len ≠ 0 := by
    simp only [ListSortInput.runSpan]
    omega
  have hone : input.runSpan.len ≠ 1 := by
    simp only [ListSortInput.runSpan]
    omega
  have hnormalized :
    replayTopLevelMergePlan? input.runSpan events =
      some implementationPlan := by
    simpa [replayTopLevelMergePlan?, hzero, hone] using hmergeReplay
  have himplementationExact := replayTopLevelMergePlan_exact hnormalized
  have hscanLeaves :
    forestRunLengths openForest =
      PolicyEvent.formedLengths scanEvents := by
    have hlengths :=
      replayPolicyEventsFrom_runLengths witness.replay.scanReplay
    simpa using hlengths
  have hformedEvents :
    PolicyEvent.formedLengths events =
      PolicyEvent.formedLengths scanEvents := by
    dsimp only [events]
    rw [witness.replay.traceSplit, PolicyEvent.formedLengths_append,
      witness.collapseFormedLengths, List.append_nil]
  have htopLevelFormed :
    topLevelFormedLengths input.runSpan events =
      PolicyEvent.formedLengths scanEvents := by
    rw [topLevelFormedLengths, if_neg hzero, if_neg hone, hformedEvents]
  let powerSortPlan := canonicalTopPairCompletion input.runSpan openForest
  have hpowerValid : PowerMergePlanValid input.runSpan.base
    (BitVec.ofNat 64 input.runSpan.len) powerSortPlan := by
    simpa [powerSortPlan] using witness.openPowerValid.canonicalCompletion_valid
  have hpowerLeavesTop :
    powerSortPlan.runLengths =
      topLevelFormedLengths input.runSpan events := by
    rw [htopLevelFormed]
    simpa [powerSortPlan, canonicalTopPairCompletion_runLengths] using
      hscanLeaves
  let profile := naturalRunProfileOfPowerPlan input hSize powerSortPlan
    hpowerValid
  have hprofileLengths :
    profile.lengths = topLevelFormedLengths input.runSpan events := by
    simpa [profile, naturalRunProfileOfPowerPlan] using hpowerLeavesTop
  have himplementationLeaves :
    implementationPlan.runLengths = profile.lengths :=
    himplementationExact.1.trans hprofileLengths.symm
  have himplementationSplit :
    implementationPlan.mergeCost =
      forestMergeCost openForest +
        PolicyEvent.logicalMergeCost collapseEvents := by
    calc
      implementationPlan.mergeCost =
        PolicyEvent.logicalMergeCost events := himplementationExact.2
      _ = PolicyEvent.logicalMergeCost scanEvents +
        PolicyEvent.logicalMergeCost collapseEvents := by
          dsimp only [events]
          rw [witness.replay.traceSplit,
            PolicyEvent.logicalMergeCost_append]
      _ = forestMergeCost openForest +
        PolicyEvent.logicalMergeCost collapseEvents := by
          rw [hscanCost]
  have hcollapseDominance :=
    witness.openPowerValid.cpythonForceCollapseCost_le_canonical
      hcollapseCost
  have himplementationLePower :
    implementationPlan.mergeCost ≤ powerSortPlan.mergeCost := by
    rw [himplementationSplit]
    simpa [powerSortPlan] using hcollapseDominance
  have hpowerEntropy : (powerSortPlan.mergeCost : Real) ≤
    (input.slice.entries.size : Real) * profile.entropy +
      2 * (input.slice.entries.size : Real) := by
    simpa [profile] using
      powerPlan_naturalProfile_entropyBound input hSize powerSortPlan
        hpowerValid
  have himplementationLePowerReal :
    (implementationPlan.mergeCost : Real) ≤
      (powerSortPlan.mergeCost : Real) := by
    exact_mod_cast himplementationLePower
  have hentropy :
    (PolicyEvent.logicalMergeCost events : Real) ≤
      (input.slice.entries.size : Real) * profile.entropy +
        2 * (input.slice.entries.size : Real) := by
    rw [← himplementationExact.2]
    exact himplementationLePowerReal.trans hpowerEntropy
  have hoptimal :
    (PolicyEvent.logicalMergeCost events : Real) ≤
      (optimalAlphabeticMergeCost profile.lengths : Real) +
        2 * (input.slice.entries.size : Real) :=
    mergeCost_le_optimalAlphabetic_add_two profile hentropy
  refine ⟨result, profile, implementationPlan, powerSortPlan, ?_⟩
  refine
    { safety := hsafety
      normalizedReplay := hnormalized
      profileLengths := hprofileLengths
      implementationLeaves := himplementationLeaves
      implementationCost := himplementationExact.2
      weightedPathCost :=
        MergePlan.mergeCost_eq_weightedPathLength implementationPlan
      formedLengthRelation :=
        replayTopLevelMergePlan_formedLengthRelation hnormalized
      powerLeaves := rfl
      powerValid := hpowerValid
      implementation_le_power := himplementationLePower
      entropyBound := hentropy
      optimalAlphabeticBound := hoptimal
      emptyCase := ?_
      singletonCase := ?_
      activeCase := ?_ }
  · intro hempty
    omega
  · intro hsingleton
    omega
  · intro _
    refine ⟨openState, openForest, closedForest, scanEvents,
      collapseEvents, collapsed, ?_⟩
    exact
      { traceSplit := witness.replay.traceSplit
        reachedCollapse := witness.reachedCollapse
        scanReplay := witness.replay.scanReplay
        scanHistorical := witness.openPowerInv
        openLayout := witness.replay.openLayout
        openPowered := witness.replay.openPowered
        openPowerValid := witness.openPowerValid
        collapseSafety := witness.replay.collapseSafety
        collapseEvents_eq := witness.replay.collapseEvents_eq
        collapseReplay := witness.replay.collapseReplay
        closedMatch := witness.replay.closedMatch
        closedSingleton := ⟨closedRoot, hclosedForest⟩
        collapseFormedLengths := witness.collapseFormedLengths
        scanCost := hscanCost
        collapseCost := hcollapseCost
        powerSortPlan_eq := rfl
        implementationCostSplit := himplementationSplit
        collapseDominance := hcollapseDominance }

end CPythonListsort

namespace CPythonListsort

/--
[listsort_mergeCost_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortCostBound.lean)
-/
@[path]
lemma listsort_mergeCost_bound
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {reverse : Bool}
  {input : ListSortInput κ ν}
-- given
  (hSize : input.slice.entries.size ≤ PY_LIST_MAX) :
-- imply
  ∃ result profile implementationPlan powerSortPlan, ListSortMergeCostPost lt reverse input result profile implementationPlan powerSortPlan := by
-- proof
  by_cases hEmpty : input.slice.entries.size = 0
  · exact listsort_mergeCost_bound_empty lt reverse input hSize hEmpty
  by_cases hSingleton : input.slice.entries.size = 1
  · exact listsort_mergeCost_bound_singleton lt reverse input hSize
    hSingleton
  have hActive : 2 ≤ input.slice.entries.size := by omega
  exact listsort_mergeCost_bound_active lt reverse input hSize hActive

end CPythonListsort

namespace CPythonListsort

/--
[listsort_mergeTree_cost_le_powerSort](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortCostBound.lean)
-/
@[path]
lemma listsort_mergeTree_cost_le_powerSort
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {reverse : Bool}
  {input : ListSortInput κ ν}
-- given
  (hSize : input.slice.entries.size ≤ PY_LIST_MAX) :
-- imply
  ∃ (result : ListSortImplResult κ ν) (profile : RunProfile input.slice.entries.size) (implementationPlan powerSortPlan : MergePlan), ListSortSafetyPost lt reverse input result ∧ replayTopLevelMergePlan? input.runSpan (listSortTraced? lt reverse input).trace.policyEvents = some implementationPlan ∧ implementationPlan.runLengths = profile.lengths ∧ powerSortPlan.runLengths = profile.lengths ∧ PowerMergePlanValid input.runSpan.base (BitVec.ofNat 64 input.runSpan.len) powerSortPlan ∧ implementationPlan.mergeCost ≤ powerSortPlan.mergeCost := by
-- proof
  rcases listsort_mergeCost_bound lt reverse input hSize with
    ⟨result, profile, implementationPlan, powerSortPlan, post⟩
  exact ⟨result, profile, implementationPlan, powerSortPlan, post.safety,
    post.normalizedReplay, post.implementationLeaves, post.powerLeaves,
    post.powerValid, post.implementation_le_power⟩

end CPythonListsort


-- created on 2026-10-23
