/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortCostBound.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.AlphabeticCostBound
import sympy.atlas.CPythonListsort.Code.Assembly.ListSortCollapseCost
import sympy.atlas.CPythonListsort.Code.Assembly.ListSortPolicyEndpoints
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.ListSortPolicyBridge
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.ListSortScanPolicy
import sympy.atlas.CPythonListsort.Code.Assembly.ListSortScanReached

/-!
# Public PowerSort merge-cost bound for the real top-level evaluator

This module is the public assembly boundary for the three merge-cost stretch
nodes.  The headline theorem has only the real top-level inputs: an arbitrary
total Boolean comparator, the reverse flag, a mode-valid `ListSortInput`, and
the platform size bound.  In particular, no order law, fuel premise, storage
premise, loop invariant, or merge-tree premise is exposed to callers.

For inputs of length at least two, `ListSortActiveMergeCostPost` retains the
actual control-flow witness for the state passed to `merge_force_collapse`.
This is deliberately stronger than reconstructing an open forest from the
policy-event projection after the fact.  Empty and singleton inputs are stated
separately because the genuine machine trace contains no formed-run event in
either bypass case; the singleton leaf exists only at the paper-facing
normalization boundary.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Evidence for the genuine scan/final-collapse path of an input of length at
least two.

The witness simultaneously identifies the state actually passed to
`mergeForceCollapseTraced?`, the checked policy replay on each side of that
call boundary, the scan-carried historical PowerSort invariant, and the exact
source-level CPython collapse-cost relation.  Thus the comparison with the
canonical top-pair completion is a theorem about the reached execution, not a
tree reconstructed solely from an event list. -/
structure ListSortActiveMergeCostPost
    (lt : BoolComparator κ) (reverse : Bool) (input : ListSortInput κ ν)
    (implementationPlan powerSortPlan : MergePlan)
    (openState : MergeState κ ν)
    (openForest closedForest : List SpannedMergeTree)
    (scanEvents collapseEvents : List PolicyEvent)
    (collapsed : MergeForceCollapseResult κ ν) : Prop where
  traceSplit :
    (listSortTraced? lt reverse input).trace.policyEvents =
      scanEvents ++ collapseEvents
  reachedCollapse :
    ListSortScanReachedCollapse reverse input.slice.entries.size openState
      collapsed (listSortTraced? lt reverse input)
  scanReplay :
    replayPolicyEventsFrom? input.runSpan [] scanEvents = some openForest
  scanHistorical :
    ScanPowerForestInv input.runSpan openForest openState
  openLayout : PendingLayout openState input.runSpan.len
  openPowered : PoweredPrefix openState
  openPowerValid : PowerOpenForestValid input.runSpan openForest
  collapseSafety :
    MergeForceCollapseSafetyPost openState input.runSpan.len collapsed
  collapseEvents_eq :
    collapseEvents =
      (mergeForceCollapseTraced? openState).trace.policyEvents
  collapseReplay :
    replayPolicyEventsFrom? input.runSpan openForest collapseEvents =
      some closedForest
  closedMatch : PolicyForestMatches closedForest collapsed.state
  closedSingleton : ∃ root, closedForest = [root]
  collapseFormedLengths : PolicyEvent.formedLengths collapseEvents = []
  scanCost :
    forestMergeCost openForest = PolicyEvent.logicalMergeCost scanEvents
  collapseCost :
    CPythonForceCollapseCost (openForestLengths openForest)
      (PolicyEvent.logicalMergeCost collapseEvents)
  powerSortPlan_eq :
    powerSortPlan = canonicalTopPairCompletion input.runSpan openForest
  implementationCostSplit :
    implementationPlan.mergeCost =
      forestMergeCost openForest +
        PolicyEvent.logicalMergeCost collapseEvents
  collapseDominance :
    forestMergeCost openForest +
        PolicyEvent.logicalMergeCost collapseEvents ≤
      (canonicalTopPairCompletion input.runSpan openForest).mergeCost

/-- Public merge-cost certificate for one genuine top-level execution.

`profile` is the exact adaptive-run profile recorded by the normalized real
trace.  `implementationPlan` is the exact checked replay of that trace.
`powerSortPlan` is the canonical source-faithful PowerSort completion on the
same leaves; on active inputs the accompanying witness exposes the actual
reached open forest from which it is completed. -/
structure ListSortMergeCostPost
    (lt : BoolComparator κ) (reverse : Bool) (input : ListSortInput κ ν)
    (result : ListSortImplResult κ ν)
    (profile : RunProfile input.slice.entries.size)
    (implementationPlan powerSortPlan : MergePlan) : Prop where
  safety : ListSortSafetyPost lt reverse input result
  normalizedReplay :
    replayTopLevelMergePlan? input.runSpan
        (listSortTraced? lt reverse input).trace.policyEvents =
      some implementationPlan
  profileLengths :
    profile.lengths =
      topLevelFormedLengths input.runSpan
        (listSortTraced? lt reverse input).trace.policyEvents
  implementationLeaves : implementationPlan.runLengths = profile.lengths
  implementationCost :
    implementationPlan.mergeCost =
      PolicyEvent.logicalMergeCost
        (listSortTraced? lt reverse input).trace.policyEvents
  weightedPathCost :
    implementationPlan.mergeCost = implementationPlan.weightedPathLength
  formedLengthRelation : ∀ push,
    .formed push ∈
        (listSortTraced? lt reverse input).trace.policyEvents →
      FormedLengthRelation push
  powerLeaves : powerSortPlan.runLengths = profile.lengths
  powerValid :
    PowerMergePlanValid input.runSpan.base
      (BitVec.ofNat 64 input.runSpan.len) powerSortPlan
  implementation_le_power :
    implementationPlan.mergeCost ≤ powerSortPlan.mergeCost
  entropyBound :
    (PolicyEvent.logicalMergeCost
        (listSortTraced? lt reverse input).trace.policyEvents : Real) ≤
      (input.slice.entries.size : Real) * profile.entropy +
        2 * (input.slice.entries.size : Real)
  optimalAlphabeticBound :
    (PolicyEvent.logicalMergeCost
        (listSortTraced? lt reverse input).trace.policyEvents : Real) ≤
      (optimalAlphabeticMergeCost profile.lengths : Real) +
        2 * (input.slice.entries.size : Real)
  emptyCase : input.slice.entries.size = 0 →
    (listSortTraced? lt reverse input).trace.policyEvents = [] ∧
      implementationPlan = .empty ∧
      powerSortPlan = .empty ∧
      profile.lengths = [] ∧
      PolicyEvent.logicalMergeCost
        (listSortTraced? lt reverse input).trace.policyEvents = 0
  singletonCase : input.slice.entries.size = 1 →
    (listSortTraced? lt reverse input).trace.policyEvents = [] ∧
      implementationPlan = .tree (.leaf 1) ∧
      powerSortPlan = .tree (.leaf 1) ∧
      profile.lengths = [1] ∧
      PolicyEvent.logicalMergeCost
        (listSortTraced? lt reverse input).trace.policyEvents = 0
  activeCase : 2 ≤ input.slice.entries.size →
    ∃ (openState : MergeState κ ν)
      (openForest closedForest : List SpannedMergeTree)
      (scanEvents collapseEvents : List PolicyEvent)
      (collapsed : MergeForceCollapseResult κ ν),
      ListSortActiveMergeCostPost lt reverse input implementationPlan
        powerSortPlan openState openForest closedForest scanEvents
        collapseEvents collapsed

/-- Reindex the profile extracted from a valid finite-width PowerSort plan by
the ordinary natural input length.  The platform bound is exactly what rules
out truncation by `BitVec.ofNat 64`. -/
private def naturalRunProfileOfPowerPlan
    (input : ListSortInput κ ν)
    (hSize : input.slice.entries.size ≤ PY_LIST_MAX)
    (plan : MergePlan)
    (hvalid : PowerMergePlanValid input.runSpan.base
      (BitVec.ofNat 64 input.runSpan.len) plan) :
    RunProfile input.slice.entries.size where
  lengths := plan.runLengths
  sum_eq := by
    have hsum := hvalid.runProfile.sum_eq
    change plan.runLengths.sum =
      (BitVec.ofNat 64 input.runSpan.len).toNat at hsum
    simpa [ListSortInput.runSpan, listSizeWord_toNat hSize] using hsum
  positive := by
    have hpositive := hvalid.runProfile.positive
    change ∀ length ∈ plan.runLengths, 0 < length at hpositive
    exact hpositive
