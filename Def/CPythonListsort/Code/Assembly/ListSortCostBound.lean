/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortCostBound.lean -/

import Def.CPythonListsort.Code.Assembly.AlphabeticCostBound.Part2
import Def.CPythonListsort.Code.Assembly.ListSortCollapseCost
import Structure.CPythonListsort.Code.Assembly.ListSortPolicyEndpoints
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.ListSortPolicyBridge
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.ListSortScanPolicy
import Inductive.CPythonListsort.Code.Assembly.ListSortScanReached
import Structure.CPythonListsort.Code.Assembly.ListSortCostBound
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

/-- Reindex the profile extracted from a valid finite-width PowerSort plan by
the ordinary natural input length.  The platform bound is exactly what rules
out truncation by `BitVec.ofNat 64`. -/
def naturalRunProfileOfPowerPlan
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

end CPythonListsort
