import Mathlib
import sympy.Basic
import Def.CPythonListsort.Code.Assembly.PowerSortCostRegression
open CPythonListsort


namespace CPythonListsort

/--
[listSort_powerSort_cost_rotation_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortCostRegression.lean)
-/
@[path]
lemma listSort_powerSort_cost_rotation_regression
-- imply
  powerSortCostRegressionInput.entries.size = 256 ∧ (initialMergeState (fun left right : Nat => decide (left < right)) false powerSortCostRegressionInput).1.mr_e = 3 ∧ (listSortImplTraced? (fun left right : Nat => decide (left < right)) false false powerSortCostRegressionInput).result.map (fun result => (result.returnCode, result.fuelExhausted)) = some (0, false) ∧ powerSortCostRegressionTrace = powerSortCostRegressionScanEvents ++ powerSortCostRegressionCollapseEvents ∧ PolicyEvent.formedLengths powerSortCostRegressionTrace = [32, 33, 83, 36, 32, 32, 8] ∧ policyBoundaryPowers { base := 0, len := 256 } (PolicyEvent.formedSpans powerSortCostRegressionTrace) = [3, 2, 1, 2, 3, 4] ∧ (replayPolicyEvents? { base := 0, len := 256 } powerSortCostRegressionScanEvents).map openForestLengths = some [148, 36, 32, 32, 8] ∧ (replayPolicyEvents? { base := 0, len := 256 } powerSortCostRegressionScanEvents).map (fun forest => policyBoundaryPowers { base := 0, len := 256 } (forest.map SpannedMergeTree.span)) = some [1, 2, 3, 4] ∧ PolicyEvent.logicalMergeCost powerSortCostRegressionScanEvents = 213 ∧ PolicyEvent.logicalMergeCosts powerSortCostRegressionCollapseEvents = [40, 68, 108, 256] ∧ PolicyEvent.logicalMergeCost powerSortCostRegressionCollapseEvents = 472 ∧ PolicyEvent.logicalMergeCost powerSortCostRegressionTrace = 685 ∧ topPairCompletionMergeCosts [148, 36, 32, 32, 8] = [40, 72, 108, 256] ∧ topPairCompletionCost [148, 36, 32, 32, 8] = 476 ∧ 213 + 476 = 689 ∧ 213 + 472 = 685 := by
-- proof
  native_decide

end CPythonListsort


-- created on 2026-10-23
