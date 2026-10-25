import Mathlib
import sympy.Basic
import Def.CPythonListsort.Code.Correctness.MergeLoRegressionKernel
open CPythonListsort


namespace CPythonListsort

/--
[mergeLoCorrectnessRegression_kernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeLoRegressionKernel.lean)
-/
@[path]
lemma mergeLoCorrectnessRegression_kernel
-- imply
  (mergeLo? mergeLoCorrectnessRegressionState 1 3 2 3).map (fun result => (result.returnCode, result.fuelExhausted, result.state.data.entries.toList)) = some (0, false, [mergeLoCorrectnessEntry 99 990, mergeLoCorrectnessEntry 2 20, mergeLoCorrectnessEntry 4 40, mergeLoCorrectnessEntry 4 41, mergeLoCorrectnessEntry 5 50, mergeLoCorrectnessEntry 6 60, mergeLoCorrectnessEntry 100 1000]) := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoCorrectnessRegression_tempStorage_kernel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeLoRegressionKernel.lean)
-/
@[path]
lemma mergeLoCorrectnessRegression_tempStorage_kernel
-- imply
  TempStorageInv mergeLoCorrectnessRegressionState.a mergeLoCorrectnessRegressionState.alloced := by
-- proof
  change 4 = (4 : Nat) ∧ 2 * 4 ≤ 256
  norm_num

end CPythonListsort


-- created on 2026-10-23
