/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeForceCollapseCorrectness.lean -/

import Def.CPythonListsort.Code.Assembly.MergeForceCollapseSafety.Part2
import Def.CPythonListsort.Code.Correctness.MergeAtCorrectness.Part2
import Structure.CPythonListsort.Code.Correctness.MergeForceCollapseCorrectness.Part2
/-!
# Functional correctness of `merge_force_collapse`

The final collapse repeatedly delegates to the already-correct `merge_at`
implementation.  This module carries the pending-run correctness and complete
entry snapshot through the actual fuel-bounded collapse evaluator; it does not
replace that evaluator by a mathematical fold.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

def forceCollapseCorrectnessRegressionView
    (result : MergeForceCollapseResult (Occurrence Nat) Nat) :
    ForceCollapseCorrectnessRegressionView :=
  { returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted
    pending := result.state.pending.toList.map (fun run =>
      (run.base, run.len.toNat))
    entries := result.state.data.entries.toList.map (fun entry =>
      (entry.key.value, entry.key.origin, entry.value)) }

def forceCollapseCorrectnessRegressionExpected :
    ForceCollapseCorrectnessRegressionView :=
  { returnCode := 0
    fuelExhausted := false
    pending := [(0, 3)]
    entries := [(7, 0, some 10), (7, 1, some 20), (7, 2, some 30)] }

end CPythonListsort
