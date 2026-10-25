/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeForceCollapseCorrectness.lean -/

import Def.CPythonListsort.Code.Assembly.MergeForceCollapseSafety.Part2
import Def.CPythonListsort.Code.Correctness.MergeAtCorrectness.Part2
import Def.CPythonListsort.Code.Correctness.MergeForceCollapseCorrectness
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

structure ForceCollapseCorrectnessRegressionView where
  returnCode : Int
  fuelExhausted : Bool
  pending : List (Nat × Nat)
  entries : List (Nat × Nat × Option Nat)
  deriving DecidableEq, Repr

end CPythonListsort
