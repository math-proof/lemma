/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeForceCollapseCorrectness.lean -/

import Def.CPythonListsort.Code.Assembly.MergeForceCollapseSafety.Part2
import Def.CPythonListsort.Code.Correctness.MergeAtCorrectness.Part2
import Structure.CPythonListsort.Code.Correctness.MergeForceCollapseCorrectness
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

def forceCollapseCorrectnessRegressionLt : BoolComparator Nat :=
  fun _ _ => false

def forceCollapseCorrectnessRegressionEntry
    (origin payload : Nat) : SortSliceEntry (Occurrence Nat) Nat :=
  { key := { value := 7, origin := origin }, value := some payload }

def forceCollapseCorrectnessRegressionState :
    MergeState (Occurrence Nat) Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[forceCollapseCorrectnessRegressionEntry 0 10,
            forceCollapseCorrectnessRegressionEntry 1 20,
            forceCollapseCorrectnessRegressionEntry 2 30] }
    a := { cells := #[], backing := .inline, hasValues := true }
    alloced := 0
    pending :=
      #[{ base := 0, len := 1, power := some 1 },
        { base := 1, len := 1, power := some 2 },
        { base := 2, len := 1, power := none }]
    key_compare := occurrenceComparator forceCollapseCorrectnessRegressionLt
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

end CPythonListsort
