/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeAtCorrectness.lean -/

import Def.CPythonListsort.Code.Assembly.GallopCorrectness
import Def.CPythonListsort.Code.Assembly.MergeAtSafety.Part4
import Def.CPythonListsort.Code.Correctness.MergeAtCorrectnessSupport
import Def.CPythonListsort.Code.Correctness.MergeHiCorrectness
import Structure.CPythonListsort.Code.Correctness.MergeLoCorrectness
import Def.CPythonListsort.Code.Correctness.PendingRunCorrectness
import Lemma.List.Atlas.CPythonListsort.Code.Policy.MergeAtPreservation
import Lemma.List.Atlas.CPythonListsort.Code.Policy.MergeTopPowerPreservation
import Structure.CPythonListsort.Code.Correctness.MergeAtCorrectness
/-!
# Functional correctness of `merge_at`

This module lifts the exact trimmed-range specifications of `merge_lo` and
`merge_hi` to the complete adjacent pair selected by `merge_at`.  Its public
postcondition is deliberately phrased at the scan invariant boundary: the
actual traced evaluator succeeds, the selected union is the mathematical
left-biased stable merge, all pending runs remain correct, the persistent
whole-entry snapshot is preserved, and no entry outside the consumed prefix
changes.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-! ## Executable branch regressions -/

/-- Compact observable tag for the three preparation outcomes.  Tags zero,
one, and two denote finished, `merge_lo`, and `merge_hi`, respectively. -/
def mergeAtPreparationObservation (prepared : MergeAtPreparation Nat Nat) :
    Nat × Int × Bool × Nat × Nat :=
  match prepared with
  | .finished result =>
      (0, result.returnCode, result.fuelExhausted, 0, 0)
  | .mergeLo call =>
      (1, 0, false, call.na, call.nb)
  | .mergeHi call =>
      (2, 0, false, call.na, call.nb)

def mergeAtEarlyLeftExhaustionRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 2
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 1, value := none },
            { key := 2, value := none }] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 1, power := some 4 },
        { base := 1, len := 1, power := none }]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

def mergeAtLoBranchRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 5
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 2, value := none },
            { key := 4, value := none },
            { key := 1, value := none },
            { key := 3, value := none },
            { key := 5, value := none }] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 2, power := some 4 },
        { base := 2, len := 3, power := none }]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

def mergeAtHiBranchRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 6
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 1, value := none },
            { key := 3, value := none },
            { key := 5, value := none },
            { key := 7, value := none },
            { key := 2, value := none },
            { key := 6, value := none }] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 4, power := some 4 },
        { base := 4, len := 2, power := none }]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

def mergeAtThirdLastSlideRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 1, value := none },
            { key := 2, value := none },
            { key := 3, value := none }] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 1, power := some 4 },
        { base := 1, len := 1, power := some 7 },
        { base := 2, len := 1, power := none }]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

/-- Deliberately inconsistent comparator: the first gallop retains all of A,
but the second gallop returns zero. -/
def mergeAtSecondTrimZeroRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 1, value := none },
            { key := 3, value := none },
            { key := 2, value := none }] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 2, power := some 4 },
        { base := 2, len := 1, power := none }]
    key_compare := fun left right => decide (left = 2 ∧ right = 1)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

end CPythonListsort
