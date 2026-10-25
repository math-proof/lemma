/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean -/

import Def.CPythonListsort.Code.Assembly.MergeAtSafety.Part4
import Lemma.List.Atlas.CPythonListsort.Code.Policy.MergeForceCollapsePreservation
import Structure.CPythonListsort.Code.Assembly.MergeForceCollapseSafety
/-!
# `merge_force_collapse` safety

This module traces the neighboring pending-run reads performed by the reviewed
sequential Lean transcription of `merge_force_collapse` and composes them with
the complete trace of each delegated `merge_at` call.  This is an exact order
claim about the Lean model; it does not impose an evaluation order on the two
operands of C's `<` operator.  The public safety theorem proves that the
pending-depth fuel supplied by the transcription is adequate for every
nonempty valid layout.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

namespace MergeForceCollapseStableFrame

/-! ## Branch and failure anti-vacuity regressions -/

def forceCollapseTwoRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 2
    basekeys := 0
    data := { entries := #[] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 1, power := none },
        { base := 1, len := 1, power := none }]
    key_compare := fun _ _ => false
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

def forceCollapseEmptyRegressionState : MergeState Nat Nat :=
  { forceCollapseTwoRegressionState with pending := #[] }

def forceCollapseLowerRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 6
    basekeys := 0
    data := { entries := #[] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 1, power := none },
        { base := 1, len := 2, power := none },
        { base := 3, len := 3, power := none }]
    key_compare := fun _ _ => false
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

def forceCollapseTieRegressionState : MergeState Nat Nat :=
  { forceCollapseLowerRegressionState with
    pending :=
      #[{ base := 0, len := 1, power := none },
        { base := 1, len := 2, power := none },
        { base := 3, len := 1, power := none }] }

def forceCollapseRejectedMergeState : MergeState Nat Nat :=
  { forceCollapseTieRegressionState with
    listlen := 0
    pending :=
      #[{ base := 0, len := 0, power := none },
        { base := 0, len := 0, power := none }] }

end MergeForceCollapseStableFrame
end CPythonListsort
