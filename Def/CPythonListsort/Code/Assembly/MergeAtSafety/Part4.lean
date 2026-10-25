/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeAtSafety.lean -/

import Def.CPythonListsort.Code.Assembly.MergeMemoryLifecycle.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Policy.MergeAtPreservation
import Structure.CPythonListsort.Code.Assembly.MergeAtSafety.Part3
/-!
# `merge_at` safety

This module instruments the pending-stack updates and the two trimming gallops
performed by `merge_at`, then delegates the selected merge continuation to the
already traced `merge_lo` or `merge_hi` evaluator.  The logical shrink of the
active pending array is not an indexed C access; the indexed reads and writes
which precede it are recorded in source order.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

namespace MergeAtStableFrame

/-! ## Logical-event anti-vacuity regression -/

def mergeAtPolicyEarlyTrimLeft : PendingRun :=
  { base := 0, len := 1, power := some 4 }

def mergeAtPolicyEarlyTrimRight : PendingRun :=
  { base := 1, len := 1, power := some 7 }

def mergeAtPolicyEarlyTrimTail : PendingRun :=
  { base := 2, len := 1, power := none }

def mergeAtPolicyEarlyTrimState : MergeState Nat Nat :=
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
      #[mergeAtPolicyEarlyTrimLeft,
        mergeAtPolicyEarlyTrimRight,
        mergeAtPolicyEarlyTrimTail]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

def mergeAtPolicyEarlyTrimCall : MergeState Nat Nat :=
  mergeAtCombinedState mergeAtPolicyEarlyTrimState 0
    mergeAtPolicyEarlyTrimLeft mergeAtPolicyEarlyTrimRight

def mergeAtFinishedSuccessShape
    (prepared : MergeAtPreparation Nat Nat) : Option (Int × Bool) :=
  match prepared with
  | .finished result => some (result.returnCode, result.fuelExhausted)
  | .mergeLo _ | .mergeHi _ => none

end MergeAtStableFrame
end CPythonListsort
