/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean -/

import Def.CPythonListsort.Code.Transcription.MergeHi.Part6
import Def.CPythonListsort.Code.Transcription.MergeLo.Part6
import Structure.CPythonListsort.Code.Transcription.MergeAt.Part3
/-!
# Pending-stack merge dispatch

This module transcribes CPython's `merge_at`.  The pending-stack replacement
happens before either galloping search, exactly as it does in C, so a later
modeled failure retains that mutation.  The two searches trim entries already
in their final positions and the shorter remaining run selects `merge_lo` or
`merge_hi`.
-/


namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

set_option linter.flexible false in
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in

def mergeAtSlideExampleState : MergeState Nat Nat :=
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

set_option linter.style.nativeDecide false in

def mergeAtPreparationShape (prepared : MergeAtPreparation Nat Nat) :
    Option (Bool × Nat × Nat) :=
  match prepared with
  | .finished _ => none
  | .mergeLo call => some (true, call.na, call.nb)
  | .mergeHi call => some (false, call.na, call.nb)

def mergeAtLoPreparationExampleState : MergeState Nat Nat :=
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

def mergeAtHiPreparationExampleState : MergeState Nat Nat :=
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

end CPythonListsort
