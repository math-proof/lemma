/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanStepCorrectness.lean -/

import Structure.CPythonListsort.Code.Assembly.ListSortTermination
import Def.CPythonListsort.Code.Correctness.BinarysortCorrectness.Part3
import Def.CPythonListsort.Code.Correctness.CountRunCorrectness.Part2
import Def.CPythonListsort.Code.Correctness.FoundNewRunCorrectness
import Theorem.CPythonListsort.Code.Correctness.ScanCorrectnessSupport
import Theorem.CPythonListsort.Code.Correctness.ScanStepSupport
import Structure.CPythonListsort.Code.Correctness.ScanStepCorrectness.Part3
/-!
# Correctness of one forward scan iteration

This module stops at the recursive-call boundary of `listSortScan?`.  It
combines the already-reviewed safety invariant with pending-run correctness,
the whole-entry unscanned snapshot, and the persistent input permutation.
-/


namespace CPythonListsort

universe u v

variable {α : Type u} {ν : Type v}

def scanStepExtensionRegressionView
    (result : ListSortImplResult (Occurrence Nat) Nat) :
    ScanStepExtensionRegressionView :=
  { returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted
    pending := result.state.pending.toList.map (fun run =>
      (run.base, run.len.toNat))
    entries := result.state.data.entries.toList.map (fun entry =>
      (entry.key.value, entry.key.origin, entry.value)) }

def scanStepExtensionRegressionExpected :
    ScanStepExtensionRegressionView :=
  { returnCode := 0
    fuelExhausted := false
    pending := [(1, 4)]
    entries :=
      [(99, 0, some 10), (0, 4, some 14), (1, 2, some 12),
       (2, 3, some 13), (3, 1, some 11), (77, 5, some 15)] }

set_option maxRecDepth 100000 in
set_option linter.style.nativeDecide false in

def scanStepNoExtensionSlice : SortSlice (Occurrence Nat) PUnit :=
  { entries := (Array.range 64).map fun index =>
      ({ key := { value := index, origin := index }, value := none } :
        SortSliceEntry (Occurrence Nat) PUnit) }

def scanStepNoExtensionState : MergeState (Occurrence Nat) PUnit :=
  let initialized :=
    (initialMergeState (occurrenceComparator scanStepRegressionLt) false
      scanStepNoExtensionSlice).1
  { initialized with
    pending := #[{ base := 0, len := BitVec.ofNat 64 24, power := none }] }

set_option maxRecDepth 100000 in
set_option linter.style.nativeDecide false in

def scanStepPolicyMergeEntry (value origin : Nat) :
    SortSliceEntry (Occurrence Nat) PUnit :=
  { key := { value := value, origin := origin }, value := none }

def scanStepPolicyMergeState : MergeState (Occurrence Nat) PUnit :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[scanStepPolicyMergeEntry 2 0,
            scanStepPolicyMergeEntry 1 1,
            scanStepPolicyMergeEntry 3 2] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[{ base := 0, len := 1, power := some 3 },
        { base := 1, len := 1, power := none }]
    key_compare := occurrenceComparator scanStepRegressionLt
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

end CPythonListsort
