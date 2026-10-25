/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanStepCorrectness.lean -/

import Structure.CPythonListsort.Code.Assembly.ListSortTermination
import Def.CPythonListsort.Code.Correctness.BinarysortCorrectness.Part3
import Def.CPythonListsort.Code.Correctness.CountRunCorrectness.Part2
import Def.CPythonListsort.Code.Correctness.FoundNewRunCorrectness
import Theorem.CPythonListsort.Code.Correctness.ScanCorrectnessSupport
import Theorem.CPythonListsort.Code.Correctness.ScanStepSupport
import Structure.CPythonListsort.Code.Correctness.ScanStepCorrectness
/-!
# Correctness of one forward scan iteration

This module stops at the recursive-call boundary of `listSortScan?`.  It
combines the already-reviewed safety invariant with pending-run correctness,
the whole-entry unscanned snapshot, and the persistent input permutation.
-/


namespace CPythonListsort

universe u v

variable {α : Type u} {ν : Type v}

/-- Abstract form of the `foundNewRun_correct` call used by the step proof.
The concrete public theorem below instantiates this provider; keeping the core
parameterized also makes the merge dependency explicit. -/
def FoundNewRunCorrectnessProvider
    (lt : BoolComparator α) (input : Array α) (source : SortSlice α ν) : Prop :=
  ∀ (state : MergeState (Occurrence α) ν) (scanned : Nat)
    (newRun : PendingRun),
    PendingRunsCorrect lt input state scanned →
    EntrySnapshotPermutation source state.data →
    state.key_compare = occurrenceComparator lt →
    state.listlen.toNat ≤ PY_LIST_MAX →
    PoweredPrefix state →
    newRun.base = state.basekeys + scanned →
    newRun.len.Nonnegative →
    0 < newRun.len.toNat →
    scanned + newRun.len.toNat ≤ state.listlen.toNat →
    TempStorageInv state.a state.alloced →
    state.a.Live →
    SortSlice.ValuesModeInvariant state.a.hasValues state.data →
    ∃ result,
      FoundNewRunCorrectnessPost lt input source state scanned newRun result

end CPythonListsort
