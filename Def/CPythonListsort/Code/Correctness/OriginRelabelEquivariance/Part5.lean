/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean -/

import Def.CPythonListsort.Code.Correctness.ScanStepCorrectness.Part3
import Def.CPythonListsort.Code.Correctness.MergeForceCollapseCorrectness.Part2
import Structure.CPythonListsort.Code.Correctness.OriginRelabelEquivariance
/-!
# Equivariance under mirrored occurrence origins

Reverse-mode correctness compares the actual initially reversed execution,
whose carried origins run backwards, with a canonical execution over the
reversed source.  This file supplies the explicit relabeling and proves that
the implementation observes only occurrence values: changing every origin by
the same mirror map commutes with the data-moving evaluator.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Whole-entry snapshot relation for a mirrored execution.  Unmirroring each
current entry must recover a permutation of the absolutely tagged source. -/
def CanonicalMirroredEntrySnapshotPermutation (source : SortSlice alpha nu)
    (size : Nat) (current : SortSlice (Occurrence alpha) nu) : Prop :=
  (current.entries.map (mirrorSortSliceEntry size)).toList.Perm
    (tagSortSliceOccurrences source).entries.toList

end CPythonListsort
