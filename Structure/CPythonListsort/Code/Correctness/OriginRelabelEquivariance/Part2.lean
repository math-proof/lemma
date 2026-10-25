/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean -/

import Def.CPythonListsort.Code.Correctness.ScanStepCorrectness.Part3
import Def.CPythonListsort.Code.Correctness.MergeForceCollapseCorrectness.Part2
import Def.CPythonListsort.Code.Correctness.OriginRelabelEquivariance.Part5
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

/-- Unscanned-suffix relation for a mirrored execution.  Bounds are stated on
the real mirrored state; its suffix agrees with the canonical source after
applying the origin involution back to every entry. -/
structure CanonicalMirroredScanRemainderEntriesMatch
    (source : SortSlice alpha nu) (size : Nat)
    (state : MergeState (Occurrence alpha) nu) (scanned : Nat) : Prop where
  scanned_le : scanned ≤ state.listlen.toNat
  state_stop_le :
    state.basekeys + state.listlen.toNat ≤ state.data.entries.size
  source_stop_le :
    state.basekeys + state.listlen.toNat ≤ source.entries.size
  entries_eq :
    ((sortSliceRangeEntries state.data (state.basekeys + scanned)
      (state.listlen.toNat - scanned)).map
        (mirrorSortSliceEntry size)).toList =
      (sortSliceRangeEntries (tagSortSliceOccurrences source)
        (state.basekeys + scanned)
        (state.listlen.toNat - scanned)).toList

end CPythonListsort
