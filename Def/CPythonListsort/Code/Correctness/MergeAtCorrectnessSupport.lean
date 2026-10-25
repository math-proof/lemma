/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeAtCorrectnessSupport.lean -/

import Def.CPythonListsort.Code.Correctness.EntrySnapshotPermutation
import Def.CPythonListsort.Code.Correctness.StableMerge
import Lemma.List.Atlas.CPythonListsort.Code.Policy.MergeAtPreservation
/-!
# Correctness support for `merge_at`

This module contains only the list algebra needed to lift one correct merge of
two adjacent pending runs to the global pending-run and input-snapshot
invariants.  Evaluator control flow remains in the eventual `merge_at`
correctness theorem.
-/


namespace CPythonListsort

universe u v

/-- Occurrence keys contributed by an explicitly supplied list of pending
runs.  Unlike `pendingOccurrenceKeys`, this view is useful before and after an
adjacent pair is replaced in the pending array. -/
def pendingOccurrenceKeysOf
    (state : MergeState (Occurrence α) ν) (runs : List PendingRun) :
    List (Occurrence α) :=
  runs.flatMap fun run => (pendingRunOccurrenceKeys state run).toList

end CPythonListsort
