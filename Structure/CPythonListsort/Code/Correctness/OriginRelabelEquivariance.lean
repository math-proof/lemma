/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean -/

import Def.CPythonListsort.Code.Correctness.ScanStepCorrectness.Part3
import Def.CPythonListsort.Code.Correctness.MergeForceCollapseCorrectness.Part2
import Theorem.CPythonListsort.Code.Correctness.OriginRelabelEquivariance.Part4
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

/-- Reverse-oriented pending correctness: the structural and sortedness facts
hold on the mirrored state itself, while stability is checked after applying
the origin involution back to the canonical orientation. -/
structure CanonicalMirroredPendingRunsCorrect (lt : BoolComparator alpha)
    (input : Array alpha) (size : Nat)
    (state : MergeState (Occurrence alpha) nu) (scanned : Nat) : Prop where
  layout : PendingLayout state scanned
  runSorted : ∀ run ∈ state.pending.toList,
    Sorted (occurrenceComparator lt) (pendingRunOccurrenceKeys state run)
  stableAfterUnmirror : StableOccurrencePermutation lt
    (canonicalOccurrenceSegment input state.basekeys scanned)
    ((pendingOccurrenceKeys state).map (mirrorOccurrence size))

end CPythonListsort
