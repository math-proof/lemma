/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanStepSupport.lean -/

import sympy.atlas.CPythonListsort.Code.Correctness.BinarysortCorrectness
import sympy.atlas.CPythonListsort.Code.Correctness.CountRunCorrectness
import sympy.atlas.CPythonListsort.Code.Correctness.EntrySnapshotPermutation
import sympy.atlas.CPythonListsort.Code.Correctness.ScanCorrectnessSupport
import sympy.atlas.CPythonListsort.Code.Policy.PushRunPreservation

/-!
# Semantic bridges for one forward scan step

These lemmas connect the already-public natural-run and binary-insertion
certificates to the scan invariant.  They contain no second implementation of
the scan: every update is the range frame or pending-stack push exported by
the transcribed operation's correctness theorem.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- The actual unconditional pending-stack push appends one newly formed
adjacent run to the semantic pending-run invariant.  `ReadyToPush` supplies
the structural layout transition; the two semantic premises are exactly the
sortedness and canonical stability certificates produced by run formation. -/
theorem pushPendingRun
    {lt : BoolComparator alpha} {input : Array alpha}
    {state : MergeState (Occurrence alpha) nu}
    {scanned : Nat} {newRun : PendingRun}
    (correct : PendingRunsCorrect lt input state scanned)
    (ready : ReadyToPush state scanned newRun)
    (newSorted : Sorted (occurrenceComparator lt)
      (pendingRunOccurrenceKeys state newRun))
    (newStable : StableOccurrencePermutation lt
      (canonicalOccurrenceSegment input (state.basekeys + scanned)
        newRun.len.toNat)
      (pendingRunOccurrenceKeys state newRun).toList) :
    PendingRunsCorrect lt input (CPythonListsort.pushPendingRun state newRun)
      (scanned + newRun.len.toNat) := by
  let pushed := CPythonListsort.pushPendingRun state newRun
  have hlayout : PendingLayout pushed (scanned + newRun.len.toNat) :=
    pushPendingRun_preserves_pendingLayout state scanned newRun ready
  have hpending : pushed.pending.toList =
      state.pending.toList ++ [newRun] := by
    simp [pushed, CPythonListsort.pushPendingRun]
  have hnewKeys : pendingRunOccurrenceKeys pushed newRun =
      pendingRunOccurrenceKeys state newRun := by
    rfl
  refine ⟨hlayout, ?_, ?_⟩
  · intro run hrun
    rw [hpending] at hrun
    rcases List.mem_append.mp hrun with hold | hnew
    · simpa [pendingRunOccurrenceKeys, pushed,
        CPythonListsort.pushPendingRun] using correct.runSorted run hold
    · simp only [List.mem_singleton] at hnew
      subst run
      rw [hnewKeys]
      exact newSorted
  · have hold := correct.stableOccurrencePermutation
    have happended := stableOccurrencePermutation_append_adjacent hold newStable
    change StableOccurrencePermutation lt
      (canonicalOccurrenceSegment input pushed.basekeys
        (scanned + newRun.len.toNat))
      (pendingOccurrenceKeys pushed)
    have hbase : pushed.basekeys = state.basekeys := rfl
    rw [hbase]
    unfold pendingOccurrenceKeys
    rw [hpending]
    rw [List.flatMap_append]
    simp only [List.flatMap_singleton]
    simpa [pendingOccurrenceKeys, pushed, CPythonListsort.pushPendingRun,
      hnewKeys] using happended

end PendingRunsCorrect

end CPythonListsort
