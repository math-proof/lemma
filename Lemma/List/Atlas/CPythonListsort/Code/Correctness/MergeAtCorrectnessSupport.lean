import Mathlib
import sympy.Basic
import Def.CPythonListsort.Code.Correctness.MergeAtCorrectnessSupport
open CPythonListsort CPythonListsort.StableOccurrencePermutation CPythonListsort.PendingRunsCorrect CPythonListsort.EntrySnapshotPermutation


namespace CPythonListsort

/--
[pendingOccurrenceKeysOf_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeAtCorrectnessSupport.lean)
-/
@[path]
lemma pendingOccurrenceKeysOf_nil
  {state : MergeState (Occurrence α) ν} :
-- imply
  pendingOccurrenceKeysOf state [] = [] := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[pendingOccurrenceKeysOf_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeAtCorrectnessSupport.lean)
-/
@[path]
lemma pendingOccurrenceKeysOf_cons
  {state : MergeState (Occurrence α) ν}
  {run : PendingRun}
  {runs : List PendingRun} :
-- imply
  pendingOccurrenceKeysOf state (run :: runs) = (pendingRunOccurrenceKeys state run).toList ++ pendingOccurrenceKeysOf state runs := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[pendingOccurrenceKeysOf_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeAtCorrectnessSupport.lean)
-/
@[path]
lemma pendingOccurrenceKeysOf_append
  {state : MergeState (Occurrence α) ν}
  {left right : List PendingRun} :
-- imply
  pendingOccurrenceKeysOf state (left ++ right) = pendingOccurrenceKeysOf state left ++ pendingOccurrenceKeysOf state right := by
-- proof
  simp [pendingOccurrenceKeysOf]

end CPythonListsort

namespace CPythonListsort

/--
[pendingOccurrenceKeys_eq_of_pending](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeAtCorrectnessSupport.lean)
-/
@[path]
lemma pendingOccurrenceKeys_eq_of_pending
  {state : MergeState (Occurrence α) ν} :
-- imply
  pendingOccurrenceKeys state = pendingOccurrenceKeysOf state state.pending.toList := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[pendingOccurrenceKeysOf_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeAtCorrectnessSupport.lean)
-/
@[path]
lemma pendingOccurrenceKeysOf_congr
  {before after : MergeState (Occurrence α) ν}
  {runs : List PendingRun}
-- given
  (hkeys : ∀ run ∈ runs, pendingRunOccurrenceKeys before run = pendingRunOccurrenceKeys after run) :
-- imply
  pendingOccurrenceKeysOf before runs = pendingOccurrenceKeysOf after runs := by
-- proof
  induction runs with
  | nil => rfl
  | cons run runs ih =>
    simp only [pendingOccurrenceKeysOf_cons]
    rw [hkeys run (by simp), ih]
    intro tail htail
    exact hkeys tail (by simp [htail])

end CPythonListsort

namespace CPythonListsort

/--
[pendingOccurrenceKeys_pair_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeAtCorrectnessSupport.lean)
-/
@[path]
lemma pendingOccurrenceKeys_pair_decomposition
  {state : MergeState (Occurrence α) ν}
  {before after : List PendingRun}
  {left right : PendingRun}
-- given
  (hsplit : state.pending.toList = before ++ left :: right :: after) :
-- imply
  pendingOccurrenceKeys state = pendingOccurrenceKeysOf state before ++ (pendingRunOccurrenceKeys state left).toList ++ (pendingRunOccurrenceKeys state right).toList ++ pendingOccurrenceKeysOf state after := by
-- proof
  rw [pendingOccurrenceKeys_eq_of_pending, hsplit]
  simp only [pendingOccurrenceKeysOf_append,
    pendingOccurrenceKeysOf_cons, List.append_assoc]

end CPythonListsort

namespace CPythonListsort

/--
[pendingOccurrenceKeys_single_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeAtCorrectnessSupport.lean)
-/
@[path]
lemma pendingOccurrenceKeys_single_decomposition
  {state : MergeState (Occurrence α) ν}
  {before after : List PendingRun}
  {run : PendingRun}
-- given
  (hsplit : state.pending.toList = before ++ run :: after) :
-- imply
  pendingOccurrenceKeys state = pendingOccurrenceKeysOf state before ++ (pendingRunOccurrenceKeys state run).toList ++ pendingOccurrenceKeysOf state after := by
-- proof
  rw [pendingOccurrenceKeys_eq_of_pending, hsplit]
  simp only [pendingOccurrenceKeysOf_append,
    pendingOccurrenceKeysOf_cons, List.append_assoc]

end CPythonListsort

namespace CPythonListsort

/--
[pendingRunOccurrenceKeys_eq_of_equalOutsideRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeAtCorrectnessSupport.lean)
-/
@[path]
lemma pendingRunOccurrenceKeys_eq_of_equalOutsideRange
  {before after : MergeState (Occurrence α) ν}
  {start count : Nat}
  {run : PendingRun}
  {frame : SortSlice.EqualOutsideRange before.data after.data start count}
-- given
  (disjoint : run.endIndex ≤ start ∨ start + count ≤ run.base) :
-- imply
  pendingRunOccurrenceKeys before run = pendingRunOccurrenceKeys after run := by
-- proof
  rw [pendingRunOccurrenceKeys_eq_sortSliceRangeKeys,
    pendingRunOccurrenceKeys_eq_sortSliceRangeKeys]
  exact frame.keys_eq_of_disjoint run.base run.len.toNat (by
    simpa only [PendingRun.endIndex] using disjoint)

end CPythonListsort

namespace CPythonListsort

/--
[pairwise_replaceSegmentPerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeAtCorrectnessSupport.lean)
-/
@[path]
lemma pairwise_replaceSegmentPerm
  {R : α → α → Prop}
  {pre original replacement suffix : List α}
  {whole : (pre ++ original ++ suffix).Pairwise R}
  {replacementPairwise : replacement.Pairwise R}
  {replacementPerm : replacement.Perm original} :
-- imply
  (pre ++ replacement ++ suffix).Pairwise R := by
-- proof
  rcases List.pairwise_append.mp whole with
    ⟨prefixOriginal, suffixPairwise, prefixOriginalToSuffix⟩
  rcases List.pairwise_append.mp prefixOriginal with
    ⟨prefixPairwise, _originalPairwise, prefixToOriginal⟩
  have prefixReplacement : (pre ++ replacement).Pairwise R := by
    apply List.pairwise_append.mpr
    refine ⟨prefixPairwise, replacementPairwise, ?_⟩
    intro earlier hearlier later hlater
    exact prefixToOriginal earlier hearlier later
      (replacementPerm.mem_iff.mp hlater)
  apply List.pairwise_append.mpr
  refine ⟨prefixReplacement, suffixPairwise, ?_⟩
  intro earlier hearlier later hlater
  obtain hearlier | hearlier := List.mem_append.mp hearlier
  · exact prefixOriginalToSuffix earlier
    (List.mem_append_left original hearlier) later hlater
  · exact prefixOriginalToSuffix earlier
    (List.mem_append_right pre
      (replacementPerm.mem_iff.mp hearlier)) later hlater

end CPythonListsort

namespace CPythonListsort.StableOccurrencePermutation

/--
[replaceSegment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeAtCorrectnessSupport.lean)
-/
@[path]
lemma replaceSegment
  {lt : BoolComparator α}
  {canonical : List (Occurrence α)}
  {pre original replacement suffix : List (Occurrence α)}
  {whole : StableOccurrencePermutation lt canonical (pre ++ original ++ suffix)}
  {segment : StableOccurrencePermutation lt original replacement} :
-- imply
  StableOccurrencePermutation lt canonical (pre ++ replacement ++ suffix) := by
-- proof
  refine ⟨?_, ?_⟩
  · exact ((segment.1.append_left pre).append_right suffix).trans whole.1
  · exact pairwise_replaceSegmentPerm whole.2 segment.2 segment.1

end CPythonListsort.StableOccurrencePermutation

namespace CPythonListsort.PendingRunsCorrect

/--
[replaceAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeAtCorrectnessSupport.lean)
-/
@[path]
lemma replaceAdjacent
  {lt : BoolComparator α}
  {input : Array α}
  {beforeState afterState : MergeState (Occurrence α) ν}
  {scanned : Nat}
  {pre suffix : List PendingRun}
  {left right merged : PendingRun}
  {correct : PendingRunsCorrect lt input beforeState scanned}
  {layout : PendingLayout afterState scanned}
  {mergedSorted : Sorted (occurrenceComparator lt) (pendingRunOccurrenceKeys afterState merged)}
  {mergedStable : StableOccurrencePermutation lt ((pendingRunOccurrenceKeys beforeState left).toList ++ (pendingRunOccurrenceKeys beforeState right).toList) (pendingRunOccurrenceKeys afterState merged).toList}
-- given
  (basekeys : afterState.basekeys = beforeState.basekeys)
  (beforePending : beforeState.pending.toList = pre ++ left :: right :: suffix)
  (afterPending : afterState.pending.toList = pre ++ merged :: suffix)
  (prefixKeys : ∀ run ∈ pre, pendingRunOccurrenceKeys beforeState run = pendingRunOccurrenceKeys afterState run)
  (suffixKeys : ∀ run ∈ suffix, pendingRunOccurrenceKeys beforeState run = pendingRunOccurrenceKeys afterState run) :
-- imply
  PendingRunsCorrect lt input afterState scanned := by
-- proof
  have prefixFlat := pendingOccurrenceKeysOf_congr prefixKeys
  have suffixFlat := pendingOccurrenceKeysOf_congr suffixKeys
  refine ⟨layout, ?_, ?_⟩
  · intro run hrun
    rw [afterPending] at hrun
    simp only [List.mem_append, List.mem_cons] at hrun
    obtain hprefix | rfl | hsuffix := hrun
    · rw [← prefixKeys run hprefix]
      apply correct.runSorted run
      rw [beforePending]
      simp [hprefix]
    · exact mergedSorted
    · rw [← suffixKeys run hsuffix]
      apply correct.runSorted run
      rw [beforePending]
      simp [hsuffix]
  · have oldStable := correct.stableOccurrencePermutation
    have oldDecomposition :=
      pendingOccurrenceKeys_pair_decomposition beforePending
    have newDecomposition :=
      pendingOccurrenceKeys_single_decomposition afterPending
    rw [oldDecomposition] at oldStable
    rw [newDecomposition, basekeys, ← prefixFlat, ← suffixFlat]
    have oldStable' : StableOccurrencePermutation lt
      (canonicalOccurrenceSegment input beforeState.basekeys scanned)
      (pendingOccurrenceKeysOf beforeState pre ++
        ((pendingRunOccurrenceKeys beforeState left).toList ++
          (pendingRunOccurrenceKeys beforeState right).toList) ++
        pendingOccurrenceKeysOf beforeState suffix) := by
      simpa only [List.append_assoc] using oldStable
    exact oldStable'.replaceSegment mergedStable

end CPythonListsort.PendingRunsCorrect

namespace CPythonListsort.EntrySnapshotPermutation

/--
[preserve_mergeRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeAtCorrectnessSupport.lean)
-/
@[path]
lemma preserve_mergeRange
  {source : SortSlice κ ν}
  {before after : SortSlice (Occurrence κ) ν}
  {start count : Nat}
  {snapshot : EntrySnapshotPermutation source before}
  {frame : SortSlice.EqualOutsideRange before after start count}
  {rangePerm : (sortSliceRangeEntries after start count).toList.Perm (sortSliceRangeEntries before start count).toList}
-- given
  (stop : start + count ≤ before.entries.size) :
-- imply
  EntrySnapshotPermutation source after :=
-- proof
  snapshot.preserve_local frame stop rangePerm

end CPythonListsort.EntrySnapshotPermutation


-- created on 2026-10-23
