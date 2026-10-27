import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.CPythonListsort.Code.Correctness.ScanCorrectnessSupport
open CPythonListsort CPythonListsort.ScanRemainderEntriesMatch CPythonListsort.PendingRunsCorrect


namespace CPythonListsort.ScanRemainderEntriesMatch

/--
[prefix_entries_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanCorrectnessSupport.lean)
-/
@[path]
lemma prefix_entries_eq
  {source : SortSlice κ ν}
  {state : MergeState (Occurrence κ) ν}
  {scanned count : Nat}
-- given
  (h : ScanRemainderEntriesMatch source state scanned)
  (hcount : count ≤ state.listlen.toNat - scanned) :
-- imply
  (sortSliceRangeEntries state.data (state.basekeys + scanned) count).toList = (sortSliceRangeEntries (tagSortSliceOccurrences source) (state.basekeys + scanned) count).toList := by
-- proof
  have hprefix := congrArg (List.take count) h.entries_eq
  simpa [sortSliceRangeEntries_toList, List.take_take, Nat.min_eq_left hcount]
    using hprefix

end CPythonListsort.ScanRemainderEntriesMatch

namespace CPythonListsort.ScanRemainderEntriesMatch

/--
[prefix_keys_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanCorrectnessSupport.lean)
-/
@[path]
lemma prefix_keys_eq
  {source : SortSlice κ ν}
  {state : MergeState (Occurrence κ) ν}
  {scanned count : Nat}
-- given
  (h : ScanRemainderEntriesMatch source state scanned)
  (hcount : count ≤ state.listlen.toNat - scanned) :
-- imply
  (sortSliceRangeKeys state.data (state.basekeys + scanned) count).toList = canonicalOccurrenceSegment (source.entries.map SortSliceEntry.key) (state.basekeys + scanned) count := by
-- proof
  have hentries := h.prefix_entries_eq hcount
  have hkeys := congrArg (List.map SortSliceEntry.key) hentries
  calc
    (sortSliceRangeKeys state.data (state.basekeys + scanned) count).toList =
      (sortSliceRangeEntries state.data
        (state.basekeys + scanned) count).toList.map SortSliceEntry.key := by
        simp [sortSliceRangeKeys]
    _ = (sortSliceRangeEntries (tagSortSliceOccurrences source)
      (state.basekeys + scanned) count).toList.map SortSliceEntry.key :=
      hkeys
    _ = canonicalOccurrenceSegment
      (source.entries.map SortSliceEntry.key)
      (state.basekeys + scanned) count := by
      rw [← Array.toList_map, ← sortSliceRangeKeys_eq_map,
        sortSliceRangeKeys_tagSortSliceOccurrences]
      rfl

end CPythonListsort.ScanRemainderEntriesMatch

namespace CPythonListsort.PendingRunsCorrect

/--
[preserve_unscanned_update](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanCorrectnessSupport.lean)
-/
@[path]
lemma preserve_unscanned_update
  {lt : BoolComparator α}
  {input : Array α}
  {before after : MergeState (Occurrence α) ν}
  {scanned changed : Nat}
-- given
  (h : PendingRunsCorrect lt input before scanned)
  (hlistlen : after.listlen = before.listlen)
  (hbasekeys : after.basekeys = before.basekeys)
  (hpending : after.pending = before.pending)
  (hframe : SortSlice.EqualOutsideRange before.data after.data (before.basekeys + scanned) changed) :
-- imply
  PendingRunsCorrect lt input after scanned := by
-- proof
  have hlayout : PendingLayout after scanned := by
    have hbeforeLayout := h.layout
    unfold PendingLayout at hbeforeLayout ⊢
    rwa [hlistlen, hbasekeys, hpending, ← hframe.size_eq]
  have hrunKeys : ∀ run ∈ before.pending.toList,
    pendingRunOccurrenceKeys after run =
      pendingRunOccurrenceKeys before run := by
    intro run hrun
    have hspec := h.layout.2.2.2.member_spec hrun
    have hrange := hframe.keys_eq_of_disjoint run.base run.len.toNat
      (Or.inl (by
        simp only [PendingRun.endIndex] at hspec
        exact hspec.2.2.2))
    simpa [pendingRunOccurrenceKeys_eq_sortSliceRangeKeys] using hrange.symm
  have hpendingKeys : pendingOccurrenceKeys after =
    pendingOccurrenceKeys before := by
    unfold pendingOccurrenceKeys
    rw [hpending]
    apply List.flatMap_congr
    intro run hrun
    exact congrArg Array.toList (hrunKeys run hrun)
  refine ⟨hlayout, ?_, ?_⟩
  · intro run hrun
    have hrunBefore : run ∈ before.pending.toList := by
      simpa [hpending] using hrun
    rw [hrunKeys run hrunBefore]
    exact h.runSorted run hrunBefore
  · rw [hbasekeys, hpendingKeys]
    exact h.stableOccurrencePermutation

end CPythonListsort.PendingRunsCorrect

/--
[canonicalOccurrenceSegment_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanCorrectnessSupport.lean)
-/
@[path]
private lemma canonicalOccurrenceSegment_add_eq
  {input : Array α}
  {base left right : Nat} :
-- imply
  canonicalOccurrenceSegment input base (left + right) = canonicalOccurrenceSegment input base left ++ canonicalOccurrenceSegment input (base + left) right := by
-- proof
  apply CPythonListsort.canonicalOccurrenceSegment_add input base left right

/--
[canonicalOccurrenceSegment_pairwise_stable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanCorrectnessSupport.lean)
-/
@[path]
private lemma canonicalOccurrenceSegment_pairwise_stable_eq
  {lt : BoolComparator α}
  {input : Array α}
  {base count : Nat} :
-- imply
  (canonicalOccurrenceSegment input base count).Pairwise fun earlier later => ComparatorEquivalent lt earlier.value later.value → earlier.origin < later.origin := by
-- proof
  apply CPythonListsort.canonicalOccurrenceSegment_pairwise_stable lt input base count

/--
[stableOccurrencePermutation_append_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanCorrectnessSupport.lean)
-/
@[path]
private lemma stableOccurrencePermutation_append_adjacent_eq
  {lt : BoolComparator α}
  {input : Array α}
  {base leftCount rightCount : Nat}
  {left right : List (Occurrence α)}
-- given
  (hleft : StableOccurrencePermutation lt (canonicalOccurrenceSegment input base leftCount) left)
  (hright : StableOccurrencePermutation lt (canonicalOccurrenceSegment input (base + leftCount) rightCount) right) :
-- imply
  StableOccurrencePermutation lt (canonicalOccurrenceSegment input base (leftCount + rightCount)) (left ++ right) := by
-- proof
  apply CPythonListsort.stableOccurrencePermutation_append_adjacent hleft hright


-- created on 2026-10-23
