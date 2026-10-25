import Mathlib
import sympy.Basic
import Def.CPythonListsort.Code.Correctness.EntrySnapshotPermutation
open CPythonListsort CPythonListsort.EntrySnapshotPermutation


namespace CPythonListsort.EntrySnapshotPermutation

/--
[with_occurrence_keys](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/EntrySnapshotPermutation.lean)
-/
@[path]
lemma with_occurrence_keys
  {κ : Type u}
  {ν : Type v}
  {input : ListSortInput κ ν} :
-- imply
  EntrySnapshotPermutation input.slice input.withOccurrenceKeys.slice :=
-- proof
List.Perm.refl _

end CPythonListsort.EntrySnapshotPermutation

namespace CPythonListsort.EntrySnapshotPermutation

/--
[initial_merge_state_raw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/EntrySnapshotPermutation.lean)
-/
@[path]
lemma initial_merge_state_raw
  {κ : Type u}
  {ν : Type v}
  {keyCompare : BoolComparator (Occurrence κ)}
  {source : SortSlice κ ν}
-- given
  (hasKeyfunc : Bool) :
-- imply
  EntrySnapshotPermutation source (CPythonListsort.initialMergeState keyCompare hasKeyfunc (tagSortSliceOccurrences source)).1.data := by
-- proof
  rw [CPythonListsort.initialMergeState_data]
  exact List.Perm.refl _

end CPythonListsort.EntrySnapshotPermutation

namespace CPythonListsort.EntrySnapshotPermutation

/--
[initial_merge_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/EntrySnapshotPermutation.lean)
-/
@[path]
lemma initial_merge_state
  {κ : Type u}
  {ν : Type v}
  {keyCompare : BoolComparator (Occurrence κ)}
  {input : ListSortInput κ ν} :
-- imply
  EntrySnapshotPermutation input.slice (CPythonListsort.initialMergeState keyCompare input.hasKeyfunc input.withOccurrenceKeys.slice).1.data := by
-- proof
  rw [CPythonListsort.initialMergeState_data]
  exact with_occurrence_keys input

end CPythonListsort.EntrySnapshotPermutation

namespace CPythonListsort.EntrySnapshotPermutation

/--
[keyed_initial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/EntrySnapshotPermutation.lean)
-/
@[path]
lemma keyed_initial
  {κ : Type u}
  {ν : Type v}
  {keyCompare : BoolComparator (Occurrence κ)}
  {entries : Array (κ × ν)} :
-- imply
  EntrySnapshotPermutation (ListSortInput.keyed entries).slice (CPythonListsort.initialMergeState keyCompare true (ListSortInput.keyed entries).withOccurrenceKeys.slice).1.data :=
-- proof
initial_merge_state keyCompare (ListSortInput.keyed entries)

end CPythonListsort.EntrySnapshotPermutation

namespace CPythonListsort.EntrySnapshotPermutation

/--
[unkeyed_initial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/EntrySnapshotPermutation.lean)
-/
@[path]
lemma unkeyed_initial
  {κ : Type u}
  {ν : Type v}
  {keyCompare : BoolComparator (Occurrence κ)}
  {keys : Array κ} :
-- imply
  EntrySnapshotPermutation (ListSortInput.unkeyed keys).slice (CPythonListsort.initialMergeState keyCompare false (ListSortInput.unkeyed keys).withOccurrenceKeys.slice).1.data :=
-- proof
initial_merge_state keyCompare (ListSortInput.unkeyed keys)

end CPythonListsort.EntrySnapshotPermutation

namespace CPythonListsort.EntrySnapshotPermutation

/--
[preserve_of_whole_entries_perm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/EntrySnapshotPermutation.lean)
-/
@[path]
lemma preserve_of_whole_entries_perm
  {κ : Type u}
  {ν : Type v}
  {source : SortSlice κ ν}
  {before after : SortSlice (Occurrence κ) ν}
  {snapshot : EntrySnapshotPermutation source before}
  {step : after.entries.toList.Perm before.entries.toList} :
-- imply
  EntrySnapshotPermutation source after :=
-- proof
  step.trans snapshot

end CPythonListsort.EntrySnapshotPermutation

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[entries_eq_prefix_range_suffix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/EntrySnapshotPermutation.lean)
-/
@[path]
private lemma entries_eq_prefix_range_suffix
  (slice : SortSlice α β) (start count : Nat) :
  slice.entries.toList =
    slice.entries.toList.take start ++
      (sortSliceRangeEntries slice start count).toList ++
        slice.entries.toList.drop (start + count) := by
  rw [sortSliceRangeEntries_toList]
  conv_lhs =>
    rw [← List.take_append_drop start slice.entries.toList]
  conv_lhs =>
    rhs
    rw [← List.take_append_drop count (slice.entries.toList.drop start)]
  simp only [List.drop_drop, List.append_assoc]

end CPythonListsort

namespace CPythonListsort

/--
[wholeEntries_perm_of_range_perm_and_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/EntrySnapshotPermutation.lean)
-/
@[path]
lemma wholeEntries_perm_of_range_perm_and_frame
  {κ : Type u}
  {ν : Type v}
  {before after : SortSlice α β}
  {start count : Nat}
  {frame : SortSlice.EqualOutsideRange before after start count}
  {localPerm : (sortSliceRangeEntries after start count).toList.Perm (sortSliceRangeEntries before start count).toList}
-- given
  (stop : start + count ≤ before.entries.size) :
-- imply
  after.entries.toList.Perm before.entries.toList := by
-- proof
  have stopAfter : start + count ≤ after.entries.size := by
    rwa [← frame.size_eq]
  have prefixEq :
    after.entries.toList.take start = before.entries.toList.take start := by
    have rangeEq := frame.entries_eq_of_disjoint 0 start (Or.inl (by omega))
    have listEq := congrArg Array.toList rangeEq
    simpa [sortSliceRangeEntries_toList] using listEq.symm
  have suffixEq :
    after.entries.toList.drop (start + count) =
      before.entries.toList.drop (start + count) := by
    have rangeEq := frame.entries_eq_of_disjoint
      (start + count) before.entries.size (Or.inr (by omega))
    have listEq := congrArg Array.toList rangeEq
    rw [sortSliceRangeEntries_toList, sortSliceRangeEntries_toList] at listEq
    have beforeLength : before.entries.toList.length = before.entries.size := by
      simp
    have afterLength : after.entries.toList.length = after.entries.size := by
      simp
    have takeBefore :
      (before.entries.toList.drop (start + count)).take before.entries.size =
        before.entries.toList.drop (start + count) := by
      apply List.take_of_length_le
      simp only [List.length_drop, beforeLength]
      omega
    have takeAfter :
      (after.entries.toList.drop (start + count)).take before.entries.size =
        after.entries.toList.drop (start + count) := by
      apply List.take_of_length_le
      simp only [List.length_drop, afterLength]
      rw [← frame.size_eq]
      omega
    simpa only [takeBefore, takeAfter] using listEq.symm
  rw [entries_eq_prefix_range_suffix after start count,
    entries_eq_prefix_range_suffix before start count, prefixEq, suffixEq]
  exact List.Perm.append
    (List.Perm.append (List.Perm.refl _) localPerm) (List.Perm.refl _)

end CPythonListsort

namespace CPythonListsort.EntrySnapshotPermutation

/--
[preserve_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/EntrySnapshotPermutation.lean)
-/
@[path]
lemma preserve_local
  {κ : Type u}
  {ν : Type v}
  {source : SortSlice κ ν}
  {before after : SortSlice (Occurrence κ) ν}
  {start count : Nat}
  {snapshot : EntrySnapshotPermutation source before}
  {frame : SortSlice.EqualOutsideRange before after start count}
  {localPerm : (sortSliceRangeEntries after start count).toList.Perm (sortSliceRangeEntries before start count).toList}
-- given
  (stop : start + count ≤ before.entries.size) :
-- imply
  EntrySnapshotPermutation source after :=
-- proof
  preserve_of_whole_entries_perm snapshot
    (wholeEntries_perm_of_range_perm_and_frame frame stop localPerm)

end CPythonListsort.EntrySnapshotPermutation

namespace CPythonListsort

/--
[entrySnapshotPermutation_rejects_wrong_keyed_payload](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/EntrySnapshotPermutation.lean)
-/
@[path]
lemma entrySnapshotPermutation_rejects_wrong_keyed_payload
  {κ : Type u}
  {ν : Type v} :
-- imply
  wrongPayloadTaggedSlice.entries.map SortSliceEntry.key = (tagSortSliceOccurrences wrongPayloadKeyedInput.slice).entries.map SortSliceEntry.key ∧ wrongPayloadTaggedSlice.entries.map SortSliceEntry.value = #[some 10, some 99] ∧ (tagSortSliceOccurrences wrongPayloadKeyedInput.slice).entries.map SortSliceEntry.value = #[some 10, some 20] ∧ wrongPayloadTaggedSlice.entries.map SortSliceEntry.value ≠ (tagSortSliceOccurrences wrongPayloadKeyedInput.slice).entries.map SortSliceEntry.value ∧ ¬EntrySnapshotPermutation wrongPayloadKeyedInput.slice wrongPayloadTaggedSlice := by
-- proof
  simp [EntrySnapshotPermutation, wrongPayloadKeyedInput,
    wrongPayloadTaggedSlice, ListSortInput.keyed, tagSortSliceOccurrences]

end CPythonListsort


-- created on 2026-10-23
