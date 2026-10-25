import Mathlib
import sympy.Basic
import Def.CPythonListsort.Code.Correctness.ScanRemainder.Part3
open CPythonListsort CPythonListsort.ScanRemainderMatches CPythonListsort.ScanRemainderEntriesMatch


namespace CPythonListsort

/--
[pendingRunOccurrenceKeys_eq_sortSliceRangeKeys](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean)
-/
@[path]
lemma pendingRunOccurrenceKeys_eq_sortSliceRangeKeys
  {state : MergeState (Occurrence α) ν}
  {run : PendingRun} :
-- imply
  pendingRunOccurrenceKeys state run = sortSliceRangeKeys state.data run.base run.len.toNat := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[tagSortSliceOccurrences_size](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean)
-/
@[path]
lemma tagSortSliceOccurrences_size
  {slice : SortSlice κ ν} :
-- imply
  (tagSortSliceOccurrences slice).entries.size = slice.entries.size := by
-- proof
  simp [tagSortSliceOccurrences]

end CPythonListsort

namespace CPythonListsort

/--
[tagSortSliceOccurrences_payloads](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean)
-/
@[path]
lemma tagSortSliceOccurrences_payloads
  {slice : SortSlice κ ν} :
-- imply
  (tagSortSliceOccurrences slice).entries.map SortSliceEntry.value = slice.entries.map SortSliceEntry.value := by
-- proof
  apply Array.ext <;>
    simp [tagSortSliceOccurrences]

end CPythonListsort

namespace CPythonListsort

/--
[sortSliceRangeKeys_tagSortSliceOccurrences](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean)
-/
@[path]
lemma sortSliceRangeKeys_tagSortSliceOccurrences
  {slice : SortSlice κ ν}
  {start count : Nat} :
-- imply
  sortSliceRangeKeys (tagSortSliceOccurrences slice) start count = (tagOccurrences (slice.entries.map SortSliceEntry.key)).extract start (start + count) := by
-- proof
  have hkeys :
    (tagSortSliceOccurrences slice).entries.map SortSliceEntry.key =
      tagOccurrences (slice.entries.map SortSliceEntry.key) := by
    apply Array.ext <;>
      simp [tagSortSliceOccurrences, tagOccurrences]
  simpa only [sortSliceRangeKeys, sortSliceRangeEntries,
    Array.map_extract] using
      congrArg (fun keys => keys.extract start (start + count)) hkeys

end CPythonListsort

namespace CPythonListsort.ScanRemainderMatches

/--
[remainder_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean)
-/
@[path]
lemma remainder_eq
  {input : Array α}
  {state : MergeState (Occurrence α) ν}
  {scanned : Nat}
-- given
  (h : ScanRemainderMatches input state scanned) :
-- imply
  (sortSliceRangeKeys state.data (state.basekeys + scanned) (state.listlen.toNat - scanned)).toList = canonicalOccurrenceSegment input (state.basekeys + scanned) (state.listlen.toNat - scanned) :=
-- proof
  h.keys_eq

end CPythonListsort.ScanRemainderMatches

namespace CPythonListsort.ScanRemainderMatches

/--
[canonicalOccurrenceSegment_drop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean)
-/
@[path]
lemma canonicalOccurrenceSegment_drop
  {input : Array α}
  {base count skipped : Nat} :
-- imply
  (canonicalOccurrenceSegment input base count).drop skipped = canonicalOccurrenceSegment input (base + skipped) (count - skipped) := by
-- proof
  simp [canonicalOccurrenceSegment, List.extract, List.drop_take,
    List.drop_drop]

end CPythonListsort.ScanRemainderMatches

namespace CPythonListsort.ScanRemainderMatches

/--
[preserve_consumed_update](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean)
-/
@[path]
lemma preserve_consumed_update
  {input : Array α}
  {before after : MergeState (Occurrence α) ν}
  {scanned : Nat}
-- given
  (h : ScanRemainderMatches input before scanned)
  (hbase : after.basekeys = before.basekeys)
  (hlistlen : after.listlen = before.listlen)
  (hframe : SortSlice.EqualOutsideRange before.data after.data before.basekeys scanned) :
-- imply
  ScanRemainderMatches input after scanned := by
-- proof
  refine
    { scanned_le := by simpa [hlistlen] using h.scanned_le
      state_stop_le := ?_
      input_stop_le := by simpa [hbase, hlistlen] using h.input_stop_le
      keys_eq := ?_ }
  · rw [hbase, hlistlen]
    rwa [← hframe.size_eq]
  · have hsuffix := hframe.keys_eq_of_disjoint
    (before.basekeys + scanned) (before.listlen.toNat - scanned)
    (Or.inr le_rfl)
    rw [hbase, hlistlen]
    rwa [← hsuffix]

end CPythonListsort.ScanRemainderMatches

namespace CPythonListsort.ScanRemainderMatches

/--
[advance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean)
-/
@[path]
lemma advance
  {input : Array α}
  {before after : MergeState (Occurrence α) ν}
  {scanned consumed : Nat}
-- given
  (h : ScanRemainderMatches input before scanned)
  (hconsumed : consumed ≤ before.listlen.toNat - scanned)
  (hbase : after.basekeys = before.basekeys)
  (hlistlen : after.listlen = before.listlen)
  (hframe : SortSlice.EqualOutsideRange before.data after.data (before.basekeys + scanned) consumed) :
-- imply
  ScanRemainderMatches input after (scanned + consumed) := by
-- proof
  have hscannedConsumed :
    scanned + consumed ≤ before.listlen.toNat := by
    have hscanned := h.scanned_le
    omega
  have htail := congrArg (List.drop consumed) h.keys_eq
  rw [sortSliceRangeKeys_toList_drop,
    canonicalOccurrenceSegment_drop] at htail
  have hbeforeTail :
    (sortSliceRangeKeys before.data
      (before.basekeys + (scanned + consumed))
      (before.listlen.toNat - (scanned + consumed))).toList =
    canonicalOccurrenceSegment input
      (before.basekeys + (scanned + consumed))
      (before.listlen.toNat - (scanned + consumed)) := by
    simpa [Nat.add_assoc, Nat.sub_sub] using htail
  have hsuffix := hframe.keys_eq_of_disjoint
    (before.basekeys + (scanned + consumed))
    (before.listlen.toNat - (scanned + consumed)) (Or.inr (by omega))
  refine
    { scanned_le := by simpa [hlistlen] using hscannedConsumed
      state_stop_le := ?_
      input_stop_le := by simpa [hbase, hlistlen] using h.input_stop_le
      keys_eq := ?_ }
  · rw [hbase, hlistlen]
    rwa [← hframe.size_eq]
  · rw [hbase, hlistlen]
    rwa [← hsuffix]

end CPythonListsort.ScanRemainderMatches

namespace CPythonListsort.ScanRemainderEntriesMatch

/--
[toScanRemainderMatches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean)
-/
@[path]
lemma toScanRemainderMatches
  {source : SortSlice κ ν}
  {state : MergeState (Occurrence κ) ν}
  {scanned : Nat}
-- given
  (h : ScanRemainderEntriesMatch source state scanned) :
-- imply
  ScanRemainderMatches (source.entries.map SortSliceEntry.key) state scanned := by
-- proof
  refine
    { scanned_le := h.scanned_le
      state_stop_le := h.state_stop_le
      input_stop_le := by simpa using h.source_stop_le
      keys_eq := ?_ }
  have hkeys := congrArg (List.map SortSliceEntry.key) h.entries_eq
  calc
    (sortSliceRangeKeys state.data (state.basekeys + scanned)
      (state.listlen.toNat - scanned)).toList =
      (sortSliceRangeEntries state.data (state.basekeys + scanned)
        (state.listlen.toNat - scanned)).toList.map
          SortSliceEntry.key := by simp [sortSliceRangeKeys]
    _ =
      (sortSliceRangeEntries (tagSortSliceOccurrences source)
        (state.basekeys + scanned)
        (state.listlen.toNat - scanned)).toList.map
          SortSliceEntry.key := hkeys
    _ =
      (sortSliceRangeKeys (tagSortSliceOccurrences source)
        (state.basekeys + scanned)
        (state.listlen.toNat - scanned)).toList := by
          simp [sortSliceRangeKeys]
    _ = canonicalOccurrenceSegment
      (source.entries.map SortSliceEntry.key)
      (state.basekeys + scanned) (state.listlen.toNat - scanned) := by
      rw [sortSliceRangeKeys_tagSortSliceOccurrences]
      rfl

end CPythonListsort.ScanRemainderEntriesMatch

namespace CPythonListsort.ScanRemainderEntriesMatch

/--
[preserve_consumed_update](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean)
-/
@[path]
lemma preserve_consumed_update
  {source : SortSlice κ ν}
  {before after : MergeState (Occurrence κ) ν}
  {scanned : Nat}
-- given
  (h : ScanRemainderEntriesMatch source before scanned)
  (hbase : after.basekeys = before.basekeys)
  (hlistlen : after.listlen = before.listlen)
  (hframe : SortSlice.EqualOutsideRange before.data after.data before.basekeys scanned) :
-- imply
  ScanRemainderEntriesMatch source after scanned := by
-- proof
  refine
    { scanned_le := by simpa [hlistlen] using h.scanned_le
      state_stop_le := ?_
      source_stop_le := by simpa [hbase, hlistlen] using h.source_stop_le
      entries_eq := ?_ }
  · rw [hbase, hlistlen]
    rwa [← hframe.size_eq]
  · have hsuffix := hframe.entries_eq_of_disjoint
    (before.basekeys + scanned) (before.listlen.toNat - scanned)
    (Or.inr le_rfl)
    rw [hbase, hlistlen]
    rwa [← hsuffix]

end CPythonListsort.ScanRemainderEntriesMatch

namespace CPythonListsort.ScanRemainderEntriesMatch

/--
[advance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean)
-/
@[path]
lemma advance
  {source : SortSlice κ ν}
  {before after : MergeState (Occurrence κ) ν}
  {scanned consumed : Nat}
-- given
  (h : ScanRemainderEntriesMatch source before scanned)
  (hconsumed : consumed ≤ before.listlen.toNat - scanned)
  (hbase : after.basekeys = before.basekeys)
  (hlistlen : after.listlen = before.listlen)
  (hframe : SortSlice.EqualOutsideRange before.data after.data (before.basekeys + scanned) consumed) :
-- imply
  ScanRemainderEntriesMatch source after (scanned + consumed) := by
-- proof
  have hscannedConsumed :
    scanned + consumed ≤ before.listlen.toNat := by
    have hscanned := h.scanned_le
    omega
  have htail := congrArg (List.drop consumed) h.entries_eq
  rw [sortSliceRangeEntries_toList_drop,
    sortSliceRangeEntries_toList_drop] at htail
  have hbeforeTail :
    (sortSliceRangeEntries before.data
      (before.basekeys + (scanned + consumed))
      (before.listlen.toNat - (scanned + consumed))).toList =
    (sortSliceRangeEntries (tagSortSliceOccurrences source)
      (before.basekeys + (scanned + consumed))
      (before.listlen.toNat - (scanned + consumed))).toList := by
    simpa [Nat.add_assoc, Nat.sub_sub] using htail
  have hsuffix := hframe.entries_eq_of_disjoint
    (before.basekeys + (scanned + consumed))
    (before.listlen.toNat - (scanned + consumed)) (Or.inr (by omega))
  refine
    { scanned_le := by simpa [hlistlen] using hscannedConsumed
      state_stop_le := ?_
      source_stop_le := by simpa [hbase, hlistlen] using h.source_stop_le
      entries_eq := ?_ }
  · rw [hbase, hlistlen]
    rwa [← hframe.size_eq]
  · rw [hbase, hlistlen]
    rwa [← hsuffix]

end CPythonListsort.ScanRemainderEntriesMatch

namespace CPythonListsort

/--
[occurrenceInputSlice_size](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean)
-/
@[path]
lemma occurrenceInputSlice_size
  {input : Array α} :
-- imply
  (occurrenceInputSlice input).entries.size = input.size := by
-- proof
  simp [occurrenceInputSlice, tagOccurrences]

end CPythonListsort

namespace CPythonListsort

/--
[sortSliceRangeKeys_occurrenceInputSlice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean)
-/
@[path]
lemma sortSliceRangeKeys_occurrenceInputSlice
  {input : Array α}
  {start count : Nat} :
-- imply
  sortSliceRangeKeys (occurrenceInputSlice input) start count = (tagOccurrences input).extract start (start + count) := by
-- proof
  apply Array.ext_getElem?
  intro i
  simp [sortSliceRangeKeys, sortSliceRangeEntries, occurrenceInputSlice,
    Function.comp_def]

end CPythonListsort

namespace CPythonListsort

/--
[scanRemainderEntriesMatch_initial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean)
-/
@[path]
lemma scanRemainderEntriesMatch_initial
  {keyCompare : BoolComparator (Occurrence κ)}
  {source : SortSlice κ ν}
-- given
  (hasKeyfunc : Bool)
  (hsize : source.entries.size ≤ PY_LIST_MAX) :
-- imply
  ScanRemainderEntriesMatch source (initialMergeState keyCompare hasKeyfunc (tagSortSliceOccurrences source)).1 0 := by
-- proof
  have hword :
    (BitVec.ofNat 64 source.entries.size : PySSize).toNat =
      source.entries.size := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hsize ⊢
    omega
  refine
    { scanned_le := by
      simp [initialMergeState, minrunInitTraced, hword]
      state_stop_le := by
        simp [initialMergeState, minrunInitTraced, hword]
      source_stop_le := by
        simp [initialMergeState, minrunInitTraced, hword]
      entries_eq := ?_ }
  simp [initialMergeState, minrunInitTraced, hword]

end CPythonListsort

namespace CPythonListsort

/--
[scanRemainderEntriesMatch_initial_listSortInput](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean)
-/
@[path]
lemma scanRemainderEntriesMatch_initial_listSortInput
  {keyCompare : BoolComparator (Occurrence κ)}
  {input : ListSortInput κ ν}
-- given
  (hsize : input.slice.entries.size ≤ PY_LIST_MAX) :
-- imply
  ScanRemainderEntriesMatch input.slice (initialMergeState keyCompare input.hasKeyfunc input.withOccurrenceKeys.slice).1 0 := by
-- proof
  simpa [ListSortInput.withOccurrenceKeys] using
    scanRemainderEntriesMatch_initial keyCompare input.hasKeyfunc
      input.slice hsize

end CPythonListsort

namespace CPythonListsort

/--
[listSortInput_keyed_occurrence_payload_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean)
-/
@[path]
lemma listSortInput_keyed_occurrence_payload_regression
-- imply
  let input := ListSortInput.keyed (#[(7, 42)] : Array (Nat × Nat)) input.withOccurrenceKeys.hasKeyfunc = true ∧ input.withOccurrenceKeys.slice.entries = #[{ key := { value := 7, origin := 0 }, value := some 42 }] := by
-- proof
  norm_num [ListSortInput.withOccurrenceKeys, ListSortInput.keyed,
    tagSortSliceOccurrences]

end CPythonListsort

namespace CPythonListsort

/--
[scanRemainderMatches_initial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean)
-/
@[path]
lemma scanRemainderMatches_initial
  {keyCompare : BoolComparator (Occurrence α)}
  {input : Array α}
-- given
  (hsize : input.size ≤ PY_LIST_MAX) :
-- imply
  ScanRemainderMatches input (initialMergeState keyCompare false (occurrenceInputSlice input)).1 0 := by
-- proof
  have hword :
    (BitVec.ofNat 64 input.size : PySSize).toNat = input.size := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hsize ⊢
    omega
  refine
    { scanned_le := by simp [initialMergeState, minrunInitTraced, hword]
      state_stop_le := by
        simp [initialMergeState, minrunInitTraced, hword]
      input_stop_le := by
        simp [initialMergeState, minrunInitTraced, hword]
      keys_eq := ?_ }
  simp only [initialMergeState, minrunInitTraced, Nat.zero_add,
    Nat.sub_zero]
  rw [sortSliceRangeKeys_occurrenceInputSlice]
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[pendingRunsCorrect_allows_wrong_suffix_but_scanRemainder_rejects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean)
-/
@[path]
lemma pendingRunsCorrect_allows_wrong_suffix_but_scanRemainder_rejects
-- imply
  PendingRunsCorrect scanRemainderRegressionLt scanRemainderRegressionInput scanRemainderWrongSuffixState 0 ∧ ¬ScanRemainderMatches scanRemainderRegressionInput scanRemainderWrongSuffixState 0 := by
-- proof
  constructor
  · norm_num [PendingRunsCorrect, PendingLayout, PendingRunsCover,
    StableOccurrencePermutation, pendingOccurrenceKeys,
    canonicalOccurrenceSegment, scanRemainderRegressionInput,
    scanRemainderWrongSuffixState, PySSize.Nonnegative,
    BitVec.toNat_ofNat, BitVec.msb, BitVec.getMsbD, BitVec.getLsbD]
    all_goals decide
  · intro h
    have hkeys := h.keys_eq
    norm_num [sortSliceRangeKeys, sortSliceRangeEntries,
      canonicalOccurrenceSegment, tagOccurrences,
      scanRemainderRegressionInput, scanRemainderWrongSuffixState,
      scanRemainderRegressionEntry] at hkeys
    have htwo : (2 : PySSize).toNat = 2 := by decide
    rw [htwo] at hkeys
    norm_num at hkeys

end CPythonListsort

namespace CPythonListsort

/--
[scanRemainder_nonzero_base_wrong_origin_rejected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean)
-/
@[path]
lemma scanRemainder_nonzero_base_wrong_origin_rejected
-- imply
  (sortSliceRangeKeys scanRemainderNonzeroBaseWrongOriginState.data 0 2).toList = canonicalOccurrenceSegment scanRemainderNonzeroBaseInput 0 2 ∧ ((sortSliceRangeKeys scanRemainderNonzeroBaseWrongOriginState.data 1 2).map Occurrence.value).toList = (scanRemainderNonzeroBaseInput.extract 1 3).toList ∧ ¬ScanRemainderMatches scanRemainderNonzeroBaseInput scanRemainderNonzeroBaseWrongOriginState 0 := by
-- proof
  constructor
  · norm_num [sortSliceRangeKeys, sortSliceRangeEntries,
    canonicalOccurrenceSegment, tagOccurrences,
    scanRemainderNonzeroBaseInput,
    scanRemainderNonzeroBaseWrongOriginState,
    scanRemainderRegressionEntry]
  constructor
  · norm_num [sortSliceRangeKeys, sortSliceRangeEntries,
    scanRemainderNonzeroBaseInput,
    scanRemainderNonzeroBaseWrongOriginState,
    scanRemainderRegressionEntry]
  · intro h
    have hkeys := h.keys_eq
    norm_num [sortSliceRangeKeys, sortSliceRangeEntries,
      canonicalOccurrenceSegment, tagOccurrences,
      scanRemainderNonzeroBaseInput,
      scanRemainderNonzeroBaseWrongOriginState,
      scanRemainderRegressionEntry] at hkeys
    have htwo : (2 : PySSize).toNat = 2 := by decide
    rw [htwo] at hkeys
    norm_num at hkeys

end CPythonListsort

/--
[tagSortSliceOccurrences_valuesMode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean)
-/
@[path]
private lemma tagSortSliceOccurrences_valuesMode_eq
  {hasKeyfunc : Bool}
  {slice : SortSlice κ ν}
-- given
  (h : SortSlice.ValuesModeInvariant hasKeyfunc slice) :
-- imply
  SortSlice.ValuesModeInvariant hasKeyfunc (tagSortSliceOccurrences slice) := by
-- proof
  apply CPythonListsort.tagSortSliceOccurrences_valuesMode h


-- created on 2026-10-23
