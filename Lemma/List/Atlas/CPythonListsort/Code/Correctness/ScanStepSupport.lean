import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Correctness.ScanStepSupport
open CPythonListsort CPythonListsort.CountRunCorrectnessPost CPythonListsort.EntrySnapshotPermutation CPythonListsort.PendingRunsCorrect


namespace CPythonListsort

/--
[sortSliceRangeKeys_toList_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanStepSupport.lean)
-/
@[path]
lemma sortSliceRangeKeys_toList_add
  {alpha : Type u}
  {nu : Type v}
  {slice : SortSlice alpha nu}
  {start leftCount rightCount : Nat} :
-- imply
  (sortSliceRangeKeys slice start (leftCount + rightCount)).toList = (sortSliceRangeKeys slice start leftCount).toList ++ (sortSliceRangeKeys slice (start + leftCount) rightCount).toList := by
-- proof
  simp only [sortSliceRangeKeys_toList, List.take_add, List.drop_drop,
    List.map_append]

end CPythonListsort

namespace CPythonListsort.CountRunCorrectnessPost

/--
[stable_from_remainder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanStepSupport.lean)
-/
@[path]
lemma stable_from_remainder
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {source : SortSlice alpha nu}
  {state : MergeState (Occurrence alpha) nu}
  {scanned : Nat}
  {base : Int}
  {nremaining : Nat}
  {result : CountRunResult (Occurrence alpha) nu}
  {post : CountRunCorrectnessPost lt state state.data base nremaining result}
  {remainder : ScanRemainderEntriesMatch source state scanned}
-- given
  (hbase : base.toNat = state.basekeys + scanned)
  (hresultRemaining : result.length ≤ state.listlen.toNat - scanned) :
-- imply
  StableOccurrencePermutation lt (canonicalOccurrenceSegment (source.entries.map SortSliceEntry.key) (state.basekeys + scanned) result.length) (sortSliceRangeKeys result.slice (state.basekeys + scanned) result.length).toList := by
-- proof
  have hsource := remainder.prefix_keys_eq hresultRemaining
  have hstable := post.stable
  rw [hbase] at hstable
  rwa [hsource] at hstable

end CPythonListsort.CountRunCorrectnessPost

namespace CPythonListsort.CountRunCorrectnessPost

/--
[stable_for_forced_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanStepSupport.lean)
-/
@[path]
lemma stable_for_forced_range
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {source : SortSlice alpha nu}
  {state : MergeState (Occurrence alpha) nu}
  {scanned force : Nat}
  {base : Int}
  {nremaining : Nat}
  {result : CountRunResult (Occurrence alpha) nu}
  {post : CountRunCorrectnessPost lt state state.data base nremaining result}
  {remainder : ScanRemainderEntriesMatch source state scanned}
-- given
  (hbase : base.toNat = state.basekeys + scanned)
  (hrunForce : result.length ≤ force)
  (hforceRemaining : force ≤ state.listlen.toNat - scanned) :
-- imply
  StableOccurrencePermutation lt (canonicalOccurrenceSegment (source.entries.map SortSliceEntry.key) (state.basekeys + scanned) force) (sortSliceRangeKeys result.slice (state.basekeys + scanned) force).toList := by
-- proof
  let input := source.entries.map SortSliceEntry.key
  let start := state.basekeys + scanned
  have hprefix : StableOccurrencePermutation lt
    (canonicalOccurrenceSegment input start result.length)
    (sortSliceRangeKeys result.slice start result.length).toList := by
    exact post.stable_from_remainder remainder hbase
      (le_trans hrunForce hforceRemaining)
  have hbeforeWhole :
    (sortSliceRangeKeys state.data start force).toList =
      canonicalOccurrenceSegment input start force := by
    exact remainder.prefix_keys_eq hforceRemaining
  have hbeforeSuffix :
    (sortSliceRangeKeys state.data (start + result.length)
      (force - result.length)).toList =
      canonicalOccurrenceSegment input (start + result.length)
        (force - result.length) := by
    have hdropped := congrArg (List.drop result.length) hbeforeWhole
    rw [sortSliceRangeKeys_toList_drop,
      ScanRemainderMatches.canonicalOccurrenceSegment_drop] at hdropped
    exact hdropped
  have hafterSuffix :
    (sortSliceRangeKeys result.slice (start + result.length)
      (force - result.length)).toList =
      canonicalOccurrenceSegment input (start + result.length)
        (force - result.length) := by
    have hpostFrame := post.frame
    rw [hbase] at hpostFrame
    have hframe := hpostFrame.keys_eq_of_disjoint
      (start + result.length) (force - result.length) (Or.inr le_rfl)
    rwa [← hframe]
  have hsuffix : StableOccurrencePermutation lt
    (canonicalOccurrenceSegment input (start + result.length)
      (force - result.length))
    (sortSliceRangeKeys result.slice (start + result.length)
      (force - result.length)).toList := by
    rw [hafterSuffix]
    exact canonicalOccurrenceSegment_countRunCanonical lt input
      (start + result.length) (force - result.length)
  have happended := stableOccurrencePermutation_append_adjacent hprefix hsuffix
  have hforce : result.length + (force - result.length) = force := by omega
  have hsplit := sortSliceRangeKeys_toList_add result.slice start
    result.length (force - result.length)
  rw [hforce] at hsplit happended
  rwa [hsplit]

end CPythonListsort.CountRunCorrectnessPost

namespace CPythonListsort.EntrySnapshotPermutation

/--
[preserve_countRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanStepSupport.lean)
-/
@[path]
lemma preserve_countRun
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {source : SortSlice alpha nu}
  {state : MergeState (Occurrence alpha) nu}
  {base : Int}
  {nremaining : Nat}
  {result : CountRunResult (Occurrence alpha) nu}
  {snapshot : EntrySnapshotPermutation source state.data}
  {post : CountRunCorrectnessPost lt state state.data base nremaining result}
-- given
  (hstop : base.toNat + result.length ≤ state.data.entries.size) :
-- imply
  EntrySnapshotPermutation source result.slice :=
-- proof
snapshot.preserve_local post.frame hstop post.entryPermutation

end CPythonListsort.EntrySnapshotPermutation

namespace CPythonListsort.EntrySnapshotPermutation

/--
[preserve_binarysort](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanStepSupport.lean)
-/
@[path]
lemma preserve_binarysort
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {source : SortSlice alpha nu}
  {canonical : List (Occurrence alpha)}
  {state : MergeState (Occurrence alpha) nu}
  {before : SortSlice (Occurrence alpha) nu}
  {base n ok : Nat}
  {result : BinarysortResult (Occurrence alpha) nu}
  {snapshot : EntrySnapshotPermutation source before}
  {post : BinarysortCorrectnessPost lt canonical state before base n ok result}
-- given
  (hstop : base + n ≤ before.entries.size) :
-- imply
  EntrySnapshotPermutation source result.slice := by
-- proof
  exact snapshot.preserve_local post.frame hstop post.rangeEntriesPerm

end CPythonListsort.EntrySnapshotPermutation

/--
[pushPendingRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanStepSupport.lean)
-/
@[path]
private lemma pushPendingRun_eq
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {input : Array alpha}
  {state : MergeState (Occurrence alpha) nu}
  {scanned : Nat}
  {newRun : PendingRun}
  {correct : PendingRunsCorrect lt input state scanned}
  {ready : ReadyToPush state scanned newRun}
  {newSorted : Sorted (occurrenceComparator lt) (pendingRunOccurrenceKeys state newRun)}
  {newStable : StableOccurrencePermutation lt (canonicalOccurrenceSegment input (state.basekeys + scanned) newRun.len.toNat) (pendingRunOccurrenceKeys state newRun).toList} :
-- imply
  PendingRunsCorrect lt input (CPythonListsort.pushPendingRun state newRun) (scanned + newRun.len.toNat) := by
-- proof
  apply CPythonListsort.PendingRunsCorrect.pushPendingRun correct ready newSorted newStable


-- created on 2026-10-23
