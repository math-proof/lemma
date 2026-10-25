import Mathlib
import sympy.Basic
import Structure.CPythonListsort.Code.Correctness.ReverseModeCorrectness
open CPythonListsort


namespace CPythonListsort

/--
[reverseMode_correct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseModeCorrectness.lean)
-/
@[path]
lemma reverseMode_correct
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {input : ListSortInput alpha nu}
-- given
  (horder : BoolStrictWeakOrder lt)
  (hLower : 2 ≤ input.slice.entries.size)
  (hMax : input.slice.entries.size ≤ PY_LIST_MAX) :
-- imply
  ∃ result, ReverseModeCorrectnessPost lt input result := by
-- proof
  rcases reverseScanTransport_correct lt horder input hLower hMax with
    ⟨canonicalTerminal, canonicalCollapsed, canonicalResult,
      terminal, collapsed, result, htransport⟩
  have hExtent :
    collapsed.state.data.entries.size = input.slice.entries.size := by
    have hlength := htransport.preFinishSnapshot.length_eq
    simpa [EntrySnapshotPermutation, tagSortSliceOccurrences] using hlength
  have hRange : SortSlice.RangeInBounds collapsed.state.data 0
    input.slice.entries.size := by
    constructor
    · omega
    · simp [hExtent]
  rcases sortsliceReverse_correct collapsed.state.data 0
    input.slice.entries.size hRange with
    ⟨reversed, hreversed, hreversedFuel, hreversedEntries⟩
  have hReversedEntries :
    reversed.slice.entries = collapsed.state.data.entries.reverse := by
    rw [hreversedEntries]
    apply Array.ext <;>
      simp [ReverseRangeSpec.reverseRangeEntries, hExtent]
  let updated : MergeState (Occurrence alpha) nu :=
    { collapsed.state with data := reversed.slice }
  have hFinalReverse : 1 < input.slice.entries.size := by omega
  have hResult : result =
    { state := mergeFreemem updated
      returnCode := 0
      fuelExhausted := false } := by
    have hfinish := htransport.finishResultEq
    simp [finishListSort?, hFinalReverse, hreversed, hreversedFuel]
      at hfinish
    exact hfinish.symm
  have hResultData : result.state.data = reversed.slice := by
    rw [hResult]
    change (mergeFreemem updated).data = reversed.slice
    unfold mergeFreemem
    split <;> rfl
  have hResultOccurrences :
    result.occurrences =
      (collapsed.state.data.entries.map SortSliceEntry.key).reverse := by
    rw [ListSortImplResult.occurrences, hResultData, hReversedEntries,
      Array.map_reverse]
  have hSnapshotReversed :
    EntrySnapshotPermutation input.slice reversed.slice := by
    apply htransport.preFinishSnapshot.preserve_of_whole_entries_perm
    rw [hReversedEntries, Array.toList_reverse]
    exact List.reverse_perm _
  refine ⟨result, ?_⟩
  exact
    { scanResultEq := htransport.resultEq
      returnCode := htransport.returnCode
      resultFuel := htransport.resultFuel
      sorted := by
        rw [hResultOccurrences]
        simpa only [occurrenceComparator_swapped] using
          htransport.preFinishSorted.reverse_swapped
      stable := by
        rwa [hResultOccurrences, Array.toList_reverse]
      entrySnapshot := by
        rw [hResultData]
        exact hSnapshotReversed }

end CPythonListsort


-- created on 2026-10-23
