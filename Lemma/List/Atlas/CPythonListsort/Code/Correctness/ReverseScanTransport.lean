import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Correctness.ReverseScanTransport
open CPythonListsort


namespace CPythonListsort

/--
[actualReverseScanState_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseScanTransport.lean)
-/
@[path]
lemma actualReverseScanState_data
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {input : ListSortInput alpha nu} :
-- imply
  (actualReverseScanState lt input).data = input.withOccurrenceKeys.slice.reverseEntries := by
-- proof
  change
    mirrorSortSlice input.slice.entries.size
      input.reverseEntries.withOccurrenceKeys.slice =
      input.withOccurrenceKeys.slice.reverseEntries
  exact input.mirror_withOccurrenceKeys_reverseEntries

end CPythonListsort

namespace CPythonListsort

/--
[actualReverseScanState_eq_initial_with_reversed_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseScanTransport.lean)
-/
@[path]
lemma actualReverseScanState_eq_initial_with_reversed_data
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {input : ListSortInput alpha nu} :
-- imply
  actualReverseScanState lt input = { (initialMergeState (occurrenceComparator lt) input.hasKeyfunc input.withOccurrenceKeys.slice).1 with data := input.withOccurrenceKeys.slice.reverseEntries } := by
-- proof
  have hsize :
    input.reverseEntries.withOccurrenceKeys.slice.entries.size =
      input.withOccurrenceKeys.slice.entries.size := by
    simp [ListSortInput.withOccurrenceKeys]
  simp [actualReverseScanState, canonicalReverseScanState, initialMergeState,
    mirrorMergeState, mirrorTempStorage, mergeInitTemp,
    ListSortInput.mirror_withOccurrenceKeys_reverseEntries, hsize]

end CPythonListsort

namespace CPythonListsort

/--
[canonicalReverseScanState_comparator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseScanTransport.lean)
-/
@[path]
lemma canonicalReverseScanState_comparator
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {input : ListSortInput alpha nu} :
-- imply
  (canonicalReverseScanState lt input).key_compare = occurrenceComparator lt := by
-- proof
  simp [canonicalReverseScanState, initialMergeState]

end CPythonListsort

namespace CPythonListsort

/--
[actualReverseScanState_comparator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseScanTransport.lean)
-/
@[path]
lemma actualReverseScanState_comparator
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {input : ListSortInput alpha nu} :
-- imply
  (actualReverseScanState lt input).key_compare = occurrenceComparator lt := by
-- proof
  simp [actualReverseScanState]

end CPythonListsort

namespace CPythonListsort

/--
[reverseScanTransport_correct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseScanTransport.lean)
-/
@[path]
lemma reverseScanTransport_correct
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {input : ListSortInput alpha nu}
-- given
  (horder : BoolStrictWeakOrder lt)
  (hLower : 2 ≤ input.slice.entries.size)
  (hMax : input.slice.entries.size ≤ PY_LIST_MAX) :
-- imply
  ∃ canonicalTerminal canonicalCollapsed canonicalResult terminal collapsed result, ReverseScanTransportPost lt input canonicalTerminal canonicalCollapsed canonicalResult terminal collapsed result := by
-- proof
  have hLowerReversed : 2 ≤ input.reverseEntries.slice.entries.size := by
    simpa using hLower
  have hMaxReversed :
    input.reverseEntries.slice.entries.size ≤ PY_LIST_MAX := by
    simpa using hMax
  have hinvariant :
    ListSortScanCorrectnessInvariant lt input.reverseEntries.slice
      input.hasKeyfunc input.slice.entries.size
      (canonicalReverseScanState lt input) 0 0 input.slice.entries.size := by
    simpa [canonicalReverseScanState] using
      listSortScanCorrectnessInvariant_initial lt input.reverseEntries
        hLowerReversed hMaxReversed
  rcases listSortScan_complete_correct (reverse := true) horder hinvariant
    (show input.slice.entries.size ≤ input.slice.entries.size from le_rfl) with
    ⟨canonicalTerminal, canonicalCollapsed, canonicalResult, hcanonical⟩
  let size := input.slice.entries.size
  let terminal := mirrorMergeState size canonicalTerminal
  let collapsed := mirrorMergeForceCollapseResult size canonicalCollapsed
  let result := mirrorListSortImplResult size canonicalResult
  have hcommutation :
    listSortScan? size (actualReverseScanState lt input) 0 size true size =
      (listSortScan? size (canonicalReverseScanState lt input) 0 size true
        size).map (mirrorListSortImplResult size) := by
    exact mirrorListSortScan lt size size (canonicalReverseScanState lt input)
      0 size true size (canonicalReverseScanState_comparator lt input)
  have hterminalCompare :
    canonicalTerminal.key_compare = occurrenceComparator lt :=
    hcanonical.terminalInvariant.safety.comparator
  have hcollapse : mergeForceCollapse? terminal = some collapsed := by
    dsimp [terminal, collapsed]
    rw [mirrorMergeForceCollapse lt size canonicalTerminal hterminalCompare,
      hcanonical.collapseResultEq]
    rfl
  have hpreFinish :
    listSortScan? size (actualReverseScanState lt input) 0 size true size =
      finishListSort? collapsed.state true size 0 false := by
    calc
      listSortScan? size (actualReverseScanState lt input) 0 size true size =
        (listSortScan? size (canonicalReverseScanState lt input) 0 size true
          size).map (mirrorListSortImplResult size) := hcommutation
      _ = (finishListSort? canonicalCollapsed.state true size 0 false).map
        (mirrorListSortImplResult size) := by
        rw [hcanonical.preFinishEquation]
      _ = finishListSort? collapsed.state true size 0 false := by
        dsimp [collapsed]
        exact (mirrorFinishListSort size canonicalCollapsed.state true size
          0 false).symm
  have hresultEq :
    listSortScan? size (actualReverseScanState lt input) 0 size true size =
      some result := by
    rw [hcommutation, hcanonical.resultEq]
    rfl
  have hfinishResult :
    finishListSort? collapsed.state true size 0 false = some result :=
    hpreFinish.symm.trans hresultEq
  have hwhole := hcanonical.wholeDataCorrect
  have hcanonicalKeys :
    input.reverseEntries.slice.entries.map SortSliceEntry.key =
      (input.slice.entries.map SortSliceEntry.key).reverse := by
    simp [SortSlice.reverseEntries, Array.map_reverse]
  have hcanonicalStable : StableOccurrencePermutation lt
    (tagOccurrences
      (input.slice.entries.map SortSliceEntry.key).reverse).toList
    (canonicalCollapsed.state.data.entries.map SortSliceEntry.key).toList := by
    rwa [← hcanonicalKeys]
  have hactualKeys :
    collapsed.state.data.entries.map SortSliceEntry.key =
      (canonicalCollapsed.state.data.entries.map SortSliceEntry.key).map
        (mirrorOccurrence size) := by
    dsimp [collapsed]
    simp [Array.map_map, Function.comp_def]
  have hsorted : Sorted (occurrenceComparator lt)
    (collapsed.state.data.entries.map SortSliceEntry.key) := by
    rw [hactualKeys]
    exact (sorted_mirror_iff lt size _).2 hwhole.1
  have hstable : ReverseStableOccurrencePermutation lt
    (tagOccurrences (input.slice.entries.map SortSliceEntry.key)).toList
    (collapsed.state.data.entries.map SortSliceEntry.key).toList := by
    rw [hactualKeys, Array.toList_map]
    simpa [size] using stable_reversedSource_mirror hcanonicalStable
  have hcanonicalSnapshot : EntrySnapshotPermutation
    input.slice.reverseEntries canonicalCollapsed.state.data := by
    simpa using hcanonical.collapsedSnapshot
  have hsnapshot :
    EntrySnapshotPermutation input.slice collapsed.state.data := by
    dsimp [collapsed]
    exact hcanonicalSnapshot.mirror_reversedSource
  refine ⟨canonicalTerminal, canonicalCollapsed, canonicalResult,
    terminal, collapsed, result, ?_⟩
  exact
    { canonicalPost := hcanonical
      terminalMirror := rfl
      collapsedMirror := rfl
      resultMirror := rfl
      scanCommutation := hcommutation
      collapseResultEq := hcollapse
      preFinishEquation := hpreFinish
      resultEq := hresultEq
      finishResultEq := hfinishResult
      returnCode := by
        dsimp [result, mirrorListSortImplResult]
        exact hcanonical.returnCode
      resultFuel := by
        dsimp [result, mirrorListSortImplResult]
        exact hcanonical.resultFuel
      preFinishSorted := hsorted
      preFinishReverseStable := hstable
      preFinishSnapshot := hsnapshot }

end CPythonListsort


-- created on 2026-10-23
