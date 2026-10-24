/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseScanTransport.lean -/

import sympy.atlas.CPythonListsort.Code.Correctness.OriginRelabelScan
import sympy.atlas.CPythonListsort.Code.Correctness.ReverseModeAlgebra

/-!
# Reverse-oriented complete-scan transport

The ordinary whole-scan theorem applies to a canonically tagged reversed
source.  The actual reverse-mode scan instead carries the original occurrence
tags through the initial physical reversal.  These two states differ only by
the total origin mirror, so raw evaluator equivariance transports the complete
scan/collapse certificate without retagging an executed result.

This module deliberately stops before assigning semantic meaning to the final
whole-array reversal.  It retains the exact `finishListSort?` equation and the
mirrored collapsed state; `ReverseModeCorrectness` consumes those facts.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Initial state for the ordinary correctness theorem on the canonically
tagged, physically reversed source. -/
def canonicalReverseScanState (lt : BoolComparator alpha)
    (input : ListSortInput alpha nu) : MergeState (Occurrence alpha) nu :=
  (initialMergeState (occurrenceComparator lt) input.hasKeyfunc
    input.reverseEntries.withOccurrenceKeys.slice).1

/-- The state seen by the actual reverse-mode scan: the canonical reversed
execution with every carried origin mirrored back to its original index. -/
def actualReverseScanState (lt : BoolComparator alpha)
    (input : ListSortInput alpha nu) : MergeState (Occurrence alpha) nu :=
  mirrorMergeState input.slice.entries.size
    (canonicalReverseScanState lt input)

/-- Complete reverse-oriented scan packet.

`canonical*` are witnesses from the ordinary theorem on the canonically tagged
reversed source.  `terminal`, `collapsed`, and `result` are their exact
origin-mirrored counterparts for the actual reverse-mode scan.  The semantic
facts intentionally stop at `collapsed.state`, before `finishListSort?`
performs the final reversal. -/
structure ReverseScanTransportPost
    (lt : BoolComparator alpha) (input : ListSortInput alpha nu)
    (canonicalTerminal : MergeState (Occurrence alpha) nu)
    (canonicalCollapsed : MergeForceCollapseResult (Occurrence alpha) nu)
    (canonicalResult : ListSortImplResult (Occurrence alpha) nu)
    (terminal : MergeState (Occurrence alpha) nu)
    (collapsed : MergeForceCollapseResult (Occurrence alpha) nu)
    (result : ListSortImplResult (Occurrence alpha) nu) : Prop where
  canonicalPost : ListSortScanCollapseCorrectnessPost lt input.reverseEntries.slice
    input.hasKeyfunc input.slice.entries.size input.slice.entries.size
    (canonicalReverseScanState lt input) 0 0 input.slice.entries.size true
    canonicalTerminal canonicalCollapsed canonicalResult
  terminalMirror : terminal =
    mirrorMergeState input.slice.entries.size canonicalTerminal
  collapsedMirror : collapsed =
    mirrorMergeForceCollapseResult input.slice.entries.size canonicalCollapsed
  resultMirror : result =
    mirrorListSortImplResult input.slice.entries.size canonicalResult
  scanCommutation :
    listSortScan? input.slice.entries.size (actualReverseScanState lt input) 0
        input.slice.entries.size true input.slice.entries.size =
      (listSortScan? input.slice.entries.size
        (canonicalReverseScanState lt input) 0 input.slice.entries.size true
        input.slice.entries.size).map
          (mirrorListSortImplResult input.slice.entries.size)
  collapseResultEq : mergeForceCollapse? terminal = some collapsed
  preFinishEquation :
    listSortScan? input.slice.entries.size (actualReverseScanState lt input) 0
        input.slice.entries.size true input.slice.entries.size =
      finishListSort? collapsed.state true input.slice.entries.size 0 false
  resultEq :
    listSortScan? input.slice.entries.size (actualReverseScanState lt input) 0
        input.slice.entries.size true input.slice.entries.size = some result
  finishResultEq :
    finishListSort? collapsed.state true input.slice.entries.size 0 false =
      some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  preFinishSorted : Sorted (occurrenceComparator lt)
    (collapsed.state.data.entries.map SortSliceEntry.key)
  preFinishReverseStable : ReverseStableOccurrencePermutation lt
    (tagOccurrences (input.slice.entries.map SortSliceEntry.key)).toList
    (collapsed.state.data.entries.map SortSliceEntry.key).toList
  preFinishSnapshot : EntrySnapshotPermutation input.slice collapsed.state.data
