/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseScanTransport.lean -/

import Def.CPythonListsort.Code.Correctness.OriginRelabelScan.Part2
import Def.CPythonListsort.Code.Correctness.ReverseModeAlgebra.Part4
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

end CPythonListsort
