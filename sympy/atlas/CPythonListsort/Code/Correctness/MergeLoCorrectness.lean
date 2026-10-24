/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeLoCorrectness.lean -/

import sympy.atlas.CPythonListsort.Code.Correctness.EntrySnapshotPermutation
import sympy.atlas.CPythonListsort.Code.Correctness.MergeLoInvariant
import sympy.atlas.CPythonListsort.Code.Correctness.MergeLoRegressionKernel

/-!
# Functional correctness of `merge_lo`

The central postcondition is exact equality of the affected whole-entry range
with the shared left-biased mathematical merge.  Sortedness, occurrence
stability, key/payload permutation, framing, and persistent snapshot
preservation are exposed as public consequences of that equality.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Public functional postcondition for the exact traced `merge_lo` execution
selected by `prepareMergeAt?`. -/
structure MergeLoCorrectnessPost
    (lt : BoolComparator alpha) (canonical : List (Occurrence alpha))
    (pre : MergeState (Occurrence alpha) nu) (scanned i : Nat)
    (call : MergeAtCall (Occurrence alpha) nu)
    (result : MergeLoResult (Occurrence alpha) nu) : Prop where
  safety : MergeLoSafetyPost pre scanned i call
    (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb) result
  exactRange :
    (sortSliceRangeEntries result.state.data call.ssa.toNat
      (call.na + call.nb)).toList = mergeLoTargetEntries lt call
  sorted : Sorted (occurrenceComparator lt)
    (sortSliceRangeKeys result.state.data call.ssa.toNat
      (call.na + call.nb))
  stable : StableOccurrencePermutation lt canonical
    (sortSliceRangeKeys result.state.data call.ssa.toNat
      (call.na + call.nb)).toList
  rangeEntriesPerm :
    (sortSliceRangeEntries result.state.data call.ssa.toNat
      (call.na + call.nb)).toList.Perm
      (sortSliceRangeEntries call.state.data call.ssa.toNat
        (call.na + call.nb)).toList
  frame : SortSlice.EqualOutsideRange call.state.data result.state.data
    call.ssa.toNat (call.na + call.nb)

/-- Functional certificate for the untraced transcription. -/
structure MergeLoRawCorrectnessPost
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu)
    (result : MergeLoResult (Occurrence alpha) nu) : Prop where
  resultEq : mergeLo? call.state call.ssa call.ssb call.na call.nb = some result
  exactRange :
    (sortSliceRangeEntries result.state.data call.ssa.toNat
      (call.na + call.nb)).toList = mergeLoTargetEntries lt call
  frame : SortSlice.EqualOutsideRange call.state.data result.state.data
    call.ssa.toNat (call.na + call.nb)

private structure MergeLoLoopCorrectPost
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu)
    (execution : Option (MergeLoResult (Occurrence alpha) nu))
    (result : MergeLoResult (Occurrence alpha) nu) : Prop where
  resultEq : execution = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  semantic : MergeLoSemanticOutput lt call result.state
