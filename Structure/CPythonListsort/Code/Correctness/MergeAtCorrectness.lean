/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeAtCorrectness.lean -/

import Def.CPythonListsort.Code.Assembly.GallopCorrectness
import Def.CPythonListsort.Code.Assembly.MergeAtSafety.Part4
import Def.CPythonListsort.Code.Correctness.MergeAtCorrectnessSupport
import Def.CPythonListsort.Code.Correctness.MergeHiCorrectness
import Structure.CPythonListsort.Code.Correctness.MergeLoCorrectness
import Def.CPythonListsort.Code.Correctness.PendingRunCorrectness
import Lemma.List.Atlas.CPythonListsort.Code.Policy.MergeAtPreservation
import Lemma.List.Atlas.CPythonListsort.Code.Policy.MergeTopPowerPreservation
import Def.CPythonListsort.Code.Correctness.MergeAtCorrectness
/-!
# Functional correctness of `merge_at`

This module lifts the exact trimmed-range specifications of `merge_lo` and
`merge_hi` to the complete adjacent pair selected by `merge_at`.  Its public
postcondition is deliberately phrased at the scan invariant boundary: the
actual traced evaluator succeeds, the selected union is the mathematical
left-biased stable merge, all pending runs remain correct, the persistent
whole-entry snapshot is preserved, and no entry outside the consumed prefix
changes.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Functional certificate for the exact pair selected by `merge_at`.

`exactRange` covers the complete pre-trimming union, not merely the smaller
middle range passed to `merge_lo` or `merge_hi`.  Thus the unchanged galloped
prefix and suffix are part of the observable result. -/
structure MergeAtSelectedPairCorrectness
    (lt : BoolComparator alpha)
    (pre : MergeState (Occurrence alpha) nu) (i : Nat)
    (result : MergeAtResult (Occurrence alpha) nu)
    (left right : PendingRun) : Prop where
  leftSelected : pre.pending[i]? = some left
  rightSelected : pre.pending[i + 1]? = some right
  pendingSplice : ∃ before after,
    before.length = i ∧
      pre.pending.toList = before ++ left :: right :: after ∧
      result.state.pending.toList =
        before ++
          ({ left with len := left.len + right.len } : PendingRun) :: after
  combinedLength :
    (left.len + right.len).toNat = left.len.toNat + right.len.toNat
  exactRange :
    (sortSliceRangeEntries result.state.data left.base
      (left.len.toNat + right.len.toNat)).toList =
        mergeAtTargetEntries lt pre left right
  sorted : Sorted (occurrenceComparator lt)
    (sortSliceRangeKeys result.state.data left.base
      (left.len.toNat + right.len.toNat))
  stable : StableOccurrencePermutation lt
    ((mergeAtLeftEntries pre left).map SortSliceEntry.key ++
      (mergeAtRightEntries pre right).map SortSliceEntry.key)
    (sortSliceRangeKeys result.state.data left.base
      (left.len.toNat + right.len.toNat)).toList
  rangeEntriesPerm :
    (sortSliceRangeEntries result.state.data left.base
      (left.len.toNat + right.len.toNat)).toList.Perm
        ((mergeAtLeftEntries pre left) ++ (mergeAtRightEntries pre right))
  frame : SortSlice.EqualOutsideRange pre.data result.state.data left.base
    (left.len.toNat + right.len.toNat)

/-- End-to-end correctness at the public scan/collapse boundary. -/
structure MergeAtCorrectnessPost
    (lt : BoolComparator alpha) (input : Array alpha)
    (source : SortSlice alpha nu)
    (pre : MergeState (Occurrence alpha) nu) (scanned i : Nat)
    (result : MergeAtResult (Occurrence alpha) nu) : Prop where
  safety : MergeAtSafetyPost pre scanned i (mergeAtTraced? pre i) result
  selected : ∃ left right,
    MergeAtSelectedPairCorrectness lt pre i result left right
  pendingRunsCorrect : PendingRunsCorrect lt input result.state scanned
  entrySnapshot : EntrySnapshotPermutation source result.state.data
  comparator : result.state.key_compare = occurrenceComparator lt
  consumedFrame : SortSlice.EqualOutsideRange pre.data result.state.data
    pre.basekeys scanned

/-- All semantic facts carried from the two `merge_at` gallops to either
directional merge implementation. -/
structure MergeAtCallCorrectnessPre
    (lt : BoolComparator alpha)
    (pre : MergeState (Occurrence alpha) nu) (scanned i : Nat)
    (call : MergeAtCall (Occurrence alpha) nu) : Prop where
  evidence : MergeAtCallsiteEvidence pre i call
  geometry : MergeAtSafetyGeometry pre scanned i call
  pairGeometry : PendingAdjacentPairGeometry pre scanned call.left call.right
  leftStop : call.left.base + call.left.len.toNat ≤ pre.data.entries.size
  rightStop : call.right.base + call.right.len.toNat ≤ pre.data.entries.size
  leftFullSorted : Sorted (occurrenceComparator lt)
    (sortSliceRangeKeys pre.data call.left.base call.left.len.toNat)
  rightFullSorted : Sorted (occurrenceComparator lt)
    (sortSliceRangeKeys pre.data call.right.base call.right.len.toNat)
  fullStable : StableOccurrencePermutation lt
    ((pendingRunOccurrenceKeys pre call.left).toList ++
      (pendingRunOccurrenceKeys pre call.right).toList)
    ((pendingRunOccurrenceKeys pre call.left).toList ++
      (pendingRunOccurrenceKeys pre call.right).toList)
  leftPartition : GallopRightPartition (occurrenceComparator lt)
    call.state.data (Int.ofNat call.left.base) call.firstB.key
    call.left.len.toNat call.trimA.index
  rightPartition : GallopLeftPartition (occurrenceComparator lt)
    call.state.data (Int.ofNat call.right.base) call.lastA.key
    call.right.len.toNat call.trimB.index
  semantic : MergeSemanticPre lt call
  trimmedStable : StableOccurrencePermutation lt
    ((sortSliceRangeKeys call.state.data call.ssa.toNat call.na).toList ++
      (sortSliceRangeKeys call.state.data call.ssb.toNat call.nb).toList)
    ((sortSliceRangeKeys call.state.data call.ssa.toNat call.na).toList ++
      (sortSliceRangeKeys call.state.data call.ssb.toNat call.nb).toList)

end CPythonListsort
