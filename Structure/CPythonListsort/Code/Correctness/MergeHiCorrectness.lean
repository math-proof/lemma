/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeHiCorrectness.lean -/

import Def.CPythonListsort.Code.Correctness.EntrySnapshotPermutation
import Theorem.CPythonListsort.Code.Correctness.MergeHiInvariant
/-!
# Public functional postcondition for `merge_hi`

The physical algorithm fills its output from right to left, but its observable
specification is the ordinary forward, left-biased `stableEntryMerge` of the
two post-trimming input runs.  Keeping the exact whole-entry equality in the
public postcondition makes sortedness, occurrence stability, payload
permutation, framing, and persistent input snapshots consequences of one
semantic result rather than independent key-only claims.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Functional correctness certificate for the exact traced `merge_hi`
execution selected by `prepareMergeAt?`.

`exactRange` is the central result: the affected whole-entry range is exactly
the shared left-biased mathematical merge.  The remaining fields expose the
standard public sortedness, stability, whole-entry permutation, and frame
interfaces without asking downstream clients to unfold that target. -/
structure MergeHiCorrectnessPost
    (lt : BoolComparator alpha) (canonical : List (Occurrence alpha))
    (pre : MergeState (Occurrence alpha) nu) (scanned i : Nat)
    (call : MergeAtCall (Occurrence alpha) nu)
    (result : MergeHiResult (Occurrence alpha) nu) : Prop where
  safety : MergeHiSafetyPost pre scanned i call
    (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb) result
  exactRange :
    (sortSliceRangeEntries result.state.data call.ssa.toNat
      (call.na + call.nb)).toList = mergeHiTargetEntries lt call
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

/-- Functional portion proved against the untraced transcription.  Separating
this certificate from `MergeHiSafetyPost` keeps the reverse-loop induction
focused on whole-entry movement while the public join below identifies its
result with the actual traced execution by exact erasure. -/
structure MergeHiRawCorrectnessPost
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu)
    (result : MergeHiResult (Occurrence alpha) nu) : Prop where
  resultEq : mergeHi? call.state call.ssa call.ssb call.na call.nb = some result
  exactRange :
    (sortSliceRangeEntries result.state.data call.ssa.toNat
      (call.na + call.nb)).toList = mergeHiTargetEntries lt call
  frame : SortSlice.EqualOutsideRange call.state.data result.state.data
    call.ssa.toNat (call.na + call.nb)

end CPythonListsort
