/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeHiInvariant.lean -/

import Def.CPythonListsort.Code.Assembly.GallopCorrectness
import Theorem.CPythonListsort.Code.Assembly.MergeHiSafety.Part5
import Def.CPythonListsort.Code.Correctness.MergeMovementCorrectness.Part2
import Structure.CPythonListsort.Code.Correctness.MergeSemanticPre
import Def.CPythonListsort.Code.Correctness.SortSliceRange
import Def.CPythonListsort.Code.Correctness.StableMerge
import Abbrev.CPythonListsort.Code.Correctness.MergeHiInvariant
/-!
# Semantic invariant for `merge_hi`

The safety invariant for `merge_hi` deliberately records only cursor geometry,
storage validity, and stable state fields.  Functional correctness needs a
separate immutable snapshot of the two post-trimming runs and a description of
the suffix already filled by the right-to-left loop.  This module introduces
that semantic vocabulary without changing the reviewed safety certificate.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Functional invariant of every live `merge_hi` cursor.

`remainingTarget` and `filledTarget` are the two halves of the immutable target
at the current count boundary.  `lowSentinel` is deliberately about the first
entries of the two retained runs, not the moving high-end heads.  Together with
`rightPositive`, it is the correctness-only fact excluding CPython's
inconsistent-comparator `nb == 0` hedge; that branch remains present and
safety-checked in the evaluator. -/
structure MergeHiSemanticCursorInvariant
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu)
    (cursor : MergeHiCursor (Occurrence alpha) nu) : Prop where
  safety : MergeHiCursorInvariant (mergeHiAllocated call).state call.nb cursor
  basea_eq : cursor.basea = call.ssa
  comparator : cursor.state.key_compare = occurrenceComparator lt
  leftCount : cursor.na <= call.na
  rightCount : cursor.nb <= call.nb
  rightPositive : 0 < cursor.nb
  activeLeft :
    (sortSliceRangeEntries cursor.state.data call.ssa.toNat cursor.na).toList =
      (mergeHiLeftEntries call).take cursor.na
  activeRight :
    MergeHiTempPrefixMatches cursor.state.a (mergeHiRightEntries call) cursor.nb
  remainingTarget :
    stableEntryMerge lt
        ((mergeHiLeftEntries call).take cursor.na)
        ((mergeHiRightEntries call).take cursor.nb) =
      (mergeHiTargetEntries lt call).take (cursor.na + cursor.nb)
  filledTarget :
    mergeHiFilledEntries call cursor =
      (mergeHiTargetEntries lt call).drop (cursor.na + cursor.nb)
  frame :
    SortSlice.EqualOutsideRange call.state.data cursor.state.data
      call.ssa.toNat (call.na + call.nb)
  lowSentinel :
    ∃ leftFirst rightFirst,
      cursor.state.data.read? call.ssa = some leftFirst ∧
      mergeHiTempRead? cursor.state.a 0 = some rightFirst ∧
      lt rightFirst.key.value leftFirst.key.value = true

end CPythonListsort
