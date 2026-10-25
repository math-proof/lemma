/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeHiInvariant.lean -/

import Def.CPythonListsort.Code.Assembly.GallopCorrectness
import Theorem.CPythonListsort.Code.Assembly.MergeHiSafety.Part5
import Def.CPythonListsort.Code.Correctness.MergeMovementCorrectness.Part2
import Structure.CPythonListsort.Code.Correctness.MergeSemanticPre
import Def.CPythonListsort.Code.Correctness.SortSliceRange
import Def.CPythonListsort.Code.Correctness.StableMerge
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

/-- Whole entries in the post-trimming left run consumed by `merge_hi`. -/
def mergeHiLeftEntries (call : MergeAtCall (Occurrence alpha) nu) :
    List (SortSliceEntry (Occurrence alpha) nu) :=
  (sortSliceRangeEntries call.state.data call.ssa.toNat call.na).toList

/-- Whole entries in the post-trimming right run copied to temporary storage. -/
def mergeHiRightEntries (call : MergeAtCall (Occurrence alpha) nu) :
    List (SortSliceEntry (Occurrence alpha) nu) :=
  (sortSliceRangeEntries call.state.data call.ssb.toNat call.nb).toList

/-- Shared mathematical target of the physical right-to-left merge. -/
def mergeHiTargetEntries (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu) :
    List (SortSliceEntry (Occurrence alpha) nu) :=
  stableEntryMerge lt (mergeHiLeftEntries call) (mergeHiRightEntries call)

/-- Entries in the main-data suffix already filled by a live backward cursor. -/
def mergeHiFilledEntries (call : MergeAtCall (Occurrence alpha) nu)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    List (SortSliceEntry (Occurrence alpha) nu) :=
  (sortSliceRangeEntries cursor.state.data
    (call.ssa.toNat + cursor.na + cursor.nb)
    (call.na + call.nb - (cursor.na + cursor.nb))).toList

/-- Pointwise whole-entry description of the initialized temporary prefix.

Using reads rather than the optional-cell representation keeps the invariant
aligned with both the reviewed prefix materializer and the direct traced gallop
source. -/
def MergeHiTempPrefixMatches
    (storage : TempStorage (Occurrence alpha) nu)
    (right : List (SortSliceEntry (Occurrence alpha) nu))
    (count : Nat) : Prop :=
  count <= right.length ∧
    ∀ i, i < count →
      mergeHiTempRead? storage (Int.ofNat i) = right[i]?

end CPythonListsort
