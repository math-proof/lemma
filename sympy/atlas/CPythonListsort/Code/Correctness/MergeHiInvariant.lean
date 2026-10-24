/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeHiInvariant.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.GallopCorrectness
import sympy.atlas.CPythonListsort.Code.Assembly.MergeHiSafety
import sympy.atlas.CPythonListsort.Code.Correctness.MergeMovementCorrectness
import sympy.atlas.CPythonListsort.Code.Correctness.MergeSemanticPre
import sympy.atlas.CPythonListsort.Code.Correctness.SortSliceRange
import sympy.atlas.CPythonListsort.Code.Correctness.StableMerge

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

/-- `merge_hi` consumes exactly the shared post-trimming semantic contract.
The direction-specific name is retained as an abbreviation so downstream
statements remain readable while both merge directions are definitionally
obligated to the same predicate shape. -/
abbrev MergeHiSemanticPre
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu) : Prop :=
  MergeSemanticPre lt call

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

/-! ## Terminal semantic effects -/

/-- If the sole right entry is strictly below every remaining left entry,
left-biased stable merge emits it first and then the untouched left list. -/
theorem stableEntryMerge_singleton_right_of_all_lt
    (lt : BoolComparator alpha)
    (right : SortSliceEntry (Occurrence alpha) nu) :
    ∀ left : List (SortSliceEntry (Occurrence alpha) nu),
      (∀ leftEntry ∈ left,
        lt right.key.value leftEntry.key.value = true) →
      stableEntryMerge lt left [right] = right :: left
  | [], _ => by simp [stableEntryMerge]
  | leftHead :: leftTail, hstrict => by
      unfold stableEntryMerge
      rw [List.cons_merge_cons]
      have hnot : ¬stableEntryLE lt leftHead right = true := by
        simp [stableEntryLE, stableOccurrenceLE,
          hstrict leftHead (by simp)]
      rw [if_neg hnot]
      simp
